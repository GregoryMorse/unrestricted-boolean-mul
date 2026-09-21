"""Scoped serial CI: no aggregate research build and no assumed axiom pass.

Linux builds use one CPU, one Lean thread, an 8-GiB Lean heap (Lakefile),
and a 12-GiB virtual-address limit, on runners with at least 14 GiB of RAM.
No heavy build runs on Windows.
Mathlib's pinned binary cache must be restored before --build.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PROFILES = {
    "n4": ("AxiomAudit.lean", ("UnrestrictedBooleanMul",)),
    "n5": ("n5/Paper2Audit.lean", (
        "UnrestrictedBooleanMul.N5.Capacity",
        "UnrestrictedBooleanMul.N5.QuadraticFlattening",
        "UnrestrictedBooleanMul.N5.Upper")),
    "models-upper": ("n6/UpperAudit.lean", ("UnrestrictedBooleanMul.N6.Upper",)),
    "n6-bilinear": ("n6/BilinearAudit.lean", (
        "UnrestrictedBooleanMul.PolynomialOrbits",
        "UnrestrictedBooleanMul.PolynomialProfile")),
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def code_only(text: str) -> str:
    """Erase nested Lean comments and strings, preserving newlines."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1; i += 2; continue
            if pair == "-/":
                depth -= 1; i += 2; continue
            out.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            if text[i] == "\\":
                out.extend("  "); i += 2
            else:
                string = text[i] != '"'
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif pair == "/-":
            depth = 1; out.append(" "); i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True; out.append(" "); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(out)


def imports(path: Path) -> list[str]:
    result = []
    for line in code_only(path.read_text(encoding="utf-8")).splitlines():
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)?import\s+(.*)$", line)
        if match:
            result.extend(match[1].split())
    return result


def closure(roots: tuple[str, ...], repo: Path = ROOT) -> list[str]:
    done, visiting, ordered = set(), set(), []
    def visit(module):
        if module in done:
            return
        if module in visiting:
            raise ValueError(f"cyclic local import: {module}")
        path = repo / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise ValueError(f"missing local module: {module}")
        visiting.add(module)
        for dep in imports(path):
            if dep == "Challenge":
                raise ValueError("a proved profile imports the admitted Challenge")
            if dep.startswith("UnrestrictedBooleanMul"):
                visit(dep)
        visiting.remove(module); done.add(module); ordered.append(module)
    for root in roots:
        visit(root)
    return ordered


def validate_axioms(output: str, expected: list[str]) -> dict[str, list[str]]:
    found = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
    for name, values in re.findall(pattern, output):
        axioms = {v.strip() for v in values.split(",") if v.strip()}
        if axioms - ALLOWED:
            raise ValueError(f"forbidden axioms for {name}: {sorted(axioms - ALLOWED)}")
        if name in found:
            raise ValueError(f"duplicate audit: {name}")
        found[name] = sorted(axioms)
    if set(found) != set(expected) or len(expected) != len(set(expected)):
        raise ValueError(f"audit names differ: missing={set(expected)-set(found)}, extra={set(found)-set(expected)}")
    return found


def inspect(profile: str) -> dict:
    audit, roots = PROFILES[profile]
    modules = closure(roots)
    files = [m.replace(".", "/") + ".lean" for m in modules] + [audit]
    for name in files:
        code = code_only((ROOT / name).read_text(encoding="utf-8"))
        if re.search(r"\b(sorry|admit|native_decide|bv_decide|ofReduceBool)\b|^\s*axiom\s", code, re.M):
            raise ValueError(f"proof escape hatch in {name}")
    if profile == "n4" and any(".N5" in m or ".N6" in m or m.endswith(".Research") for m in modules):
        raise ValueError("research leaked into the n4 dependency closure")
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / audit).read_text(encoding="utf-8"), re.M)
    if not expected:
        raise ValueError("empty axiom audit")
    if set(imports(ROOT / audit)) != set(roots):
        raise ValueError("audit imports differ from the declared build roots")
    return {"profile": profile, "roots": roots, "modules": modules, "audit": audit,
            "expected_axioms": expected,
            "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in files}}


def validate_runner_memory(physical_bytes: int):
    # Leave room for the runner and the small parent Lake process. The prior
    # 4-GiB experiment failed in n4 QuarticIdempotence; the earlier 4.33.1
    # recheck passed the entire n4 chain at 8 GiB. Never silently remove caps.
    if physical_bytes < 14 * 1024**3:
        raise RuntimeError('This bounded proof build requires at least 14 GiB of runner RAM.')


def limits():
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (12 * 1024**3, 12 * 1024**3))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})


def run(argv: list[str], report: dict, timeout: int = 900) -> str:
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    start = time.monotonic()
    proc = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                            start_new_session=True, preexec_fn=limits)
    try:
        output, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        output, _ = proc.communicate()
        report["commands"].append({"argv": argv, "timeout": timeout, "output": output})
        raise RuntimeError(f"bounded command timed out: {argv}")
    report["commands"].append({"argv": argv, "exit_code": proc.returncode,
                               "seconds": round(time.monotonic() - start, 3), "output": output})
    print(output, end="", flush=True)
    if proc.returncode:
        raise RuntimeError(f"command failed ({proc.returncode}): {argv}")
    return output


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=PROFILES, required=True)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = inspect(args.profile)
    if not args.build:
        print(json.dumps(report, indent=2) if args.json else f"{args.profile}: {len(report['modules'])} local modules; source checks passed")
        return 0
    if sys.platform != "linux":
        raise SystemExit("Heavy proof builds are Linux-only; use the scoped GitHub workflow.")
    physical_bytes = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
    validate_runner_memory(physical_bytes)
    report['resource_limits'] = {'lean_heap_mib': 8192, 'address_space_gib': 12,
                                 'cpu_workers': 1, 'physical_memory_bytes': physical_bytes}
    report.update(complete=False, commands=[])
    output_path = ROOT / ".lake" / "ci" / f"{args.profile}.json"
    output_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        version = run(["lake", "env", "lean", "--version"], report)
        if "version 4.33.1" not in version or "819816b2e0a3" not in version:
            raise ValueError(f"unexpected compiler: {version}")
        for module in report["modules"]:
            print(f"Building {module}", flush=True)
            run(["lake", "build", module], report)
        output = run(["lake", "env", "lean", "-j1", "-M8192", report["audit"]], report)
        report["axioms"] = validate_axioms(output, report["expected_axioms"])
        if args.profile == "n4":
            run(["lake", "build"], report)
            run(["lake", "build", "Challenge"], report)
            run(["lake", "build", "Solution"], report)
        if args.replay:
            for module in report["roots"]:
                run(["lake", "env", "leanchecker", module], report, timeout=2400)
        report["complete"] = True
        return 0
    finally:
        output_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    raise SystemExit(main())
