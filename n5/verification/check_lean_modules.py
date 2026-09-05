#!/usr/bin/env python3
"""Check selected Lean sources sequentially, reusing cached dependencies.

This is a bounded Linux repair check, not a replacement for `lake build` or
the release's independent leanchecker replay.  Requested modules are always
checked; missing project dependencies are checked first.  Cached dependency
objects are reused as-is, so use Lake/CI for a complete rebuild.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import signal
import subprocess
import time


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    if args.memory_mb <= 0 or args.timeout <= 0:
        parser.error("memory and timeout must be positive")
    root = Path(__file__).resolve().parents[2]
    objects = root / ".lake/build/lib/lean"
    requested = set(args.modules)
    seen: set[str] = set()
    plan: list[str] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        if not re.fullmatch(r"UnrestrictedBooleanMul(?:\.[A-Za-z0-9_]+)*", module):
            raise ValueError(f"expected a project module, got {module!r}")
        seen.add(module)
        relative = Path(*module.split("."))
        if module not in requested and (objects / relative.with_suffix(".olean")).exists():
            return
        source = root / relative.with_suffix(".lean")
        text = source.read_text(encoding="utf-8")
        for dependency in re.findall(r"(?m)^import\s+(UnrestrictedBooleanMul[.\w]*)", text):
            visit(dependency)
        plan.append(module)

    for module in args.modules:
        visit(module)
    print(f"Checking {len(plan)} source modules; cached dependencies are reused.", flush=True)
    for module in plan:
        print(module, flush=True)
        if args.plan:
            continue
        if os.name != "posix":
            parser.error("run bounded repair checks on Linux; use CI for Windows workspaces")
        relative = Path(*module.split("."))
        output = objects / relative.with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [args.lake, "env", "lean", "-M", str(args.memory_mb),
                   "-o", str(output), str(relative.with_suffix(".lean"))]
        started = time.monotonic()
        process = subprocess.Popen(command, cwd=root, start_new_session=True)
        try:
            result = process.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise SystemExit(f"TIMEOUT after {args.timeout}s: {module}") from None
        if result:
            raise SystemExit(f"FAIL exit={result}: {module}")
        print(f"PASS {time.monotonic() - started:.2f}s: {module}", flush=True)


if __name__ == "__main__":
    main()
