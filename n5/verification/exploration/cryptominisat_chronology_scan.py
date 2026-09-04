#!/usr/bin/env python3
"""Run the exact flag SAT probe over every defect chronology.

This driver parallelizes independent invocations of
``cryptominisat_flag_probe.py``.  A satisfying result is replayed by that
probe before it is reported.  Unsatisfying results remain discovery evidence
unless accompanied by a separately checked proof certificate.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
import time


def run_one(
    probe: Path,
    n: int,
    gates: int,
    positions: tuple[int, ...],
    timeout_seconds: float,
) -> dict[str, object]:
    command = [
        sys.executable,
        str(probe),
        str(n),
        str(gates),
        "--defect-positions=" + ",".join(map(str, positions)),
        f"--timeout-seconds={timeout_seconds}",
    ]
    started = time.monotonic()
    completed = subprocess.run(
        command,
        check=False,
        capture_output=True,
        text=True,
        timeout=timeout_seconds + 30,
    )
    elapsed = time.monotonic() - started
    lines = [line for line in completed.stdout.splitlines() if line.strip()]
    if completed.returncode or not lines:
        return {
            "defect_positions": positions,
            "result": "driver-error",
            "returncode": completed.returncode,
            "elapsed_seconds": round(elapsed, 3),
            "stderr": completed.stderr[-2000:],
        }
    report = json.loads(lines[0])
    report["wall_seconds"] = round(elapsed, 3)
    if report["result"] is True and len(lines) > 1:
        report["witness"] = json.loads(lines[1])
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=5)
    parser.add_argument("--gates", type=int, default=12)
    parser.add_argument("--workers", type=int, default=32)
    parser.add_argument("--timeout-seconds", type=float, default=60.0)
    parser.add_argument("--results-jsonl")
    args = parser.parse_args()

    target_count = 2 * args.n - 1
    defect_count = args.gates - target_count
    if defect_count < 0:
        raise ValueError("gate count is below the target dimension")

    probe = Path(__file__).with_name("cryptominisat_flag_probe.py")
    chronologies = list(combinations(range(args.gates), defect_count))
    started = time.monotonic()
    reports: list[dict[str, object]] = []
    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {
            executor.submit(
                run_one,
                probe,
                args.n,
                args.gates,
                chronology,
                args.timeout_seconds,
            ): chronology
            for chronology in chronologies
        }
        for completed, future in enumerate(as_completed(futures), start=1):
            report = future.result()
            reports.append(report)
            if report["result"] is True:
                print(json.dumps(report, sort_keys=True), flush=True)
            if completed % max(1, args.workers) == 0 or completed == len(futures):
                counts = {
                    str(value): sum(r["result"] == value for r in reports)
                    for value in (False, None, True, "driver-error")
                }
                print(json.dumps({
                    "completed": completed,
                    "total": len(futures),
                    "counts": counts,
                    "elapsed_seconds": round(time.monotonic() - started, 3),
                }, sort_keys=True), flush=True)

    reports.sort(key=lambda report: report["defect_positions"])
    if args.results_jsonl:
        output_path = Path(args.results_jsonl)
        with output_path.open("w", encoding="utf-8") as output:
            for report in reports:
                output.write(json.dumps(report, sort_keys=True) + "\n")

    print(json.dumps({
        "n": args.n,
        "gates": args.gates,
        "chronologies": len(chronologies),
        "unsat": sum(report["result"] is False for report in reports),
        "unknown": sum(report["result"] is None for report in reports),
        "sat": sum(report["result"] is True for report in reports),
        "errors": sum(report["result"] == "driver-error" for report in reports),
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
