"""Check Palomar's repository-wide Lean source policy, not just build roots.

Uses the Git index, so ignored/private local research is not a submitted source.
The official pinned Palomar workflow remains the authoritative acceptance check.
"""
from pathlib import Path
import re
import subprocess

from ci_verify import ROOT, COMPILER_VERSION


def check_source(name: str, source: str, mode: str = '100644') -> None:
    if mode == '120000':
        raise ValueError(f'{name}: Lean symlinks are not allowed')
    if len(source.splitlines()) > 10_000:
        raise ValueError(f'{name}: exceeds 10,000 physical lines')
    if Path(name).name == 'lakefile.lean':
        return
    i = 0
    while i < len(source):
        if source[i].isspace():
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end + 1
        elif source.startswith(('/--', '/-!'), i):
            raise ValueError(f'{name}: documentation must follow module')
        elif source.startswith('/-', i):
            depth, i = 1, i + 2
            while i < len(source) and depth:
                if source.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif source.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError(f'{name}: unterminated header comment')
        else:
            break
    if not re.match(r'module\b', source[i:]):
        raise ValueError(f'{name}: must begin with the module header keyword')


def main() -> None:
    expected = 'leanprover/lean4:v' + COMPILER_VERSION
    if (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip() != expected:
        raise SystemExit('lean-toolchain must pin ' + expected)
    entries = subprocess.check_output(
        ['git', 'ls-files', '--stage', '-z', '*.lean'], cwd=ROOT).decode().split('\0')
    count = 0
    for entry in filter(None, entries):
        meta, name = entry.split('\t', 1)
        mode, _, stage = meta.split()
        if stage != '0':
            raise SystemExit('Unmerged Lean source: ' + name)
        check_source(name, (ROOT / name).read_text(encoding='utf-8'), mode)
        count += 1
    if not count:
        raise SystemExit('No submitted Lean sources found')
    print(f'LEAN_SOURCE_POLICY_PASS files={count} toolchain={expected}')


if __name__ == '__main__':
    main()
