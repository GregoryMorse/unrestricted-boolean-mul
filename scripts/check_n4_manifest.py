"""Verify the exact n4 proof/configuration snapshot; never accept a partial list."""
import hashlib
from pathlib import Path
import sys

from ci_verify import ROOT, inspect

EXTRA = {
    'Challenge.lean', 'Solution.lean', 'comparator.json', 'formalization.yaml',
    'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'LICENSE',
    'README.md', 'CITATION.cff', 'n4/README.md', 'n4/AXIOM_AUDIT.txt',
    'n4/PALOMAR_AUDIT.md', 'n4/SUBMISSION.md',
    '.github/workflows/lean.yml', '.github/workflows/palomar.yml',
    'scripts/ci_verify.py', 'scripts/test_ci_verify.py', 'scripts/check_n4_manifest.py',
}


def expected():
    files = set(inspect('n4')['source_sha256']) | EXTRA
    return {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(files)}


def main():
    values = expected()
    lines = [f'{digest}  {name}' for name, digest in values.items()]
    if '--print' in sys.argv:
        print('\n'.join(lines))
        return
    actual = (ROOT / 'n4/LEAN_SHA256SUMS.txt').read_text(encoding='utf-8').splitlines()
    if actual != lines:
        raise SystemExit('n4 manifest does not match the complete current proof/configuration closure')
    print(f'N4_SOURCE_MANIFEST_PASS files={len(lines)}')


if __name__ == '__main__':
    main()
