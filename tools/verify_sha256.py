from __future__ import annotations
import hashlib
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
manifest = root / 'SHA256SUMS.txt'
failed = []
checked = 0
for raw in manifest.read_text(encoding='utf-8-sig').splitlines():
    if not raw.strip():
        continue
    digest, rel = raw.split('  ', 1)
    p = root / rel
    if not p.is_file():
        failed.append((rel, 'missing'))
        continue
    h = hashlib.sha256(p.read_bytes()).hexdigest()
    checked += 1
    if h != digest:
        failed.append((rel, f'{h} != {digest}'))
print(f'checked {checked} files')
if failed:
    for item in failed:
        print('FAIL', *item)
    sys.exit(1)
print('PASS: repository SHA-256 manifest verified')
