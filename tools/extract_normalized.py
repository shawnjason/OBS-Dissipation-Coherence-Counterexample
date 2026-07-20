from __future__ import annotations
import argparse
from pathlib import Path
import zipfile

ap = argparse.ArgumentParser()
ap.add_argument('archive')
ap.add_argument('destination')
a = ap.parse_args()
archive = Path(a.archive)
dest = Path(a.destination)
dest.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(archive) as zf:
    for info in zf.infolist():
        name = info.filename.replace('\\', '/')
        if not name or name.endswith('/'):
            (dest / name).mkdir(parents=True, exist_ok=True)
            continue
        out = dest / name
        out.parent.mkdir(parents=True, exist_ok=True)
        with zf.open(info) as src, out.open('wb') as dst:
            dst.write(src.read())
print(dest.resolve())
