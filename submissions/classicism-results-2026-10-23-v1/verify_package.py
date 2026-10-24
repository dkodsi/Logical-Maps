#!/usr/bin/env python3
"""Verify a directory or ZIP using only Python's standard library; never runs Lean."""
import argparse, hashlib, json
from pathlib import Path
import zipfile

def hashed(f):
    h=hashlib.sha256()
    for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--archive',type=Path);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args()
    failures=[]
    if a.archive:
        with zipfile.ZipFile(a.archive) as z:
            names=z.namelist();roots=[n[:-len('SHA256SUMS')] for n in names if n.count('/')==1 and n.endswith('/SHA256SUMS')]
            if len(roots)!=1:raise SystemExit('Expected one package root and checksum list')
            prefix=roots[0];rows=z.read(prefix+'SHA256SUMS').decode().splitlines()
            expected=set()
            for row in rows:
                sha,p=row.split('  ',1);expected.add(prefix+p)
                try:
                    with z.open(prefix+p) as f:got=hashed(f)
                    if got!=sha:failures.append(p+': hash mismatch')
                except KeyError:failures.append(p+': missing')
            actual={n for n in names if not n.endswith('/')}
            failures += ['unexpected: '+n for n in actual-expected-{prefix+'SHA256SUMS'}]
            if len(names)!=len(set(names)):failures.append('duplicate ZIP entries')
    else:
        rows=(a.root/'SHA256SUMS').read_text().splitlines();expected=set()
        for row in rows:
            sha,p=row.split('  ',1);expected.add(p)
            try:
                with (a.root/p).open('rb') as f:got=hashed(f)
                if got!=sha:failures.append(p+': hash mismatch')
            except FileNotFoundError:failures.append(p+': missing')
        actual={p.relative_to(a.root).as_posix() for p in a.root.rglob('*') if p.is_file()}
        failures += ['unexpected: '+p for p in actual-expected-{'SHA256SUMS'}]
    print(json.dumps({'verified_files':len(rows),'failures':failures,'lean_compilation_performed':False}))
    raise SystemExit(bool(failures))
if __name__=='__main__':main()
