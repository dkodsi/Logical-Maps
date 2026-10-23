#!/usr/bin/env python3
"""Relocate a saved manifest's exact sources and invoke the original serial checker.
Requires an existing matching Lean/Mathlib installation; never downloads.
The default prints a plan. Compilation requires --run explicitly.
"""
import argparse,json,shutil,subprocess,sys
from pathlib import Path

def main():
    p=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser();ap.add_argument('--manifest',required=True);ap.add_argument('--lean',required=True)
    ap.add_argument('--precompiled-root',action='append',default=[]);ap.add_argument('--cache',type=Path,required=True)
    ap.add_argument('--timeout',type=int,default=180);ap.add_argument('--lock-wait',type=int,default=30);ap.add_argument('--run',action='store_true')
    a=ap.parse_args();audit=json.loads((p/'CERTIFICATE-AUDIT.json').read_text())
    entry=next((e for e in audit['manifests'] if e['path']==a.manifest or Path(e['path']).name==a.manifest),None)
    if entry is None:raise SystemExit('Manifest not in release certificate audit')
    if entry['format']=='legacy':raise SystemExit('Legacy manifest: use its archived driver and reproduction notes; no per-file source map was recorded')
    if entry['missing_or_changed']:raise SystemExit('This manifest has missing or changed source files; inspect CERTIFICATE-AUDIT.json before reproducing it')
    root=p/'source';m=json.loads((root/entry['path']).read_text());deps=json.loads((p/'DEPENDENCY-SOURCES.json').read_text())
    by_key={(e['module'],e['sha256']):e for e in deps['entries']}
    staged=a.cache.resolve()/'recorded-external-sources'
    cmd=[sys.executable,str(root/'research/2026-10-22/lean-formalization/check_module.py'),'--lean',str(Path(a.lean).resolve()),'--cache',str(a.cache.resolve()),'--source-root',str(staged),'--timeout',str(a.timeout),'--lock-wait',str(a.lock_wait)]
    for r in a.precompiled_root:cmd += ['--precompiled-root',str(Path(r).resolve())]
    targets=[]
    for target in m['modules']:
        if target.endswith('.lean') and Path(target).is_absolute():
            original=json.loads((p/'PROVENANCE.json').read_text())['original_workspace'];target=str(Path(target).relative_to(original))
        targets.append(target)
    if any('MaxAtomicityInconsistency' in t for t in targets):
        targets=['Mathlib.Lean.Expr.Rat','Mathlib.Algebra.Order.Ring.Unbundled.Rat','Mathlib.Tactic.Ring.Basic','Mathlib.Data.PNat.Basic','Mathlib.Util.AtomM.Recurse']+targets
    cmd += targets
    print(json.dumps({'command':cmd,'cwd':str(root),'run_requested':a.run},indent=2))
    if not a.run:return
    if not a.precompiled_root:raise SystemExit('Provide the pinned dependency binary roots; the toolchain alone is insufficient')
    for mod,s in m['sources'].items():
        e=by_key.get((mod,s['sha256']))
        if e:
            dest=staged/(mod.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p/e['package_path'],dest)
    raise SystemExit(subprocess.call(cmd,cwd=root))
if __name__=='__main__':main()
