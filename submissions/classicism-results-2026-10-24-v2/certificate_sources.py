#!/usr/bin/env python3
"""Verify selected exact certificate sources; optionally materialize one closure.
Uses only the standard library. Does not compile, download, or modify certificates.
"""
import argparse
import hashlib
import json
from pathlib import Path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--certificate', help='Selected receipt ID from evidence/CERTIFICATES.json')
    parser.add_argument('--output', type=Path, help='New, empty destination for the selected module closure')
    args = parser.parse_args()
    root = args.root.resolve()
    index = json.loads((root / 'evidence/CERTIFICATES.json').read_text())
    selected = [x for x in index['certificates'] if not args.certificate or x['id'] == args.certificate]
    if not selected:
        parser.error('No matching certificate')
    if args.output and (not args.certificate or len(selected) != 1):
        parser.error('--output requires one --certificate')
    failures, files, modules, receipts = [], {}, {}, []

    def checked(path, expected):
        p = (root / path).resolve()
        if not p.is_relative_to(root):
            failures.append(path + ': outside package')
            return b''
        try:
            data = p.read_bytes()
        except OSError:
            failures.append(path + ': missing')
            return b''
        if digest(data) != expected:
            failures.append(path + ': hash mismatch')
        files[path] = expected
        return data

    for entry in selected:
        receipt = json.loads((root / entry['path']).read_text())
        receipts.append(receipt['id'])
        original_bytes = checked(receipt['source_manifest_path'], receipt['source_manifest_sha256'])
        if not original_bytes:
            continue
        original = json.loads(original_bytes)
        successes = {x['module']: x for x in original['checked'] if x.get('exit_code') == 0}
        sources = {x['module']: x for x in receipt['sources']}
        for target in receipt['selected_targets']:
            if target not in successes or target not in sources:
                failures.append(receipt['id'] + ': target lacks successful exact source record: ' + target)
        for module, source in sources.items():
            checked(source['path'], source['sha256'])
            if module not in successes or original['sources'].get(module, {}).get('sha256') != source['sha256']:
                failures.append(receipt['id'] + ': source not authenticated by original successful record: ' + module)
            if args.output:
                modules[module] = source
        for log in receipt['logs']:
            data = checked(log['path'], log['sha256'])
            if b'sorryAx' in data:
                failures.append(log['path'] + ': sorryAx in principal log')
            if log['module'] not in receipt['selected_targets']:
                failures.append(log['path'] + ': unexpected principal log')
        if receipt['selected_targets_exit_code'] != 0:
            failures.append(receipt['id'] + ': nonzero selected-target verdict')

    if failures:
        print(json.dumps({'failures': failures, 'lean_compilation_performed': False}, indent=2))
        raise SystemExit(1)
    if args.output:
        dest = args.output.resolve()
        if dest == root or dest.is_relative_to(root):
            parser.error('Materialize outside the verified package')
        if dest.exists() and any(dest.iterdir()):
            parser.error('Output directory must be absent or empty')
        dest.mkdir(parents=True, exist_ok=True)
        for module, source in modules.items():
            target = dest / (module.replace('.', '/') + '.lean')
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((root / source['path']).read_bytes())
        (dest / 'certificate.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'certificates': receipts, 'verified_evidence_files': len(files),
                      'materialized_modules': len(modules) if args.output else 0,
                      'failures': [], 'lean_compilation_performed': False}))


if __name__ == '__main__':
    main()
