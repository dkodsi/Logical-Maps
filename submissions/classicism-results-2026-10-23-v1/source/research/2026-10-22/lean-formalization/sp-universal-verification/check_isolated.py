#!/usr/bin/env python3
"""Run the source-fingerprinted helper with an isolated output cache and logs."""
import importlib.util
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
CACHE = Path('/tmp/classicism-sp-universal-cache')
if not CACHE.is_dir():
    raise SystemExit('The isolated compiler cache must already exist; no pre-lock seeding is permitted.')
spec = importlib.util.spec_from_file_location('sp_universal_check_module', HERE.parent / 'check_module.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
module.HANDOFF = HERE
sys.argv.extend(['--cache', str(CACHE)])
print(f'Isolated verification wrapper PID: {os.getpid()}', flush=True)
module.main()
