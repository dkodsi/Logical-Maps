#!/usr/bin/env python3
"""Use only the pinned, precompiled dependency roots recorded beside this file."""
import json, subprocess, sys
from pathlib import Path
p = Path(__file__).resolve().parent
config = json.loads((p / "mathlib-dependencies.json").read_text())
args = [sys.executable, str(p / "check_module.py"), "--lean", config["compiler"]]
for root in config["precompiled_roots"]:
    args += ["--precompiled-root", root]
raise SystemExit(subprocess.call(args + sys.argv[1:], cwd=p.parents[2]))
