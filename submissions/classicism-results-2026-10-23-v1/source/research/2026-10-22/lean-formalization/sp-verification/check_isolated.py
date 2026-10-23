#!/usr/bin/env python3
"""Run the existing fingerprinted checker with isolated logs and output cache."""
import importlib.util
import json
from pathlib import Path
import sys
here = Path(__file__).resolve().parent
parent = here.parent
spec = importlib.util.spec_from_file_location("sp_isolated_checker", parent / "check_module.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
checker.HANDOFF = here
sys.argv += ["--cache", "/tmp/classicism-sp-verification-cache"]
if "--mathlib" in sys.argv:
    sys.argv.remove("--mathlib")
    for root in json.loads((parent / "mathlib-dependencies.json").read_text())["precompiled_roots"]:
        sys.argv += ["--precompiled-root", root]
checker.main()
