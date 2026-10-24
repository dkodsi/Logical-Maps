#!/usr/bin/env python3
"""Focused checker regression tests; uses a tiny fake compiler, never Lean."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
RUNNER = HERE / "check_module.py"
spec = importlib.util.spec_from_file_location("checker_under_test", RUNNER)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class CheckerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="classicism-checker-test-")
        self.root = Path(self.temporary.name)
        # These subprocesses only invoke the fake compiler. Keep their shared
        # test lock separate from active real verification jobs.
        self.lock = self.root / "fake-compiler.lock"
        self.lock_patch = patch.object(checker, "GLOBAL_LOCK", self.lock)
        self.lock_patch.start()
        self.source = self.root / "source"
        self.source.mkdir()
        self.cache = self.root / "cache"
        self.handoff = self.root / "handoff"
        self.driver = self.root / "driver.py"
        self.driver.write_text(
            "import importlib.util, os\nfrom pathlib import Path\n"
            f"spec=importlib.util.spec_from_file_location('checker', {str(RUNNER)!r})\n"
            "module=importlib.util.module_from_spec(spec)\nspec.loader.exec_module(module)\n"
            "module.HANDOFF=Path(os.environ['TEST_HANDOFF'])\n"
            "module.GLOBAL_LOCK=Path(os.environ['TEST_LOCK'])\nmodule.main()\n")
        self.compiler = self.root / "fake-lean"
        self.compiler.write_text(f"#!{sys.executable}\n" + """
import json, os, pathlib, sys, time
if '--version' in sys.argv:
    print('Fake Lean test compiler 1')
    raise SystemExit(0)
source = pathlib.Path(sys.argv[-1])
data = source.read_text()
marker = os.environ.get('TEST_MARKER')
if marker:
    pathlib.Path(marker).write_text(str(os.getpid()))
if 'SLEEP' in data:
    time.sleep(1.5)
    data = source.read_text()
if 'CHECK_OVERLAY' in data:
    root = pathlib.Path(os.environ['LEAN_PATH'])
    assert (root / 'Mathlib/Base.olean').read_text() == 'pinned base'
    assert (root / 'Mathlib/Other.olean').read_text() == 'pinned other'
    assert (root / 'Mathlib/Local.olean').read_text().startswith('artifact:')
    assert (root / 'Mathlib/Base.ir.sig').read_text() == 'pinned IR signature'
    assert (root / 'Mathlib/Base.ir.sig.hash').read_text() == 'pinned signature hash'
out = pathlib.Path(sys.argv[sys.argv.index('-o') + 1])
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text('artifact:' + data)
pathlib.Path(str(out) + '.private').write_text('private:' + data)
out.with_suffix('.ir.sig').write_text('IR signature:' + data)
if 'FAIL' in data:
    print('error: deliberate fake failure')
    raise SystemExit(1)
if 'AUDIT_BAD' in data:
    print('fake audit: 1 of 2 theorems derived')
if os.environ.get('TEST_DONE'):
    pathlib.Path(os.environ['TEST_DONE']).write_text('done')
""")
        self.compiler.chmod(0o755)

    def tearDown(self):
        self.lock_patch.stop()
        self.temporary.cleanup()

    def write(self, name, content):
        target = self.source / (name.replace(".", "/") + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)
        return target

    def command(self, modules=("Demo",), cache=None, extra=()):
        return [sys.executable, str(self.driver), *modules, "--lean", str(self.compiler),
                "--source-root", str(self.source), "--cache", str(cache or self.cache),
                "--lock-wait", "0", "--timeout", "5", *extra]

    def environment(self, handoff=None, **extra):
        return dict(os.environ, TEST_HANDOFF=str(handoff or self.handoff),
                    TEST_LOCK=str(self.lock), **extra)

    def run_check(self, modules=("Demo",), cache=None, extra=(), **env):
        result = subprocess.run(self.command(modules, cache, extra),
                                env=self.environment(**env), text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=10)
        return result

    def report(self):
        return json.loads((self.handoff / "last-check.json").read_text())

    def wait_file(self, path, process=None):
        deadline = time.monotonic() + 5
        while not path.exists():
            if process is not None and process.poll() is not None:
                self.fail("Fake compiler wrapper exited before marker: " + process.communicate()[0])
            self.assertLess(time.monotonic(), deadline)
            time.sleep(0.02)

    def test_reuse_tampering_and_legacy_stamp(self):
        self.write("Demo", "good")
        self.assertEqual(self.run_check().returncode, 0)
        self.assertEqual(self.run_check().returncode, 0)
        self.assertTrue(self.report()["checked"][0]["reused"])
        for suffix in (".olean", ".olean.private", ".ir.sig"):
            (self.cache / ("Demo" + suffix)).write_text("tampered")
            self.assertEqual(self.run_check().returncode, 0)
            self.assertNotIn("reused", self.report()["checked"][0])
        (self.cache / "Demo.artifacts.json").unlink()
        self.assertEqual(self.run_check().returncode, 0)
        self.assertNotIn("reused", self.report()["checked"][0])

    def test_failed_rebuild_preserves_prior_cache(self):
        source = self.write("Demo", "good")
        self.assertEqual(self.run_check().returncode, 0)
        before = {p.name: p.read_bytes() for p in self.cache.glob("Demo.*")}
        source.write_text("FAIL")
        self.assertEqual(self.run_check().returncode, 1)
        self.assertEqual(before, {p.name: p.read_bytes() for p in self.cache.glob("Demo.*")})
        self.assertFalse(self.report()["complete"])
        self.assertEqual(self.report()["state"], "failed")

    def test_incomplete_audit_is_failure_without_publication(self):
        self.write("Demo", "AUDIT_BAD")
        self.assertEqual(self.run_check().returncode, 1)
        self.assertFalse((self.cache / "Demo.olean").exists())
        self.assertEqual(self.report()["checked"][0]["exit_code"], 1)

    def test_keep_going_reports_skipped_dependencies_and_independent_success(self):
        self.write("Bad", "FAIL")
        self.write("Needs", "import Bad")
        self.write("Independent", "good")
        result = self.run_check(modules=("Needs", "Independent"), extra=("--keep-going",))
        self.assertEqual(result.returncode, 1, result.stdout)
        outcomes = {entry["module"]: entry["exit_code"] for entry in self.report()["checked"]}
        self.assertEqual(outcomes, {"Bad": 1, "Needs": 125, "Independent": 0})
        self.assertFalse(self.report()["complete"])
        self.assertEqual(self.report()["state"], "failed")

    def test_timeout_preserves_prior_cache_and_releases_lock(self):
        source = self.write("Demo", "good")
        self.assertEqual(self.run_check().returncode, 0)
        before = {p.name: p.read_bytes() for p in self.cache.glob("Demo.*")}
        source.write_text("SLEEP")
        result = self.run_check(extra=("--timeout", "1"))
        self.assertEqual(result.returncode, 124, result.stdout)
        self.assertEqual(before, {p.name: p.read_bytes() for p in self.cache.glob("Demo.*")})
        self.assertEqual(self.report()["state"], "failed")
        source.write_text("good")
        self.assertEqual(self.run_check().returncode, 0)

    def test_cross_handoff_and_cache_global_lock(self):
        self.write("Demo", "SLEEP")
        marker = self.root / "started"
        process = subprocess.Popen(self.command(), env=self.environment(TEST_MARKER=str(marker)),
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        try:
            self.wait_file(marker, process)
            other = self.run_check(cache=self.root / "other-cache", handoff=self.root / "other-handoff")
            self.assertEqual(other.returncode, 75, other.stdout)
            self.assertFalse((self.root / "other-cache").exists())
        finally:
            output = process.communicate(timeout=8)[0]
        self.assertEqual(process.returncode, 0, output)

    def test_parent_death_keeps_lock_until_compiler_exits(self):
        self.write("Demo", "SLEEP")
        marker, done = self.root / "started", self.root / "done"
        process = subprocess.Popen(self.command(), env=self.environment(
            TEST_MARKER=str(marker), TEST_DONE=str(done)), stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True)
        self.wait_file(marker, process)
        process.kill()
        process.communicate(timeout=3)
        try:
            other = self.run_check(cache=self.root / "other-cache", handoff=self.root / "other-handoff")
            self.assertEqual(other.returncode, 75, other.stdout)
        finally:
            self.wait_file(done)
        # The completion marker precedes process exit by a tiny interval.
        deadline = time.monotonic() + 3
        while True:
            try:
                with checker.compiler_lock(0, {"test": "released"}):
                    break
            except checker.BusyError:
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.02)

    def test_snapshot_compilation_and_live_source_drift(self):
        source = self.write("Demo", "SLEEP old bytes")
        marker = self.root / "started"
        process = subprocess.Popen(self.command(), env=self.environment(TEST_MARKER=str(marker)),
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        self.wait_file(marker, process)
        source.write_text("new bytes")
        output = process.communicate(timeout=8)[0]
        self.assertEqual(process.returncode, 3, output)
        self.assertEqual((self.cache / "Demo.olean").read_text(), "artifact:SLEEP old bytes")
        self.assertEqual(self.report()["source_drift"], ["Demo"])
        snapshot = Path(self.report()["source_snapshot"]) / "Demo.lean"
        self.assertEqual(snapshot.read_text(), "SLEEP old bytes")
        self.assertFalse(self.report()["complete"])

    def test_capture_retries_changes_before_snapshot(self):
        source = self.write("Demo", "first")
        original = Path.read_bytes
        calls = 0

        def changing_read(path):
            nonlocal calls
            if path == source:
                calls += 1
                if calls == 2:
                    source.write_text("second")
            return original(path)

        with patch.object(Path, "read_bytes", changing_read):
            ordered, _, _ = checker.capture_sources(argparse.Namespace(modules=["Demo"]),
                                                     [self.source], [])
        self.assertEqual(ordered[0][3], b"second")
        self.assertGreaterEqual(calls, 4)

    def test_merged_import_overlay_excludes_stale_cache(self):
        binary = self.root / "pinned"
        (binary / "Mathlib").mkdir(parents=True)
        (binary / "Mathlib/Base.olean").write_text("pinned base")
        (binary / "Mathlib/Other.olean").write_text("pinned other")
        (binary / "Mathlib/Base.ir.sig").write_text("pinned IR signature")
        (binary / "Mathlib/Base.ir.sig.hash").write_text("pinned signature hash")
        (self.cache / "Mathlib").mkdir(parents=True)
        (self.cache / "Mathlib/Base.olean").write_text("stale cache base")
        self.write("Mathlib.Local", "local module")
        self.write("Demo", "import Mathlib.Local Mathlib.Base Mathlib.Other\nCHECK_OVERLAY")
        result = self.run_check(extra=("--precompiled-root", str(binary)))
        self.assertEqual(result.returncode, 0, result.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
