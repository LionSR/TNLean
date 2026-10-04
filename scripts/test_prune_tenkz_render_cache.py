#!/usr/bin/env python3
"""Standard-library CLI regressions for tenkz render-cache pruning."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("prune_tenkz_render_cache.py")
KEPT = "tenkz-0123456789abcdef"
STALE = "tenkz-fedcba9876543210"


class PruneRenderCacheTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.web = self.root / "web"
        self.cache = self.root / "compile-cache"

    def write(self, path: Path, text: str = "cached product") -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def run_pruner(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--web-root", str(self.web),
             "--compile-cache", str(self.cache)],
            capture_output=True, text=True, check=False,
        )

    def seed_products(self, name: str) -> list[Path]:
        paths = [self.web / "tenkz_svg" / f"{name}.svg"]
        paths.extend(self.cache / f"{name}.{suffix}"
                     for suffix in ("tex", "pdf", "aux", "log", "events.json"))
        for path in paths:
            self.write(path)
        return paths

    def test_preserves_referenced_products_and_removes_stale_products(self) -> None:
        kept = self.seed_products(KEPT)
        stale = self.seed_products(STALE)
        self.write(self.web / "index.html", "<html>No figures here.</html>")
        self.write(self.web / "chapters" / "example.html",
                   f'<img src="../tenkz_svg/{KEPT}.svg">')
        unrelated = [self.web / "tenkz_svg" / "logo.svg", self.cache / "README"]
        for path in unrelated:
            self.write(path)
        directory = self.cache / f"{STALE}.directory"
        directory.mkdir()

        result = self.run_pruner()

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("kept 1 pictures; removed 1 SVGs and 5 compile products", result.stdout)
        for path in kept + unrelated:
            self.assertEqual(path.read_text(encoding="utf-8"), "cached product")
        for path in stale:
            self.assertFalse(path.exists(), path)
        self.assertTrue(directory.is_dir())
        # Repeating the operation does not delete referenced products.
        repeated = self.run_pruner()
        self.assertEqual(repeated.returncode, 0, repeated.stderr)
        self.assertIn("removed 0 SVGs and 0 compile products", repeated.stdout)

    def test_zero_figure_build_prunes_every_cached_picture(self) -> None:
        products = self.seed_products(STALE)
        self.write(self.web / "index.html", "<html>Blueprint without diagrams.</html>")

        result = self.run_pruner()

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("kept 0 pictures; removed 1 SVGs and 5 compile products", result.stdout)
        for path in products:
            self.assertFalse(path.exists(), path)
        self.assertTrue((self.web / "index.html").is_file())

    def test_missing_or_pageless_build_preserves_cache(self) -> None:
        for state in ("missing", "empty", "assets-only", "html-directory"):
            with self.subTest(state=state):
                self.web = self.root / state
                product = self.cache / f"{STALE}.pdf"
                self.write(product)
                if state != "missing":
                    self.web.mkdir()
                if state == "assets-only":
                    self.write(self.web / "tenkz_svg" / f"{STALE}.svg")
                if state == "html-directory":
                    (self.web / "index.html").mkdir()

                result = self.run_pruner()

                self.assertNotEqual(result.returncode, 0)
                self.assertIn("no generated HTML pages", result.stderr)
                self.assertTrue(product.is_file())
                if state == "assets-only":
                    self.assertTrue((self.web / "tenkz_svg" / f"{STALE}.svg").is_file())

    def test_valid_build_without_cache_directories_succeeds(self) -> None:
        self.write(self.web / "index.html", "<html>No diagrams.</html>")

        result = self.run_pruner()

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("removed 0 SVGs and 0 compile products", result.stdout)


if __name__ == "__main__":
    unittest.main()
