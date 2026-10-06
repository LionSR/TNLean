#!/usr/bin/env python3
"""Unit regressions for blueprint search preparation; no Pagefind needed."""

from __future__ import annotations

import contextlib
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import add_blueprint_search as search

PAGE = (
    '<html lang="en"><head><title>Normal tensors</title></head><body>'
    '<header><h1>Tensor Network Theory</h1></header><nav>Navigation only</nav>'
    '<div class="main-text"><h1>Normal tensors</h1><p>Injective tensors</p></div>'
    '</body></html>'
)


class SearchPreparationTests(unittest.TestCase):
    def test_content_and_chapter_title_are_tagged(self):
        html, injected = search._process(PAGE)
        self.assertTrue(injected)
        self.assertIn('<div class="main-text" data-pagefind-body>', html)
        self.assertIn('<title data-pagefind-meta="title">Normal tensors</title>', html)
        self.assertIn('<nav>Navigation only</nav>', html)
        self.assertEqual(html.count('data-pagefind-body'), 1)

    def test_assets_box_and_script_have_their_own_locations(self):
        html, _ = search._process(PAGE)
        self.assertLess(html.index(search.HEAD_SNIPPET), html.index('</head>'))
        self.assertLess(html.index(search.BOX_SNIPPET), html.index('</header>'))
        self.assertGreater(html.index(search.SCRIPT_SNIPPET), html.index('</header>'))
        self.assertLess(html.index(search.SCRIPT_SNIPPET), html.index('</body>'))

    def test_repeated_processing_is_byte_identical(self):
        once, _ = search._process(PAGE)
        twice, injected = search._process(once)
        self.assertEqual(once, twice)
        self.assertFalse(injected)
        self.assertEqual(twice.count('id="blueprint-search"'), 1)
        self.assertEqual(twice.count('data-pagefind-meta="title"'), 1)

    def test_headerless_page_still_has_search_but_no_index_body(self):
        page = '<html><head><title>Graphs</title></head><body>Graphs</body></html>'
        html, injected = search._process(page)
        self.assertTrue(injected)
        self.assertIn('<body>' + search.BOX_SNIPPET, html)
        self.assertNotIn('data-pagefind-body', html)

    def test_incomplete_document_gets_no_partial_ui(self):
        for page in ('<html><head></head></html>', '<body>Fragment</body>'):
            with self.subTest(page=page):
                html, injected = search._process(page)
                self.assertFalse(injected)
                self.assertNotIn(search.MARKER + ':begin', html)

    def test_python_module_is_preferred(self):
        with patch.object(search.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0)) as run:
            self.assertEqual(search._pagefind_command(), [sys.executable, '-m', 'pagefind'])
            self.assertEqual(run.call_count, 1)

    def test_installed_executable_is_used_without_downloading(self):
        with patch.object(search.subprocess, 'run', side_effect=[
            subprocess.CompletedProcess([], 1), subprocess.CompletedProcess([], 0),
        ]):
            self.assertEqual(search._pagefind_command(), ['pagefind'])

    def test_missing_pagefind_reports_pinned_installation(self):
        with patch.object(search.subprocess, 'run', side_effect=FileNotFoundError) as run:
            with self.assertRaisesRegex(SystemExit, r'pagefind\[extended\]==1.5.2'):
                search._pagefind_command()
            self.assertEqual(run.call_count, 2)

    def test_index_failure_propagates(self):
        with patch.object(search, '_pagefind_command', return_value=['pagefind']), \
                patch.object(search.subprocess, 'run', side_effect=subprocess.CalledProcessError(1, 'pagefind')):
            with self.assertRaises(subprocess.CalledProcessError):
                search._run_pagefind(Path('/unused'))

    def test_missing_search_assets_fail(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'pagefind').mkdir()
            (root / 'pagefind/pagefind-ui.js').touch()
            with patch.object(search, '_pagefind_command', return_value=['pagefind']), \
                    patch.object(search.subprocess, 'run'):
                with self.assertRaisesRegex(SystemExit, 'pagefind.js'):
                    search._run_pagefind(root)

    def test_main_rebuilds_index_without_duplicating_html(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            page = root / 'chapter.html'
            page.write_text(PAGE, encoding='utf-8')
            with patch.object(sys, 'argv', ['search', '--web-root', str(root)]), \
                    patch.object(search, '_run_pagefind') as index, \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(search.main(), 0)
                once = page.read_bytes()
                self.assertEqual(search.main(), 0)
                self.assertEqual(page.read_bytes(), once)
                self.assertEqual(index.call_count, 2)

    def test_empty_root_fails_before_indexing(self):
        with tempfile.TemporaryDirectory() as temporary:
            with patch.object(sys, 'argv', ['search', '--web-root', temporary]), \
                    patch.object(search, '_run_pagefind') as index:
                with self.assertRaisesRegex(SystemExit, 'no generated blueprint pages'):
                    search.main()
                index.assert_not_called()


if __name__ == '__main__':
    unittest.main()
