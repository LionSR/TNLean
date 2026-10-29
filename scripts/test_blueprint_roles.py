#!/usr/bin/env python3
"""Unit regressions for scripts/blueprint_roles.py on a small synthetic blueprint."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import blueprint_roles as roles  # noqa: E402

CONTENT = r"""
\input{chapter/one}
\input{chapter/two}
"""

ONE = r"""\chapter{First}\label{ch:one}
Theorem~\ref{thm:main} is the point; Theorem~\ref{thm:aux} supports it.
\begin{theorem}[Main]\label{thm:main}
    \lean{Foo.main}
    \leanok
    \uses{thm:aux, def:x}
    Statement with
    \begin{enumerate}
        \item a nested item \label{it:main_a}
        \begin{theorem}[odd nesting]\label{thm:nested}
            inner
        \end{theorem}
    \end{enumerate}
    \begin{align}
        x & = y \label{eq:main}
    \end{align}
\end{theorem}
\begin{proof}
    \leanok
    \uses{thm:aux}
    By Theorem \ref{thm:aux} and Theorems~\ref{thm:aux} and~\ref{prop:p}.
\end{proof}
\begin{theorem}[Auxiliary]\label{thm:aux}
    \lean{Foo.aux}
    \leanok
    Aux.
\end{theorem}
\begin{proposition}[A proposition]\label{prop:p}
    \lean{Foo.p}
    P.
\end{proposition}
% \begin{theorem} in a comment is ignored
\begin{definition}[Def]\label{def:x}
    Definition text.
\end{definition}
"""

TWO = r"""\chapter{Second}\label{ch:two}
\input{chapter/two_body}
"""

TWO_BODY = r"""\begin{lemma}[Promoted]\label{lem:promoted}
    \lean{Bar.promoted}
    \uses{thm:main}
    Uses Theorem~\ref{thm:main}.
\end{lemma}
\begin{theorem}[Variant]\label{thm:variant}\label{thm:variant_alias}
    \lean{Bar.variant}
    Variant of Theorem~\ref{thm:main}.
\end{theorem}
\begin{corollary}[Unlisted]\label{cor:unlisted}
    By Theorem~\ref{thm:aux}, Corollary~\ref{thm:variant_alias}, and
    Theorems~\ref{thm:aux}
    and~\ref{thm:main}.
    Also Lemma~\ref{def:x} names a definition, Theorem~\ref{it:main_a}
    an item, and Propositions~\ref{prop:p}, \ref{thm:aux}, and~\ref{cor:unlisted}.
\end{corollary}
"""

ROLES = {
    "chapters": {
        "ch:one": {"theorems": ["thm:main"], "notes": {"thm:main": "the point"}},
        # Grouping is cosmetic: lem:promoted is listed under ch:one but lives in ch:two.
        "ch:elsewhere": {"theorems": ["lem:promoted"], "corollaries": ["thm:variant_alias"]},
    }
}


class BlueprintRolesTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.src = root / "src"
        (self.src / "chapter").mkdir(parents=True)
        files = {
            "content.tex": CONTENT,
            "chapter/one.tex": ONE,
            "chapter/two.tex": TWO,
            "chapter/two_body.tex": TWO_BODY,
        }
        for name, text in files.items():
            (self.src / name).write_text(text, encoding="utf-8")
        self.roles_path = root / "roles.json"
        self.roles_path.write_text(json.dumps(ROLES), encoding="utf-8")

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def run_main(self, *args: str) -> tuple[int, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
            code = roles.main([*args, "--src", str(self.src), "--roles", str(self.roles_path)])
        return code, out.getvalue()

    def read(self, name: str) -> str:
        return (self.src / name).read_text(encoding="utf-8")

    def test_begin_end_pairing_with_nested_environments(self) -> None:
        scan = roles.scan_file(Path("one.tex"), ONE)
        self.assertEqual(scan.errors, [])
        by_label = {e.label: e for e in scan.envs}
        main = by_label["thm:main"]
        self.assertEqual(ONE[slice(*main.begin_name_span)], "theorem")
        self.assertEqual(ONE[slice(*main.end_name_span)], "theorem")
        # The matching \end{theorem} is the outer one, after the align.
        self.assertGreater(main.end_name_span[0], ONE.index(r"\end{align}"))
        self.assertEqual(main.labels, ["thm:main"])
        self.assertIn("thm:nested", by_label)
        self.assertNotIn(None, by_label)

    def test_unbalanced_environments_are_reported(self) -> None:
        scan = roles.scan_file(Path("bad.tex"), "\\begin{theorem}\n\\end{lemma}\n")
        self.assertTrue(any("closes" in err for err in scan.errors))

    def test_chapters_follow_nested_inputs(self) -> None:
        bp = roles.Blueprint(self.src)
        self.assertEqual([c.key for c in bp.chapters], ["ch:one", "ch:two"])
        chapters = {e.label: e.chapter for e in bp.envs}
        self.assertEqual(chapters["thm:main"], "ch:one")
        self.assertEqual(chapters["lem:promoted"], "ch:two")

    def test_apply_sets_roles_and_rewrites_prose(self) -> None:
        code, out = self.run_main("--apply")
        self.assertEqual(code, 0, out)
        one, body = self.read("chapter/one.tex"), self.read("chapter/two_body.tex")
        # Listed theorem stays; unlisted theorem and proposition become lemmas.
        self.assertIn("\\begin{theorem}[Main]\\label{thm:main}", one)
        self.assertIn("\\begin{lemma}[Auxiliary]\\label{thm:aux}", one)
        self.assertIn("\\begin{lemma}[A proposition]\\label{prop:p}", one)
        self.assertNotIn("proposition}", one)
        self.assertIn("\\begin{definition}[Def]", one)
        self.assertIn("% \\begin{theorem} in a comment is ignored", one)
        # A lemma listed as a theorem is promoted, from another chapter's list.
        self.assertIn("\\begin{theorem}[Promoted]\\label{lem:promoted}", body)
        # A listed second label makes its entry a corollary; an unlisted corollary is a lemma.
        self.assertIn("\\begin{corollary}[Variant]", body)
        self.assertIn("\\begin{lemma}[Unlisted]\\label{cor:unlisted}", body)
        self.assertEqual(body.count("\\end{lemma}"), 1)
        self.assertEqual(body.count("\\end{corollary}"), 1)
        # Singular forms with a tie or a space.
        self.assertIn("Lemma~\\ref{thm:aux} supports it", one)
        self.assertIn("By Lemma \\ref{thm:aux}", one)
        self.assertIn("Uses Theorem~\\ref{thm:main}", body)
        self.assertIn("Corollary~\\ref{thm:variant_alias}", body)
        # Plural forms, also across a line break.
        self.assertIn("Lemmas~\\ref{thm:aux} and~\\ref{prop:p}", one)
        self.assertIn("Lemmas~\\ref{prop:p}, \\ref{thm:aux}, and~\\ref{cor:unlisted}", body)
        # A mixed list is reported and left unchanged.
        self.assertIn("Theorems~\\ref{thm:aux}\n    and~\\ref{thm:main}", body)
        self.assertIn("refers to lemma, theorem", out)
        # References to definitions and to items are not touched.
        self.assertIn("Lemma~\\ref{def:x}", body)
        self.assertIn("Theorem~\\ref{it:main_a}", body)

    def test_labels_and_tags_are_conserved(self) -> None:
        before = {p: p.read_text(encoding="utf-8") for p in roles.tex_files(self.src)}
        self.run_main("--apply")
        after = {p: p.read_text(encoding="utf-8") for p in roles.tex_files(self.src)}
        self.assertEqual(roles.verify_texts(before, after), [])
        summary_before = roles.tag_summary(before)
        summary_after = roles.tag_summary(after)
        for key in ("label", "lean", "uses", "leanok", "proof"):
            self.assertEqual(summary_before[key], summary_after[key], key)
        self.assertIn("thm:variant_alias", summary_after["label"])

    def test_verify_detects_a_lost_tag(self) -> None:
        before = {Path("a.tex"): "\\begin{theorem}\\label{thm:a}\\leanok x\\end{theorem}"}
        after = {Path("a.tex"): "\\begin{lemma}\\label{thm:b} x\\end{lemma}"}
        problems = roles.verify_texts(before, after)
        self.assertTrue(any("label" in p for p in problems))
        self.assertTrue(any("leanok" in p for p in problems))

    def test_check_and_dry_run(self) -> None:
        code, out = self.run_main("--check")
        self.assertEqual(code, 1)
        self.assertIn("thm:aux should be lemma", out)
        code, out = self.run_main("--dry-run")
        self.assertEqual(code, 0)
        self.assertIn("== ch:one: First", out)
        self.assertIn("[theorem] thm:main: Main", out)
        self.run_main("--apply")
        code, out = self.run_main("--check")
        # Only the mixed list remains, and it needs a human decision.
        self.assertEqual(code, 1)
        self.assertIn("name both environments", out)
        self.assertNotIn("should be", out)

    def test_unknown_roles_label_is_a_problem(self) -> None:
        data = json.loads(self.roles_path.read_text(encoding="utf-8"))
        data["chapters"]["ch:one"]["theorems"].append("thm:gone")
        self.roles_path.write_text(json.dumps(data), encoding="utf-8")
        code, out = self.run_main("--apply")
        self.assertEqual(code, 1)
        self.assertIn("thm:gone", out)
        self.assertIn("\\begin{theorem}[Auxiliary]", self.read("chapter/one.tex"))


if __name__ == "__main__":
    unittest.main()
