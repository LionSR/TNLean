#!/usr/bin/env python3
"""Build the paper-gap section of the GitHub Pages site.

Usage:
    python3 scripts/paper_gaps_site.py OUT_DIR   # generate site tree
    python3 scripts/paper_gaps_site.py --check   # verify referenced notes exist

Reads every note in ``docs/paper-gaps/*.tex`` and produces, under OUT_DIR:

* ``index.html``       -- grouped, titled index linking to the PDFs
* ``<slug>.pdf``       -- copied from docs/paper-gaps when present
* ``paper-gaps.bib``   -- one @techreport per note, key ``gap:<slug>``

``--check`` scans the Lean sources, the blueprint (chapters and committed
commentary), the Markdown documentation, and the notes themselves for
``paper-gaps/<name>.tex`` references and fails when a referenced note does
not exist, the same way ``leanblueprint checkdecls`` fails on an unresolved
declaration. It also enforces the ``<key>_<topic>.tex`` naming convention
of ``docs/paper-gaps/policy.tex`` and the ``\\gapnote{<kind>}{<status>}``
verdict marker every note declares (policy, Classification); the index
lists open notes first and dims the resolved ones.
"""

from __future__ import annotations

import datetime
import html
import re
import shutil
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
GAPS = REPO / "docs" / "paper-gaps"
SITE_BASE = "https://sirui-lu.com/TNLean"
GITHUB_BLOB = "https://github.com/LionSR/TNLean/blob/main/docs/paper-gaps"
# Machinery, not notes.
EXCLUDE = {"command.tex", "common.tex", "template.tex", "references.bib"}
POLICY = "policy.tex"
# Registered source keys: every note is named <key>_<topic>.tex. Author
# initials plus two-digit year, or an established short name for the source
# (a book or review such as ``wolf``/``rmp``, or a paper known by its
# subject such as ``mpu``/``peps``); a key may also cover a small fixed set
# of companion sources examined together (``cpsv17``). ``tnlean`` marks
# internal theorem-surface audits with no single external source. The
# registry is enforced by ``--check``.
SOURCE_KEYS = {
    "cpgsv17": "arXiv:1606.00608 (MPDO renormalization fixed points)",
    "cpgsv21": "Cirac, Perez-Garcia, Schuch, Verstraete, Rev. Mod. Phys. 93 (2021)",
    "cpsv16": "arXiv:1606.00608 (matrix product density operators)",
    "cpsv17": "arXiv:1606.00608 / arXiv:1703.09188 mixed",
    "dccsp17": "arXiv:1708.00029 (irreducible forms of MPS)",
    "hjpw04": "Hayden, Jozsa, Petz, Winter (2004)",
    "knabe88": "Knabe, J. Stat. Phys. 52 (1988)",
    "mpu": "arXiv:1703.09188 (matrix product unitaries)",
    "peps": "arXiv:1804.04964 (normal PEPS)",
    "pgvwc07": "quant-ph/0608197 (MPS representations)",
    "pgwsvc08": "arXiv:0802.0447 (string order and symmetries)",
    "rmp": "Cirac, Perez-Garcia, Schuch, Verstraete, Rev. Mod. Phys. 93 (2021)",
    "spc11": "arXiv:1010.3732 (SPT classification)",
    "spwc10": "arXiv:0909.5347 (quantum Wielandt inequality)",
    "tnlean": "internal theorem-surface audit, no single external source",
    "wolf": "Wolf, Quantum Channels & Operations (2012 lecture notes)",
}
# Verdict marker vocabulary (docs/paper-gaps/policy.tex, Classification).
# Every note declares ``\gapnote{<kind>}{<status>}``; ``--check`` enforces
# exactly one marker with a registered kind and status, and the index
# lists open notes first and dims the resolved ones.
GAP_KINDS = {"clarification", "local-correction", "scope-restriction",
             "unfaithful", "false-source", "open-gap"}
GAP_STATUSES = ("open", "historical", "resolved")
GAPNOTE_RE = re.compile(r"\\gapnote\{([a-z<>-]+)\}\{([a-z<>-]+)\}")
# Keys listed here are folded into their target key's group on the index
# page, so one source gets one heading. Both filename prefixes remain
# registered and accepted.
GROUP_ALIASES = {"cpgsv17": "cpsv16", "cpgsv21": "rmp"}
# Slugs published before the source-key registry, mapped to the notes that
# hold their content today. The site keeps serving the old PDF URLs so
# external citations do not break. ``--check`` verifies the targets exist.
LEGACY_ALIASES = {
    "1703_two_projection_projector_typo": "mpu_two_projection_projector_typo",
    "1708_normal_canonical_irreducible_form_weights":
        "dccsp17_normal_canonical_irreducible_form_weights",
    "1708_periodic_overlap_route_alignment": "dccsp17_periodic_overlap_route_alignment",
    "algebraic_ft_same_state_combined_mpv_gap":
        "tnlean_algebraic_ft_same_state_combined_mpv_gap",
    "breuer_hall_even_dim_restriction": "wolf_breuer_hall_even_dim_restriction",
    "brouwer_general_compact_convex": "wolf_brouwer_general_compact_convex",
    "canonical_bnt_ft_theorem_surface": "tnlean_bnt_ft_theorem_surface",
    "choi_rectangular_scope": "wolf_choi_rectangular_scope",
    "common_sector_relabeling_hypothesis": "cpsv16_sector_relabeling_hypothesis",
    "conditional_after_blocking_ft_cpsv_statement":
        "rmp_conditional_after_blocking_ft_statement",
    "cpgsv17_mpu_blocking_rank_product_exponent": "mpu_blocking_rank_product_exponent",
    "david2006_direct_sum_input": "pgvwc07_direct_sum_input",
    "ft_one_copy_scope_restriction": "cpsv16_ft_one_copy_scope_restriction",
    "issue1530_ft_dependency_audit": "tnlean_ft_dependency_audit",
    "knabe_finite_range_coefficient": "knabe88_finite_range_coefficient",
    "mps_common_blocking_span_equality": "rmp_common_blocking_span_equality",
    "nonperiodic_mps_bnt_comparison_inputs": "rmp_nonperiodic_bnt_comparison_inputs",
    "periodic_thm41_root_kraus_rank": "dccsp17_root_kraus_rank_thm41",
    "power_sum_alternative_route": "cpsv16_power_sum_alternative_route",
    "quantum_wielandt_deviation": "spwc10_wielandt_one_step_subspace",
    "quantum_wielandt_deviation_v1": "spwc10_wielandt_one_step_subspace",
    "schuch2011_spt_interpolation_upper_range": "spc11_spt_interpolation_upper_range",
    "schur_complement_tfae": "wolf_schur_complement_tfae",
}
BIB_AUTHOR = "The {TNLean} contributors"


# --------------------------------------------------------------------------
# TeX parsing


def _detex(s: str) -> str:
    """TeX title to plain text."""
    s = s.replace(r"\\", " ")
    s = re.sub(r"\\(?:path|texttt|leanid|emph|textit|textbf|textsc)\s*{([^{}]*)}", r"\1", s)
    s = re.sub(r"\\(?:text|mathrm|mathcal|mathbb)\s*{([^{}]*)}", r"\1", s)
    accents = {"'": "\u0301", "`": "\u0300", '"': "\u0308", "^": "\u0302", "~": "\u0303"}
    for mark, combining in accents.items():
        s = re.sub(
            r"\\" + re.escape(mark) + r"(?:{\\?([a-zA-Z])}|\\?([a-zA-Z]))",
            lambda m, c=combining: (m.group(1) or m.group(2)) + c, s)
    s = re.sub(r"\\(?:large|Large|small|footnotesize|normalsize)\b\s*", "", s)
    s = re.sub(r"\\mathcal\s*", "", s)
    s = s.replace(r"\eta", "\u03b7").replace(r"\S", "\u00a7")
    s = s.replace("---", "\u2014").replace("--", "\u2013").replace("~", "\u00a0")
    s = s.replace("\\&", "&").replace("\\_", "_").replace("\\%", "%")
    s = re.sub(r"(?<!\\)[{}$]", "", s)
    return re.sub(r"\s+", " ", s).strip()


def _braced_arg(tex: str, command: str) -> str | None:
    """The (possibly nested-brace) argument of ``\\command{...}``."""
    m = re.search(r"\\" + command + r"\s*{", tex)
    if not m:
        return None
    depth, start = 1, m.end()
    for i in range(start, len(tex)):
        if tex[i] == "{" and tex[i - 1] != "\\":
            depth += 1
        elif tex[i] == "}" and tex[i - 1] != "\\":
            depth -= 1
            if depth == 0:
                return tex[start:i]
    return None


def _bib_escape(s: str) -> str:
    """Escape TeX-special characters for a printable BibTeX field."""
    return re.sub(r"([&%#_])", r"\\\1", s)


def _git_date(path: Path) -> str:
    out = subprocess.run(
        ["git", "log", "-1", "--format=%as", "--", str(path)],
        cwd=REPO, capture_output=True, text=True,
    ).stdout.strip()
    return out or "n.d."


@dataclass
class Note:
    slug: str
    title: str = ""
    date: str = ""
    kind: str = ""
    status: str = ""
    citations: int = 0

    @property
    def prefix(self) -> str:
        return self.slug.split("_", 1)[0]

    @property
    def year(self) -> str:
        m = re.match(r"(\d{4})", self.date)
        return m.group(1) if m else str(datetime.date.today().year)

    def bibtex(self) -> str:
        title = _bib_escape(self.title.replace("\u2013", "--").replace("\u2014", "---"))
        return (
            f"@techreport{{gap:{self.slug},\n"
            f"  author      = {{{BIB_AUTHOR}}},\n"
            f"  title       = {{{title}}},\n"
            f"  institution = {{TNLean}},\n"
            f"  type        = {{Paper-gap note}},\n"
            f"  number      = {{{_bib_escape(self.slug)}}},\n"
            f"  year        = {{{self.year}}},\n"
            f"  url         = {{{SITE_BASE}/paper-gaps/{self.slug}.pdf}},\n"
            f"}}"
        )


def parse_note(path: Path) -> Note:
    tex = path.read_text(encoding="utf-8")
    note = Note(slug=path.stem)
    raw_title = _braced_arg(tex, "title")
    note.title = _detex(raw_title) if raw_title else path.stem.replace("_", " ")
    raw_date = _braced_arg(tex, "date") or ""
    note.date = _git_date(path) if "today" in raw_date or not raw_date else raw_date.strip()
    m = GAPNOTE_RE.search(tex)
    if m:
        note.kind, note.status = m.group(1), m.group(2)
    return note


# --------------------------------------------------------------------------
# Cross-reference scan


REF_RE = re.compile(r"paper-gaps/([A-Za-z0-9_\-]+)\.tex")


def scan_references() -> tuple[Counter, dict[str, set[str]]]:
    """Reference counts per slug from Lean, blueprint, and other notes."""
    counts: Counter = Counter()
    locations: dict[str, set[str]] = {}
    # ``blueprint`` is scanned per committed subtree so that local build
    # output under ``blueprint/web`` and ``blueprint/print`` stays out.
    for root, glob in ((REPO / "TNLean", "*.lean"),
                       (REPO / "blueprint" / "src", "*.tex"),
                       (REPO / "blueprint" / "comments", "*.tex"),
                       (REPO / "docs", "*.md"),
                       (GAPS, "*.tex")):
        for f in sorted(root.rglob(glob)):
            try:
                text = f.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                continue
            for slug in REF_RE.findall(text):
                if f.stem == slug:
                    continue
                counts[slug] += 1
                locations.setdefault(slug, set()).add(str(f.relative_to(REPO)))
    return counts, locations


def check() -> int:
    counts, locations = scan_references()
    existing = {p.stem for p in GAPS.glob("*.tex")}
    failures = 0
    for slug in sorted(set(counts) - existing):
        where = ", ".join(sorted(locations.get(slug, []))[:3])
        print(f"::error::paper-gap note '{slug}.tex' is referenced but does not exist ({where})")
        failures += 1
    for p in sorted(GAPS.glob("*.tex")):
        if p.name in EXCLUDE or p.name == POLICY:
            continue
        key, _, topic = p.stem.partition("_")
        if key not in SOURCE_KEYS or not topic:
            print(f"::error::paper-gap note '{p.name}' is not named <key>_<topic>.tex "
                  f"with a registered source key (see SOURCE_KEYS in "
                  f"scripts/paper_gaps_site.py)")
            failures += 1
        elif re.search(r"_v\d+$", p.stem):
            print(f"::error::paper-gap note '{p.name}' carries a version suffix; "
                  f"notes are revised in place (docs/paper-gaps/policy.tex, Naming)")
            failures += 1
        markers = GAPNOTE_RE.findall(p.read_text(encoding="utf-8"))
        if len(markers) != 1:
            print(f"::error::paper-gap note '{p.name}' must declare exactly one "
                  f"\\gapnote{{<kind>}}{{<status>}} verdict marker, found "
                  f"{len(markers)} (docs/paper-gaps/policy.tex, Classification)")
            failures += 1
        else:
            kind, status = markers[0]
            if kind not in GAP_KINDS:
                print(f"::error::paper-gap note '{p.name}' declares unknown verdict "
                      f"kind '{kind}'; the vocabulary is "
                      f"{', '.join(sorted(GAP_KINDS))}")
                failures += 1
            if status not in GAP_STATUSES:
                print(f"::error::paper-gap note '{p.name}' declares unknown verdict "
                      f"status '{status}'; the vocabulary is "
                      f"{', '.join(GAP_STATUSES)}")
                failures += 1
    for old, new in sorted(LEGACY_ALIASES.items()):
        if new not in existing:
            print(f"::error::legacy alias '{old}' points at '{new}.tex', "
                  f"which does not exist")
            failures += 1
    if not failures:
        print(f"paper-gaps check: {len(counts)} referenced slugs resolve, "
              f"all note names carry registered source keys, and every note "
              f"declares a verdict marker")
    return 1 if failures else 0


# --------------------------------------------------------------------------
# HTML


STYLE = """
body { margin:2.5rem auto; max-width:46rem; padding:0 1rem; color:#222;
  font:16px/1.55 Georgia, "Times New Roman", serif; }
h1 { font-size:1.6rem; margin-bottom:.2rem; }
h2 { font-size:1.15rem; margin-top:2.2rem; border-bottom:1px solid #ddd;
  padding-bottom:.2rem; }
h2 small { font-weight:400; color:#777; font-size:.8rem; }
a { color:#1a5276; text-decoration:none; } a:hover { text-decoration:underline; }
p.lede, td.date, span.n { color:#777; }
table { border-collapse:collapse; width:100%; font-size:.95rem; }
td { padding:.3rem .5rem .3rem 0; vertical-align:top; }
td.date { white-space:nowrap; width:6.5rem; font-size:.85rem; }
span.n { font-size:.8rem; white-space:nowrap; }
tr.resolved { opacity:.55; }
"""


def group_heading(prefix: str) -> str:
    """Heading text for a source-key group, from the registry."""
    keys = ", ".join([prefix] + sorted(k for k, v in GROUP_ALIASES.items() if v == prefix))
    desc = SOURCE_KEYS.get(prefix)
    return f"{keys} \u00b7 {desc}" if desc else keys


def build(out: Path) -> None:
    notes = {
        p.stem: parse_note(p)
        for p in sorted(GAPS.glob("*.tex"))
        if p.name not in EXCLUDE and p.name != POLICY
    }
    counts, _ = scan_references()
    for slug, n in notes.items():
        n.citations = counts[slug]

    out.mkdir(parents=True, exist_ok=True)
    copied = 0
    for pdf in GAPS.glob("*.pdf"):
        if pdf.stem in notes or pdf.stem == "policy":
            shutil.copy2(pdf, out / pdf.name)
            copied += 1
    # Old published URLs keep resolving: serve each pre-registry slug as a
    # copy of the note that holds its content today.
    for old, new in LEGACY_ALIASES.items():
        src = GAPS / f"{new}.pdf"
        if src.exists():
            shutil.copy2(src, out / f"{old}.pdf")
    (out / "paper-gaps.bib").write_text(
        "\n\n".join(notes[s].bibtex() for s in sorted(notes)) + "\n", encoding="utf-8")

    groups: dict[str, list[Note]] = {}
    for n in notes.values():
        groups.setdefault(GROUP_ALIASES.get(n.prefix, n.prefix), []).append(n)
    ordered = sorted(groups, key=lambda g: (-len(groups[g]), g))

    rows = []
    for g in ordered:
        # Open notes first, resolved last (docs/paper-gaps/policy.tex,
        # Classification); slug order within each status.
        rank = {st: i for i, st in enumerate(GAP_STATUSES)}
        members = sorted(groups[g],
                         key=lambda n: (rank.get(n.status, len(rank)), n.slug))
        heading = group_heading(g)
        rows.append(f"<h2>{html.escape(heading)} <small>{len(members)}</small></h2>")
        rows.append("<table>")
        for n in members:
            cited = (f' <span class="n">\u00b7 cited \u00d7{n.citations}</span>'
                     if n.citations else "")
            verdict = (f' <span class="n">\u00b7 {html.escape(n.kind)}'
                       f' ({html.escape(n.status)})</span>' if n.kind else "")
            cls = ' class="resolved"' if n.status == "resolved" else ""
            rows.append(
                f'<tr{cls}><td class="date">{html.escape(n.date)}</td>'
                f'<td><a href="{n.slug}.pdf">{html.escape(n.title)}</a>{verdict}{cited} '
                f'<span class="n">(<a href="{GITHUB_BLOB}/{n.slug}.tex">tex</a>)</span>'
                f"</td></tr>")
        rows.append("</table>")

    page = f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>TNLean paper-gap notes</title>
<style>{STYLE}</style>
</head>
<body>
<h1>TNLean paper-gap notes</h1>
<p class="lede">Mathematical notes recording each discrepancy between a cited
source and the <a href="../">TNLean</a> formalization: missing hypotheses,
scalar corrections, scope restrictions, and replacement proof routes.
{len(notes)} notes, grouped by source; the conventions are stated in the
<a href="policy.pdf">policy note</a>. Cite a note by its permanent URL
<code>{SITE_BASE}/paper-gaps/&lt;name&gt;.pdf</code> or via
<a href="paper-gaps.bib">paper-gaps.bib</a>.</p>
{''.join(rows)}
</body>
</html>
"""
    (out / "index.html").write_text(page, encoding="utf-8")
    print(f"paper-gaps site: {len(notes)} notes, {copied} PDFs, "
          f"{sum(n.citations for n in notes.values())} citations resolved")


def main() -> int:
    if "--check" in sys.argv:
        return check()
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    build(Path(sys.argv[1]).resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
