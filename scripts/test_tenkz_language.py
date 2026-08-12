#!/usr/bin/env python3
"""Focused contract tests for the executable tenkz language registry."""

from __future__ import annotations

import os
import re
import subprocess
import tempfile
from pathlib import Path

import tenkz_language


ROOT = Path(__file__).resolve().parents[1]


def run(*args: str, cwd: Path = ROOT, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args, cwd=cwd, check=check, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=120,
    )


def compile_source(source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="tenkz-language-") as tmp:
        path = Path(tmp)
        (path / "case.tex").write_text(source, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:"
        return subprocess.run(
            ("xelatex", "-interaction=nonstopmode", "-halt-on-error", "case.tex"),
            cwd=path, env=env, check=False, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=120,
        )


def compile_event_source(source: str) -> tuple[subprocess.CompletedProcess[str], str]:
    with tempfile.TemporaryDirectory(prefix="tenkz-language-events-") as tmp:
        path = Path(tmp)
        (path / "case.tex").write_text(source, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:"
        result = subprocess.run(
            ("xelatex", "-interaction=nonstopmode", "-halt-on-error", "case.tex"),
            cwd=path, env=env, check=False, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=120,
        )
        log = (path / "case.tnlog").read_text(encoding="utf-8") if result.returncode == 0 else ""
        return result, log


def main() -> int:
    run("python3", "scripts/tenkz_language.py", "check")
    registry = tenkz_language.load_registry()
    mpo_preludes = [
        entry.fields
        for entry in registry
        if entry.kind == "prelude" and entry.fields[:2] == ("skin", "mpo")
    ]
    if mpo_preludes != [("skin", "mpo", "base=box")]:
        raise SystemExit("the executable registry lost the stock MPO box declaration")
    reference = tenkz_language.REFERENCE.read_text(encoding="utf-8")
    if "Prelude class & Name & Declaration" not in reference or "base=box" not in reference:
        raise SystemExit("the generated language reference omitted the stock MPO declaration")
    # Both chapters say they are generated, so both must equal what the
    # generator emits from the registry as committed.  Without this a registry
    # row could change its prose and the published reference keep the old
    # sentence, which is exactly the drift the one-record rule forbids.
    drifted = tenkz_language.stale_generated_chapters(registry)
    if drifted:
        raise SystemExit(
            "generated chapters drifted from the registry:\n" + "\n".join(drifted)
        )
    distinct_skin = tenkz_language.Entry(
        kind="prelude", fields=("skin", "probe", "base=ring")
    )
    distinct_errors = tenkz_language.check([*registry, distinct_skin])
    if distinct_errors:
        raise SystemExit(
            "a distinct stock skin was rejected:\n" + "\n".join(distinct_errors)
        )
    duplicate_skin = tenkz_language.Entry(
        kind="prelude", fields=("skin", "mpo", "base=box")
    )
    duplicate_errors = tenkz_language.check([*registry, duplicate_skin])
    if duplicate_errors != ["duplicate prelude records: skin:mpo"]:
        raise SystemExit(
            "an exact stock-skin duplicate was not rejected by class:name"
        )
    for declaration_class, descriptor in (
        ("atom", "skin=box"),
        ("species", "hue=source:red"),
    ):
        name = f"invalid-{declaration_class}"
        invalid = tenkz_language.Entry(
            kind="prelude", fields=(declaration_class, name, descriptor)
        )
        expected = (
            f"prelude declaration {name!r} has unsupported class "
            f"{declaration_class!r}; expected 'skin'"
        )
        if tenkz_language.check([*registry, invalid]) != [expected]:
            raise SystemExit(
                f"the registry validator accepted a {declaration_class} prelude"
            )
    for declaration_class, name, descriptor in (
        ("atom", "mpo-command-leak", "skin=box"),
        ("species", "mpo-species-leak", "hue=source:red"),
    ):
        rejected = compile_source(
            rf"""\documentclass{{standalone}}
\usepackage{{tenkz}}
\ExplSyntaxOn
\__tenkz_kernel_install_prelude:nnn
  {{{declaration_class}}}{{{name}}}{{{descriptor}}}
\ExplSyntaxOff
\begin{{document}}x\end{{document}}
"""
        )
        if (
            rejected.returncode == 0
            or "TKZ-LANG-PRELUDE-CLASS" not in rejected.stdout
        ):
            raise SystemExit(
                f"the runtime installer accepted a {declaration_class} prelude"
            )
    good = compile_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\tndeclareatom{\tnphase}{skin=box, ports={west:virtual,east:virtual}}
\begin{document}
\begin{tenkz}[rows={wire}]\tn{A}&\tnphase{B}\end{tenkz}
\end{document}
""")
    if good.returncode:
        raise SystemExit(f"typed declaration did not compile:\n{good.stdout}")
    bad = compile_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\tndeclareatom{\tnbad}{skin=box, ports={west:physical}}
\begin{document}x\end{document}
""")
    if bad.returncode == 0 or "TKZ-ATOM-INVALID-PORT" not in bad.stdout:
        raise SystemExit("invalid typed port did not produce TKZ-ATOM-INVALID-PORT")
    # No alias remains since the S4 surface swap, so the event-equivalence
    # probe compares a sugar row with its kernel expansion instead.
    canonical, canonical_events = compile_event_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkz}[rows={ket,op,bra}, cols=2]\end{tenkz}
\end{document}
""")
    sugared, sugared_events = compile_event_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkz}[sandwich, cols=2]\end{tenkz}
\end{document}
""")
    if canonical.returncode or sugared.returncode:
        raise SystemExit("kernel/sugar event-equivalence probe did not compile")
    if canonical_events != sugared_events:
        raise SystemExit("sandwich and rows={ket,op,bra} emitted different semantic events")
    # Each retired word stays installed as a parser branch that refuses the
    # spelling and states the migration.  What is pinned here is that the
    # branch fires and prints its own words: the four are read out of the
    # kernel source rather than written again, so a migration reworded in one
    # place and not the other cannot pass.  Holding those branches to the
    # registry's tombstone rows is the ledger's own check and arrives with it
    # (issue #6187).
    form_row = next(
        entry.fields
        for entry in registry
        if entry.kind == "key" and entry.fields[:2] == ("kernel-mark", "form")
    )
    if form_row[2] != "enum(bracket|enclosure|label|prose)":
        raise SystemExit(f"the mark form alphabet is no longer the contract's: {form_row[2]}")
    kernel = (ROOT / "tex/tenkz/tenkz-kernel.code.tex").read_text(encoding="utf-8")
    branches = re.findall(
        r"\\__tenkz_kernel_tombstone:nnnn\s*\{\s*tenkz-kernel-mark\s*\}"
        r"\s*\{\s*form\s*\}\s*\{\s*([a-z-]+)\s*\}\s*\{(.*?)\}\n",
        kernel,
        re.DOTALL,
    )
    if len(branches) != 4:
        raise SystemExit(
            f"expected four retired mark forms in the parser, found {len(branches)}"
        )
    for word, migration in branches:
        refused = compile_source(
            rf"""\documentclass{{standalone}}
\usepackage{{tenkz}}
\begin{{document}}
\begin{{tenkz}}[rows={{ket}}, cols=2, bonds=none]
  \tn[name=a]{{A}} & \tn[name=b]{{B}}
  \tnmark[form={word}]{{(1,1) .. (1,2)}}{{$L$}}
\end{{tenkz}}
\end{{document}}
"""
        )
        # l3msg wraps a long diagnostic and prefixes each continuation line
        # with the package name, which lands between the words it broke.  The
        # comparison therefore drops that prefix and then every space, so it
        # asks only which characters were printed and never where the engine
        # of the day chose to break the line.
        transcript = re.sub(
            r"\s+|\(tenkz\)", "", refused.stdout.replace("(tenkz)", " ")
        )

        def printed(text: str) -> bool:
            return re.sub(r"\s+|~", "", text) in transcript

        if refused.returncode == 0 or not printed("TKZ-LANG-TOMBSTONE"):
            raise SystemExit(f"form={word} was not refused as a tombstone")
        if not printed(migration):
            raise SystemExit(
                f"form={word} was refused without the parser's own migration"
            )

    live = compile_source(r"""\documentclass{standalone}
\usepackage{tenkz}
\begin{document}
\begin{tenkz}[rows={ket}, cols=2]
  \tn{A} & \tn{A}
  \tnmark[form=bracket]{(1,1) .. (1,2)}{$L$}
\end{tenkz}
\end{document}
""")
    if live.returncode:
        raise SystemExit(f"the surviving bracket form did not compile:\n{live.stdout}")
    print(
        "PASS: registry, typed atom diagnostic, sugar event equivalence, "
        "and the four retired mark forms refused by a compile"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
