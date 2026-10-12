#!/usr/bin/env python3
"""Check the actual mixed-symbol leaf, diagrams, and source orientations.

Default: source/mutation checks plus the native production wrapper and hard
signature audit. --source-only needs no TeX or tenkz installation. --web-root
checks existing strict web output; --browser also applies the existing
1440/360-pixel MathJax layout gate. This script does not build the blueprint
or validate Lean proofs. It never fetches dependencies or skips failures.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch30_mpo_mixed_symbols.tex"
WIRES = {
    "L": [("seqana.0@1", "fussyn.180@1"),
          ("seqana.0@2", "fussyn.180@2"),
          ("seqana.0@3", "fussyn.180@3")],
    "F": [("leftouter.0@1", "leftinner.180"),
          ("rightouter.0@2", "rightinner.180")],
}
EXPECTED = [
    ("open:e, open:w", 1, 2),
    ("open:e, open:w", 2, 5),
    ("open:e, open:e, open:e, open:w", 2, 5),
    ("open:e, open:e, open:e, open:w", 2, 5),
]
OPEN_LABELS = [["s", "r"], [r"\alpha", r"\beta", r"\gamma", "z"]]
F_COEFFICIENT = r"$=\displaystyle\sum_{f,\lambda,\sigma}F_{q,t}$"


def bodies(source: str | None = None) -> list[str]:
    source = CHAPTER.read_text(encoding="utf-8") if source is None else source
    assert r"\begin{tikzpicture}" not in source
    assert source.count(r"\begin{tenkzequation}") == 2
    assert source.count(r"\begin{tenkz}") == 4
    result = []
    for name, expected in WIRES.items():
        begin, end = [f"% TENKZ-MIXED-SYMBOLS-{name}-{edge}" for edge in ("BEGIN", "END")]
        assert source.count(begin) == source.count(end) == 1
        body = source.split(begin, 1)[1].split(end, 1)[0]
        assert body.count(r"\begin{tenkzequation}") == 1
        assert body.count(r"\begin{tenkz}") == 2
        assert re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", body) == expected
        assert all(token not in body for token in (r"\dagger", r"\overline", "physical:"))
        result.append(body)
    for token in (r"{C_{ij,ck\mu}}", r"{\widetilde H_{ij}}", r"{\widetilde R_{ck\mu}}"):
        assert result[0].count(token) == 1, token
    assert result[0].index(r"{\widetilde H_{ij}}") < result[0].index(r"{\widetilde R_{ck\mu}}")
    for token in (r"{\widetilde V_{ec;d\nu}}", r"{\widetilde V_{ab;e\mu}}",
                  r"{\widetilde V_{af;d\sigma}}", r"{\widetilde V_{bc;f\lambda}}",
                  F_COEFFICIENT):
        assert result[1].count(token) == 1, token
    for index, labels in enumerate(OPEN_LABELS):
        for label in labels:
            assert result[index].count(f"virtual:${label}$") == 2, (index, label)
    return result


def source_check() -> dict[str, object]:
    source = CHAPTER.read_text(encoding="utf-8")
    bodies(source)
    for token in (r"(D_0+D_1)^{-1}(D_0L_0+D_1L_1)",
                  r"(\chi_{0,d}+\chi_{1,d})^{-1}",
                  r"(\chi_{0,d}F_0+\chi_{1,d}F_1)",
                  r"\tau_{\chi_{p,d}}(H^\ell_{p,q}S^r_{p,t})",
                  r"$H^\ell_{p,q}=\sum_t(F_p)_{q,t}H^r_{p,t}$",
                  r"\gamma=0,1", r"\tau_0(M)=0"):
        assert token in source, token
    # Check declaration spelling against the owned modules without running Lean.
    owners = [ROOT / f"TNLean/MPS/Symmetry/MPOSymmetry/{name}.lean" for name in
              ("MixedEndpointTripleMaps", "MixedEndpointMPOActionSymbols",
               "MixedEndpointMPOFusionSymbols")]
    lean_source = "\n".join(path.read_text(encoding="utf-8") for path in owners)
    declarations = re.findall(r"\\lean\{([^}]+)\}", source, re.S)
    names = [name.strip() for block in declarations for name in block.split(",")]
    for name in names:
        short = name.rsplit(".", 1)[-1]
        assert re.search(r"\b(?:theorem|def)\s+" + re.escape(short) + r"\b", lean_source), name
    public_names = set(re.findall(r"\b(?:theorem|def)\s+(\w+)", lean_source))
    linked_names = {name.rsplit(".", 1)[-1] for name in names}
    assert len(names) == len(linked_names) == 24
    assert linked_names == public_names, sorted(public_names ^ linked_names)
    # Verify every dependency/cross-reference against the source tree, even
    # before the coordinating task adds this leaf to the chapter router.
    chapters = ROOT / "blueprint/src"
    all_tex = "\n".join(path.read_text(encoding="utf-8") for path in chapters.rglob("*.tex"))
    labels = set(re.findall(r"\\label\{([^}]+)\}", all_tex))
    refs = re.findall(r"\\ref\{([^}]+)\}", source)
    refs += [label.strip() for block in re.findall(r"\\uses\{([^}]+)\}", source, re.S)
             for label in block.split(",")]
    assert set(refs) <= labels, sorted(set(refs) - labels)
    assert not any(token in source for token in
                   (r"\begin{equation}", r"\begin{gather}", r"\[", r"\eqref"))
    return {"marked_rows": 2, "native_panels": 4, "declaration_names": names,
            "references": sorted(set(refs)), "lean_proofs_checked": False}


def source_mutations() -> list[str]:
    source = CHAPTER.read_text(encoding="utf-8")
    changes = {
        "third_contracted_leg": (r"\tnwire{seqana.0@3}{fussyn.180@3}",
                                 r"\tnwire{seqana.0@3}{fussyn.180@2}"),
        "sequential_analysis": (r"{\widetilde H_{ij}}", r"{\widetilde R_{ij}}"),
        "fusion_synthesis": (r"{\widetilde R_{ck\mu}}", r"{\widetilde H_{ck\mu}}"),
        "left_fusion_order": (r"{\widetilde V_{ab;e\mu}}", r"{\widetilde V_{ba;e\mu}}"),
        "right_fusion_order": (r"{\widetilde V_{bc;f\lambda}}", r"{\widetilde V_{cb;f\lambda}}"),
        "transposed_f_coefficient": (F_COEFFICIENT, F_COEFFICIENT.replace("F_{q,t}", "F_{t,q}")),
        "invented_adjoint": (r"{\widetilde V_{af;d\sigma}}", r"{\widetilde V_{af;d\sigma}^{\dagger}}"),
        "third_open_leg": (r"0@3:virtual:$\gamma$", r"0@3:virtual:$\beta$"),
    }
    for name, (old, new) in changes.items():
        assert old in source
        try:
            bodies(source.replace(old, new, 1))
        except AssertionError:
            continue
        raise AssertionError(f"source mutation escaped: {name}")
    return list(changes)


def native_check(output: Path) -> dict[str, object]:
    from tenkz_paths import ensure_pythonpath, tenkz_tex
    ensure_pythonpath()
    from tenkz_audit import Audit
    engine = shutil.which("xelatex")
    assert engine, "xelatex is required"
    macros = (ROOT / "blueprint/src/macros/print.tex").read_text(encoding="utf-8")
    wrapper = re.search(r"\\newenvironment\{tenkzequation\}[^\n]+", macros)
    assert wrapper, "production print wrapper missing"
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
    results = {}
    for mode in ("wrapper", "signature"):
        body = "\n".join(bodies())
        if mode == "signature":
            body = body.replace(r"\begin{tenkzequation}", r"\begin{tenkzeq}[check={signature}]")
            body = body.replace(r"\end{tenkzequation}", r"\end{tenkzeq}")
            body = body.replace(F_COEFFICIENT, "=").replace("$=$", "=")
        source = ("\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
                  "\\usepackage{tenkz}\n\\pagestyle{empty}\n" + wrapper.group(0)
                  + "\n\\begin{document}\n" + body + "\n\\end{document}\n")
        tex = output / f"mixed-symbols-{mode}.tex"
        tex.write_text(source, encoding="utf-8")
        run = subprocess.run([engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
                             cwd=output, env=env, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, check=False)
        (output / f"{mode}-stdout.log").write_text(run.stdout, encoding="utf-8")
        assert run.returncode == 0, run.stdout[-8000:]
        audit = Audit(tex.with_suffix(".tnlog"), tex)
        audit.run()
        hard = [str(f) for f in audit.findings if f.severity == "HARD"]
        assert not hard, hard
        panels, atoms, wires, labels = [], [], [], []
        for event in audit.events():
            if event.kind == "atom":
                atoms.append(event)
            elif event.kind == "wire":
                wires.append(event)
            elif event.kind == "kernel-boundary":
                panels.append((event.attrs["signature"], len(atoms), len(wires)))
                labels.append([w.attrs.get("port-label") for w in wires
                               if w.attrs.get("origin") == "port-open"])
                assert not any(w.attrs.get("origin") in {"grid", "trace"} for w in wires)
                atoms, wires = [], []
        assert panels == EXPECTED, panels
        for group, expected in enumerate(OPEN_LABELS):
            for actual in labels[2*group:2*group+2]:
                assert sorted(actual) == sorted(expected), (group, actual)
        results[mode] = {"panels": panels, "open_labels": labels, "hard": hard,
                         "findings": [str(f) for f in audit.findings]}
    return results


def web_check(root: Path, browser: bool) -> dict[str, object]:
    matches = [p for p in root.glob("*.html")
               if 'id="sec:mpo_mixed_symbols"' in p.read_text(encoding="utf-8")]
    assert len(matches) == 1, matches
    path = matches[0]
    source = path.read_text(encoding="utf-8")
    start = source.index('id="sec:mpo_mixed_symbols"')
    following = re.search(r'<h[123]\b[^>]*\bid="', source[start+1:])
    end = start+1+following.start() if following else len(source)
    relevant = source[start:end]
    assert relevant.count('class="tenkz-equation"') == 2
    assert relevant.count('class="tenkz-pic ') == 4

    class InspectHTML(HTMLParser):
        def __init__(self):
            super().__init__()
            self.text, self.images = [], []
            self.paragraph = False

        def handle_data(self, data):
            self.text.append(data)

        def handle_starttag(self, tag, attrs):
            attrs = dict(attrs)
            if tag == "p":
                assert not self.paragraph, "nested generated paragraph"
                self.paragraph = True
            if tag == "div" and "tenkz-equation" in attrs.get("class", "").split():
                assert not self.paragraph, "equation wrapper inside paragraph"
            if tag == "img" and "tenkz-pic" in attrs.get("class", "").split():
                self.images.append(attrs["src"])

        def handle_endtag(self, tag):
            if tag == "p":
                assert self.paragraph, "unopened generated paragraph"
                self.paragraph = False

    visible = InspectHTML()
    visible.feed(source)
    visible.close()
    assert not visible.paragraph
    assert not any(token in "".join(visible.text) for token in (r"\tnwire", r"\begin{tenkz}"))
    for image in visible.images:
        assert (root / image).is_file(), image
    result = {"page": path.name, "wrappers": 2, "pictures": 4, "browser": False}
    if browser:
        from playwright.sync_api import sync_playwright
        from test_tenkz_equation_web import serve, _assert_chapter_picture_layout
        with serve(root) as url, sync_playwright() as playwright:
            chromium = playwright.chromium.launch()
            page = chromium.new_page()
            for width in (1440, 360):
                page.set_viewport_size({"width": width, "height": 1000})
                page.goto(f"{url}/{path.name}", wait_until="domcontentloaded", timeout=300_000)
                page.wait_for_function("() => window.MathJax && window.MathJax.startup")
                page.wait_for_function("async () => { await MathJax.startup.promise; return true; }",
                                       timeout=300_000)
                page.evaluate("showmore_update(2)")
                page.wait_for_function("() => [...document.querySelectorAll('.tenkz-pic')]"
                                       ".every(i => i.complete && i.naturalWidth > 0)")
                _assert_chapter_picture_layout(page, path.name)
            chromium.close()
        result["browser"] = True
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--web-root", type=Path)
    parser.add_argument("--browser", action="store_true")
    args = parser.parse_args()
    if args.browser and not args.web_root:
        parser.error("--browser requires --web-root")
    with tempfile.TemporaryDirectory(prefix="tenkz_mixed_symbols_") as tmp:
        output = (args.output_dir or Path(tmp)).resolve()
        output.mkdir(parents=True, exist_ok=True)
        results = {"source": source_check(), "source_mutations": source_mutations()}
        if not args.source_only:
            results["native"] = native_check(output)
        if args.web_root:
            results["web"] = web_check(args.web_root.resolve(), args.browser)
        (output / "validation.json").write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
