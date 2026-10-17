#!/usr/bin/env python3
"""Render the note's digest page in the campaign-board style.

    python3 docs/notes/one_dimensional_note/build_page.py [DIR]

Reads DIR/presentation.json (the theorems, the proof as routes of stages,
glossary and references, written in the vocabulary of docs/campaign/README.md:
`physics`, `delivers`, `diagrams` with `src` and `caption`, `symbols`,
`{{tn:NAME}}` inline equations and `{{cite:Key}}` citations), inlines the
compiled SVGs under DIR/diagrams/ as data URIs, reuses the board stylesheet
scripts/campaign_board/board.css, and writes DIR/digest.html, a self-contained
page whose only external requests are Google Fonts and MathJax.
"""
from __future__ import annotations

import base64
import html
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
INLINE_SLOT = re.compile(r"\{\{tn:([A-Za-z0-9_-]+)\}\}([.,;:]?)\s*")
CITE_SLOT = re.compile(r"\{\{cite:([A-Za-z0-9_,-]+)\}\}")
ALT_LINE = re.compile(r"^% alt: (.+)$", re.MULTILINE)

EXTRA_CSS = r"""
.wrap { max-width: 1120px; }
.thmgrid { display: grid; grid-template-columns: repeat(auto-fit, minmax(340px, 1fr)); gap: 18px; }
.thm .stmt { font-size: 16.5px; }
.thm .formula { font-size: 18px; }
.route > header { display: grid; gap: 6px; margin-bottom: 26px; }
.route > header p { margin: 0; color: var(--muted); max-width: 72ch; font: 16px/1.55 var(--f-display); }
.stage .phys + .phys { margin-top: 2px; }
.stage .twice { font: 500 11px/2 var(--f-body); text-transform: uppercase; letter-spacing: 0.07em; color: var(--muted); }
.stage .prec { margin: 0; max-width: 66ch; font: 15px/1.6 var(--f-display); color: var(--ink); border-left: 2px solid var(--line); padding-left: 14px; }
.stage .prec p { margin: 0 0 8px; }
.stage .secs a { color: inherit; }
img.tnimg.wide, .tnfig img.wide { max-width: 100%; }
.mapt { border-collapse: collapse; font-size: 13.5px; max-width: 900px; }
.mapt td, .mapt th { padding: 6px 10px; border-bottom: 1px solid var(--soft); vertical-align: top; text-align: left; }
.mapt th { font-size: 11.5px; text-transform: uppercase; letter-spacing: 0.06em; color: var(--muted); font-weight: 500; }
mjx-container[display="true"] { overflow-x: auto; overflow-y: hidden; max-width: 100%; }
.stage .dot { border-color: var(--accent); color: var(--accent); }
"""


def diagram(path: pathlib.Path) -> dict:
    svg = path.read_bytes()
    width = re.search(rb'<svg[^>]*\bwidth="([0-9.]+)', svg)
    source = path.with_suffix(".tex")
    alt = ALT_LINE.search(source.read_text()) if source.exists() else None
    return {"src": "data:image/svg+xml;base64," + base64.b64encode(svg).decode("ascii"),
            "width": float(width.group(1)) if width else None,
            "alt": alt.group(1).strip() if alt else ""}


def main() -> None:
    directory = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    pres = json.loads((directory / "presentation.json").read_text())
    refs = pres.get("references", {})
    cite_no: dict[str, int] = {}

    def cite(m: re.Match) -> str:
        keys = m.group(1).split(",")
        for k in keys:
            if k not in refs:
                raise KeyError(f"no reference {k}")
            cite_no.setdefault(k, len(cite_no) + 1)
        nums = sorted(cite_no[k] for k in keys)
        return '<span class="cite">[' + ", ".join(f'<a href="#ref-{k}">{cite_no[k]}</a>' for k in sorted(keys, key=cite_no.get)) + "]</span>"

    def inline(m: re.Match) -> str:
        name, punct = m.group(1), m.group(2)
        d = diagram(directory / "diagrams" / "inline" / f"{name}.svg")
        w = f' width="{round(d["width"] * 1.5)}"' if d["width"] else ""
        return f'<span class="tnd"><img class="tni" src="{d["src"]}" alt="{html.escape(d["alt"])}"{w}>{punct}</span>'

    def text(s: str) -> str:
        return CITE_SLOT.sub(cite, INLINE_SLOT.sub(inline, s or ""))

    out = []
    out.append(f'''<div class="mast">
  <nav class="eyebrow">{html.escape(pres["eyebrow"])}</nav>
  <h1>{pres["heading"]}</h1>
  <p class="lede">{text(pres["lede"])}</p>
  <div class="stamp">{"".join(f"<span>{s}</span>" for s in pres.get("stamp", []))}</div>
</div>''')
    # theorems
    out.append('<section><header><div class="eyebrow">The two theorems</div><h2>What is proved</h2></header><div class="thmgrid">')
    for t in pres["theorems"]:
        fig = ""
        if t.get("diagram"):
            d = diagram(directory / t["diagram"])
            fig = f'<img class="fig tnimg" src="{d["src"]}" alt="{html.escape(d["alt"])}">'
        out.append(f'''<div class="thm"><div class="eyebrow">{html.escape(t["eyebrow"])}</div><h3>{t["title"]}</h3>
<p class="stmt">{text(t["statement"])}</p><div class="formula">{t["formula"]}</div>{fig}
<p class="defs">{text(t["defs"])}</p><p class="why">{text(t["why"])}</p></div>''')
    out.append("</div></section>")
    # map table
    if pres.get("map"):
        out.append('<section><header><div class="eyebrow">Two dimensions to one</div><h2>What survives, what simplifies, what disappears</h2></header><div class="tablebox"><table class="mapt"><thead><tr><th>Two-dimensional ingredient</th><th>Fate in one dimension</th></tr></thead><tbody>')
        for a, b in pres["map"]:
            out.append(f"<tr><td>{a}</td><td>{b}</td></tr>")
        out.append("</tbody></table></div></section>")
    # routes
    for route in pres["routes"]:
        out.append(f'<section class="part route-wrap"><div class="route" id="{route["id"]}"><header><div class="eyebrow">{html.escape(route["eyebrow"])}</div><h2>{route["heading"]}</h2><p>{text(route["intro"])}</p></header>')
        for idx, st in enumerate(route["stages"]):
            figs = []
            if st.get("symbols"):
                figs.append('<div class="key"><div class="keyhead">Symbols on this stage</div><dl>' + "".join(f"<div><dt>{a}</dt><dd>{b}</dd></div>" for a, b in st["symbols"]) + "</dl></div>")
            for d in st.get("diagrams", []):
                dd = diagram(directory / d["src"])
                w = f' width="{round(dd["width"] * 2.4)}"' if dd["width"] else ""
                alt = html.escape(re.sub(r"<[^>]+>", "", d.get("alt") or dd["alt"] or d.get("caption", "")))
                figs.append(f'<figure class="sfig tnfig"><img src="{dd["src"]}" alt="{alt}"{w}>' + (f'<figcaption>{text(d["caption"])}</figcaption>' if d.get("caption") else "") + "</figure>")
            secs = f'<span class="secs">{html.escape(st["secs"])}</span>' if st.get("secs") else ""
            phys = "".join(f'<p class="phys">{text(p)}</p>' for p in (st["physics"] if isinstance(st["physics"], list) else [st["physics"]]))
            prec = ""
            if st.get("precisely"):
                prec = '<div class="twice">Precisely</div><div class="prec">' + "".join(f"<p>{text(p)}</p>" for p in st["precisely"]) + "</div>"
            out.append(f'''<div class="stage" id="stage-{route["id"]}-{idx+1}">
  <div class="rail"><div class="dot">{idx+1}</div><div class="line"></div></div>
  <div class="body"><div class="head"><h3>{html.escape(st["title"])}</h3>{secs}</div>
    <div class="lead {'hasfig' if figs else ''}"><div class="txt"><div class="twice">In words</div>{phys}
      <p class="out"><span class="sc">Delivers</span> {text(st["delivers"])}</p>{prec}</div>
      {'<div class="figs">' + "".join(figs) + '</div>' if figs else ''}</div>
  </div></div>''')
        out.append("</div></section>")
    # glossary
    if pres.get("glossary"):
        out.append('<section class="part"><header><h2>Terms used here</h2></header><dl class="glossary">' + "".join(f"<div><dt>{a}</dt><dd>{b}</dd></div>" for a, b in pres["glossary"]) + "</dl></section>")
    # references
    if cite_no:
        out.append('<section class="part" id="refs"><header><div class="eyebrow">Sources</div><h2>References</h2></header><ol class="refs">')
        for k, n in sorted(cite_no.items(), key=lambda kv: kv[1]):
            r = refs[k]
            venue = f", {r['venue']}" if r.get("venue") else ""
            out.append(f'<li id="ref-{k}">{html.escape(r["authors"])}, <i>{html.escape(r["title"])}</i>{venue} ({r["year"]}). <a href="{r["url"]}" target="_blank" rel="noopener">{html.escape(r["url"])}</a></li>')
        out.append("</ol></section>")
    out.append(f'<p class="note">{text(pres.get("footer", ""))}</p>')

    css = (ROOT / "scripts" / "campaign_board" / "board.css").read_text() + EXTRA_CSS
    page = f'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>{html.escape(pres["pageTitle"])}</title>
<meta name="description" content="{html.escape(pres.get("description", ""))}">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Newsreader:ital,opsz,wght@0,6..72,400;0,6..72,500;0,6..72,600;1,6..72,400&family=IBM+Plex+Sans:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500&family=Noto+Sans+Math&display=swap">
<script>window.MathJax = {{tex: {{inlineMath: [['\\\\(','\\\\)']], displayMath: [['\\\\[','\\\\]']]}}}};</script>
<script src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml-full.js"></script>
<style>
{css}
</style>
</head>
<body>
<div class="wrap">
{"".join(out)}
</div>
</body>
</html>
'''
    target = directory / "digest.html"
    target.write_text(page)
    # The same page as an Artifact body: the publish step wraps it in its own skeleton.
    artifact = ('<title>One-Dimensional Collar-Free Route</title>\n'
                '<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Newsreader:ital,opsz,wght@0,6..72,400;0,6..72,500;0,6..72,600;1,6..72,400&family=IBM+Plex+Sans:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500&family=Noto+Sans+Math&display=swap">\n'
                '<script>window.MathJax = {tex: {inlineMath: [["\\\\(","\\\\)"]], displayMath: [["\\\\[","\\\\]"]]}};</script>\n'
                '<script src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml-full.js"></script>\n'
                '<style>\n' + css + '\nbody { margin: 0; padding-left: max(16px, env(safe-area-inset-left, 0px)); padding-right: max(16px, env(safe-area-inset-right, 0px)); }\n.wrap { padding-inline: 0; }\n</style>\n'
                '<div class="wrap">\n' + "".join(out) + '\n</div>\n')
    (directory / "artifact_page.html").write_text(artifact)
    print(f"{target}: {target.stat().st_size // 1024} KiB, {len(cite_no)} references")


if __name__ == "__main__":
    main()
