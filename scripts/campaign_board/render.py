#!/usr/bin/env python3
"""Render a campaign board page from a snapshot.

    python3 scripts/campaign_board/render.py CAMPAIGN_DIR SNAPSHOT.json OUT_DIR

Writes OUT_DIR/index.html, a self-contained page whose only external requests
are Google Fonts, and OUT_DIR/data.json, the snapshot with the campaign's
configuration and gap summaries merged in.

CAMPAIGN_DIR provides config.json, gaps.json, and optionally intro.html,
references.json (the works that {{cite:Key}} tokens in the texts cite),
figures.js (the stage figures named in config.json) and the tensor-network
diagrams under diagrams/ that stages name, which are inlined as data URIs and
are compiled by build_diagrams.py; the page shell,
stylesheet and script are shared by every campaign and live next to this file.
"""
from __future__ import annotations

import base64
import html
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORKFLOW = ".github/workflows/campaign-board.yml"


DIAGRAM_SLOT = re.compile(r"\{\{DIAGRAM:([^}]+)\}\}")
INLINE_SLOT = re.compile(r"\{\{tn:([A-Za-z0-9_-]+)\}\}")
CITE_SLOT = re.compile(r"\{\{cite:([A-Za-z0-9_,-]+)\}\}")


ALT_LINE = re.compile(r"^% alt: (.+)$", re.MULTILINE)


def diagram(campaign_dir: pathlib.Path, path: str) -> dict:
    """One compiled diagram as a data URI with its natural width in points.

    The alternative text is the `% alt:` line of the diagram's source, if any.
    """
    svg_path = campaign_dir / path
    svg = svg_path.read_bytes()
    width = re.search(rb'<svg[^>]*\bwidth="([0-9.]+)', svg)
    source = svg_path.with_suffix(".tex")
    alt = ALT_LINE.search(source.read_text()) if source.exists() else None
    return {
        "src": "data:image/svg+xml;base64," + base64.b64encode(svg).decode("ascii"),
        "width": float(width.group(1)) if width else None,
        "alt": alt.group(1).strip() if alt else "",
    }


def diagrams(campaign_dir: pathlib.Path, config: dict) -> dict:
    """Inline every diagram a stage names, keyed by its path."""
    return {d["src"]: diagram(campaign_dir, d["src"])
            for route in config["routes"] for stage in route["stages"]
            for d in stage.get("diagrams", [])}


def inline_diagrams(campaign_dir: pathlib.Path, *texts: dict) -> dict:
    """Inline every {{tn:name}} equation the given configuration and gap texts use, keyed by name."""
    names = {name for text in texts for name in INLINE_SLOT.findall(json.dumps(text, ensure_ascii=False))}
    return {name: diagram(campaign_dir, f"diagrams/inline/{name}.svg") for name in sorted(names)}


GAP_TEXT_FIELDS = ("summary", "context", "claims", "found", "impact", "plan")


def cited_texts(config: dict, gaps: dict) -> list[str]:
    """The texts the page renders citations in: route introductions, stage prose and
    captions, and the gap entries' prose fields.

    A stage's schematic caption is shown only when figures.js defines its figure, which
    this script cannot check; a citation there with no such figure is not shown."""
    texts = []
    for route in config["routes"]:
        texts.append(route.get("intro", ""))
        for stage in route["stages"]:
            texts += [stage.get("physics", ""), stage.get("delivers", ""), stage.get("caption", "")]
            texts += [d.get("caption", "") for d in stage.get("diagrams", [])]
    for entry in gaps.get("entries", []):
        texts += [entry.get(f, "") for f in GAP_TEXT_FIELDS]
    return [t or "" for t in texts]


def references(campaign_dir: pathlib.Path, config: dict, gaps: dict) -> dict:
    """The works cited by {{cite:Key,...}} tokens in the page's texts, from references.json.

    A token naming a key absent from references.json, or a token in a field the page
    does not render citations in, stops the render, as a missing diagram does, so the
    page never shows a citation without its reference or a raw token.
    """
    path = campaign_dir / "references.json"
    library = json.loads(path.read_text()) if path.exists() else {}
    texts = cited_texts(config, gaps)
    everything = json.dumps([config, gaps], ensure_ascii=False)
    malformed = everything.count("{{cite:") - len(CITE_SLOT.findall(everything))
    if malformed:
        raise ValueError(f"{malformed} malformed {{{{cite:...}}}} token(s): write {{{{cite:Key}}}} or "
                         "{{cite:Key1,Key2}}, with no spaces")
    rendered = sum(len(CITE_SLOT.findall(t)) for t in texts)
    if len(CITE_SLOT.findall(everything)) != rendered:
        raise ValueError("{{cite:...}} tokens may appear only in route introductions, stage "
                         "physics, delivers and captions, and gap prose fields")
    keys = {k for text in texts for m in CITE_SLOT.findall(text) for k in m.split(",")}
    missing = sorted(keys - library.keys())
    if missing:
        raise KeyError(f"{path}: no entry for cited keys {', '.join(missing)}")
    for k in sorted(keys):
        entry = library[k]
        bad = [f for f in ("authors", "title", "url") if not isinstance(entry.get(f), str) or not entry[f].strip()]
        bad += [] if type(entry.get("year")) is int else ["year"]  # bool is an int subclass
        bad += [] if isinstance(entry.get("venue", ""), str) else ["venue"]
        if bad:
            raise ValueError(f"{path}: entry {k} lacks a valid {', '.join(bad)}")
    return {k: library[k] for k in sorted(keys)}


def intro_html(campaign_dir: pathlib.Path) -> str:
    """The campaign introduction, with each {{DIAGRAM:path}} slot replaced by its image."""
    intro = campaign_dir / "intro.html"
    if not intro.exists():
        return ""

    def image(m: re.Match) -> str:
        d = diagram(campaign_dir, m.group(1))
        width = f' width="{round(d["width"] * 2.4)}"' if d["width"] else ""
        return f'<img class="tnimg" src="{d["src"]}"{width} alt="{html.escape(d["alt"])}">'

    return DIAGRAM_SLOT.sub(image, intro.read_text())


def render(campaign_dir: pathlib.Path, snapshot_path: pathlib.Path, out_dir: pathlib.Path) -> pathlib.Path:
    config = json.loads((campaign_dir / "config.json").read_text())
    gaps_path = campaign_dir / "gaps.json"
    data = json.loads(snapshot_path.read_text())
    primary = next(r for r in config["repos"] if r.get("primary"))
    blob_url = f"https://github.com/{primary['slug']}/blob/main/"
    gaps_rel = gaps_path.resolve().relative_to(ROOT).as_posix()
    data["diagrams"] = diagrams(campaign_dir, config)
    gaps = json.loads(gaps_path.read_text()) if gaps_path.exists() else {"entries": [], "checked": []}
    data["inlineDiagrams"] = inline_diagrams(campaign_dir, config, gaps)
    data["references"] = references(campaign_dir, config, gaps)
    data.update({
        "config": config,
        "gaps": gaps,
        "meta": {"workflowUrl": blob_url + WORKFLOW, "gapsPath": gaps_rel, "gapsUrl": blob_url + gaps_rel},
    })
    figures = campaign_dir / "figures.js"
    replacements = {
        "{{TITLE}}": html.escape(config["pageTitle"]),
        "{{DESCRIPTION}}": html.escape(config.get("description", "")),
        "{{CSS}}": (HERE / "board.css").read_text(),
        "{{INTRO}}": intro_html(campaign_dir),
        "{{FIGURES}}": figures.read_text() if figures.exists() else "",
        "{{JS}}": (HERE / "board.js").read_text(),
        # Inline JSON must not close the surrounding <script> element.
        "{{DATA}}": json.dumps(data, separators=(",", ":"), ensure_ascii=False).replace("</", "<\\/"),
    }
    page = (HERE / "page.html").read_text()
    for slot, value in replacements.items():
        page = page.replace(slot, value)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "index.html").write_text(page)
    (out_dir / "data.json").write_text(json.dumps(data, indent=1, ensure_ascii=False))
    return out_dir / "index.html"


def main() -> None:
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    index = render(*(pathlib.Path(a) for a in sys.argv[1:]))
    print(f"{index}: {index.stat().st_size // 1024} KiB")


if __name__ == "__main__":
    main()
