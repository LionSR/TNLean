#!/usr/bin/env python3
"""Render a campaign board page from a snapshot.

    python3 scripts/campaign_board/render.py CAMPAIGN_DIR SNAPSHOT.json OUT_DIR

Writes OUT_DIR/index.html, a self-contained page whose only external requests
are Google Fonts, and OUT_DIR/data.json, the snapshot with the campaign's
configuration and gap summaries merged in.

CAMPAIGN_DIR provides config.json, gaps.json, and optionally intro.html,
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


def diagrams(campaign_dir: pathlib.Path, config: dict) -> dict:
    """Inline every stage diagram as a data URI with its natural width in points."""
    out = {}
    for route in config["routes"]:
        for stage in route["stages"]:
            if "diagram" not in stage:
                continue
            svg = (campaign_dir / stage["diagram"]).read_bytes()
            width = re.search(rb'<svg[^>]*\bwidth="([0-9.]+)', svg)
            out[stage["diagram"]] = {
                "src": "data:image/svg+xml;base64," + base64.b64encode(svg).decode("ascii"),
                "width": float(width.group(1)) if width else None,
            }
    return out


def render(campaign_dir: pathlib.Path, snapshot_path: pathlib.Path, out_dir: pathlib.Path) -> pathlib.Path:
    config = json.loads((campaign_dir / "config.json").read_text())
    gaps_path = campaign_dir / "gaps.json"
    data = json.loads(snapshot_path.read_text())
    primary = next(r for r in config["repos"] if r.get("primary"))
    blob_url = f"https://github.com/{primary['slug']}/blob/main/"
    gaps_rel = gaps_path.resolve().relative_to(ROOT).as_posix()
    data["diagrams"] = diagrams(campaign_dir, config)
    data.update({
        "config": config,
        "gaps": json.loads(gaps_path.read_text()) if gaps_path.exists() else {"entries": [], "checked": []},
        "meta": {"workflowUrl": blob_url + WORKFLOW, "gapsPath": gaps_rel, "gapsUrl": blob_url + gaps_rel},
    })
    intro = campaign_dir / "intro.html"
    figures = campaign_dir / "figures.js"
    replacements = {
        "{{TITLE}}": html.escape(config["pageTitle"]),
        "{{DESCRIPTION}}": html.escape(config.get("description", "")),
        "{{CSS}}": (HERE / "board.css").read_text(),
        "{{INTRO}}": intro.read_text() if intro.exists() else "",
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
