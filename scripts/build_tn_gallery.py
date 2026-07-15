#!/usr/bin/env python3
"""Build the labelled tensor-network audit gallery.

The gallery is derived entirely from the public TeX declarations.  It contains
every registered atom, every chapter-facing diagram, and every dark-theme slide
diagram.  No second diagram registry is maintained here.
"""

from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "blueprint/src"
BUILD = ROOT / "tmp/tn-gallery"
OUTPUT = ROOT / "output/pdf/tn_diagram_audit_gallery.pdf"
SEMANTIC_OUTPUT = ROOT / "output/tn_diagram_semantic_graphs.json"
RENDERER = SRC / "Packages/tn_diagrams.py"


def load_renderer():
    sys.path.insert(0, str(RENDERER.parent))
    spec = importlib.util.spec_from_file_location("tn_diagrams_gallery", RENDERER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {RENDERER}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def labelled_page(label: str, body: str) -> str:
    return rf"""
\clearpage
\noindent\texttt{{\detokenize{{{label}}}}}
\vfill
\begin{{center}}
\adjustbox{{margin=3pt}}{{{body}}}
\end{{center}}
\vfill
"""


def declared_diagram_page(declaration) -> str:
    contexts = ", ".join(declaration.contexts)
    label = (
        f"{declaration.name} | role={declaration.role} | "
        f"profile={declaration.profile} | context={contexts}"
    )
    return rf"""
\clearpage
\noindent\texttt{{\detokenize{{{label}}}}}

\vspace{{1.5em}}
\noindent Actual publication size
\begin{{center}}
\adjustbox{{margin=3pt}}{{{declaration.sample}}}
\end{{center}}

\vfill
\noindent Magnified inspection view
\begin{{center}}
\scalebox{{1.75}}{{\adjustbox{{margin=3pt}}{{{declaration.sample}}}}}
\end{{center}}
\vfill
"""


def light_source(renderer) -> str:
    pages = []
    for atom in renderer.atom_declarations():
        port_schema = ", ".join(
            f"{port.name}:{port.kind}" for port in atom.ports
        ) or "no ports"
        pages.append(
            labelled_page(
                f"{atom.name} | profile={atom.profile} | ports={port_schema}",
                atom.sample,
            )
        )

    for declaration in renderer.diagram_declarations():
        pages.append(declared_diagram_page(declaration))

    return rf"""\documentclass[10pt]{{article}}
\usepackage[paperwidth=18in,paperheight=12in,margin=0.55in]{{geometry}}
\usepackage{{amsmath,amssymb,amsthm,mathtools,tikz,graphicx,adjustbox}}
\newcounter{{chapter}}
\pagestyle{{empty}}
\input{{macros/common}}
\input{{macros/tn_print}}
\begin{{document}}
{''.join(pages)}
\end{{document}}
"""


def dark_source(renderer) -> str:
    pages = [
        labelled_page(name, call)
        for name, call in renderer.slide_diagram_samples()
    ]
    return rf"""\documentclass[10pt]{{article}}
\usepackage[paperwidth=18in,paperheight=12in,margin=0.55in]{{geometry}}
\usepackage{{amsmath,amssymb,amsthm,mathtools,tikz,xcolor,adjustbox}}
\newcounter{{chapter}}
\definecolor{{darkbg}}{{RGB}}{{21,21,21}}
\definecolor{{cardbg}}{{RGB}}{{30,30,30}}
\definecolor{{dimwhite}}{{RGB}}{{180,180,180}}
\definecolor{{leangreen}}{{RGB}}{{34,180,34}}
\definecolor{{leanblue}}{{RGB}}{{70,130,180}}
\definecolor{{amber}}{{RGB}}{{255,191,0}}
\definecolor{{softred}}{{RGB}}{{220,80,80}}
\pagecolor{{darkbg}}\color{{white}}
\pagestyle{{empty}}
\input{{macros/common}}
\input{{../../docs/slides/tn_library_dark}}
\begin{{document}}
{''.join(pages)}
\end{{document}}
"""


def compile_tex(stem: str, source: str) -> Path:
    BUILD.mkdir(parents=True, exist_ok=True)
    tex = BUILD / f"{stem}.tex"
    tex.write_text(source, encoding="utf-8")
    result = subprocess.run(
        [
            "latexmk",
            "-lualatex",
            "-interaction=nonstopmode",
            "-halt-on-error",
            f"-outdir={BUILD}",
            str(tex),
        ],
        cwd=SRC,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode:
        raise RuntimeError(f"Gallery build failed for {stem}:\n{result.stdout}")
    return BUILD / f"{stem}.pdf"


def _event_fields(line: str) -> tuple[str, dict[str, str]]:
    parts = line.strip().split("|")
    fields = {}
    for part in parts[1:]:
        if "=" in part:
            key, value = part.split("=", 1)
            fields[key] = value
    return parts[0], fields


def semantic_graphs(event_log: Path, *, theme: str) -> list[dict[str, object]]:
    """Validate and canonicalize the semantic events emitted by TeX."""

    if not event_log.exists():
        raise RuntimeError(f"Missing tensor-network semantic log: {event_log}")
    current_diagram = "atom-catalogue"
    pictures: dict[str, dict[str, object]] = defaultdict(
        lambda: {
            "diagram": current_diagram,
            "atoms": {},
            "ports": {},
            "aliases": [],
            "connections": [],
            "motifs": [],
        }
    )
    for raw_line in event_log.read_text(encoding="utf-8").splitlines():
        kind, fields = _event_fields(raw_line)
        if kind == "diagram":
            current_diagram = fields.get("name", "unnamed")
            continue
        picture = fields.get("picture")
        if picture is None:
            continue
        record = pictures[picture]
        record["diagram"] = current_diagram
        if kind in {"atom", "port"}:
            collection = record[f"{kind}s"]
            assert isinstance(collection, dict)
            name = fields["name"]
            if name in collection:
                raise RuntimeError(f"Duplicate {kind} {name} in picture {picture}")
            collection[name] = fields["kind" if kind == "atom" else "type"]
        elif kind in {"alias", "connection", "motif"}:
            collection = record[f"{kind}s"]
            assert isinstance(collection, list)
            collection.append(fields)

    canonical = []
    for picture, record in sorted(pictures.items(), key=lambda item: int(item[0])):
        ports = record["ports"]
        aliases = record["aliases"]
        connections = record["connections"]
        assert isinstance(ports, dict)
        assert isinstance(aliases, list)
        assert isinstance(connections, list)
        for alias in aliases:
            source = alias["source"]
            if source not in ports or ports[source] != alias["type"]:
                raise RuntimeError(
                    f"Invalid alias {alias['name']} -> {source} in picture {picture}"
                )
        for connection in connections:
            if connection["from"] == connection["to"]:
                raise RuntimeError(f"Self-connection in picture {picture}")
            for endpoint in (connection["from"], connection["to"]):
                if endpoint not in ports or ports[endpoint] != connection["type"]:
                    raise RuntimeError(
                        f"Invalid {connection['type']} endpoint {endpoint} "
                        f"in picture {picture}"
                    )

        atoms = record["atoms"]
        motifs = record["motifs"]
        assert isinstance(atoms, dict)
        assert isinstance(motifs, list)
        canonical.append(
            {
                "theme": theme,
                "picture": int(picture),
                "diagram": record["diagram"],
                "atoms": sorted(
                    [
                        {"name": name, "kind": atom_kind}
                        for name, atom_kind in atoms.items()
                    ],
                    key=lambda item: (item["name"], item["kind"]),
                ),
                "ports": sorted(
                    [
                        {"name": name, "type": port_type}
                        for name, port_type in ports.items()
                    ],
                    key=lambda item: (item["name"], item["type"]),
                ),
                "aliases": sorted(
                    aliases,
                    key=lambda item: (item["name"], item["source"], item["type"]),
                ),
                "connections": sorted(
                    connections,
                    key=lambda item: (
                        item["type"], item["from"], item["to"], item["route"]
                    ),
                ),
                "motifs": sorted(
                    motifs,
                    key=lambda item: (item.get("name", ""), item.get("kind", "")),
                ),
            }
        )
    return canonical


def main() -> int:
    renderer = load_renderer()
    light = compile_tex("tn_gallery_light", light_source(renderer))
    dark = compile_tex("tn_gallery_dark", dark_source(renderer))
    graphs = semantic_graphs(BUILD / "tn_gallery_light.tnlog", theme="print")
    graphs.extend(semantic_graphs(BUILD / "tn_gallery_dark.tnlog", theme="dark"))
    SEMANTIC_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    SEMANTIC_OUTPUT.write_text(
        json.dumps(graphs, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    pdfunite = shutil.which("pdfunite")
    if pdfunite is None:
        raise RuntimeError("pdfunite is required to assemble the audit gallery")
    subprocess.run([pdfunite, str(light), str(dark), str(OUTPUT)], check=True)
    print(OUTPUT)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
