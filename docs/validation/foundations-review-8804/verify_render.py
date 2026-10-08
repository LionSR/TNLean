#!/usr/bin/env python3
"""Verify the focused PDF/static HTML and both directions of source coverage."""

import argparse
from collections import Counter
from dataclasses import asdict
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit


RETIRED = [
    "card_le_square_of_latticeL1Distance_le", "card_le_square_of_walks",
    "card_le_square_of_edist_le", "card_support_le_square",
    "card_supports_containing_le_square", "sum_supportWeights_containing_le_square",
    "interactionChainWeightSum_le_lattice_pow",
]
RETIRED_LABELS = ["thm:area_square_count", "thm:area_lattice_budget"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Scan(HTMLParser):
    def __init__(self):
        super().__init__()
        self.ids, self.anchors, self.hrefs, self.lean = [], [], [], []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.append(attrs["id"])
            self.anchors.append(attrs["id"])
        if tag == "a" and "name" in attrs:
            self.anchors.append(attrs["name"])
        if "href" in attrs:
            self.hrefs.append(attrs["href"])
        if "lean_decl" in attrs.get("class", "").split():
            self.lean.append(attrs.get("href", ""))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--visual-review", type=Path)
    args = parser.parse_args()
    root, out = args.root.resolve(), args.out.resolve()
    snapshot, src, web = out / "source", out / "blueprint/src", out / "blueprint/web"
    manifest = json.loads((out / "focus-manifest.json").read_text())
    revision = manifest["source_revision"]

    def command(*argv):
        return subprocess.check_output(argv, cwd=root, text=True)

    assert manifest["source_tree"] == command("git", "rev-parse", f"{revision}^{{tree}}").strip()

    # Bind every copied input to its actual immutable Git blob, independently
    # of the preparation manifest and any concurrent checkout metadata edits.
    tree = command("git", "ls-tree", "-r", revision)
    blobs = {row.split("\t", 1)[1]: row.split("\t", 1)[0].split()[2]
             for row in tree.splitlines() if row.split()[1] == "blob"}
    for name, digest in manifest["snapshot_inputs"].items():
        path = snapshot / name
        data = path.read_bytes()
        assert sha(path) == digest, name
        blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        assert blob == blobs[name], name
    sys.path.insert(0, str(snapshot / "scripts"))
    from blueprint_lean_sync import (  # noqa: E402
        collect_blueprint_entries, collect_blueprint_lean_refs, collect_file_lean_decls,
    )
    import test_blueprint_web_render as reader  # noqa: E402

    leaves = manifest["target_leaves"]
    text = "\n".join((snapshot / "blueprint/src/chapter" / name).read_text()
                     for name in leaves)
    for name, digest in leaves.items():
        assert sha(src / "chapter" / name) == digest, name
    entries = [entry for entry in collect_blueprint_entries(snapshot / "blueprint/src")
               if any(entry.file.endswith(name) for name in leaves)]
    names = [entry.lean_decl for entry in entries]
    assert len(names) == len(set(names)) == 43
    assert all(entry.has_leanok for entry in entries)
    refs = collect_blueprint_lean_refs(snapshot / "blueprint/src")
    owners = Counter(entry.lean_decl for entry in refs)
    assert all(owners[name] == 1 for name in names)
    assert not any(owners[f"TNLean.PEPS.AreaLaw.{name}"] for name in RETIRED)
    decls = [decl for path in manifest["production_modules"]
             for decl in collect_file_lean_decls(snapshot / path, snapshot / "TNLean")]
    public = [decl for decl in decls if not decl.is_private]
    private = [decl for decl in decls if decl.is_private]
    assert len(public) == 43 and len(private) == 5
    assert set(names) == {decl.fqn for decl in public}
    assert not ({decl.fqn for decl in private} & set(names))
    production_lines = sum(len((snapshot / path).read_text().splitlines())
                           for path in manifest["production_modules"])
    assert production_lines == 1202
    assert set((out / "blueprint/lean_decls").read_text().splitlines()) == set(names)
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    assert len(labels) == len(set(labels))
    global_labels = Counter()
    global_dependencies = []
    for path in (snapshot / "blueprint/src").rglob("*.tex"):
        source = path.read_text()
        global_labels.update(re.findall(r"\\label\{([^}]+)\}", source))
        for payload in re.findall(r"\\(?:uses|ref|eqref|autoref)\{([^}]+)\}", source):
            global_dependencies.extend(name.strip() for name in payload.split(","))
    assert all(global_labels[label] == 1 for label in labels)
    assert not (set(RETIRED_LABELS) & (set(global_labels) | set(global_dependencies)))
    local_references = re.findall(r"\\(?:ref|eqref|autoref)\{([^}]+)\}", text)
    uses = [name.strip() for group in re.findall(r"\\uses\{([^}]+)\}", text)
            for name in group.split(",")]
    assert set(local_references + uses) <= set(labels)
    indicator = text.split(r"\label{thm:area_target_indicator}", 1)[1]
    indicator_proof = indicator.split(r"\begin{proof}", 1)[1].split(r"\end{proof}", 1)[0]
    indicator_uses = [name.strip() for group in re.findall(r"\\uses\{([^}]+)\}", indicator_proof)
                      for name in group.split(",")]
    assert "thm:area_diamond_budget" not in indicator_uses
    assert text.count(r"\leanok") == 35
    proofs = re.findall(r"\\begin\{proof\}.*?\\end\{proof\}", text, re.S)
    assert len(proofs) == 15 and all(r"\leanok" in proof for proof in proofs)
    entry_count = len(re.findall(r"\\begin\{(?:definition|theorem|lemma|corollary)\}", text))
    assert entry_count == 20
    pictures = re.findall(r"\\begin\{(?:tenkz|tikzpicture|tikzcd)\}|\\tnpic\b", text)
    assert not pictures

    html_paths = reader._generated_pages(web)
    reader._assert_generated_source(html_paths)
    pages = {}
    for path in html_paths:
        scanner = Scan()
        scanner.feed(path.read_text())
        pages[path.name] = scanner
    missing, duplicates, sentinels = [], [], []
    for name, page in pages.items():
        duplicates += [(name, key) for key, count in Counter(page.ids).items() if count > 1]
        for link in page.hrefs:
            target = urlsplit(link)
            if (target.scheme or target.netloc or not target.fragment
                    or (target.path and not target.path.endswith(".html"))):
                continue
            filename = target.path or name
            if filename not in pages or unquote(target.fragment) not in pages[filename].anchors:
                missing.append((name, link))
        html = (web / name).read_text()
        sentinels += [(name, marker) for marker in (
            "plastex-unknown", "??", "<merror", "<mjx-merror", "NaNpx", "nanpt",
        ) if marker in html]
    assert not missing and not duplicates and not sentinels, (missing, duplicates, sentinels)
    chapter = pages["ch-area_graph_foundations.html"]
    assert set(labels) <= set(chapter.anchors)
    html_names = [unquote(link.split("#doc/", 1)[-1]) for link in chapter.lean]
    assert Counter(html_names) == Counter(names)
    assert not set(RETIRED_LABELS) & set(chapter.anchors)
    graph_edges = {}
    for path in sorted(web.glob("dep_graph_*.html")):
        graph = re.search(r"\.renderDot\(`(.*?)`\)", path.read_text(), re.S)
        if not graph:
            continue
        edges = re.findall(r'"([^"\n]+)"\s*->\s*"([^"\n]+)"', graph.group(1))
        assert ("thm:area_diamond_budget", "thm:area_target_indicator") not in edges
        assert all((label, "thm:area_target_indicator") in edges for label in indicator_uses)
        assert not any(label in graph.group(1) for label in RETIRED_LABELS)
        graph_edges[path.name] = len(edges)
    assert graph_edges
    pdf = src / "print.pdf"
    info = command("pdfinfo", str(pdf))
    urls = command("pdfinfo", "-url", str(pdf))
    destinations = command("pdfinfo", "-dests", str(pdf))
    pdf_names = re.findall(r"#doc/([^\s]+)", urls)
    assert Counter(pdf_names) == Counter(names)
    aux, records = (src / "print.aux").read_text(), {}
    for label in labels:
        match = re.search(r"\\newlabel\{" + re.escape(label)
                          + r"\}\{\{([^}]*)\}\{([^}]*)\}\{[^}]*\}\{([^}]*)\}", aux)
        assert match, label
        number, page, destination = match.groups()
        assert f'"{destination}"' in destinations
        records[label] = {"number": number, "printed_page": int(page), "destination": destination}
    problems = [line for line in (src / "print.log").read_text().splitlines()
                if re.search(r"Overfull|undefined|Missing character|^!", line)]
    assert not problems, problems
    assert "??" not in (out / "print.txt").read_text()
    web_log = (out / "web-build.log").read_text()
    assert not re.search(r"^ERROR|could not be resolved|Traceback", web_log, re.M)
    page_count = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))
    page_images = sorted((out / "pdf-pages").glob("page-*.png"))
    assert len(page_images) == page_count
    visual = {"status": "pending direct visual inspection"}
    if args.visual_review:
        visual = json.loads(args.visual_review.read_text())
        assert visual["status"] == "passed"
        assert visual["page_image_sha256"] == {path.name: sha(path) for path in page_images}
    report = {
        "status": "passed focused PDF and static HTML verification",
        "source_revision": revision,
        "source_tree": manifest["source_tree"],
        "source_inputs": {name: manifest["snapshot_inputs"][name] for name in (
            *manifest["production_modules"],
            *(f"blueprint/src/chapter/{name}" for name in leaves),
        )},
        "immutable_snapshot_files_checked": len(manifest["snapshot_inputs"]),
        "focus_manifest_sha256": sha(out / "focus-manifest.json"),
        "public_declarations": [asdict(decl) for decl in public],
        "private_helpers": [asdict(decl) for decl in private],
        "coverage": {
            "production_modules": 7, "production_lines": production_lines,
            "public_declarations": 43, "unique_global_tag_owners": 43,
            "reverse_coverage_missing": [], "retired_declaration_tags": [],
            "retired_labels_or_references": [], "entries": entry_count,
            "proofs": len(proofs), "checked_markers": 35,
            "generated_lean_decls": 43, "pdf_declaration_links": 43,
            "html_declaration_links": 43, "source_labels": len(labels),
            "local_text_references": len(local_references), "uses_edges": len(uses),
            "indicator_proof_dependencies": indicator_uses,
        },
        "retired_declarations_checked": RETIRED,
        "retired_labels_checked": RETIRED_LABELS,
        "pdf_pages": page_count, "pdf_labels": records,
        "missing_html_anchors": missing, "duplicate_html_ids": duplicates,
        "html_error_sentinels": sentinels, "pdf_log_problems": problems,
        "dependency_graph_edges": graph_edges,
        "stale_diamond_to_indicator_graph_edge": False,
        "diagrams": 0, "tenkz_sweep": "not applicable: neither leaf contains a picture",
        "tools": manifest["tools"], "visual_review": visual,
        "warnings": [line for log in ("pdf-build.log", "web-build.log")
                     for line in (out / log).read_text().splitlines()
                     if re.search(r"warning|warn:", line, re.I)],
        "limits": [
            "Focused chapter PDF and static HTML only; no full-book, browser, MathJax runtime or mobile check.",
            "No Lean/Lake execution or cache mutation. Native and axiom checks are recorded separately.",
            "Declaration links have the exact source identifiers; remote URL availability was not checked.",
            "No physical commutator propagation, full Lemma 4.1, area law or PEPS approximation is certified.",
            "No remote publication, CI, review resolution or merge action was performed by this renderer.",
        ],
        "artifacts": {str(path.relative_to(out)): sha(path) for path in (
            pdf, *html_paths, *page_images,
            out / "pdf-build.log", out / "web-build.log", out / "print.txt",
        )},
    }
    (out / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    for name, body in (("pdf-info.txt", info), ("pdf-links.txt", urls),
                       ("pdf-destinations.txt", destinations)):
        (out / name).write_text(body)
    print(json.dumps({key: report[key] for key in (
        "status", "source_revision", "coverage", "pdf_pages", "pdf_log_problems",
        "missing_html_anchors", "duplicate_html_ids", "diagrams", "visual_review",
    )}, indent=2))


if __name__ == "__main__":
    main()
