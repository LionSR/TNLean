"""Check the four PR #8824 prose repairs against an already rendered fixture.

Usage: python3 checks.py REPOSITORY FOCUSED_FIXTURE
Does not compile Lean, rebuild documents, access the network, or mutate inputs.
"""

from collections import Counter
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit
import hashlib
import json
import os
import re
import subprocess
import sys

from pypdf import PdfReader


repo, fixture = map(Path, sys.argv[1:])
revision = os.environ.get("SOURCE_REVISION", "c3e93223e69ea89bc06ea5305c3b8d15a60c8adc")
leaf = "blueprint/src/chapter/ch24_peps_angular_reset_width.tex"
lean_path = "TNLean/PEPS/Approximation/AngularResetWidth.lean"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=repo)


def sha(data):
    return hashlib.sha256(data).hexdigest()


before = git("show", f"{revision}^:{leaf}").decode()
after = git("show", f"{revision}:{leaf}").decode()
expected = before.replace(
    "Uniform width at every processed scale", "Uniform width at every scale"
).replace("every processed layer", "every annular layer")
dependencies = [
    "thm:peps_reset_polylog_width",
    "thm:peps_angular_reset_uniform_width",
]
for dependency, following in zip(dependencies, ["Take $S$", "If $w(L,s)"]):
    tag = "    \\uses{" + dependency + "}\n"
    assert expected.count(tag) == 1
    expected = expected.replace(tag, "")
    proof_start = "\\begin{proof}\n    \\leanok\n"
    needle = proof_start + "    " + following
    assert expected.count(needle) == 1
    expected = expected.replace(needle, proof_start + tag + "    " + following)
assert after == expected
assert (repo / leaf).read_text() == (fixture / leaf).read_text() == after
changed = git("diff", "--name-only", revision + "^", revision).decode().splitlines()
assert changed == [leaf]
assert git("show", f"{revision}^:{lean_path}") == git("show", f"{revision}:{lean_path}")
assert (repo / lean_path).read_bytes() == git("show", f"{revision}:{lean_path}")
statements = re.findall(r"\\begin\{(?:theorem|corollary)\}.*?\\end\{(?:theorem|corollary)\}", after, re.S)
assert len(statements) == 3 and all("\\uses" not in s for s in statements)
assert after.count("\\leanok") == 6
assert "processed" not in after


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.ids, self.anchors, self.links, self.declarations = [], set(), [], []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.append(attrs["id"])
            self.anchors.add(attrs["id"])
        if tag == "a" and "name" in attrs:
            self.anchors.add(attrs["name"])
        if tag == "a" and "href" in attrs:
            self.links.append(attrs["href"])
            if "lean_decl" in attrs.get("class", "").split():
                self.declarations.append(attrs["href"])


web = fixture / "blueprint/web"
pages = {p.name: Page(p.read_text()) for p in web.glob("*.html")}
chapter = pages["sect0001.html"]
names = [n.strip() for group in re.findall(r"\\lean\{([^}]+)\}", after) for n in group.split(",")]
assert len(names) == len(set(names)) == 4
for name in names:
    assert re.search(r"^theorem\s+" + re.escape(name.split(".")[-1]) + r"\b", (repo / lean_path).read_text(), re.M)
html_names = [unquote(urlsplit(h).fragment).removeprefix("doc/") for h in chapter.declarations]
assert Counter(names) == Counter(html_names)
labels = re.findall(r"\\label\{([^}]+)\}", after)
assert len(labels) == 7 and set(labels) <= chapter.anchors
internal_links = 0
for name, page in pages.items():
    assert len(page.ids) == len(set(page.ids))
    for href in page.links:
        url = urlsplit(href)
        if url.scheme or url.netloc or ".." in Path(url.path).parts:
            continue
        target = url.path or name
        if target.endswith(".html"):
            internal_links += 1
            assert target in pages, href
            assert not url.fragment or unquote(url.fragment) in pages[target].anchors, href

edges = [
    (dependencies[0], dependencies[1]),
    (dependencies[1], "cor:peps_angular_reset_width_fits"),
]
graph_checks = {}
for name in ["dep_graph_document.html", "dep_graph_chapter_1.html"]:
    content = (web / name).read_text()
    dot = re.search(r"\.renderDot\(`(.*?)`\)", content, re.S).group(1)
    actual = re.findall(r'"([^"]+)"\s*->\s*"([^"]+)"\s*;', dot)
    assert Counter(actual) == Counter(edges)
    assert "style=dashed" not in dot
    assert "Uniform width at every scale" in content and "processed" not in content
    graph_checks[name] = {"proof_edges": actual, "statement_edges": 0}

src = fixture / "blueprint/src"
reader = PdfReader(src / "print.pdf")
pdf_names = []
for page in reader.pages:
    box = list(map(float, page.mediabox))
    for ref in page.get("/Annots", []):
        obj = ref.get_object()
        url = obj.get("/A", {}).get("/URI", "")
        if "/find/" in url and "#doc/" in url:
            pdf_names.append(unquote(urlsplit(url).fragment).removeprefix("doc/"))
        if "/Rect" in obj:
            rect = list(map(float, obj["/Rect"]))
            assert box[0] <= rect[0] <= rect[2] <= box[2]
            assert box[1] <= rect[1] <= rect[3] <= box[3]
assert Counter(names) == Counter(pdf_names)
pdftext = "\n".join(p.extract_text() for p in reader.pages)
for phrase in ["Uniform width at every scale", "every annular layer"]:
    assert phrase in pdftext and phrase in (web / "sect0001.html").read_text()
assert "processed" not in pdftext
assert all("\\newlabel{" + label + "}" in (src / "print.aux").read_text() for label in labels)
assert not re.search(r"^!|Overfull|Underfull|Missing character|undefined", (src / "print.log").read_text(), re.M)
assert not re.search(r"WARNING: unrecognized (command|environment)|Using default renderer|^ERROR:|Traceback", (fixture / "web-build.log").read_text(), re.M)
assert pdftext.count("Stmt") == 3 and pdftext.count("\u2713 Proof") == 3

print(json.dumps({
    "source_revision": revision,
    "parent_revision": git("rev-parse", revision + "^").decode().strip(),
    "changed_paths": changed,
    "exact_four_requested_changes": True,
    "production_lean_byte_identical_to_parent": True,
    "source_leaf_sha256": sha(after.encode()),
    "source_leaf_parent_sha256": sha(before.encode()),
    "production_lean_sha256": sha((repo / lean_path).read_bytes()),
    "declarations": names,
    "source_labels": labels,
    "source_checked_markers": 6,
    "pdf_pages": len(reader.pages),
    "pdf_declaration_links": len(pdf_names),
    "html_declaration_links": len(html_names),
    "html_pages_checked": len(pages),
    "static_internal_html_links_checked": internal_links,
    "dependency_graphs": graph_checks,
    "layout_errors": 0,
    "unresolved_static_anchors": 0,
    "duplicate_html_ids": 0,
    "invalid_pdf_annotation_rectangles": 0,
}, indent=2))
