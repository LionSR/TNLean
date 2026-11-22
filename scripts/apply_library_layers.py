#!/usr/bin/env python3
"""Apply the module map of ``docs/library_layers.md`` to the TNLean tree.

The map ``scripts/library_layers_module_map.txt`` has one line per module that
changes, ``Old.Module -> New.Module``; several old modules sent to one new
module are concatenated, each line then ending in ``@N``, the position of that
part in the concatenation (a part comes after every part it imports).  Lines
starting with ``#`` are comments.

``--check`` validates the map against the current tree and changes nothing:

* every old module exists (a missing one is reported and skipped: the tree is
  still changing, and modules move to QICLean);
* no new module collides with a module that stays, and two old modules share a
  new module only as numbered parts of a merge;
* every ``import TNLean.…`` of every module resolves after the map;
* the import graph after the map, merges included, has no cycle;
* every import points to an allowed layer (``LAYERS``/``ALLOWED`` below); every
  violation is reported;
* pairs of directories that import each other (at the depth used by
  ``scripts/check_import_layers.py``), before and after the map, and pairs of
  sibling subdirectories at any depth that import each other;
* directories with more than ``MAX_PER_LEVEL`` modules at one level;
* merged parts that declare the same private name or anonymous instances.

Without ``--check`` the map is applied: ``git mv`` for each move, concatenation
for each merge (imports unioned, module docstrings combined, each part wrapped
in its own ``section`` so that ``variable``, ``open`` and local attributes stay
local), rewriting of ``import`` lines in ``TNLean/`` and ``scripts/``, of module
names and paths in ``blueprint/src``, ``docs/``, ``CLAUDE.md`` and ``scripts/``
(never inside ``\\lean{…}``), and of ``MUTUAL_DIRECTORIES`` in
``scripts/check_import_layers.py``; the aggregators are then regenerated.  The
application is idempotent: an entry whose old module is gone and whose new
module exists is already applied.
"""

from __future__ import annotations

import argparse
import collections
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_import_syntax import strip_lean_comments  # noqa: E402

MAP_PATH = "scripts/library_layers_module_map.txt"
CHECKER_PATH = "scripts/check_import_layers.py"
MAX_PER_LEVEL = 40

# Layers after the map: module-name prefix -> layer, first match wins.
LAYERS: list[tuple[str, str]] = [
    ("TNLean.Algebra", "base"),
    ("TNLean.Tactic", "base"),
    ("TNLean.Circuit", "base"),
    ("TNLean.Lattice", "base"),
    ("TNLean.QCA", "base"),
    ("TNLean.QICLeanInterface", "base"),
    ("TNLean.MPS.Tensor", "MPS/Tensor"),
    ("TNLean.MPS.Transfer", "MPS/Transfer"),
    ("TNLean.MPS.Operator", "MPS/Operator"),
    ("TNLean.MPS.CanonicalForm", "MPS/CanonicalForm"),
    ("TNLean.MPS.FundamentalTheorem", "MPS/FundamentalTheorem"),
    ("TNLean.MPS.ParentHamiltonian", "MPS/ParentHamiltonian"),
    ("TNLean.MPS.Symmetry", "MPS/Symmetry"),
    ("TNLean.MPS.MPDO", "MPS/MPDO"),
    ("TNLean.MPS.MPU", "MPS/MPU"),
    ("TNLean.MPS.Preparation", "MPS/Preparation"),
    ("TNLean.MPS.AreaLaw", "MPS/AreaLaw"),
    ("TNLean.MPS.RFP", "MPS/RFP"),
    ("TNLean.MPS.Examples", "MPS/Examples"),
    ("TNLean.PEPS.Graph", "PEPS/Graph"),
    ("TNLean.PEPS.Tensor", "PEPS/Tensor"),
    ("TNLean.PEPS.Injectivity", "PEPS/Injectivity"),
    ("TNLean.PEPS.FundamentalTheorem", "PEPS/FundamentalTheorem"),
    ("TNLean.PEPS.ParentHamiltonian", "PEPS/ParentHamiltonian"),
    ("TNLean.PEPS.AreaLaw", "PEPS/AreaLaw"),
    ("TNLean.PEPS.Approximation", "PEPS/Approximation"),
    ("TNLean.PEPS.Examples", "PEPS/Examples"),
]
# Directly allowed lower layers; the relation is closed transitively.
BELOW: dict[str, list[str]] = {
    "base": [],
    "MPS/Tensor": ["base"],
    "MPS/Transfer": ["MPS/Tensor"],
    "MPS/Operator": ["MPS/Transfer"],
    "MPS/CanonicalForm": ["MPS/Operator"],
    "MPS/FundamentalTheorem": ["MPS/CanonicalForm"],
    "MPS/ParentHamiltonian": ["MPS/FundamentalTheorem"],
    "MPS/Symmetry": ["MPS/ParentHamiltonian"],
    "MPS/MPDO": ["MPS/ParentHamiltonian"],
    "MPS/MPU": ["MPS/ParentHamiltonian"],
    "MPS/Preparation": ["MPS/ParentHamiltonian"],
    "MPS/AreaLaw": ["MPS/ParentHamiltonian"],
    "MPS/RFP": ["MPS/ParentHamiltonian"],
    "MPS/Examples": ["MPS/Symmetry", "MPS/MPDO", "MPS/MPU", "MPS/Preparation",
                     "MPS/AreaLaw", "MPS/RFP"],
    "PEPS/Graph": ["base"],
    "PEPS/Tensor": ["PEPS/Graph", "MPS/ParentHamiltonian"],
    "PEPS/Injectivity": ["PEPS/Tensor"],
    "PEPS/FundamentalTheorem": ["PEPS/Injectivity"],
    "PEPS/ParentHamiltonian": ["PEPS/FundamentalTheorem"],
    "PEPS/AreaLaw": ["PEPS/ParentHamiltonian"],
    "PEPS/Approximation": ["PEPS/AreaLaw"],
    "PEPS/Examples": ["PEPS/Approximation", "MPS/Examples"],
}


def _closure() -> dict[str, frozenset[str]]:
    out: dict[str, frozenset[str]] = {}

    def below(layer: str) -> set[str]:
        result: set[str] = set()
        for lower in BELOW[layer]:
            result |= {lower} | below(lower)
        return result

    for layer in BELOW:
        out[layer] = frozenset(below(layer) | {layer})
    return out


ALLOWED = _closure()
DEEP_ROOTS = frozenset({"MPS", "PEPS"})
IMPORT_RE = re.compile(
    r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_'.]*)\s*$"
)
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)\b\s*([^\s:({\[]*)"
)
PRIVATE_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*private\s+(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|instance)\s+([^\s:({\[]+)"
)
SCOPE_OPEN_RE = re.compile(r"^\s*(?:noncomputable\s+)?(namespace|section)\b\s*([^\s]*)")
SCOPE_END_RE = re.compile(r"^\s*end\b\s*([^\s]*)\s*$")
MODULE_DOC_RE = re.compile(r"/-!(.*?)-/", re.S)


# ----------------------------------------------------------------- reading
def layer_of(module: str) -> str | None:
    for prefix, layer in LAYERS:
        if module == prefix or module.startswith(prefix + "."):
            return layer
    return None


def module_of_path(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def path_of_module(module: str) -> str:
    return module.replace(".", "/") + ".lean"


class Tree:
    """The Lean sources below ``TNLean/``, from the working tree or a revision."""

    def __init__(self, root: Path, rev: str | None) -> None:
        self.root = root
        self.rev = rev
        if rev is None:
            listing = subprocess.run(
                ["git", "-C", str(root), "ls-files", "-co", "--exclude-standard", "--", "TNLean"],
                check=True, capture_output=True, text=True,
            ).stdout.split("\n")
            paths = [p for p in listing if p.endswith(".lean") and (root / p).exists()]
            self.sources = {module_of_path(p): (root / p).read_text(encoding="utf-8")
                            for p in paths}
        else:
            listing = subprocess.run(
                ["git", "-C", str(root), "ls-tree", "-r", "--name-only", rev, "TNLean"],
                check=True, capture_output=True, text=True,
            ).stdout.split()
            paths = [p for p in listing if p.endswith(".lean")]
            proc = subprocess.run(
                ["git", "-C", str(root), "cat-file", "--batch"],
                input="".join(f"{rev}:{p}\n" for p in paths).encode(),
                check=True, capture_output=True,
            )
            out, i, self.sources = proc.stdout, 0, {}
            for p in paths:
                nl = out.index(b"\n", i)
                size = int(out[i:nl].split()[2])
                self.sources[module_of_path(p)] = out[nl + 1: nl + 1 + size].decode("utf-8")
                i = nl + 1 + size + 1
        self.sources = {m: s for m, s in self.sources.items()
                        if not m.startswith("TNLean.Archive.")}
        self.parsed = {m: parse(s) for m, s in self.sources.items()}

    def is_aggregator(self, module: str) -> bool:
        return self.parsed[module][1]

    def imports(self, module: str) -> list[str]:
        return self.parsed[module][0]


def parse(source: str) -> tuple[list[str], bool]:
    uncommented, _ = strip_lean_comments(source)
    imports, only = [], True
    for line in uncommented.splitlines():
        command = line.strip()
        if not command:
            continue
        match = IMPORT_RE.match(command)
        if match:
            imports.append(match.group(1))
        else:
            only = False
    return imports, only and bool(imports)


# ----------------------------------------------------------------- the map
class ModuleMap:
    def __init__(self, text: str) -> None:
        self.entries: list[tuple[str, str, int | None, int]] = []
        self.errors: list[str] = []
        self.recorded_edges: set[str] = set()
        self.recorded_siblings: set[str] = set()
        for number, raw in enumerate(text.splitlines(), start=1):
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            if line.startswith("!"):
                body = line[1:].strip()
                pair = re.fullmatch(r"(\S+)\s*<->\s*(\S+)", body)
                edge = re.fullmatch(r"(\S+)\s*->\s*(\S+)", body)
                if pair:
                    self.recorded_siblings.add(" <-> ".join(sorted(pair.groups())))
                elif edge:
                    self.recorded_edges.add(f"{edge.group(1)} -> {edge.group(2)}")
                else:
                    self.errors.append(f"line {number}: cannot read recorded entry {raw!r}")
                continue
            match = re.fullmatch(r"(\S+)\s*->\s*(\S+)(?:\s+@(\d+))?", line)
            if not match:
                self.errors.append(f"line {number}: cannot read {raw!r}")
                continue
            old, new, order = match.group(1), match.group(2), match.group(3)
            self.entries.append((old, new, int(order) if order else None, number))
        self.target: dict[str, str] = {}
        self.parts: dict[str, list[tuple[int, str]]] = collections.defaultdict(list)
        for old, new, order, number in self.entries:
            if old in self.target:
                self.errors.append(f"line {number}: {old} is mapped twice")
                continue
            self.target[old] = new
            self.parts[new].append((order if order is not None else -1, old))
        for new, parts in self.parts.items():
            parts.sort()
            if len(parts) > 1:
                orders = [o for o, _ in parts]
                if -1 in orders:
                    self.errors.append(
                        f"{new}: {len(parts)} old modules without merge positions @N")
                elif len(set(orders)) != len(orders):
                    self.errors.append(f"{new}: repeated merge position")

    def new(self, module: str) -> str:
        return self.target.get(module, module)


# ----------------------------------------------------------------- graphs
def expand_aggregators(tree: Tree, module: str, seen: frozenset[str] = frozenset()) -> set[str]:
    if module not in tree.sources or not tree.is_aggregator(module) or module in seen:
        return {module}
    out: set[str] = set()
    for imported in tree.imports(module):
        if imported.startswith("TNLean."):
            out |= expand_aggregators(tree, imported, seen | {module})
    return out


def graph_after(tree: Tree, mmap: ModuleMap, present: set[str]) -> tuple[dict[str, set[str]], list[str]]:
    """Import graph between modules with declarations after the map, and unresolved imports."""
    graph: dict[str, set[str]] = collections.defaultdict(set)
    unresolved: list[str] = []
    for module in tree.sources:
        if tree.is_aggregator(module):
            continue
        source_new = mmap.new(module) if module in present else module
        graph.setdefault(source_new, set())
        for imported in tree.imports(module):
            if not imported.startswith("TNLean."):
                continue
            if imported not in tree.sources:
                unresolved.append(f"{module} imports missing {imported}")
                continue
            for target in expand_aggregators(tree, imported):
                target_new = mmap.new(target) if target in present else target
                if target_new != source_new:
                    graph[source_new].add(target_new)
    return graph, unresolved


def cycles(graph: dict[str, set[str]]) -> list[list[str]]:
    """Strongly connected components with more than one module (iterative Tarjan)."""
    index, low, on, stack, out = {}, {}, set(), [], []
    counter = [0]
    for start in sorted(graph):
        if start in index:
            continue
        work = [(start, iter(sorted(graph.get(start, ()))))]
        index[start] = low[start] = counter[0]
        counter[0] += 1
        stack.append(start)
        on.add(start)
        while work:
            node, it = work[-1]
            advanced = False
            for nxt in it:
                if nxt not in index:
                    index[nxt] = low[nxt] = counter[0]
                    counter[0] += 1
                    stack.append(nxt)
                    on.add(nxt)
                    work.append((nxt, iter(sorted(graph.get(nxt, ())))))
                    advanced = True
                    break
                if nxt in on:
                    low[node] = min(low[node], index[nxt])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] == index[node]:
                component = []
                while True:
                    x = stack.pop()
                    on.discard(x)
                    component.append(x)
                    if x == node:
                        break
                if len(component) > 1:
                    out.append(sorted(component))
    return out


def directory_of(module: str) -> str | None:
    parts = module.split(".")[1:-1]
    if not parts:
        return None
    depth = 2 if parts[0] in DEEP_ROOTS else 1
    return "/".join(parts[:depth])


def mutual_pairs(graph: dict[str, set[str]]) -> dict[str, tuple[str, str]]:
    witness: dict[tuple[str, str], str] = {}
    for module in sorted(graph):
        a = directory_of(module)
        if a is None:
            continue
        for target in sorted(graph[module]):
            b = directory_of(target)
            if b is None or a == b:
                continue
            witness.setdefault((a, b), f"{module} -> {target}")
    return {f"{a} <-> {b}": (w, witness[(b, a)])
            for (a, b), w in witness.items() if a < b and (b, a) in witness}


def sibling_pairs(graph: dict[str, set[str]]) -> dict[str, int]:
    """Pairs of sibling directories, at any depth, importing each other."""
    count: collections.Counter[tuple[str, str]] = collections.Counter()
    for module, targets in graph.items():
        a = module.split(".")[:-1]
        for target in targets:
            b = target.split(".")[:-1]
            k = 0
            while k < min(len(a), len(b)) and a[k] == b[k]:
                k += 1
            if k < len(a) and k < len(b):
                count[(".".join(a[: k + 1]), ".".join(b[: k + 1]))] += 1
    return {f"{x} <-> {y}": count[(x, y)] + count[(y, x)]
            for (x, y) in count if x < y and (y, x) in count}


# ----------------------------------------------------------------- check
def check(root: Path, rev: str | None, map_path: Path, verbose: bool) -> int:
    tree = Tree(root, rev)
    mmap = ModuleMap(map_path.read_text(encoding="utf-8"))
    problems: list[str] = list(mmap.errors)
    report: list[str] = []

    present = {old for old in mmap.target if old in tree.sources}
    missing = sorted(old for old in mmap.target if old not in tree.sources)
    already = [old for old in missing if mmap.target[old] in tree.sources]
    report.append(f"map: {len(mmap.target)} entries, {len(present)} present, "
                  f"{len(missing)} missing ({len(already)} of them already applied); "
                  "missing entries are skipped")
    if verbose:
        for old in missing:
            report.append(f"  skipped (not in tree): {old}")

    for old in present:
        if tree.is_aggregator(old):
            problems.append(f"{old} is a generated aggregator; aggregators are not mapped")

    # collisions with modules that stay
    staying = {m for m in tree.sources if m not in present}
    for new, parts in mmap.parts.items():
        live = [old for _, old in parts if old in present]
        if not live:
            continue
        if new in staying and new not in [old for _, old in parts]:
            problems.append(f"new module {new} collides with a module that stays")

    graph, unresolved = graph_after(tree, mmap, present)
    problems += unresolved

    # merges: private-name collisions and anonymous instances
    for new, parts in mmap.parts.items():
        live = [old for _, old in parts if old in present]
        if len(live) < 2:
            continue
        privates: collections.Counter[str] = collections.Counter()
        for old in live:
            text, _ = strip_lean_comments(tree.sources[old])
            for line in text.splitlines():
                match = PRIVATE_RE.match(line)
                if match:
                    privates[match.group(1)] += 1
        for name, n in privates.items():
            if n > 1:
                problems.append(f"merge {new}: private name {name} declared in {n} parts")
        # anonymous instances receive names generated from their types; two parts
        # with the same anonymous instance header would receive the same name
        anonymous: collections.Counter[str] = collections.Counter()
        for old in live:
            text, _ = strip_lean_comments(tree.sources[old])
            for header in set(re.findall(r"(?m)^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?"
                                         r"instance\s*(?:\(priority[^)]*\)\s*)?:\s*([^\n]*)",
                                         text)):
                anonymous[" ".join(header.split(":=")[0].split())] += 1
        for header, n in anonymous.items():
            if n > 1:
                problems.append(f"merge {new}: anonymous instance `{header}` in {n} parts")
        position = {old: i for i, old in enumerate(live)}
        for old in live:
            for t in tree.imports(old):
                if t in position and position[t] > position[old]:
                    problems.append(f"merge {new}: part {old} imports later part {t}")

    for component in cycles(graph):
        problems.append("import cycle after the map: " + " -> ".join(component[:12])
                        + (" …" if len(component) > 12 else ""))

    # layers
    unlayered = sorted({m for m in graph if layer_of(m) is None})
    violations: list[str] = []
    for module, targets in sorted(graph.items()):
        a = layer_of(module)
        if a is None:
            continue
        for target in sorted(targets):
            b = layer_of(target)
            if b is None:
                continue
            if b not in ALLOWED[a]:
                violations.append(f"{module} -> {target}")
    report.append(f"modules without a layer after the map: {len(unlayered)}")
    for module in unlayered[: (None if verbose else 20)]:
        report.append(f"  unlayered: {module}")
    recorded_now = [v for v in violations if v in mmap.recorded_edges]
    unrecorded = [v for v in violations if v not in mmap.recorded_edges]
    stale = sorted(mmap.recorded_edges - set(violations))
    report.append(f"imports outside the allowed layers: {len(violations)} "
                  f"({len(recorded_now)} recorded in the map as declaration-level work, "
                  f"{len(unrecorded)} not recorded)")
    for v in unrecorded:
        a, b = v.split(" -> ")
        report.append(f"  layer violation: {a} [{layer_of(a)}] -> {b} [{layer_of(b)}]")
    if verbose:
        for v in recorded_now:
            report.append(f"  recorded: {v}")
    for v in stale:
        report.append(f"  recorded but no longer a violation (remove it from the map): {v}")

    # mutual pairs before and after
    before, _ = graph_after(tree, ModuleMap(""), set())
    pb, pa = mutual_pairs(before), mutual_pairs(graph)
    report.append(f"pairs of directories importing each other: {len(pb)} before, {len(pa)} after")
    for pair, (fw, bw) in sorted(pa.items()):
        report.append(f"  mutual: {pair}  ({fw}; {bw})")
    sib = sibling_pairs(graph)
    same_layer = {p: n for p, n in sib.items()
                  if len({layer_of(d + ".X") for d in p.split(" <-> ")}) == 1}
    unrec_sib = {p: n for p, n in same_layer.items() if p not in mmap.recorded_siblings}
    report.append(f"pairs of sibling directories (any depth) importing each other after: "
                  f"{len(sib)}, of which {len(same_layer)} inside one layer "
                  f"({len(same_layer) - len(unrec_sib)} recorded)")
    for pair, n in sorted(sib.items()):
        tag = "" if pair in same_layer else " (two layers; see the layer violations)"
        if pair in unrec_sib or verbose:
            report.append(f"  sibling: {pair} ({n} imports){tag}")
    for pair in sorted(mmap.recorded_siblings - set(same_layer)):
        report.append(f"  recorded sibling pair no longer occurs (remove it from the map): {pair}")

    # sizes
    sizes = collections.Counter(".".join(m.split(".")[:-1]) for m in graph)
    big = sorted((n, d) for d, n in sizes.items() if n > MAX_PER_LEVEL)
    report.append(f"directories with more than {MAX_PER_LEVEL} modules at one level: {len(big)}")
    for n, d in sorted(big, reverse=True):
        report.append(f"  {n:4d} {d}")

    print("\n".join(report))
    for p in problems:
        print(f"ERROR: {p}")
    problems += [f"recorded entry no longer occurs: {v}" for v in stale]
    print(f"{len(problems)} errors, {len(unrecorded)} unrecorded layer violations "
          f"({len(recorded_now)} recorded), {len(unrec_sib)} unrecorded sibling pairs, "
          f"{len(pa)} mutual directory pairs, {len(unlayered)} unlayered modules")
    return 1 if problems or unrecorded or unrec_sib or unlayered else 0


# ----------------------------------------------------------------- apply
def split_header(source: str) -> tuple[str, list[str], str]:
    """Return (copyright block, import lines, body) of a Lean source."""
    rest = source
    header = ""
    m = re.match(r"\s*/-(?!!).*?-/\s*", rest, re.S)
    if m and "Copyright" in m.group(0):
        header = m.group(0).strip() + "\n"
        rest = rest[m.end():]
    imports: list[str] = []
    lines = rest.split("\n")
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if not s or s.startswith("--"):
            i += 1
            continue
        if IMPORT_RE.match(s):
            imports.append(IMPORT_RE.match(s).group(1))
            i += 1
            continue
        break
    return header, imports, "\n".join(lines[i:])


def unclosed_scopes(body: str) -> list[str]:
    text, _ = strip_lean_comments(body)
    stack: list[tuple[str, str]] = []
    for line in text.splitlines():
        if line.startswith((" ", "\t")):
            continue
        m = SCOPE_OPEN_RE.match(line)
        if m and not line.lstrip().startswith(("section_", "namespace_")):
            if m.group(1) == "namespace":
                for part in m.group(2).split("."):
                    stack.append(("namespace", part))
            else:
                stack.append(("section", m.group(2)))
            continue
        m = SCOPE_END_RE.match(line)
        if m and stack:
            name = m.group(1)
            if name and stack[-1][0] == "namespace":
                for _ in name.split("."):
                    if stack:
                        stack.pop()
            else:
                stack.pop()
    return [f"end {name}".rstrip() for kind, name in reversed(stack)]


def demote(doc: str) -> str:
    return re.sub(r"(?m)^(#+) ", lambda m: "#" + m.group(1) + " ", doc)


def concatenate(parts: list[tuple[str, str]], rename) -> str:
    """Concatenate ``(module, source)`` parts into one module source."""
    header = ""
    imports: list[str] = []
    docs: list[str] = []
    bodies: list[str] = []
    names = {m for m, _ in parts}
    for k, (module, source) in enumerate(parts):
        h, imps, body = split_header(source)
        header = header or h
        for imp in imps:
            if imp in names:
                continue
            for target in rename(imp):
                if target not in imports and target not in names:
                    imports.append(target)
        m = MODULE_DOC_RE.search(body)
        if m and body[: m.start()].strip() == "":
            docs.append(m.group(1).strip() if k == 0 else demote(m.group(1).strip()))
            body = body[: m.start()] + body[m.end():]
        closers = unclosed_scopes(body)
        bodies.append(f"section\n\n{body.strip()}\n" + "".join(c + "\n" for c in closers)
                      + "\nend\n")
    out = header + "\n".join(f"import {i}" for i in imports) + "\n\n"
    if docs:
        out += "/-!\n" + "\n\n".join(docs) + "\n-/\n\n"
    return out + "\n".join(bodies)


def git(root: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(root), *args], check=True)


def declaration_names(tree: Tree) -> set[str]:
    names: set[str] = set()
    for source in tree.sources.values():
        text, _ = strip_lean_comments(source)
        namespace: list[str] = []
        for line in text.splitlines():
            m = SCOPE_OPEN_RE.match(line)
            if m and m.group(1) == "namespace":
                namespace += m.group(2).split(".")
                continue
            m = SCOPE_END_RE.match(line)
            if m and m.group(1) and namespace:
                del namespace[-len(m.group(1).split(".")):]
                continue
            m = DECL_RE.match(line)
            if m and m.group(2):
                n = m.group(2).replace("_root_.", "")
                names.add(".".join(namespace + [n]) if namespace else n)
    return names


def rewrite_text(text: str, renames: dict[str, str], decls: set[str], latex: bool) -> str:
    """Rewrite module names (dotted, unless a declaration has that name) and paths."""
    if not renames:
        return text
    olds = sorted(renames, key=len, reverse=True)
    path_re = re.compile(
        r"TNLean/((?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+)(\.lean)?(?![A-Za-z0-9_/])")

    def path_sub(m: re.Match[str]) -> str:
        module = "TNLean." + m.group(1).replace("/", ".")
        if module in renames:
            return "TNLean/" + renames[module][len("TNLean."):].replace(".", "/") + (m.group(2) or "")
        return m.group(0)

    protected: list[tuple[int, int]] = []
    if latex:
        protected = [(m.start(), m.end()) for m in re.finditer(r"\\(?:lean|uses|label|ref)\{[^}]*\}", text)]
    dotted_re = re.compile(
        r"(?<![A-Za-z0-9_'.])(" + "|".join(re.escape(o) for o in olds if o not in decls)
        + r")(?![A-Za-z0-9_'])(?!\.[A-Za-z_])") if any(o not in decls for o in olds) else None

    def outside(span: tuple[int, int]) -> bool:
        return not any(a <= span[0] < b for a, b in protected)

    out, last = [], 0
    pieces = []
    for m in path_re.finditer(text):
        if outside((m.start(), m.end())):
            pieces.append((m.start(), m.end(), path_sub(m)))
    if dotted_re is not None:
        for m in dotted_re.finditer(text):
            if outside((m.start(), m.end())):
                pieces.append((m.start(), m.end(), renames[m.group(1)]))
    short = {o[len("TNLean."):].replace(".", "/"): n[len("TNLean."):].replace(".", "/")
             for o, n in renames.items()}
    for m in re.finditer(r"`((?:[A-Za-z0-9_]+/)+[A-Za-z0-9_]+)(\.lean)?`", text):
        if m.group(1) in short and outside((m.start(), m.end())):
            pieces.append((m.start(1), m.end(1), short[m.group(1)]))
    pieces.sort()
    for a, b, rep in pieces:
        if a < last:
            continue
        out.append(text[last:a])
        out.append(rep)
        last = b
    out.append(text[last:])
    return "".join(out)


def apply(root: Path, map_path: Path) -> int:
    tree = Tree(root, None)
    mmap = ModuleMap(map_path.read_text(encoding="utf-8"))
    if mmap.errors:
        for e in mmap.errors:
            print(f"ERROR: {e}")
        return 1
    # after a first run, the aggregator generator may write a file at an old
    # path; it is not a module still to be moved
    present = {old for old in mmap.target
               if old in tree.sources and not tree.is_aggregator(old)}
    renames = {old: mmap.target[old] for old in present if mmap.target[old] != old}
    decls = declaration_names(tree)

    # aggregator imports whose members move are replaced by the members' new modules
    def rename_import(module: str) -> list[str]:
        if module in tree.sources and tree.is_aggregator(module):
            members = expand_aggregators(tree, module)
            if any(x in renames for x in members):
                return sorted({renames.get(x, x) for x in members})
        return [renames.get(module, module)]

    # 1. moves and merges; a target still occupied by a module that moves away
    # later is retried after that module has moved.
    done = 0
    pending = {new: [old for _, old in parts if old in present]
               for new, parts in mmap.parts.items()}
    pending = {new: live for new, live in pending.items() if live and live != [new]}
    while pending:
        progress = False
        for new, live in sorted(pending.items()):
            new_path = root / path_of_module(new)
            if new_path.exists() and new not in live:
                continue
            new_path.parent.mkdir(parents=True, exist_ok=True)
            if len(live) == 1:
                git(root, "mv", path_of_module(live[0]), path_of_module(new))
            else:
                pieces = [(old, tree.sources[old]) for old in live]
                merged = concatenate(pieces, rename_import)
                for old in live:
                    if old != new:
                        git(root, "rm", "-q", path_of_module(old))
                new_path.write_text(merged, encoding="utf-8")
                git(root, "add", path_of_module(new))
            del pending[new]
            done += 1
            progress = True
        if not progress:
            for new in sorted(pending):
                print(f"ERROR: target {new} stays occupied; resolve by hand")
            return 1

    # 2. imports in TNLean/ and scripts/*.lean
    lean_files = [p for p in root.glob("TNLean/**/*.lean")] + list(root.glob("scripts/*.lean"))
    for path in lean_files:
        text = path.read_text(encoding="utf-8")
        own = module_of_path(str(path.relative_to(root))) if str(path).find("/TNLean/") >= 0 else ""
        lines, seen, changed = [], set(), False
        for line in text.split("\n"):
            m = IMPORT_RE.match(line.strip())
            if m and m.group(1).startswith("TNLean."):
                targets = rename_import(m.group(1))
                prefix = line[: line.index("import")]
                new_lines = []
                for t in targets:
                    if t == own or t in seen:
                        continue
                    seen.add(t)
                    new_lines.append(f"{prefix}import {t}")
                if new_lines != [line]:
                    changed = True
                lines.extend(new_lines)
            else:
                lines.append(line)
        if changed:
            path.write_text("\n".join(lines), encoding="utf-8")

    # 3. references in documents and scripts
    targets = [root / "CLAUDE.md"] + list(root.glob("docs/**/*.md")) \
        + list(root.glob("docs/**/*.tex")) + list(root.glob("blueprint/src/**/*.tex")) \
        + [p for p in root.glob("scripts/*.py") if p.name != "apply_library_layers.py"]
    for path in targets:
        text = path.read_text(encoding="utf-8")
        new_text = rewrite_text(text, renames, decls, latex=path.suffix == ".tex")
        if new_text != text:
            path.write_text(new_text, encoding="utf-8")

    # 4. the recorded pairs of directories that import each other
    after = Tree(root, None)
    graph, _ = graph_after(after, ModuleMap(""), set())
    pairs = sorted(mutual_pairs(graph))
    checker = (root / CHECKER_PATH).read_text(encoding="utf-8")
    block = "MUTUAL_DIRECTORIES: frozenset[str] = frozenset(\n    {\n" + "".join(
        f'        "{p}",\n' for p in pairs) + "    }\n)"
    checker = re.sub(r"MUTUAL_DIRECTORIES: frozenset\[str\] = frozenset\(\n    \{\n.*?\n    \}\n\)",
                     lambda _: block, checker, flags=re.S)
    (root / CHECKER_PATH).write_text(checker, encoding="utf-8")

    # 5. aggregators
    subprocess.run([sys.executable, str(root / "scripts/generate_import_aggregators.py")],
                   cwd=root, check=False)
    print(f"applied {done} moves and merges; {len(pairs)} recorded mutual pairs remain")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--map", type=Path, default=None)
    parser.add_argument("--check", action="store_true", help="validate the map; change nothing")
    parser.add_argument("--rev", default=None,
                        help="with --check: read the sources at this revision instead of the "
                             "working tree")
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    map_path = args.map or root / MAP_PATH
    if args.check:
        return check(root, args.rev, map_path, args.verbose)
    if args.rev:
        parser.error("--rev is only meaningful with --check")
    return apply(root, map_path)


if __name__ == "__main__":
    raise SystemExit(main())
