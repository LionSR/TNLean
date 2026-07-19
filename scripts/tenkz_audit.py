#!/usr/bin/env python3
"""Audit a tenkz `.tnlog` event stream (tenkz spec section 5).

A `.tnlog` is a line-oriented stream `event|key=value|...` written by the
tenkz LaTeX environments.  Every picture opens with `picture|id=N|lang=L`
(langs: grid, cd, lattice, free, planes); subsequent events carry an
explicit `picture=N` back-reference.  `tree|picture=0` marks a `\\tntree`
typeset outside any environment (legal in running math).

Hard errors (exit 1):
  malformed-event      A field fails its type (e.g. an unexpanded expl3
                       token such as `\\l__tenkz_nrows_int` in a numeric
                       slot).  The stream is the contraction record; a
                       non-numeric coordinate names no cell, so the event
                       describes no drawable ink.
  malformed-tree       A tree's canonical numeric bracketing is not a
                       rooted binary tree, or disagrees with its declared
                       leaf and vertex counts.
  duplicate-picture    Two `picture` lines share one id: picture identity
                       is the key of every back-reference.
  conflicting-faceports
                       Two faceports records declare different slots for the
                       same cell face.  The first valid declaration remains
                       authoritative; identical retries are idempotent.
  dangling-picture-ref An event references an undeclared picture.
  empty-picture        A grid/lattice/free picture emitted no content
                       events.  A tensor diagram with no atoms and no
                       regions denotes no tensor network -- historically
                       the "34 fake diagrams" class.
  pairleg-faceport-mismatch
                       A grid pairleg names a contraction slot absent from the
                       upper cell's declared down face.  Explicit declarations
                       resolve `center`, comma-separated slots, `rows`, and
                       `none`.  If no faceports event exists, the check is
                       skipped for compatibility with legacy logs, including
                       simple centred faces.

Advisories (never affect the exit code):
  eq-boundary-mismatch Consecutive grid pictures joined by `=` in the
                       source have different boundary signatures.  A
                       tensor equation equates two maps of one type, so
                       the multisets of open legs must agree side-to-side.
  periodic-no-dots     A traced (periodic) chain of >= 4 columns without
                       an ellipsis cell: a closed word of generic length n
                       drawn with every site reads as fixed length.
  repeated-topology    Identical canonical atom+bond content in several
                       pictures: the figure is a candidate `\\tndefine`.
  dialect-mismatch     An event kind foreign to its picture's language
                       (each sub-language owns its event dialect).
  unknown-event/lang   Forward-compatibility notes.
  stale-log            The source declares picture constructs but the log
                       has none (failed or interrupted compile).

Source heuristic (documented, deliberately simple): picture-producing
constructs (`\\begin{tenkz...}` and `\\tnpic`) are matched to log pictures
in order of appearance; the match is used only when the counts agree.
Two consecutive grid pictures are "one displayed equation" when the
source between them contains `=` and no math-mode boundary (`$`, `\\[`,
`\\]`), no cell separator `&`, no other environment, and is short.

Usage: tenkz_audit.py file.tnlog [file.tex]
If file.tex is omitted, a sibling `<stem>.tex` is used when present.
Exit status: 1 iff hard errors were found.
"""

from __future__ import annotations

import hashlib
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Optional

INT_RE = re.compile(r"-?\d+")
CELL_RE = re.compile(r"-?\d+--?\d+")  # r-c with signed components

KNOWN_LANGS = {"grid", "cd", "lattice", "free", "planes"}

# Empty-picture hard check applies exactly to the spec's list (section 5.4).
EMPTY_CHECK_LANGS = {"grid", "lattice", "free"}

# Event kinds each dialect is expected to emit.  `lattice` and `planes`
# are left open while their event vocabularies are still growing.
DIALECT_KINDS = {
    "grid": {"atom", "bond", "faceports", "pairleg", "trace", "pairtrace",
             "phtrace", "hooks", "cup", "hole", "warning", "boundary"},
    "free": {"atom", "join", "boundary"},
    "cd": {"cdcell", "cdobject", "cdarrow", "cdmap", "tree"},
}


def _parse_int(v: str) -> Optional[int]:
    if INT_RE.fullmatch(v) is None:
        return None
    try:
        return int(v)
    except ValueError:  # Python's configured decimal-digit safety limit
        return None


def _is_int(v: str) -> bool:
    return _parse_int(v) is not None


def _is_positive_int(v: str) -> bool:
    parsed = _parse_int(v)
    return parsed is not None and parsed > 0


def _is_nonnegative_int(v: str) -> bool:
    parsed = _parse_int(v)
    return parsed is not None and parsed >= 0


def _is_cell(v: str) -> bool:
    return re.fullmatch(r"\d+-\d+", v) is not None


def _is_nonnegative_int(v: str) -> bool:
    if not _is_int(v):
        return False
    try:
        return int(v) >= 0
    except ValueError:
        return False


def _is_pairleg_port(v: str) -> bool:
    """A contraction starts at the centred face or a positive face slot."""
    if v == "center":
        return True
    if not _is_int(v):
        return False
    try:
        return int(v) > 0
    except ValueError:
        return False


def _enum(*vals: str) -> Callable[[str], bool]:
    allowed = set(vals)
    return lambda v: v in allowed


def _any(v: str) -> bool:
    return v != ""


# kind -> {field: validator}; fields absent here are accepted as opaque.
# Numeric slots are validated strictly: they are cell/row coordinates, and
# a coordinate that is not an integer addresses nothing.
FIELD_VALIDATORS: dict[str, dict[str, Callable[[str], bool]]] = {
    "picture": {"id": _is_int, "lang": _any},
    "atom": {"picture": _is_int, "cell": _is_cell, "name": _any, "kind": _any},
    "faceports": {"picture": _is_int, "cell": _is_cell,
                  "face": _enum("up", "down", "west", "east"),
                  "arity": _is_nonnegative_int, "at": _any},
    "pairleg": {"picture": _is_int, "upper": _is_cell, "lower": _is_cell,
                "upper-port": _is_pairleg_port,
                "column": _is_int},
    # The emitter normalizes the user-facing `bond dir=left|right` to
    # forward/reverse (direction along the wire); accept both spellings.
    "bond": {"picture": _is_int, "row": _is_int, "from": _is_int, "to": _is_int,
             "dir": _enum("none", "left", "right", "forward", "reverse")},
    "trace": {"picture": _is_int, "row": _is_int, "side": _enum("above", "below")},
    "hooks": {"picture": _is_int, "row": _is_int, "side": _enum("above", "below")},
    "pairtrace": {"picture": _is_int, "row": _is_int, "col": _is_int, "site": _is_cell},
    "phtrace": {"picture": _is_int, "row": _is_int, "col": _is_int},
    "cup": {"picture": _is_int, "side": _enum("west", "east"),
            "top": _is_int, "bottom": _is_int, "matrix": _is_int},
    "hole": {"picture": _is_int, "row": _is_int, "col": _is_int},
    "warning": {"picture": _is_int, "code": _any},
    "boundary": {"picture": _is_int, "virtual-west": _is_int, "virtual-east": _is_int,
                 "physical-up": _is_int, "physical-down": _is_int},
    "cdcell": {"picture": _is_int, "index": _is_int},
    "cdobject": {"picture": _is_int, "cell": _is_cell},
    "cdarrow": {"picture": _is_int, "from": _any, "to": _any},
    "cdmap": {"picture": _is_int, "from": _is_cell, "to": _is_cell,
              "fused": _enum("0", "1"),
              "role": _enum("none", "operator", "marked", "extra", "passive"),
              "species": _any},
    "tree": {"picture": _is_int, "id": _is_positive_int,
             "style": _enum("wire", "ribbon"),
             "leaves": _is_positive_int, "vertices": _is_nonnegative_int,
             "topology": _any,
             "role": _enum("none", "operator", "marked", "extra", "passive"),
             "species": _any},
    "join": {"picture": _is_int, "from": _any, "to": _any},
}


@dataclass
class Event:
    kind: str
    attrs: dict[str, str]
    line: int
    raw: str


@dataclass
class Picture:
    ident: int
    lang: str
    line: int
    events: list[Event] = field(default_factory=list)

    def content(self) -> list[Event]:
        """Events that denote ink.  Derived boundaries and warning
        diagnostics do not contribute to the canonical topology."""
        return [e for e in self.events if e.kind not in {"boundary", "warning"}]

    def boundary(self) -> Optional[tuple[int, int, int, int]]:
        for e in self.events:
            if e.kind == "boundary":
                try:
                    return tuple(int(e.attrs[k].strip()) for k in
                                 ("virtual-west", "virtual-east",
                                  "physical-up", "physical-down"))  # type: ignore[return-value]
                except (KeyError, ValueError):
                    return None
        return None

    def ncols(self) -> int:
        n = 0
        for e in self.events:
            if e.kind == "atom" and "cell" in e.attrs and _is_cell(e.attrs["cell"].strip()):
                n = max(n, int(e.attrs["cell"].strip().split("-")[1]))
            elif e.kind == "bond":
                for k in ("from", "to"):
                    v = e.attrs.get(k, "").strip()
                    if _is_int(v):
                        n = max(n, int(v))
        return n


@dataclass
class Finding:
    severity: str  # "HARD" | "ADV" | "NOTE"
    rule: str
    where: str
    msg: str


class Audit:
    def __init__(self, log_path: Path, tex_path: Optional[Path]) -> None:
        self.log_path = log_path
        self.tex_path = tex_path
        self.findings: list[Finding] = []
        self.pictures: list[Picture] = []
        self.by_id: dict[int, Picture] = {}
        self.constructs: list["Construct"] = []
        self.tex_linked = False

    def hard(self, rule: str, where: str, msg: str) -> None:
        self.findings.append(Finding("HARD", rule, where, msg))

    def adv(self, rule: str, where: str, msg: str) -> None:
        self.findings.append(Finding("ADV", rule, where, msg))

    def note(self, rule: str, where: str, msg: str) -> None:
        self.findings.append(Finding("NOTE", rule, where, msg))

    # ---------------- parsing ----------------

    def parse_log(self) -> None:
        name = self.log_path.name
        for lineno, raw in enumerate(
                self.log_path.read_text(encoding="utf-8").splitlines(), 1):
            line = raw.strip()
            if not line:
                continue
            where = f"{name}:{lineno}"
            parts = line.split("|")
            kind = parts[0].strip()
            attrs: dict[str, str] = {}
            ok = True
            for p in parts[1:]:
                if "=" not in p:
                    self.hard("malformed-event", where,
                              f"bare field {p.strip()!r} (expected key=value): {line}")
                    ok = False
                    continue
                k, v = p.split("=", 1)
                attrs[k.strip()] = v.strip()
            ev = Event(kind, attrs, lineno, line)
            validators = FIELD_VALIDATORS.get(kind)
            if validators is None:
                self.adv("unknown-event", where, f"unrecognized event kind {kind!r}")
            else:
                for k, v in attrs.items():
                    check = validators.get(k)
                    if check is not None and not check(v):
                        self.hard("malformed-event", where,
                                  f"{kind} field {k}={v!r} fails validation: {line}")
                        ok = False
                if kind != "picture" and "picture" not in attrs:
                    self.hard("malformed-event", where,
                              f"{kind} event lacks required picture=: {line}")
                    ok = False
            if kind == "picture":
                if not ok or "id" not in attrs or not _is_int(attrs["id"]):
                    continue
                pid = int(attrs["id"])
                lang = attrs.get("lang", "")
                if lang not in KNOWN_LANGS:
                    self.adv("unknown-lang", where, f"picture {pid} has lang={lang!r}")
                if pid in self.by_id:
                    self.hard("duplicate-picture", where,
                              f"picture id {pid} already declared at line "
                              f"{self.by_id[pid].line}")
                    continue
                pic = Picture(pid, lang, lineno)
                self.by_id[pid] = pic
                self.pictures.append(pic)
                continue
            if kind == "tree":
                self.check_tree_event(ev)
            ref = attrs.get("picture", "")
            if not _is_int(ref):
                continue
            pid = int(ref)
            if pid == 0 and kind == "tree":
                continue  # \tntree in running math, outside any picture
            if pid not in self.by_id:
                self.hard("dangling-picture-ref", where,
                          f"{kind} references undeclared picture {pid}")
                continue
            self.by_id[pid].events.append(ev)

    def check_tree_event(self, event: Event) -> None:
        """Validate the tree event as structural data, not display text."""
        where = f"{self.log_path.name}:{event.line}"
        required = {"id", "style", "leaves", "vertices", "topology",
                    "role", "species"}
        missing = sorted(required - event.attrs.keys())
        if missing:
            self.hard("malformed-tree", where,
                      f"tree event lacks required field(s): {', '.join(missing)}")
            return
        shape = parse_tree_topology(event.attrs["topology"])
        if shape is None:
            self.hard("malformed-tree", where,
                      f"invalid canonical topology {event.attrs['topology']!r}")
            return
        leaves, vertices = shape
        if not (_is_positive_int(event.attrs["leaves"])
                and _is_nonnegative_int(event.attrs["vertices"])):
            return  # generic field validation already reports these values
        declared = (int(event.attrs["leaves"]), int(event.attrs["vertices"]))
        if declared != (leaves, vertices):
            self.hard("malformed-tree", where,
                      f"topology has {leaves} leaves and {vertices} vertices, "
                      f"but event declares {declared[0]} and {declared[1]}")

    # ---------------- log-only checks ----------------

    def check_empty_pictures(self) -> None:
        for pic in self.pictures:
            if pic.content():
                continue
            where = f"{self.log_path.name}:{pic.line}"
            if pic.lang in EMPTY_CHECK_LANGS:
                self.hard("empty-picture", where,
                          f"picture {pic.ident} (lang={pic.lang}) emitted no "
                          f"content events")
            else:
                self.adv("empty-picture", where,
                         f"picture {pic.ident} (lang={pic.lang}) emitted no "
                         f"content events (lang outside the hard-check list)")

    def check_dialects(self) -> None:
        for pic in self.pictures:
            allowed = DIALECT_KINDS.get(pic.lang)
            if allowed is None:
                continue
            for e in pic.content():
                if e.kind not in allowed:
                    self.adv("dialect-mismatch", f"{self.log_path.name}:{e.line}",
                             f"{e.kind} event inside picture {pic.ident} "
                             f"(lang={pic.lang}); not part of that dialect")
                elif e.kind == "atom":
                    want = "cell" if pic.lang == "grid" else "name"
                    if want not in e.attrs:
                        self.adv("dialect-mismatch",
                                 f"{self.log_path.name}:{e.line}",
                                 f"atom in {pic.lang} picture {pic.ident} lacks "
                                 f"{want}=")

    @staticmethod
    def _declared_face_ports(
            event: Event) -> Optional[tuple[set[str], Optional[int]]]:
        """Resolve explicit slots and an optional inclusive `rows` bound."""
        at = event.attrs.get("at", "").strip()
        if at == "center":
            return {"center"}, None
        if at == "none":
            return set(), None
        if at == "rows":
            arity = event.attrs.get("arity", "")
            if not _is_nonnegative_int(arity):
                return None
            count = int(arity)
            # A one-row physical face emits its unique contraction as `center`.
            return ({"center"} if count == 1 else set()), count
        slots = [slot.strip() for slot in at.split(",")]
        if slots and all(
                _is_pairleg_port(slot) and slot != "center" for slot in slots):
            return set(slots), None
        return None

    def check_pairleg_faceports(self) -> None:
        """Cross-check pairleg slots against explicit upper down-face declarations.

        Older event streams did not always emit faceports records.  Absence is
        therefore deliberately not an error; an explicit declaration is the
        authority whenever one is present.
        """
        for pic in self.pictures:
            if pic.lang != "grid":
                continue
            declared: dict[
                tuple[str, str], tuple[set[str], Optional[int], int]
            ] = {}
            for event in pic.events:
                if event.kind != "faceports":
                    continue
                cell = event.attrs.get("cell", "")
                face = event.attrs.get("face", "")
                if (not _is_cell(cell)
                        or face not in {"up", "down", "west", "east"}):
                    continue
                missing = [
                    field for field in ("arity", "at")
                    if field not in event.attrs
                ]
                if missing:
                    fields = ",".join(f"{field}=" for field in missing)
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} faceports cell={cell} face={face} "
                        f"lacks required {fields}",
                    )
                    continue
                at = event.attrs["at"]
                arity = event.attrs["arity"]
                if not at or not _is_nonnegative_int(arity):
                    continue  # FIELD_VALIDATORS already emitted malformed-event.
                declaration = self._declared_face_ports(event)
                if declaration is None:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} faceports cell={cell} "
                        f"face={face} has invalid at={at!r}",
                    )
                    continue
                ports, row_count = declaration
                expected_arity = row_count if row_count is not None else len(ports)
                if int(arity) != expected_arity:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} faceports cell={cell} face={face} "
                        f"declares arity={arity} but at={at!r} resolves to "
                        f"{expected_arity} port(s)",
                    )
                    continue
                key = cell, face
                previous = declared.get(key)
                if previous is None:
                    declared[key] = ports, row_count, event.line
                    continue
                previous_ports, previous_rows, previous_line = previous
                if previous_ports == ports and previous_rows == row_count:
                    continue
                self.hard(
                    "conflicting-faceports",
                    f"{self.log_path.name}:{event.line}",
                    f"picture {pic.ident} cell={cell} face={face} conflicts "
                    f"with its declaration on line {previous_line}",
                )
            for event in pic.events:
                if event.kind != "pairleg":
                    continue
                upper = event.attrs.get("upper", "")
                port = event.attrs.get("upper-port", "")
                down_key = upper, "down"
                if (not _is_cell(upper) or not _is_pairleg_port(port)
                        or down_key not in declared):
                    continue
                ports, row_count, _ = declared[down_key]
                matches = port in ports
                if not matches and row_count is not None and port != "center":
                    matches = int(port) <= row_count
                if matches:
                    continue
                available_parts = sorted(
                    ports,
                    key=lambda slot: -1 if slot == "center" else int(slot),
                )
                if row_count is not None:
                    available_parts.append(f"rows 1..{row_count}")
                available = ",".join(available_parts) or "none"
                self.hard(
                    "pairleg-faceport-mismatch",
                    f"{self.log_path.name}:{event.line}",
                    f"picture {pic.ident} pairleg upper={upper} names upper-port={port!r}, "
                    f"but its declared down face has ports {available}",
                )

    def check_repeated_topology(self) -> None:
        groups: dict[tuple[str, str], list[Picture]] = {}
        for pic in self.pictures:
            atoms = [e for e in pic.content() if e.kind == "atom"]
            if len(atoms) < 2:
                continue  # a lone bead repeated is not worth a \tndefine
            groups.setdefault((pic.lang, canonical_hash(pic)), []).append(pic)
        for (lang, digest), pics in sorted(groups.items(),
                                           key=lambda kv: kv[1][0].ident):
            if len(pics) < 2:
                continue
            # A cd parent emits its final addressed edges after all object
            # cells have been typeset.  Grid pictures declared inside that
            # line interval are therefore nested object cells.  Repeating an
            # object in several rows of one map family is the point of a
            # small-multiple diagram, not a candidate for a global named
            # figure definition.
            parents = []
            for pic in pics:
                containing = [
                    parent for parent in self.pictures
                    if parent.lang == "cd"
                    and parent.line < pic.line
                    and parent.content()
                    and pic.line < max(e.line for e in parent.content())
                ]
                parents.append(max(containing, key=lambda p: p.line,
                                   default=None))
            if parents[0] is not None and all(
                    parent is not None
                    and parent.ident == parents[0].ident
                    for parent in parents):
                continue
            ids = ", ".join(str(p.ident) for p in pics)
            self.adv("repeated-topology", self.log_path.name,
                     f"pictures {ids} (lang={lang}) share canonical topology "
                     f"{digest}; consider a \\tndefine")

    def check_periodic_dots(self) -> None:
        for idx, pic in enumerate(self.pictures):
            if pic.lang != "grid":
                continue
            if not any(e.kind == "trace" for e in pic.events):
                continue
            ncols = pic.ncols()
            if ncols < 4:
                continue
            if self._has_dots_cell(idx, pic, ncols):
                continue
            self.adv("periodic-no-dots", f"{self.log_path.name}:{pic.line}",
                     f"picture {pic.ident}: traced chain of {ncols} columns "
                     f"without an ellipsis cell; a generic-length word should "
                     f"show \\tndots")

    def _has_dots_cell(self, idx: int, pic: Picture, ncols: int) -> bool:
        """Prefer the source (`\\tndots` in the matched body); otherwise use
        the atom-gap proxy: `\\tndots` emits no atom, so a column with no
        atom in any row is an ellipsis candidate.  The proxy over-detects
        (`\\tnX`/`\\tnghost` also emit no atom), so it only ever
        under-reports -- safe for an advisory."""
        if self.tex_linked:
            return re.search(r"\\tndots\b", self.constructs[idx].body) is not None
        cols_with_atoms = {int(e.attrs["cell"].split("-")[1])
                           for e in pic.events
                           if e.kind == "atom" and _is_cell(e.attrs.get("cell", ""))}
        return any(c not in cols_with_atoms for c in range(1, ncols + 1))

    # ---------------- source-linked checks ----------------

    def link_tex(self) -> None:
        if self.tex_path is None or not self.tex_path.exists():
            return
        src = strip_comments(self.tex_path.read_text(encoding="utf-8"))
        self.constructs = scan_constructs(src)
        if len(self.constructs) == len(self.pictures) and self.pictures:
            self.tex_linked = True
        elif self.constructs and not self.pictures:
            self.adv("stale-log", self.log_path.name,
                     f"{self.tex_path.name} declares {len(self.constructs)} "
                     f"picture construct(s) but the log has none (failed or "
                     f"interrupted compile?)")
        elif len(self.constructs) != len(self.pictures):
            self.note("tex-unlinked", self.log_path.name,
                      f"{len(self.constructs)} construct(s) in "
                      f"{self.tex_path.name} vs {len(self.pictures)} picture(s) "
                      f"in the log; source-linked advisories disabled "
                      f"(macro-generated pictures?)")
        if self.tex_linked:
            self._tex_src = src

    def check_equation_boundaries(self) -> None:
        if not self.tex_linked:
            return
        for i in range(len(self.pictures) - 1):
            a, b = self.pictures[i], self.pictures[i + 1]
            if a.lang != "grid" or b.lang != "grid":
                continue
            ca, cb = self.constructs[i], self.constructs[i + 1]
            if ca.end > cb.start:
                continue  # nested constructs: no linear separator
            sep = self._tex_src[ca.end:cb.start]
            if not same_equation(sep):
                continue
            sig_a, sig_b = a.boundary(), b.boundary()
            if sig_a is None or sig_b is None or sig_a == sig_b:
                continue
            self.adv("eq-boundary-mismatch",
                     f"{self.log_path.name}:{a.line}",
                     f"pictures {a.ident} and {b.ident} sit on one `=` but "
                     f"open-leg signatures differ: "
                     f"(vw,ve,pu,pd) {sig_a} vs {sig_b} "
                     f"[{self.tex_path.name}:{ca.line}]")

    # ---------------- driver ----------------

    def run(self) -> int:
        self.parse_log()
        self.link_tex()
        self.check_empty_pictures()
        self.check_dialects()
        self.check_pairleg_faceports()
        self.check_equation_boundaries()
        self.check_periodic_dots()
        self.check_repeated_topology()
        return self.report()

    def report(self) -> int:
        hard = [f for f in self.findings if f.severity == "HARD"]
        advs = [f for f in self.findings if f.severity == "ADV"]
        notes = [f for f in self.findings if f.severity == "NOTE"]
        tex = self.tex_path.name if self.tex_path and self.tex_path.exists() else "none"
        linked = " (linked)" if self.tex_linked else ""
        print(f"== tenkz audit: {self.log_path.name} -- "
              f"{len(self.pictures)} picture(s); tex: {tex}{linked} ==")
        for f in hard + advs + notes:
            print(f"  {f.severity:<4} [{f.rule}] {f.where}: {f.msg}")
        if hard:
            print(f"  FAIL: {len(hard)} hard error(s), {len(advs)} advisory(ies)")
            return 1
        print(f"  ok: no hard errors ({len(advs)} advisory(ies))")
        return 0


# ---------------- canonical topology ----------------

def parse_tree_topology(value: str) -> Optional[tuple[int, int]]:
    """Return (leaves, internal vertices) for canonical numeric bracketing.

    A canonical tree is either the next positive leaf number or a pair of
    canonical trees.  Consequently the leaf sequence must be exactly
    1,2,...,n; labels and TeX never enter this structural field.
    """
    pos = 0
    leaf_numbers: list[int] = []

    def parse_node() -> Optional[int]:
        nonlocal pos
        if pos >= len(value):
            return None
        if value[pos].isdigit():
            start = pos
            while pos < len(value) and value[pos].isdigit():
                pos += 1
            leaf = int(value[start:pos])
            if leaf <= 0:
                return None
            leaf_numbers.append(leaf)
            return 0
        if value[pos] != "(":
            return None
        pos += 1
        left = parse_node()
        if left is None or pos >= len(value) or value[pos] != ",":
            return None
        pos += 1
        right = parse_node()
        if right is None or pos >= len(value) or value[pos] != ")":
            return None
        pos += 1
        return left + right + 1

    try:
        vertices = parse_node()
    except (RecursionError, ValueError):
        return None
    if (vertices is None or pos != len(value)
            or leaf_numbers != list(range(1, len(leaf_numbers) + 1))):
        return None
    return len(leaf_numbers), vertices


def canonical_hash(pic: Picture) -> str:
    """Order-free digest of a picture's content.  Attributes are sorted,
    the `picture` back-reference is dropped (identity must not depend on
    position in the document), and `dir=none` is normalized away so logs
    from emitters before the `dir` attribute hash identically."""
    lines = []
    for e in pic.content():
        attrs = {k: v for k, v in e.attrs.items() if k != "picture"}
        if e.kind == "bond" and attrs.get("dir") == "none":
            del attrs["dir"]
        if e.kind == "faceports":
            at = attrs.get("at", "")
            try:
                if at == "rows":
                    slots = range(1, int(attrs["arity"]) + 1)
                    attrs["at"] = ",".join(str(slot) for slot in slots)
                elif at not in {"center", "none"}:
                    slots = sorted({int(slot) for slot in at.split(",")})
                    attrs["at"] = ",".join(str(slot) for slot in slots)
            except (KeyError, ValueError):
                pass  # malformed fields are reported by the parser
        lines.append(e.kind + "|" + "|".join(
            f"{k}={v}" for k, v in sorted(attrs.items())))
    payload = "\n".join(sorted(lines)).encode("utf-8")
    return hashlib.sha1(payload).hexdigest()[:12]


# ---------------- TeX source scanning ----------------

@dataclass
class Construct:
    name: str      # environment name or "tnpic"
    start: int     # offset of the construct's first character
    end: int       # offset one past its last character
    body: str
    line: int


def strip_comments(src: str) -> str:
    """Replace unescaped `%`-comments with spaces, preserving offsets so
    positions in the stripped text index the original file."""
    out: list[str] = []
    for line in src.split("\n"):
        buf = list(line)
        i = 0
        while i < len(buf):
            if buf[i] == "\\":
                i += 2
                continue
            if buf[i] == "%":
                for j in range(i, len(buf)):
                    buf[j] = " "
                break
            i += 1
        out.append("".join(buf))
    return "\n".join(out)


def _match_group(src: str, i: int, open_ch: str, close_ch: str) -> int:
    """Offset one past the group opening at `src[i]`, brace-aware: a `]`
    inside `{...}` does not close a `[...]` group.  Works for both brace
    and bracket groups.  Returns -1 if unbalanced."""
    depth_group = 0
    depth_brace = 0
    while i < len(src):
        c = src[i]
        if c == "\\":
            i += 2
            continue
        if c == open_ch and (open_ch == "{" or depth_brace == 0):
            depth_group += 1
        elif c == close_ch and (close_ch == "}" or depth_brace == 0):
            depth_group -= 1
            if depth_group == 0:
                return i + 1
        elif c == "{":
            depth_brace += 1
        elif c == "}":
            depth_brace -= 1
        i += 1
    return -1


def _find_env_end(src: str, name: str, pos: int) -> Optional[re.Match[str]]:
    """Match of the `\\end{name}` closing the `\\begin{name}` whose body
    starts at `pos`, depth-counting nested same-name environments so an
    inner `\\end` never closes the outer construct.  None if unclosed."""
    token_re = re.compile(r"\\(begin|end)\{" + re.escape(name) + r"\}")
    depth = 1
    for tok in token_re.finditer(src, pos):
        depth += 1 if tok.group(1) == "begin" else -1
        if depth == 0:
            return tok
    return None


def scan_constructs(src: str) -> list[Construct]:
    """Picture-producing constructs in source order.  tenkz assigns picture
    ids at `\\begin` time, so source order of construct starts equals log
    order even when a `\\tnpic` nests inside a `tenkzcd` cell."""
    found: list[Construct] = []
    env_re = re.compile(r"\\begin\{(tenkz(?:cd|lattice|free|planes)?)\}")
    for m in env_re.finditer(src):
        name = m.group(1)
        end_m = _find_env_end(src, name, m.end())
        end = end_m.end() if end_m else len(src)
        body_start = m.end()
        if src[body_start:body_start + 1] == "[":
            closed = _match_group(src, body_start, "[", "]")
            if closed != -1:
                body_start = closed
        body_end = end_m.start() if end_m else len(src)
        found.append(Construct(name, m.start(), end,
                               src[body_start:body_end],
                               src.count("\n", 0, m.start()) + 1))
    for m in re.finditer(r"\\tnpic\b", src):
        i = m.end()
        while i < len(src) and src[i] in " \t\n":
            i += 1
        if src[i:i + 1] == "[":
            closed = _match_group(src, i, "[", "]")
            if closed == -1:
                continue
            i = closed
            while i < len(src) and src[i] in " \t\n":
                i += 1
        if src[i:i + 1] != "{":
            continue
        closed = _match_group(src, i, "{", "}")
        if closed == -1:
            continue
        found.append(Construct("tnpic", m.start(), closed,
                               src[i + 1:closed - 1],
                               src.count("\n", 0, m.start()) + 1))
    found.sort(key=lambda c: c.start)
    return found


def same_equation(sep: str) -> bool:
    """Heuristic: the comment-stripped source between two constructs is a
    single displayed equation's glue iff it contains `=`, crosses no
    math-mode boundary and no other environment, and is short.  This keeps
    the check to `A = B` pairs like the gauge/blocking benchmarks."""
    if "=" not in sep:
        return False
    if any(tok in sep for tok in ("$", "\\[", "\\]", "&", "\\begin", "\\end")):
        return False
    return len(sep.strip()) <= 200


# ---------------- CLI ----------------

def main(argv: list[str]) -> int:
    args = [a for a in argv if not a.startswith("-")]
    if "-h" in argv or "--help" in argv or not 1 <= len(args) <= 2:
        print(__doc__.strip().splitlines()[0])
        print("usage: tenkz_audit.py file.tnlog [file.tex]")
        return 0 if ("-h" in argv or "--help" in argv) else 2
    log_path = Path(args[0])
    if not log_path.exists():
        print(f"tenkz_audit: no such file: {log_path}", file=sys.stderr)
        return 2
    if len(args) == 2:
        tex_path: Optional[Path] = Path(args[1])
    else:
        sibling = log_path.with_suffix(".tex")
        tex_path = sibling if sibling.exists() else None
    return Audit(log_path, tex_path).run()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
