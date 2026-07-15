r"""plasTeX renderers for TNLean tensor-network diagrams.

The PDF blueprint renders the chapter-facing ``\TN...`` macros from
``macros/tn_print.tex`` together with the repository-wide core and library in
``tex/tn``.  The web blueprint invokes the same public commands and compiles
the same TeX sources to cached SVG files.  Thus the semantic TikZ calculus is
common to print and web output.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import posixpath
import re
import shutil
import subprocess
from dataclasses import dataclass
from functools import lru_cache
from html import escape
from pathlib import Path
from typing import Iterable

from _tnlean_utils import stringify_tex_item
from plasTeX import Command


log = logging.getLogger(__name__)

_SRC_DIR = Path(__file__).resolve().parents[1]
_REPO_ROOT = _SRC_DIR.parents[1]
_TN_SHARED_DIR = _REPO_ROOT / "tex/tn"
_TN_CORE_FILE = _TN_SHARED_DIR / "tn_core.tex"
_TN_LIBRARY_FILE = _TN_SHARED_DIR / "tn_library.tex"
_TN_ATOMS_FILE = _TN_SHARED_DIR / "tn_atoms.tex"
_TN_CATALOGUE_FILE = _TN_SHARED_DIR / "tn_catalogue.tex"
_TN_MOTIF_FILES = tuple(sorted(_TN_SHARED_DIR.glob("tn_motifs_*.tex")))
_CACHE_DIR = _SRC_DIR / ".tn_svg_cache"
_SVG_SUBDIR = "tn_svg"
_RENDER_SOURCE_FILES = (
    _SRC_DIR / "macros/common.tex",
    _TN_CORE_FILE,
    _TN_LIBRARY_FILE,
    _TN_ATOMS_FILE,
    *_TN_MOTIF_FILES,
    _TN_CATALOGUE_FILE,
    _SRC_DIR / "macros/tn_print.tex",
)
_TEMPLATE_FILE = _SRC_DIR / "plastex_templates/TensorNetworkDiagrams.jinja2s"
_SLIDE_DIR = _REPO_ROOT / "docs/slides"
_SLIDE_LIBRARY = _SLIDE_DIR / "tn_library_dark.tex"
_SLIDE_CATALOGUE = _TN_SHARED_DIR / "tn_slide_catalogue.tex"
_GRAMMAR_FILE = _REPO_ROOT / "docs/tn_diagram_grammar.md"
_AUDITED_DIAGRAM_SOURCES = tuple(
    path
    for path in sorted(_TN_SHARED_DIR.glob("*.tex"))
    if path != _TN_CORE_FILE
) + (_SLIDE_LIBRARY,)

_LITERAL_COORDINATE_PATTERN = re.compile(
    r"(?<![A-Za-z])\((-?\d+(?:\.\d+)?(?:cm)?),"
    r"(-?\d+(?:\.\d+)?(?:cm)?)\)"
)
_RAW_GLYPH_PATTERNS = {
    "filled circles": re.compile(r"\\fill(?:\[[^\]]*\])?[^;\n]*\bcircle\b"),
    "circle nodes": re.compile(
        r"\\node\[[^\]]*(?<![A-Za-z])circle(?:\s|,|\])"
    ),
    "styled glyph nodes": re.compile(
        r"\\node\[[^\]]*(?<![A-Za-z])tn (?:tensor node|insertion node|"
        r"component node|factor node|"
        r"map node|tensor dot|operator dot|tensor box|map box)\b"
    ),
    "legacy glyph commands": re.compile(
        r"\\TN@(?:tensordot|opdot(?:above|below|left|right)?|subspinbox)\b"
    ),
}
_RAW_WIRE_PATTERN = re.compile(
    r"\\draw\s*\[[^\]]*(?<![A-Za-z])tn(?:\s|/)[^\]]*\]"
)
_LEGACY_WIRE_COMMAND_PATTERN = re.compile(
    r"\\TN@(?:leftleg|rightleg|upleg|downleg|subspinlink)\b"
)
_SEMANTIC_GLYPH_COMMANDS = frozenset(
    {
        "TN@component",
        "TN@cofusionmap",
        "TN@expression",
        "TN@factor",
        "TN@factorwithlegs",
        "TN@fusionmap",
        "TN@insertion",
        "TN@junction",
        "TN@map",
        "TN@mergemap",
        "TN@mposite",
        "TN@mpssite",
        "TN@operatorstate",
        "TN@pepssite",
        "TN@pepsvertex",
        "TN@splitmap",
        "TN@state",
        "TN@tensor",
        "TN@labeledinsertion",
        "TN@threeLegTensorFan",
    }
)
_POINT_CONNECTOR_COMMANDS = frozenset(
    {"TN@connectpoints", "TN@pconnectpoints", "TN@vconnectpoints"}
)
_SIMPLE_NODE_NAME_PATTERN = re.compile(r"[#A-Za-z\\][#A-Za-z0-9@_\\-]*\Z")
_SYMBOLIC_PORT_PATTERN = re.compile(r"[#A-Za-z\\][#A-Za-z0-9@_\\-]*\Z")
_CONTROL_WORD_DELIMITER_PATTERN = re.compile(r"(\\[A-Za-z@]+)\s+")
_UNTYPED_PORT_COMMAND_PATTERN = re.compile(
    r"\\TN@(?:port|betweenport|westport|eastport|northport|southport|registerport)\b"
)
_PRIVATE_COMMAND_PATTERN = re.compile(r"\\TN@[A-Za-z@]+")
_CLIENT_TIKZ_PATTERN = re.compile(
    r"\\begin\{tikzpicture\}|\\begin\{scope\}(?:\[[^]]*\])?|"
    r"\\(?:draw|coordinate|node)\b|\\path\s*(?:\[|\()"
)
_LOCAL_GEOMETRY_PATTERN = re.compile(
    r"(?:scale|xshift|yshift)\s*=|"
    r"(?:minimum\s+(?:width|height|size)|inner\s+sep|outer\s+sep|"
    r"line\s+width|rounded\s+corners|fill|shape)\s*="
)
_TYPED_PORT_COMMAND_ARITIES = {
    "TN@vconnectports": (2, (0, 1)),
    "TN@vconnectportshv": (2, (0, 1)),
    "TN@vconnectportsvh": (2, (0, 1)),
    "TN@pconnectports": (2, (0, 1)),
    "TN@pconnectportshv": (2, (0, 1)),
    "TN@pconnectportsvh": (2, (0, 1)),
    "TN@mconnectports": (2, (0, 1)),
    "TN@mconnectportshv": (2, (0, 1)),
    "TN@mconnectportsvh": (2, (0, 1)),
    "TN@vopenport": (2, (0,)),
    "TN@popenport": (2, (0,)),
    "TN@vtraceportsbelow": (4, (0, 1)),
    "TN@vtraceportsabove": (4, (0, 1)),
    "TN@vtraceportsright": (4, (0, 1)),
    "TN@ptraceportsbelow": (4, (0, 1)),
    "TN@ptraceportsabove": (4, (0, 1)),
    "TN@ptraceportsright": (4, (0, 1)),
}


@dataclass(frozen=True)
class DiagramDeclaration:
    """One chapter-facing diagram, as declared in ``tn_catalogue.tex``."""

    name: str
    arguments: tuple[str, ...]
    role: str
    profile: str
    sample: str
    contexts: tuple[str, ...]
    body: str
    source_line: int

    @property
    def plastex_args(self) -> str:
        return " ".join(self.arguments)


@dataclass(frozen=True)
class AtomPort:
    """One named, typed port in an atomic tensor-network glyph."""

    name: str
    kind: str


@dataclass(frozen=True)
class AtomDeclaration:
    """One public atom, as declared in ``tn_atoms.tex``."""

    name: str
    ports: tuple[AtomPort, ...]
    profile: str
    sample: str
    source_line: int


@dataclass(frozen=True)
class TexDeclarationCall:
    """One line-initial TeX declaration and the offsets of its group bodies."""

    groups: tuple[str, ...]
    source_offset: int
    group_offsets: tuple[int, ...]


@dataclass(frozen=True)
class DiagramCatalogue:
    """The ordered declarations read from ``tn_catalogue.tex``."""

    declarations: tuple[DiagramDeclaration, ...]

    @property
    def names(self) -> tuple[str, ...]:
        return tuple(declaration.name for declaration in self.declarations)

    def declaration(self, name: str) -> DiagramDeclaration:
        for declaration in self.declarations:
            if declaration.name == name:
                return declaration
        raise KeyError(name)


@dataclass(frozen=True)
class AtomCatalogue:
    """The ordered declarations read from ``tn_atoms.tex``."""

    declarations: tuple[AtomDeclaration, ...]

    @property
    def names(self) -> tuple[str, ...]:
        return tuple(declaration.name for declaration in self.declarations)


# The catalogues are initialized after the balanced TeX-group reader below.
# All renderer metadata is subsequently obtained from these immutable objects.
_DIAGRAM_CATALOGUE: DiagramCatalogue
_ATOM_CATALOGUE: AtomCatalogue


def diagram_declarations() -> tuple[DiagramDeclaration, ...]:
    """Return the catalogue declarations in their TeX source order."""

    return _DIAGRAM_CATALOGUE.declarations


def atom_declarations() -> tuple[AtomDeclaration, ...]:
    """Return the atom declarations in their TeX source order."""

    return _ATOM_CATALOGUE.declarations


def _sample_tex_call(name: str) -> str:
    return _DIAGRAM_CATALOGUE.declaration(name).sample


def _assert_no_duplicate_diagram_definitions() -> None:
    """Reject a second chapter-diagram definition outside the catalogue."""

    duplicates: list[str] = []
    pattern = re.compile(
        r"\\(?:"
        r"(?:(?:new|renew|provide)command|"
        r"(?:New|Renew|Provide|Declare)DocumentCommand)\*?\s*(?:\{\s*)?"
        r"|(?:def|gdef|edef|xdef|let)\s*"
        r")\\(TN(?!@)\w+)"
    )
    definition_sources = (
        _SRC_DIR / "macros/tn_print.tex",
        *sorted(
            path
            for path in _TN_SHARED_DIR.glob("*.tex")
            if path != _TN_CATALOGUE_FILE
        ),
    )
    for path in definition_sources:
        if not path.exists():
            continue
        source = _mask_tex_comments(path.read_text(encoding="utf-8"))
        duplicates.extend(
            _source_line(path, match.start())
            for match in pattern.finditer(source)
            if match.group(1) in _DIAGRAM_CATALOGUE.names
        )
    if duplicates:
        raise RuntimeError(
            "Chapter-facing tensor-network diagrams must be defined only by "
            "\\TNDeclareDiagram in tex/tn/tn_catalogue.tex: "
            + _abbreviate_locations(duplicates)
        )


def _assert_diagram_templates_are_catalogue_independent() -> None:
    pattern = re.compile(r"^name:\s+(.+)$", re.MULTILINE)
    template = _TEMPLATE_FILE.read_text(encoding="utf-8")
    rendered_names = {
        name
        for line in pattern.findall(template)
        for name in line.split()
    }
    required = {"TensorNetworkDiagram"}
    stale_templates = sorted(
        name for name in rendered_names if name in _DIAGRAM_CATALOGUE.names
    )
    if not required <= rendered_names or stale_templates:
        raise RuntimeError(
            "Tensor-network diagrams must share the catalogue-independent "
            "TensorNetworkDiagram HTML template "
            f"(missing={sorted(required - rendered_names)}, "
            f"parallel_templates={stale_templates})."
        )


def _source_line(path: Path, offset: int) -> str:
    """Return a stable ``path:line`` description for a source offset."""

    text = path.read_text(encoding="utf-8")
    try:
        relative = path.relative_to(_REPO_ROOT)
    except ValueError:
        relative = path
    return f"{relative}:{text.count(chr(10), 0, offset) + 1}"


def _mask_tex_comments(source: str) -> str:
    """Replace unescaped TeX comments by spaces while preserving offsets."""

    characters = list(source)
    index = 0
    while index < len(characters):
        if characters[index] != "%":
            index += 1
            continue
        if _is_escaped(source, index):
            index += 1
            continue
        cursor = index
        while cursor < len(characters) and characters[cursor] != "\n":
            characters[cursor] = " "
            cursor += 1
        index = cursor
    return "".join(characters)


def _is_escaped(source: str, offset: int) -> bool:
    """Whether the character at ``offset`` follows an odd backslash run."""

    backslashes = 0
    cursor = offset - 1
    while cursor >= 0 and source[cursor] == "\\":
        backslashes += 1
        cursor -= 1
    return backslashes % 2 == 1


def _unescaped_parameter_indices(source: str) -> set[int]:
    """Return the TeX macro parameters ``#1`` through ``#9`` used in source."""

    return {
        int(match.group(1))
        for match in re.finditer(r"#([1-9])", source)
        if not _is_escaped(source, match.start())
    }


def _pattern_locations(path: Path, pattern: re.Pattern[str]) -> list[str]:
    text = _mask_tex_comments(path.read_text(encoding="utf-8"))
    return [_source_line(path, match.start()) for match in pattern.finditer(text)]


def _assert_diagram_roles_match_chapters() -> None:
    """Check declared roles and contexts against every chapter use."""

    actual: dict[str, set[str]] = {
        declaration.name: set() for declaration in diagram_declarations()
    }
    declared_contexts = {
        declaration.name: set(declaration.contexts)
        for declaration in diagram_declarations()
    }
    actual_contexts: dict[str, set[str]] = {
        declaration.name: set() for declaration in diagram_declarations()
    }
    call_pattern = re.compile(r"\\(TN[A-Z]\w*)")
    figure_pattern = re.compile(r"\\begin\{figure\}.*?\\end\{figure\}", re.DOTALL)
    for path in sorted((_SRC_DIR / "chapter").rglob("*.tex")):
        relative = path.relative_to(_SRC_DIR).as_posix()
        source = _mask_tex_comments(path.read_text(encoding="utf-8"))
        figure_spans = [match.span() for match in figure_pattern.finditer(source)]
        for match in call_pattern.finditer(source):
            name = match.group(1)
            if name not in actual:
                continue
            role = (
                "figure"
                if any(start <= match.start() < end for start, end in figure_spans)
                else "display"
            )
            actual[name].add(role)
            actual_contexts[name].add(relative)

    mixed = sorted(name for name, roles in actual.items() if len(roles) > 1)
    mismatched = sorted(
        name
        for name, roles in actual.items()
        if roles and roles != {_DIAGRAM_CATALOGUE.declaration(name).role}
    )
    context_mismatches = {
        name: {
            "declared": sorted(declared_contexts[name]),
            "actual": sorted(actual_contexts[name]),
        }
        for name in _DIAGRAM_CATALOGUE.names
        if declared_contexts[name] != actual_contexts[name]
    }
    if mixed or mismatched or context_mismatches:
        raise RuntimeError(
            "Tensor-network display/figure roles or chapter contexts are inconsistent "
            f"(mixed={mixed}, mismatched={mismatched}, "
            f"contexts={context_mismatches})."
        )


def _assert_no_chapter_local_tikz() -> None:
    """Require chapter sources to use the public tensor-network vocabulary."""

    forbidden = re.compile(
        r"\\begin\{tikzpicture\}|\\tikz(?:set|style)?\b|"
        r"\\(?:draw|fill|filldraw|shade|shadedraw|coordinate|node)\b|"
        r"\\path\s*(?:\[|\()"
    )
    violations = [
        location
        for path in sorted((_SRC_DIR / "chapter").rglob("*.tex"))
        for location in _pattern_locations(path, forbidden)
    ]
    if violations:
        raise RuntimeError(
            "Chapter-local tensor-network TikZ is forbidden; define a public "
            "mathematical diagram command instead: " + ", ".join(violations)
        )


def _private_command_definitions(source: str) -> set[str]:
    """Return private commands defined by ``\\newcommand`` in a TeX source."""

    return set(
        re.findall(
            r"\\newcommand\{\\(TN@[A-Za-z@]+)\}",
            _mask_tex_comments(source),
        )
    )


def _assert_audit_commands_defined() -> None:
    """Require every command classified by the audit to exist in the library."""

    implementation = "\n".join(
        path.read_text(encoding="utf-8")
        for path in (_TN_CORE_FILE, _TN_LIBRARY_FILE)
    )
    defined = _private_command_definitions(implementation)
    classified = (
        _SEMANTIC_GLYPH_COMMANDS
        | _POINT_CONNECTOR_COMMANDS
        | frozenset(_TYPED_PORT_COMMAND_ARITIES)
    )
    stale = sorted(classified - defined)
    if stale:
        raise RuntimeError(
            "The semantic audit classifies undefined private commands: "
            + ", ".join(stale)
        )


def _assert_no_unused_private_commands() -> None:
    """Reject private TeX constructors which no repository diagram uses."""

    sources = [
        _mask_tex_comments(path.read_text(encoding="utf-8"))
        for path in sorted(_TN_SHARED_DIR.glob("*.tex"))
    ]
    implementation = "\n".join(sources)
    definitions = set().union(
        *(_private_command_definitions(source) for source in sources)
    )
    unused = sorted(
        name
        for name in definitions
        if len(re.findall(r"\\" + re.escape(name) + r"\b", implementation)) == 1
    )
    if unused:
        raise RuntimeError(
            "Private tensor-network commands have no repository use: "
            + ", ".join(unused)
        )


def _assert_typed_port_syntax() -> None:
    """Require typed compositions to use symbolic ports and typed constructors."""

    command_names = frozenset(_TYPED_PORT_COMMAND_ARITIES)
    malformed: list[str] = []
    untyped: list[str] = []
    forbidden_options = re.compile(
        r"(?:^|,)\s*(?:<?-+>?|dashed|densely dashed|tn (?:grouping|factor) region|"
        r"tn (?:morphism|comparison) arrow)\s*(?:,|$)"
    )
    for path in _AUDITED_DIAGRAM_SOURCES:
        source = _mask_tex_comments(path.read_text(encoding="utf-8"))
        untyped.extend(
            _source_line(path, match.start())
            for match in _UNTYPED_PORT_COMMAND_PATTERN.finditer(source)
        )
        for command, arguments, offset, option in _tex_command_calls(
            source, command_names
        ):
            arity, endpoint_indices = _TYPED_PORT_COMMAND_ARITIES[command]
            if len(arguments) != arity:
                malformed.append(_source_line(path, offset))
                continue
            # TeX discards whitespace used to terminate a control word, as in
            # ``\\name E``.  Other whitespace survives tokenization and cannot
            # belong to a symbolic port identifier.
            endpoints = [
                _CONTROL_WORD_DELIMITER_PATTERN.sub(r"\1", arguments[index]).strip()
                for index in endpoint_indices
            ]
            if any(not _SYMBOLIC_PORT_PATTERN.fullmatch(value) for value in endpoints):
                malformed.append(_source_line(path, offset))
            if option and forbidden_options.search(option):
                malformed.append(_source_line(path, offset))
    if untyped:
        raise RuntimeError(
            "Untyped port constructors are private to tex/tn/tn_core.tex: "
            + _abbreviate_locations(untyped)
        )
    if malformed:
        raise RuntimeError(
            "Typed tensor-network composition has a non-symbolic endpoint, wrong "
            "arity, or category-changing style at "
            + _abbreviate_locations(sorted(set(malformed)))
        )


def _assert_no_raw_glyph_nodes() -> None:
    """Reject locally styled boxes and dots outside the semantic node vocabulary."""

    appearance = re.compile(
        r"(?:^|,)\s*(?:draw(?:=|,|$)|fill(?:=|,|$)|circle(?:,|$)|rectangle(?:,|$)|"
        r"rounded corners|shape=|minimum (?:width|height|size))"
    )
    approved = re.compile(
        r"(?:^|,)\s*tn (?:label|region label \w+|vertex distinguished)(?:,|$)"
    )
    violations: list[str] = []
    for path in _AUDITED_DIAGRAM_SOURCES:
        source = _mask_tex_comments(path.read_text(encoding="utf-8"))
        for match in re.finditer(r"\\node\s*\[([^]]*)\]", source):
            options = match.group(1)
            if appearance.search(options) and not approved.search(options):
                violations.append(_source_line(path, match.start()))
    if violations:
        raise RuntimeError(
            "Raw tensor-network glyph appearance is forbidden outside semantic "
            "node constructors: " + _abbreviate_locations(violations)
        )


def _assert_documented_public_vocabulary() -> None:
    """Keep the mathematical style guide synchronized with the TeX API."""

    source = _GRAMMAR_FILE.read_text(encoding="utf-8")
    begin_marker = "<!-- TN-PUBLIC-VOCABULARY:BEGIN -->"
    end_marker = "<!-- TN-PUBLIC-VOCABULARY:END -->"
    if source.count(begin_marker) != 1 or source.count(end_marker) != 1:
        raise RuntimeError(
            "docs/tn_diagram_grammar.md must contain one checked public-"
            "vocabulary block."
        )
    block = source.split(begin_marker, 1)[1].split(end_marker, 1)[0]
    documented = set(re.findall(r"`(TN[A-Za-z0-9]+)`", block))

    implementation = "\n".join(
        path.read_text(encoding="utf-8")
        for path in (_TN_CORE_FILE, _TN_LIBRARY_FILE)
    )
    defined_commands = set(
        re.findall(
            r"\\(?:newcommand|renewcommand)\{\\(TN(?!@)[A-Za-z0-9]+)\}",
            implementation,
        )
    )
    defined_environments = set(
        re.findall(
            r"\\(?:newenvironment|NewDocumentEnvironment)\{(TN[A-Za-z0-9]+)\}",
            implementation,
        )
    )
    declared_atoms = set(_ATOM_CATALOGUE.names)
    declared_diagrams = set(_DIAGRAM_CATALOGUE.names)
    known = defined_commands | defined_environments | declared_atoms | declared_diagrams

    missing_atoms = sorted(declared_atoms - documented)
    stale = sorted(documented - known)
    forbidden = {
        "TNPoint",
        "TNPointBetween",
        "TNLabel",
        "TNPlacedLabel",
        "TNCanvas",
        "TNGroupBoundary",
        "TNFactorBoundary",
        "TNAnnotation",
        "TNSelectedPath",
        "TNSecondaryPath",
        "TNSelectedRegionPath",
        "TNSecondaryRegionPath",
        "TNComplementRegionPath",
    }
    documented_escape_hatches = sorted(documented & forbidden)
    if missing_atoms or stale or documented_escape_hatches:
        raise RuntimeError(
            "The checked tensor-network vocabulary is inconsistent "
            f"(missing_atoms={missing_atoms}, stale={stale}, "
            f"escape_hatches={documented_escape_hatches})."
        )


def _assert_slide_diagram_contract() -> None:
    """Check the dark theme over the repository-wide tensor-network core."""

    if not _SLIDE_LIBRARY.exists():
        raise RuntimeError(f"Missing slide tensor-network library: {_SLIDE_LIBRARY}")

    preamble = (_SLIDE_DIR / "preamble.tex").read_text(encoding="utf-8")
    if r"\input{tn_library_dark}" not in preamble:
        raise RuntimeError("The slide preamble must load tn_library_dark.tex.")

    decks = sorted(_SLIDE_DIR.glob("presentation*.tex"))
    deck_source = "\n".join(path.read_text(encoding="utf-8") for path in decks)
    calls = re.findall(r"\\(SlideTN[A-Z]\w*)\b", deck_source)
    counts = {name: calls.count(name) for name in sorted(set(calls))}
    declared_slides = _declared_slide_diagram_arities()
    unknown = sorted(set(counts) - set(declared_slides))
    unused = sorted(set(declared_slides) - set(counts))
    if unknown or unused:
        raise RuntimeError(
            "Slide tensor-network definitions and deck calls disagree "
            f"(unknown={unknown}, unused={unused})."
        )

    legacy_style = re.compile(
        r"(?:^|[,{ ])(?:tn|bond|phys)/\.style|"
        r"\\(?:node|draw)\[(?:tn|bond|phys)(?:,|\])",
        re.MULTILINE,
    )
    violations = [
        location
        for path in decks
        for location in _pattern_locations(path, legacy_style)
    ]
    if violations:
        raise RuntimeError(
            "Slide tensor networks must use the SlideTN vocabulary, not local "
            "tn/bond/phys styles: " + ", ".join(violations)
        )

    library_source = _SLIDE_LIBRARY.read_text(encoding="utf-8")
    required_shared_inputs = (r"\usetikzlibrary{tn}", r"\input{tn_slide_catalogue}")
    missing_inputs = [
        path for path in required_shared_inputs if path not in library_source
    ]
    if missing_inputs:
        raise RuntimeError(
            "The slide tensor-network theme must load the universal core and "
            "library: " + ", ".join(missing_inputs)
        )

    core_source = _TN_CORE_FILE.read_text(encoding="utf-8")
    palette_pattern = re.compile(
        r"^\s*\\colorlet\{(tn[A-Za-z]+)\}", re.MULTILINE
    )
    core_palette_keys = set(palette_pattern.findall(core_source))
    slide_palette_keys = set(palette_pattern.findall(library_source))
    missing_palette_keys = sorted(core_palette_keys - slide_palette_keys)
    invalid_palette_keys = sorted(slide_palette_keys - core_palette_keys)
    if missing_palette_keys or invalid_palette_keys:
        raise RuntimeError(
            "The slide palette overrides must match the color slots declared in "
            "tex/tn/tn_core.tex "
            f"(missing={missing_palette_keys}, invalid={invalid_palette_keys})."
        )

    theme_geometry = re.compile(
        r"(?:baseline|scale|xshift|yshift|shape|font|line width|"
        r"minimum (?:width|height|size)|inner sep|outer sep|rounded corners)\s*="
    )
    if theme_geometry.search(_mask_tex_comments(library_source)):
        raise RuntimeError(
            "The slide theme may change only the palette; tensor-network "
            "geometry and typography belong to tex/tn/tn_core.tex."
        )

    duplicate_kernel = re.compile(
        r"slidetn/|^\\newcommand\{\\SlideTN(?:Tensor|Component|State|Insertion|"
        r"PhysicalLeg|VirtualBond|OpenLeft|OpenRight|OmittedChain|TraceClosure)\}",
        re.MULTILINE,
    )
    if duplicate_kernel.search(library_source):
        raise RuntimeError(
            "The slide theme duplicates tensor-network atoms instead of using "
            "the universal TN core."
        )

    catalogue_source = _SLIDE_CATALOGUE.read_text(encoding="utf-8")
    raw_slide_draw = re.compile(
        r"^[ \t]*\\(?:draw|path|coordinate|fill|filldraw|shade|shadedraw)\b",
        re.MULTILINE,
    )
    if raw_slide_draw.search(catalogue_source):
        raise RuntimeError(
            "Complete slide tensor networks must compose universal TN commands, "
            "not contain raw TikZ paths or coordinates."
        )

    dashed_contraction = re.compile(
        r"\\TN@(?:v|p)(?:connect|open|trace)[A-Za-z@]*"
        r"(?:\[[^\]]*(?:dashed|densely dashed)[^\]]*\])"
    )
    if dashed_contraction.search(catalogue_source):
        raise RuntimeError(
            "A slide contraction or trace is dashed; dashed strokes are reserved "
            "for grouping regions."
        )

    macro_pattern = re.compile(
        r"^\\newcommand\{\\(SlideTN[A-Z]\w*)\}\[(\d+)\]", re.MULTILINE
    )
    matches = list(macro_pattern.finditer(catalogue_source))
    ignored: dict[str, list[int]] = {}
    for index, match in enumerate(matches):
        body_end = matches[index + 1].start() if index + 1 < len(matches) else len(
            catalogue_source
        )
        body = catalogue_source[match.end() : body_end]
        arity = int(match.group(2))
        referenced = _unescaped_parameter_indices(body)
        missing = [argument for argument in range(1, arity + 1) if argument not in referenced]
        if missing:
            ignored[match.group(1)] = missing
    if ignored:
        raise RuntimeError(f"Slide tensor-network macros ignore arguments: {ignored}")


def _declared_slide_diagram_arities() -> dict[str, int]:
    """Read slide diagram names and arities from the shared slide catalogue."""

    if not _SLIDE_CATALOGUE.is_file():
        return {}
    source = _mask_tex_comments(_SLIDE_CATALOGUE.read_text(encoding="utf-8"))
    pattern = re.compile(
        r"^\\newcommand\{\\(SlideTN[A-Z]\w*)\}(?:\[(\d+)\])?",
        re.MULTILINE,
    )
    declarations: dict[str, int] = {}
    for name, raw_arity in pattern.findall(source):
        if name in declarations:
            raise RuntimeError(f"Duplicate slide tensor-network diagram: {name}.")
        declarations[name] = int(raw_arity or 0)
    return declarations


def slide_diagram_samples() -> tuple[tuple[str, str], ...]:
    """Generate gallery samples directly from the slide macro definitions."""

    return tuple(
        (name, rf"\{name}" + "{A}" * arity)
        for name, arity in _declared_slide_diagram_arities().items()
    )


def _noncore_tikz_style_locations() -> list[str]:
    """Locate semantic style declarations outside the universal TN core."""

    core_path = _TN_CORE_FILE.resolve()
    forbidden = re.compile(r"^[ \t]*(?:\\tikzset\b|\\tikzstyle\b)", re.MULTILINE)
    return [
        location
        for root in (_SRC_DIR, _TN_SHARED_DIR)
        for path in sorted(root.rglob("*.tex"))
        if path.resolve() != core_path
        for location in _pattern_locations(path, forbidden)
    ]


def _client_source_paths() -> tuple[Path, ...]:
    """Return every TeX source that consumes, rather than implements, TN atoms."""

    chapters = tuple(sorted((_SRC_DIR / "chapter").rglob("*.tex")))
    return (
        _SRC_DIR / "macros/tn_print.tex",
        _SLIDE_LIBRARY,
        _SLIDE_CATALOGUE,
        *chapters,
    )


def _client_pattern_locations(pattern: re.Pattern[str]) -> list[str]:
    return [
        location
        for path in _client_source_paths()
        for location in _pattern_locations(path, pattern)
    ]


def _client_geometry_locations() -> list[str]:
    """Locate geometry specified by clients of the tensor-network calculus."""

    locations = []
    for path in _client_source_paths():
        source = path.read_text(encoding="utf-8")
        source = _mask_tex_comments(source)
        locations.extend(
            _source_line(path, match.start())
            for match in _LOCAL_GEOMETRY_PATTERN.finditer(source)
        )
    return locations


def _catalogue_pattern_locations(pattern: re.Pattern[str]) -> list[str]:
    """Locate client-level constructs inside declared diagram bodies."""

    return _pattern_locations(_TN_CATALOGUE_FILE, pattern)


def _catalogue_geometry_locations() -> list[str]:
    """Locate numerical placement and local appearance in the catalogue."""

    combined = re.compile(
        _LITERAL_COORDINATE_PATTERN.pattern + "|" + _LOCAL_GEOMETRY_PATTERN.pattern
    )
    return _catalogue_pattern_locations(combined)


def _skip_tex_space(source: str, offset: int) -> int:
    """Skip TeX whitespace and comments beginning at ``offset``."""

    while offset < len(source):
        if source[offset].isspace():
            offset += 1
            continue
        if source[offset] == "%":
            newline = source.find("\n", offset)
            return len(source) if newline < 0 else _skip_tex_space(source, newline + 1)
        return offset
    return offset


def _tex_group(source: str, offset: int, opener: str, closer: str) -> tuple[str, int]:
    """Read one balanced TeX group and return its contents and final offset."""

    if offset >= len(source) or source[offset] != opener:
        raise ValueError(f"expected {opener!r} at source offset {offset}")
    depth = 0
    for index in range(offset, len(source)):
        escaped = _is_escaped(source, index)
        if source[index] == opener and not escaped:
            depth += 1
        elif source[index] == closer and not escaped:
            depth -= 1
            if depth == 0:
                return source[offset + 1 : index], index + 1
    raise ValueError(f"unterminated {opener!r} group at source offset {offset}")


def _tex_command_calls(
    source: str, command_names: frozenset[str]
) -> list[tuple[str, list[str], int, str | None]]:
    """Find calls to selected commands, including balanced mandatory arguments."""

    if not command_names:
        return []
    alternatives = "|".join(re.escape(name) for name in sorted(command_names))
    pattern = re.compile(r"\\(" + alternatives + r")(?=[^A-Za-z@]|\Z)")
    calls: list[tuple[str, list[str], int, str | None]] = []
    for match in pattern.finditer(source):
        offset = _skip_tex_space(source, match.end())
        option = None
        if offset < len(source) and source[offset] == "[":
            option, offset = _tex_group(source, offset, "[", "]")
            offset = _skip_tex_space(source, offset)
        arguments = []
        while offset < len(source) and source[offset] == "{":
            argument, offset = _tex_group(source, offset, "{", "}")
            arguments.append(argument)
            offset = _skip_tex_space(source, offset)
        calls.append((match.group(1), arguments, match.start(), option))
    return calls


def _tex_declaration_calls(
    source: str, command_name: str
) -> list[TexDeclarationCall]:
    """Read top-level, line-initial calls to a declaration command."""

    pattern = re.compile(
        r"^[ \t]*\\" + re.escape(command_name) + r"(?=\s*\{)",
        re.MULTILINE,
    )
    calls: list[TexDeclarationCall] = []
    for match in pattern.finditer(source):
        offset = _skip_tex_space(source, match.end())
        groups: list[str] = []
        group_offsets: list[int] = []
        while offset < len(source) and source[offset] == "{":
            group_offsets.append(offset + 1)
            group, offset = _tex_group(source, offset, "{", "}")
            groups.append(group)
            offset = _skip_tex_space(source, offset)
        calls.append(
            TexDeclarationCall(
                groups=tuple(groups),
                source_offset=match.start(),
                group_offsets=tuple(group_offsets),
            )
        )
    return calls


def _parse_argument_schema(raw_schema: str, *, location: str) -> tuple[str, ...]:
    """Parse the comma-separated plasTeX argument names in one declaration."""

    if not raw_schema.strip():
        return ()
    arguments = tuple(part.strip() for part in raw_schema.split(","))
    invalid = [
        argument
        for argument in arguments
        if not re.fullmatch(r"[a-z][a-z0-9_]*", argument)
    ]
    duplicates = sorted(
        argument for argument in set(arguments) if arguments.count(argument) > 1
    )
    if invalid or duplicates:
        raise RuntimeError(
            f"Invalid tensor-network argument schema at {location} "
            f"(invalid={invalid}, duplicates={duplicates})."
        )
    return arguments


def _parse_contexts(raw_contexts: str, *, name: str, location: str) -> tuple[str, ...]:
    """Parse and validate comma-separated source contexts."""

    contexts = tuple(part.strip() for part in raw_contexts.split(","))
    if not contexts or any(not context for context in contexts):
        raise RuntimeError(f"{name} has an empty chapter context at {location}.")
    duplicates = sorted(
        context for context in set(contexts) if contexts.count(context) > 1
    )
    if duplicates:
        raise RuntimeError(
            f"{name} repeats chapter contexts at {location}: {duplicates}."
        )
    for context in contexts:
        if not re.fullmatch(r"chapter/[A-Za-z0-9_./-]+\.tex", context):
            raise RuntimeError(
                f"{name} has invalid chapter context {context!r} at {location}."
            )
        path = (_SRC_DIR / context).resolve()
        try:
            path.relative_to((_SRC_DIR / "chapter").resolve())
        except ValueError as error:
            raise RuntimeError(
                f"{name} chapter context escapes blueprint/src/chapter at {location}."
            ) from error
        if not path.is_file():
            raise RuntimeError(
                f"{name} names a missing chapter context {context!r} at {location}."
            )
    return contexts


def _assert_exact_sample_call(
    sample: str, *, name: str, arity: int, location: str
) -> None:
    """Require a complete sample call to the declaration itself."""

    source = sample.strip()
    match = re.match(r"\\" + re.escape(name) + r"(?=[^A-Za-z@]|\Z)", source)
    if match is None:
        raise RuntimeError(
            f"{name} has a sample that is not a call to itself at {location}."
        )
    offset = _skip_tex_space(source, match.end())
    if offset < len(source) and source[offset] == "[":
        raise RuntimeError(f"{name} has an optional sample argument at {location}.")
    arguments = []
    while offset < len(source) and source[offset] == "{":
        argument, offset = _tex_group(source, offset, "{", "}")
        arguments.append(argument)
        offset = _skip_tex_space(source, offset)
    if offset != len(source) or len(arguments) != arity:
        raise RuntimeError(
            f"{name} sample arity is inconsistent at {location} "
            f"(declared={arity}, sample={len(arguments)})."
        )


def _load_diagram_declarations() -> dict[str, DiagramDeclaration]:
    r"""Read and validate every ``\TNDeclareDiagram`` catalogue record."""

    if not _TN_CATALOGUE_FILE.is_file():
        raise RuntimeError(
            "Missing tensor-network declaration catalogue: "
            f"{_TN_CATALOGUE_FILE.relative_to(_REPO_ROOT)}"
        )
    source = _mask_tex_comments(_TN_CATALOGUE_FILE.read_text(encoding="utf-8"))
    calls = _tex_declaration_calls(source, "TNDeclareDiagram")
    if not calls:
        raise RuntimeError("tn_catalogue.tex contains no \\TNDeclareDiagram records.")

    declarations: dict[str, DiagramDeclaration] = {}
    for call in calls:
        groups = call.groups
        offset = call.source_offset
        location = _source_line(_TN_CATALOGUE_FILE, offset)
        if len(groups) != 7:
            raise RuntimeError(
                "\\TNDeclareDiagram requires exactly seven mandatory groups at "
                f"{location} (found {len(groups)})."
            )
        raw_name, raw_schema, raw_role, raw_profile, sample, raw_contexts, body = groups
        name = raw_name.strip()
        role = raw_role.strip()
        profile = raw_profile.strip()
        if not re.fullmatch(r"TN[A-Za-z]+", name):
            raise RuntimeError(f"Invalid diagram name {name!r} at {location}.")
        if name in declarations:
            previous = declarations[name]
            raise RuntimeError(
                f"Duplicate diagram declaration {name} at {location}; first declared "
                f"at tex/tn/tn_catalogue.tex:{previous.source_line}."
            )
        arguments = _parse_argument_schema(raw_schema, location=location)
        if len(arguments) > 9:
            raise RuntimeError(f"{name} exceeds TeX's nine-argument limit at {location}.")
        if role not in {"display", "figure"}:
            raise RuntimeError(f"{name} has invalid role {role!r} at {location}.")
        if profile not in {"compact", "normal"}:
            raise RuntimeError(f"{name} has invalid profile {profile!r} at {location}.")
        contexts = _parse_contexts(
            raw_contexts, name=name, location=location
        )
        _assert_exact_sample_call(
            sample, name=name, arity=len(arguments), location=location
        )
        referenced = _unescaped_parameter_indices(body)
        out_of_range = sorted(index for index in referenced if index > len(arguments))
        ignored = [
            index
            for index in range(1, len(arguments) + 1)
            if index not in referenced
        ]
        if out_of_range:
            raise RuntimeError(
                f"{name} has inconsistent body arguments at {location} "
                f"(ignored={ignored}, out_of_range={out_of_range})."
            )
        declarations[name] = DiagramDeclaration(
            name=name,
            arguments=arguments,
            role=role,
            profile=profile,
            sample=sample.strip(),
            contexts=contexts,
            body=body,
            source_line=int(location.rsplit(":", 1)[1]),
        )
    return declarations


def _parse_atom_ports(
    raw_ports: str, *, name: str, location: str
) -> tuple[AtomPort, ...]:
    """Parse the atom's comma-separated ``Port:kind`` schema."""

    if not raw_ports.strip():
        return ()
    ports: list[AtomPort] = []
    for entry in raw_ports.split(","):
        pieces = [piece.strip() for piece in entry.split(":")]
        if (
            len(pieces) != 2
            or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", pieces[0])
            or pieces[1] not in {"virtual", "physical", "morphism"}
        ):
            raise RuntimeError(
                f"{name} has invalid atom port entry {entry!r} at {location}."
            )
        ports.append(AtomPort(*pieces))
    duplicates = sorted(
        port_name
        for port_name in {port.name for port in ports}
        if sum(port.name == port_name for port in ports) > 1
    )
    if duplicates:
        raise RuntimeError(
            f"{name} repeats atom ports at {location}: {duplicates}."
        )
    return tuple(ports)


def _load_atom_declarations() -> dict[str, AtomDeclaration]:
    r"""Read and validate every ``\TNDeclareAtom`` catalogue record."""

    if not _TN_ATOMS_FILE.is_file():
        raise RuntimeError(
            "Missing tensor-network atom catalogue: "
            f"{_TN_ATOMS_FILE.relative_to(_REPO_ROOT)}"
        )
    source = _mask_tex_comments(_TN_ATOMS_FILE.read_text(encoding="utf-8"))
    calls = _tex_declaration_calls(source, "TNDeclareAtom")
    if not calls:
        raise RuntimeError("tn_atoms.tex contains no \\TNDeclareAtom records.")
    declarations: dict[str, AtomDeclaration] = {}
    for call in calls:
        groups = call.groups
        offset = call.source_offset
        location = _source_line(_TN_ATOMS_FILE, offset)
        if len(groups) != 4:
            raise RuntimeError(
                "\\TNDeclareAtom requires exactly four mandatory groups at "
                f"{location} (found {len(groups)})."
            )
        raw_name, raw_ports, raw_profile, raw_sample = groups
        name = raw_name.strip()
        profile = raw_profile.strip()
        sample = raw_sample.strip()
        if not re.fullmatch(r"TN[A-Z][A-Za-z0-9]*", name):
            raise RuntimeError(f"Invalid atom name {name!r} at {location}.")
        if name in declarations:
            previous = declarations[name]
            raise RuntimeError(
                f"Duplicate atom declaration {name} at {location}; first declared "
                f"at tex/tn/tn_atoms.tex:{previous.source_line}."
            )
        if profile not in {"compact", "normal"}:
            raise RuntimeError(f"{name} has invalid profile {profile!r} at {location}.")
        if not sample:
            raise RuntimeError(
                f"{name} has an empty atom sample at {location}."
            )
        declarations[name] = AtomDeclaration(
            name=name,
            ports=_parse_atom_ports(raw_ports, name=name, location=location),
            profile=profile,
            sample=sample,
            source_line=int(location.rsplit(":", 1)[1]),
        )
    return declarations


_DIAGRAM_CATALOGUE = DiagramCatalogue(
    tuple(_load_diagram_declarations().values())
)
_ATOM_CATALOGUE = AtomCatalogue(tuple(_load_atom_declarations().values()))
_DUPLICATE_PUBLIC_NAMES = sorted(
    set(_DIAGRAM_CATALOGUE.names) & set(_ATOM_CATALOGUE.names)
)
if _DUPLICATE_PUBLIC_NAMES:
    raise RuntimeError(
        "Names occur in both the atom and diagram catalogues: "
        + ", ".join(_DUPLICATE_PUBLIC_NAMES)
    )


def _tex_macro_definitions(source: str) -> list[tuple[str, str, int]]:
    """Return complete macro and diagram bodies with their source offsets."""

    pattern = re.compile(
        r"^\\newcommand\{\\(?P<name>[A-Za-z@]+)\}(?:\[\d+\])?",
        re.MULTILINE,
    )
    definitions = []
    for match in pattern.finditer(source):
        offset = _skip_tex_space(source, match.end())
        if offset >= len(source) or source[offset] != "{":
            continue
        body, body_end = _tex_group(source, offset, "{", "}")
        definitions.append((match.group("name"), body, offset + 1))
        if body_end <= offset:
            raise AssertionError("balanced TeX group did not advance")
    definitions.extend(
        (call.groups[0].strip(), call.groups[6], call.group_offsets[6])
        for call in _tex_declaration_calls(source, "TNDeclareDiagram")
        if len(call.groups) == 7
    )
    return definitions


def _semantic_node_names(body: str) -> set[str]:
    names = set()
    for _, arguments, _, _ in _tex_command_calls(body, _SEMANTIC_GLYPH_COMMANDS):
        if not arguments:
            continue
        name = arguments[0].strip()
        if _SIMPLE_NODE_NAME_PATTERN.fullmatch(name):
            names.add(name)
    return names


def _named_port_debt(path: Path, source: str) -> dict[str, list[dict[str, object]]]:
    """Locate point connectors that bypass the atomic named-port vocabulary."""

    bare_node_connectors: list[dict[str, object]] = []
    for macro_name, body, body_offset in _tex_macro_definitions(source):
        semantic_names = _semantic_node_names(body)
        for command, arguments, call_offset, _ in _tex_command_calls(
            body, _POINT_CONNECTOR_COMMANDS
        ):
            point_arguments = (
                arguments[1:3] if command == "TN@connectpoints" else arguments[:2]
            )
            inexact_nodes = sorted(
                stripped
                for argument in point_arguments
                if (stripped := argument.strip()) in semantic_names
                or stripped in {name + ".center" for name in semantic_names}
            )
            if inexact_nodes:
                bare_node_connectors.append(
                    {
                        "location": _source_line(path, body_offset + call_offset),
                        "macro": macro_name,
                        "command": command,
                        "references": inexact_nodes,
                    }
                )

    return {"bare_node_point_connectors": bare_node_connectors}


def _source_semantic_debt(path: Path, source: str) -> dict[str, object]:
    raw_glyph_locations = {
        name: [_source_line(path, match.start()) for match in pattern.finditer(source)]
        for name, pattern in _RAW_GLYPH_PATTERNS.items()
    }
    direct_draw_locations = [
        _source_line(path, match.start()) for match in _RAW_WIRE_PATTERN.finditer(source)
    ]
    legacy_wire_locations = [
        _source_line(path, match.start())
        for match in _LEGACY_WIRE_COMMAND_PATTERN.finditer(source)
    ]
    port_debt = _named_port_debt(path, source)
    return {
        "raw_glyph_locations": raw_glyph_locations,
        "raw_glyph_count": sum(len(locations) for locations in raw_glyph_locations.values()),
        "direct_tn_draw_locations": direct_draw_locations,
        "legacy_wire_locations": legacy_wire_locations,
        "raw_wire_count": len(direct_draw_locations) + len(legacy_wire_locations),
        **port_debt,
        "named_port_debt_count": sum(len(locations) for locations in port_debt.values()),
    }


def _ignored_diagram_arguments() -> dict[str, list[int]]:
    """Return declared arguments which do not occur in their diagram bodies."""

    ignored: dict[str, list[int]] = {}
    for declaration in diagram_declarations():
        if not declaration.arguments:
            continue
        referenced = _unescaped_parameter_indices(declaration.body)
        missing = [
            index
            for index in range(1, len(declaration.arguments) + 1)
            if index not in referenced
        ]
        if missing:
            ignored[declaration.name] = missing
    return ignored


def _assert_diagram_arguments_used() -> None:
    """Require each declared argument to affect the corresponding diagram."""

    ignored = _ignored_diagram_arguments()
    if ignored:
        raise RuntimeError(
            "Public tensor-network macros ignore declared arguments: "
            + _format_ignored_arguments(ignored)
        )


def _semantic_audit_counts() -> dict[str, object]:
    """Collect migration measures without assigning mathematical meaning to them."""

    catalogue_path = _TN_CATALOGUE_FILE
    core_path = _TN_CORE_FILE
    catalogue_source = catalogue_path.read_text(encoding="utf-8")
    core_source = core_path.read_text(encoding="utf-8")
    library_path = _TN_LIBRARY_FILE
    library_source = (
        library_path.read_text(encoding="utf-8") if library_path.exists() else ""
    )
    private_source = core_source + "\n" + library_source
    public_macros = [
        (declaration.name, len(declaration.arguments), declaration.body)
        for declaration in diagram_declarations()
    ]
    chapter_paths = sorted((_SRC_DIR / "chapter").rglob("*.tex"))
    chapter_sources = [path.read_text(encoding="utf-8") for path in chapter_paths]
    chapter_source = "\n".join(chapter_sources)

    chapter_calls = re.findall(r"\\(TN[A-Z]\w+)", chapter_source)
    ignored_arguments = _ignored_diagram_arguments()
    unused_diagrams = sorted(
        name
        for name, _, _ in public_macros
        if name not in chapter_calls
    )

    audited_sources = {
        "tex/tn/tn_catalogue.tex": _source_semantic_debt(
            catalogue_path, catalogue_source
        ),
        "tex/tn/tn_library.tex": _source_semantic_debt(library_path, library_source),
    }
    raw_glyph_counts = {
        name: sum(
            len(source_debt["raw_glyph_locations"][name])
            for source_debt in audited_sources.values()
        )
        for name in _RAW_GLYPH_PATTERNS
    }
    direct_wire_commands = sum(
        len(source_debt["direct_tn_draw_locations"])
        for source_debt in audited_sources.values()
    )
    legacy_wire_commands = sum(
        len(source_debt["legacy_wire_locations"])
        for source_debt in audited_sources.values()
    )
    named_port_debt = sum(
        int(source_debt["named_port_debt_count"])
        for source_debt in audited_sources.values()
    )
    return {
        "atoms": len(atom_declarations()),
        "diagrams": len(diagram_declarations()),
        "public": len(public_macros),
        "concrete": sum(r"\begin{tikzpicture}" in body for _, _, body in public_macros),
        "zero_argument": sum(arity == 0 for _, arity, _ in public_macros),
        "chapter_files": sum(
            bool(re.search(r"\\TN[A-Z]\w+", source)) for source in chapter_sources
        ),
        "chapter_calls": len(chapter_calls),
        "chapter_commands": len(set(chapter_calls)),
        "private_commands": len(
            re.findall(r"^\\newcommand\{\\TN@\w+\}", private_source, re.MULTILINE)
        ),
        "private_lengths": len(
            re.findall(r"^\\def\\TN@\w+", private_source, re.MULTILINE)
        ),
        "core_styles": len(
            re.findall(r"^\s*tn [^/]+?/\.style", core_source, re.MULTILINE)
        ),
        "literal_coordinates": len(
            _LITERAL_COORDINATE_PATTERN.findall(catalogue_source)
        ),
        "draw_commands": len(re.findall(r"\\draw\b", catalogue_source)),
        "node_commands": len(re.findall(r"\\node\b", catalogue_source)),
        "raw_glyph_counts": raw_glyph_counts,
        "direct_wire_commands": direct_wire_commands,
        "legacy_wire_commands": legacy_wire_commands,
        "raw_wire_commands": direct_wire_commands + legacy_wire_commands,
        "named_port_debt": named_port_debt,
        "audited_sources": audited_sources,
        "noncore_style_locations": _noncore_tikz_style_locations(),
        "ignored_arguments": ignored_arguments,
        "unused_diagrams": unused_diagrams,
        "private_client_calls": _client_pattern_locations(_PRIVATE_COMMAND_PATTERN),
        "raw_client_tikz": _client_pattern_locations(_CLIENT_TIKZ_PATTERN),
        "local_geometry": _client_geometry_locations(),
        "catalogue_private_calls": _catalogue_pattern_locations(
            _PRIVATE_COMMAND_PATTERN
        ),
        "catalogue_raw_tikz": _catalogue_pattern_locations(_CLIENT_TIKZ_PATTERN),
        "catalogue_geometry": _catalogue_geometry_locations(),
    }


def _format_ignored_arguments(ignored: dict[str, list[int]]) -> str:
    return ", ".join(
        f"{name}({','.join(f'#{index}' for index in indices)})"
        for name, indices in sorted(ignored.items())
    )


def _debt_locations(
    audited_sources: dict[str, object], categories: tuple[str, ...]
) -> list[str]:
    locations = []
    for source_debt in audited_sources.values():
        assert isinstance(source_debt, dict)
        for category in categories:
            records = source_debt[category]
            assert isinstance(records, list)
            for record in records:
                if isinstance(record, str):
                    locations.append(record)
                else:
                    assert isinstance(record, dict)
                    locations.append(str(record["location"]))
    return locations


def _raw_glyph_locations(audited_sources: dict[str, object]) -> list[str]:
    locations = []
    for source_debt in audited_sources.values():
        assert isinstance(source_debt, dict)
        by_kind = source_debt["raw_glyph_locations"]
        assert isinstance(by_kind, dict)
        locations.extend(
            location
            for kind_locations in by_kind.values()
            for location in kind_locations
        )
    return locations


def _abbreviate_locations(locations: list[str], limit: int = 16) -> str:
    visible = locations[:limit]
    suffix = f", ... ({len(locations) - limit} more)" if len(locations) > limit else ""
    return ", ".join(visible) + suffix


def _run_semantic_audit(*, strict: bool, machine_readable: bool) -> None:
    """Check stable invariants and report the remaining diagram migration debt."""

    _assert_no_duplicate_diagram_definitions()
    _assert_diagram_templates_are_catalogue_independent()
    _assert_diagram_roles_match_chapters()
    _assert_diagram_arguments_used()
    _assert_audit_commands_defined()
    _assert_no_unused_private_commands()
    _assert_no_chapter_local_tikz()
    _assert_typed_port_syntax()
    _assert_no_raw_glyph_nodes()
    _assert_documented_public_vocabulary()

    counts = _semantic_audit_counts()
    raw_glyph_counts = counts["raw_glyph_counts"]
    assert isinstance(raw_glyph_counts, dict)
    ignored_arguments = counts["ignored_arguments"]
    assert isinstance(ignored_arguments, dict)
    unused_diagrams = counts["unused_diagrams"]
    assert isinstance(unused_diagrams, list)
    noncore_style_locations = counts["noncore_style_locations"]
    assert isinstance(noncore_style_locations, list)
    audited_sources = counts["audited_sources"]
    assert isinstance(audited_sources, dict)
    private_client_calls = counts["private_client_calls"]
    assert isinstance(private_client_calls, list)
    raw_client_tikz = counts["raw_client_tikz"]
    assert isinstance(raw_client_tikz, list)
    local_geometry = counts["local_geometry"]
    assert isinstance(local_geometry, list)
    catalogue_private_calls = counts["catalogue_private_calls"]
    assert isinstance(catalogue_private_calls, list)
    catalogue_raw_tikz = counts["catalogue_raw_tikz"]
    assert isinstance(catalogue_raw_tikz, list)
    catalogue_geometry = counts["catalogue_geometry"]
    assert isinstance(catalogue_geometry, list)

    if machine_readable:
        print(json.dumps(counts, indent=2, sort_keys=True))
    else:
        print(
            "tensor-network semantic audit: "
            f"{counts['atoms']} atoms, {counts['concrete']} concrete diagrams, "
            f"{counts['diagrams']} diagrams, "
            f"{counts['chapter_calls']} calls to {counts['chapter_commands']} commands in "
            f"{counts['chapter_files']} chapter files"
        )
        print(
            "tensor-network private vocabulary: "
            f"{counts['core_styles']} styles, {counts['private_lengths']} lengths, "
            f"{counts['private_commands']} drawing commands"
        )
        print(
            "tensor-network migration measures: "
            f"{counts['zero_argument']} zero-argument public commands, "
            f"{counts['literal_coordinates']} literal coordinate pairs, "
            f"{counts['draw_commands']} draw commands, {counts['node_commands']} node commands"
        )
        print(
            "tensor-network raw aliases: "
            + ", ".join(f"{name}={value}" for name, value in raw_glyph_counts.items())
            + f", direct tn draw commands={counts['direct_wire_commands']}, "
            + f"legacy wire commands={counts['legacy_wire_commands']}"
        )
        for source_name, source_debt in audited_sources.items():
            assert isinstance(source_debt, dict)
            print(
                f"tensor-network structural debt in {source_name}: "
                f"raw glyphs={source_debt['raw_glyph_count']}, "
                f"raw wires={source_debt['raw_wire_count']}, "
                f"named-port violations={source_debt['named_port_debt_count']}"
            )
        if noncore_style_locations:
            print(
                "tensor-network non-core style declarations: "
                + ", ".join(noncore_style_locations)
            )
        print(
            "tensor-network ignored public arguments: "
            + (
                _format_ignored_arguments(ignored_arguments)
                if ignored_arguments
                else "none"
            )
        )
        if unused_diagrams:
            print("tensor-network unused public diagrams: " + ", ".join(unused_diagrams))
        print(
            "tensor-network client implementation debt: "
            f"private calls={len(private_client_calls)}, "
            f"raw TikZ operations={len(raw_client_tikz)}, "
            f"local geometry overrides={len(local_geometry)}"
        )
        print(
            "tensor-network catalogue implementation debt: "
            f"private calls={len(catalogue_private_calls)}, "
            f"raw TikZ operations={len(catalogue_raw_tikz)}, "
            f"local geometry overrides={len(catalogue_geometry)}"
        )

    if strict:
        failures = []
        if noncore_style_locations:
            failures.append(
                "TikZ styles outside tex/tn/tn_core.tex at "
                + _abbreviate_locations(noncore_style_locations)
            )
        raw_glyph_total = sum(raw_glyph_counts.values())
        raw_wire_total = int(counts["raw_wire_commands"])
        if raw_glyph_total or raw_wire_total:
            raw_locations = _raw_glyph_locations(audited_sources) + _debt_locations(
                audited_sources,
                ("direct_tn_draw_locations", "legacy_wire_locations"),
            )
            failures.append(
                "raw glyph aliases or tensor-network draws in tex/tn/tn_catalogue.tex "
                "and tex/tn/tn_library.tex "
                f"(glyphs={raw_glyph_total}, wires={raw_wire_total}) at "
                + _abbreviate_locations(raw_locations)
            )
        named_port_total = int(counts["named_port_debt"])
        if named_port_total:
            port_locations = _debt_locations(
                audited_sources,
                ("bare_node_point_connectors",),
            )
            failures.append(
                "semantic contractions bypass the atomic named-port vocabulary "
                f"({named_port_total} calls) at "
                + _abbreviate_locations(port_locations)
            )
        if ignored_arguments:
            failures.append(
                "public tensor-network macros ignore declared arguments: "
                + _format_ignored_arguments(ignored_arguments)
            )
        if unused_diagrams:
            failures.append(
                "unused theorem diagram commands: " + ", ".join(unused_diagrams)
            )
        if private_client_calls:
            failures.append(
                "private TN@ commands outside tex/tn at "
                + _abbreviate_locations(private_client_calls)
            )
        if raw_client_tikz:
            failures.append(
                "client-side TikZ operations bypass the public calculus at "
                + _abbreviate_locations(raw_client_tikz)
            )
        if local_geometry:
            failures.append(
                "client-side numerical geometry or glyph overrides at "
                + _abbreviate_locations(local_geometry)
            )
        if catalogue_private_calls:
            failures.append(
                "catalogue declarations call private implementation commands at "
                + _abbreviate_locations(catalogue_private_calls)
            )
        if catalogue_raw_tikz:
            failures.append(
                "catalogue declarations contain raw TikZ operations at "
                + _abbreviate_locations(catalogue_raw_tikz)
            )
        if catalogue_geometry:
            failures.append(
                "catalogue declarations contain numerical placement or local "
                "appearance overrides at "
                + _abbreviate_locations(catalogue_geometry)
            )
        if failures:
            raise RuntimeError("Strict tensor-network audit failed: " + "; ".join(failures))


def _read_chapter_with_includes(path: Path, seen: set[Path] | None = None) -> str:
    """Read a chapter file together with all files reached by ``\\input``.

    The PEPS chapter is split across several ``\\input{chapter/...}`` section
    files, so the PEPS-macro usage check must look at the combined text rather
    than the top-level chapter file alone.
    """
    if seen is None:
        seen = set()
    path = path.resolve()
    if path in seen:
        return ""
    seen.add(path)
    include_pattern = re.compile(r"\\input\{([^}]+)\}")
    text = path.read_text(encoding="utf-8")
    parts = [text]
    for include in include_pattern.findall(text):
        include_path = _SRC_DIR / include
        if not include_path.suffix:
            include_path = include_path.with_suffix(".tex")
        if include_path.exists():
            parts.append(_read_chapter_with_includes(include_path, seen))
    return "\n".join(parts)


def _assert_peps_macros_used_in_chapter() -> None:
    intentionally_unused: set[str] = set()
    peps_macros = sorted(
        name for name in _DIAGRAM_CATALOGUE.names if name.startswith("TNPEPS")
    )
    chapter = _read_chapter_with_includes(_SRC_DIR / "chapter/ch24_peps_ft.tex")
    stale_records = sorted(intentionally_unused - set(peps_macros))
    if stale_records:
        raise RuntimeError(
            "Recorded intentionally unused PEPS diagram macros are not public "
            f"declarations in tn_catalogue.tex: {stale_records}"
        )
    unused = [
        name
        for name in peps_macros
        if (
            rf"\{name}" not in chapter
            and name not in intentionally_unused
        )
    ]
    if unused:
        raise RuntimeError(
            "Public PEPS diagram macros must be used in the PEPS chapter or recorded "
            f"as intentionally unused: {unused}"
        )


_assert_no_duplicate_diagram_definitions()


def _tex_call(obj: Command) -> str:
    source = getattr(obj, "source", "").strip()
    if source.startswith(rf"\{obj.macroName}"):
        return source

    args = _DIAGRAM_CATALOGUE.declaration(obj.macroName).arguments
    chunks = [rf"\{obj.macroName}"]
    for name in args:
        chunks.append("{" + stringify_tex_item(obj.attributes.get(name, "")) + "}")
    return "".join(chunks)


def _output_dir(doc: object) -> Path:
    configured = Path(str(doc.config["files"]["directory"]))
    if configured.is_absolute():
        return configured

    working_dir = Path(doc.userdata.get("working-dir", _SRC_DIR))
    return (working_dir / configured).resolve()


def _nearest_output_url(obj: object) -> str | None:
    current = obj
    while current is not None:
        url = getattr(current, "url", None)
        if url:
            return str(url)
        current = getattr(current, "parentNode", None)
    return None


def _svg_src(obj: Command, svg_path: Path, output_dir: Path) -> str:
    output_url = _nearest_output_url(obj)
    if output_url is None:
        return posixpath.join(_SVG_SUBDIR, svg_path.name)

    html_path = Path(output_url)
    if not html_path.is_absolute():
        html_path = output_dir / html_path
    return Path(os.path.relpath(svg_path, start=html_path.parent)).as_posix()


def _hash_tex(tex: str) -> str:
    digest = hashlib.sha256()
    digest.update(_render_source_digest().encode("ascii"))
    digest.update(b"\0")
    digest.update(_latex_document(tex).encode("utf-8"))
    return digest.hexdigest()[:16]


@lru_cache(maxsize=1)
def _render_source_digest() -> str:
    digest = hashlib.sha256()
    for source_file in _RENDER_SOURCE_FILES:
        digest.update(source_file.name.encode("utf-8"))
        digest.update(b"\0")
        digest.update(source_file.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def _latex_document(tex_call: str) -> str:
    return rf"""\documentclass[varwidth,border=2pt]{{standalone}}
\usepackage{{amssymb,amsthm,amsmath,mathtools}}
\usepackage{{tikz}}
% standalone is based on article, which already supplies section and subsection.
% Those counters give the local displayed-theorem numbering. Only chapter is
% absent, so define it before loading macros/common.
\newcounter{{chapter}}
\input{{macros/common}}
\input{{macros/tn_print}}
\begin{{document}}
{tex_call}
\end{{document}}
"""


def _run(cmd: Iterable[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(cmd),
        cwd=cwd,
        env=_tex_env(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=90,
        check=False,
    )


@lru_cache(maxsize=1)
def _tex_env() -> dict[str, str]:
    env = os.environ.copy()
    env["TEXINPUTS"] = (
        str(_TN_SHARED_DIR) + "//:" + env.get("TEXINPUTS", "")
    )
    kpsewhich = shutil.which("kpsewhich")
    if kpsewhich is None:
        return env

    for name in ("TEXMFCNF", "TEXMFROOT"):
        if env.get(name):
            continue
        result = subprocess.run(
            [kpsewhich, f"-var-value={name}"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=10,
            check=False,
        )
        value = result.stdout.strip()
        if result.returncode == 0 and value:
            env[name] = value
    return env


def _engine_command(stem: str) -> tuple[list[str], str] | None:
    dvisvgm = shutil.which("dvisvgm")
    if dvisvgm is None:
        return None

    latex = shutil.which("latex")
    if latex is not None:
        return [
            latex,
            "-interaction=nonstopmode",
            "-halt-on-error",
            "-output-directory",
            str(_CACHE_DIR),
            str(_CACHE_DIR / f"{stem}.tex"),
        ], "dvi"

    xelatex = shutil.which("xelatex")
    if xelatex is not None:
        return [
            xelatex,
            "-no-pdf",
            "-interaction=nonstopmode",
            "-halt-on-error",
            "-output-directory",
            str(_CACHE_DIR),
            str(_CACHE_DIR / f"{stem}.tex"),
        ], "xdv"

    lualatex = shutil.which("lualatex")
    if lualatex is not None:
        return [
            lualatex,
            "-interaction=nonstopmode",
            "-halt-on-error",
            "-output-directory",
            str(_CACHE_DIR),
            str(_CACHE_DIR / f"{stem}.tex"),
        ], "pdf"

    return None


def _dvisvgm_command(stem: str, ext: str, svg_path: Path) -> list[str]:
    input_path = _CACHE_DIR / f"{stem}.{ext}"
    cmd = [
        shutil.which("dvisvgm") or "dvisvgm",
        "--no-fonts",
        "--exact",
        "--bbox=3pt",
        f"--output={svg_path}",
    ]
    if ext == "pdf":
        cmd.append("--pdf")
    cmd.append(str(input_path))
    return cmd


def _missing_tools_html(tex_call: str) -> str:
    return (
        '<span class="tn-svg-missing">'
        "TikZ SVG unavailable: install LaTeX and dvisvgm to render "
        f"<code>{escape(tex_call)}</code>."
        "</span>"
    )


def _compile_svg(tex_call: str, stem: str, svg_path: Path) -> str | None:
    svg_path.parent.mkdir(parents=True, exist_ok=True)
    _CACHE_DIR.mkdir(parents=True, exist_ok=True)
    tex_path = _CACHE_DIR / f"{stem}.tex"
    tex_path.write_text(_latex_document(tex_call), encoding="utf-8")

    engine = _engine_command(stem)
    if engine is None:
        return None

    engine_cmd, ext = engine
    engine_result = _run(engine_cmd, cwd=_SRC_DIR)
    if engine_result.returncode != 0:
        log_path = _CACHE_DIR / f"{stem}.compile.log"
        log_path.write_text(engine_result.stdout, encoding="utf-8")
        raise RuntimeError(f"TikZ compilation failed for {tex_call}; see {log_path}")

    svg_result = _run(_dvisvgm_command(stem, ext, svg_path), cwd=_SRC_DIR)
    if svg_result.returncode != 0:
        log_path = _CACHE_DIR / f"{stem}.dvisvgm.log"
        log_path.write_text(svg_result.stdout, encoding="utf-8")
        raise RuntimeError(f"dvisvgm failed for {tex_call}; see {log_path}")

    tex_path.unlink(missing_ok=True)
    return svg_path.name


def _smoke_render(names: Iterable[str]) -> list[Path]:
    rendered = []
    for name in names:
        if name not in _DIAGRAM_CATALOGUE.names:
            raise ValueError(f"Unknown tensor-network diagram macro: {name}")
        tex_call = _sample_tex_call(name)
        stem = f"tn-smoke-{name}"
        svg_path = _CACHE_DIR / "smoke" / f"{stem}.svg"
        if _compile_svg(tex_call, stem, svg_path) is None:
            raise RuntimeError("TikZ SVG smoke check needs LaTeX and dvisvgm on PATH.")
        rendered.append(svg_path)
    return rendered


def _svg_for(obj: Command, tex_call: str) -> str | None:
    stem = f"tn-{_hash_tex(tex_call)}"
    output_dir = _output_dir(obj.ownerDocument)
    svg_path = output_dir / _SVG_SUBDIR / f"{stem}.svg"
    if not svg_path.exists() and _compile_svg(tex_call, stem, svg_path) is None:
        return None
    return _svg_src(obj, svg_path, output_dir)


class _TensorNetworkDiagramCommand(Command):
    blockType = False
    # plasTeX's renderer reads ``templateName`` as a string attribute of the
    # command; see ``plasTeX.Renderers.Renderer.render``.
    templateName = "TensorNetworkDiagram"

    @property
    def tn_svg_html(self) -> str:
        tex_call = _tex_call(self)
        src = _svg_for(self, tex_call)
        if src is None:
            logged = self.ownerDocument.userdata.setdefault("_tn_svg_missing_tools", False)
            if not logged:
                log.warning("TikZ SVG rendering needs LaTeX and dvisvgm on PATH.")
                self.ownerDocument.userdata["_tn_svg_missing_tools"] = True
            if os.environ.get("CI") == "true":
                raise RuntimeError(
                    f"TikZ SVG rendering needs LaTeX and dvisvgm on PATH for {tex_call}."
                )
            return _missing_tools_html(tex_call)

        role = _DIAGRAM_CATALOGUE.declaration(self.macroName).role
        return (
            f'<img class="tn-svg tn-svg-{role}" '
            f'src="{escape(src, quote=True)}" '
            f'alt="{escape(tex_call, quote=True)}">'
        )


for _declaration in diagram_declarations():
    _macro_name = _declaration.name
    globals()[_macro_name] = type(
        _macro_name,
        (_TensorNetworkDiagramCommand,),
        {"args": _declaration.plastex_args, "macroName": _macro_name},
    )


def _main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check TNLean tensor-network diagram TeX/Python synchronization."
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="check catalogue metadata and reject duplicate diagram definitions",
    )
    parser.add_argument(
        "--check-peps-usage",
        action="store_true",
        help="check that public PEPS diagram macros are used in the PEPS chapter",
    )
    parser.add_argument(
        "--check-slides",
        action="store_true",
        help="check the shared tensor-network calculus under the slide dark theme",
    )
    parser.add_argument(
        "--audit",
        action="store_true",
        help=(
            "enforce stable tensor-network vocabulary invariants and report "
            "remaining migration measures without failing on them"
        ),
    )
    parser.add_argument(
        "--audit-strict",
        action="store_true",
        help=(
            "also reject non-core TikZ styles, raw glyph or wire aliases, and "
            "semantic paths that bypass the atomic named-port vocabulary"
        ),
    )
    parser.add_argument(
        "--audit-json",
        action="store_true",
        help="emit the semantic audit measures as JSON (requires --audit)",
    )
    parser.add_argument(
        "--smoke-render",
        nargs="*",
        metavar="MACRO",
        help=(
            "render sample SVGs for the named public macros; with no names, "
            "render every registered macro"
        ),
    )
    args = parser.parse_args(argv)

    if args.audit_json and not args.audit:
        parser.error("--audit-json requires --audit")
    if args.audit_strict and not args.audit:
        parser.error("--audit-strict requires --audit")

    if (
        not args.check
        and not args.check_peps_usage
        and not args.check_slides
        and not args.audit
        and args.smoke_render is None
    ):
        parser.print_help()
        return 0

    if args.check:
        _assert_no_duplicate_diagram_definitions()
        _assert_diagram_templates_are_catalogue_independent()
        _assert_diagram_roles_match_chapters()
        _assert_diagram_arguments_used()
        _assert_audit_commands_defined()
        _assert_no_unused_private_commands()
        print(
            f"checked {len(diagram_declarations())} tensor-network diagram "
            "declarations"
        )

    if args.check_peps_usage:
        _assert_peps_macros_used_in_chapter()
        print("checked public PEPS diagram usage in the PEPS chapter")

    if args.check_slides:
        _assert_slide_diagram_contract()
        deck_source = "\n".join(
            path.read_text(encoding="utf-8")
            for path in sorted(_SLIDE_DIR.glob("presentation*.tex"))
        )
        slide_calls = len(re.findall(r"\\SlideTN[A-Z]\w*\b", deck_source))
        print(
            f"checked {slide_calls} tensor-network diagrams under the shared "
            "calculus and slide theme"
        )

    if args.audit:
        _run_semantic_audit(
            strict=args.audit_strict,
            machine_readable=args.audit_json,
        )

    if args.smoke_render is not None:
        names = args.smoke_render or list(_DIAGRAM_CATALOGUE.names)
        rendered = _smoke_render(names)
        print(f"rendered {len(rendered)} tensor-network diagram SVGs")

    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
