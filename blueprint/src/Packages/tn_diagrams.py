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
_CACHE_DIR = _SRC_DIR / ".tn_svg_cache"
_SVG_SUBDIR = "tn_svg"
_RENDER_SOURCE_FILES = (
    _SRC_DIR / "macros/common.tex",
    _TN_CORE_FILE,
    _TN_LIBRARY_FILE,
    _SRC_DIR / "macros/tn_print.tex",
)
_TEMPLATE_FILE = _SRC_DIR / "plastex_templates/TensorNetworkDiagrams.jinja2s"
_SLIDE_DIR = _REPO_ROOT / "docs/slides"
_SLIDE_LIBRARY = _SLIDE_DIR / "tn_library_dark.tex"

_EXPECTED_SLIDE_DIAGRAM_CALLS = {
    "SlideTNPeriodicMPS": 7,
    "SlideTNGaugeConjugation": 2,
    "SlideTNBlockingIdentity": 1,
    "SlideTNBlockingComparison": 1,
    "SlideTNMixedTransfer": 1,
    "SlideTNTransferMap": 1,
}

_PUBLIC_MACRO_PATTERN = re.compile(
    r"^\\newcommand\{\\(TN(?!@)\w+)\}(?:\[(\d+)\])?", re.MULTILINE
)
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
        "TN@labeledmposite",
        "TN@labeledmpssite",
        "TN@map",
        "TN@mergemap",
        "TN@mposite",
        "TN@mpssite",
        "TN@operatorstate",
        "TN@pinsertion",
        "TN@pepssite",
        "TN@pepsvertex",
        "TN@scalar",
        "TN@splitmap",
        "TN@state",
        "TN@subspinbox",
        "TN@systemancillamapdown",
        "TN@systemancillamapup",
        "TN@tensor",
        "TN@labeledtensor",
        "TN@labeledinsertion",
        "TN@threeLegTensorFan",
        "TN@vcomponent",
        "TN@vexpression",
        "TN@vfactor",
        "TN@vinsertion",
        "TN@vstate",
    }
)
_GENERAL_WIRE_COMMANDS = frozenset(
    {"TN@ppath", "TN@ptracepath", "TN@vpath", "TN@vtracepath"}
)
_POINT_CONNECTOR_COMMANDS = frozenset(
    {"TN@connectpoints", "TN@pconnectpoints", "TN@vconnectpoints"}
)
_TRACE_PATH_COMMANDS = frozenset({"TN@ptracepath", "TN@vtracepath"})
_OFFSET_ANCHOR_POINT_PATTERN = re.compile(
    r"\(\$\(\s*(?P<reference>[#A-Za-z\\][#A-Za-z0-9@_\\-]*\."
    r"(?:north|south|east|west)(?:\s+(?:east|west))?)\s*\)\s*[+-][^$]*\$\)"
)
_SIMPLE_NODE_NAME_PATTERN = re.compile(r"[#A-Za-z\\][#A-Za-z0-9@_\\-]*\Z")
_SYMBOLIC_PORT_PATTERN = re.compile(r"[#A-Za-z\\][#A-Za-z0-9@_\\-]*\Z")
_CONTROL_WORD_DELIMITER_PATTERN = re.compile(r"(\\[A-Za-z@]+)\s+")
_UNTYPED_PORT_COMMAND_PATTERN = re.compile(
    r"\\TN@(?:port|betweenport|westport|eastport|northport|southport|registerport)\b"
)
_TYPED_PORT_COMMAND_ARITIES = {
    "TN@vconnectports": (2, (0, 1)),
    "TN@vconnectportshv": (2, (0, 1)),
    "TN@vconnectportsvh": (2, (0, 1)),
    "TN@pconnectports": (2, (0, 1)),
    "TN@mconnectports": (2, (0, 1)),
    "TN@mcompareports": (2, (0, 1)),
    "TN@vopenport": (2, (0,)),
    "TN@popenport": (2, (0,)),
    "TN@vtraceportsbelow": (4, (0, 1)),
    "TN@vtraceportsabove": (4, (0, 1)),
    "TN@vtraceportsright": (4, (0, 1)),
    "TN@ptraceportsbelow": (4, (0, 1)),
    "TN@ptraceportsabove": (4, (0, 1)),
    "TN@ptraceportsright": (4, (0, 1)),
}


_DIAGRAM_ARGS: dict[str, str] = {
    "TNTikZDiagram": "rendered body",
    "TNMPSLocal": "tensor label",
    "TNMPSWord": "tensor left right length",
    "TNMPV": "tensor left right length",
    "TNBlocking": "tensor left right length",
    "TNMPVOverlap": "left right length",
    "TNTransferMap": "tensor",
    "TNMPOCell": "tensor top bottom",
    "TNMPOChain": "tensor top_left bottom_left top_right bottom_right length",
    "TNMPOLocalPurification": "",
    "TNMPORenormalizationTS": "",
    "TNEtaSectorDecomposition": "",
    "TNMPDOTwoSiteTraceAndShift": "",
    "TNMPDOThreeSiteTraceAndShift": "",
    "TNMPDORefinementConstruction": "",
    "TNMPDORefinementDirection": "",
    "TNMPDOBlockedRFPChannels": "",
    "TNMPDOPhysicalIsometryTransport": "",
    "TNMPDOTwoSiteClosureFactorization": "",
    "TNMPDOThreeSiteClosureFactorization": "",
    "TNMPDOFixedSectorAdjacentCommutativity": "",
    "TNMPDOCyclicEtaContraction": "",
    "TNMPDOSectorAdaptedDecomposition": "",
    "TNMPDOInverseMapThreeSiteContraction": "",
    "TNMPDOHorizontalOperator": "",
    "TNMPDOFirstSiteContractions": "",
    "TNMPDOVerticalDirectSum": "",
    "TNMPDOVerticalReducingSectors": "",
    "TNMPDOVerticalGaugeGramComparison": "",
    "TNMPDOInverseContraction": "",
    "TNMPDOSectorPairing": "",
    "TNMPDOSectorZCLIdentity": "",
    "TNMPDONormalizedFourSiteTail": "",
    "TNMPDOHayashiSectorComparison": "",
    "TNMPDOSectorFactorization": "",
    "TNMPDOLocalOrthogonality": "",
    "TNMPSInverseContraction": "",
    "TNBNTDecomposition": "",
    "TNMPDOZCLIdempotence": "",
    "TNMPDOFixedFinalFusionBracketings": "",
    "TNMPDOFixedFinalComparisonUnitary": "",
    "TNMPDOFourfoldBondReassociationPentagon": "",
    "TNMPDOCompleteZipperFusionPentagon": "",
    "TNMPDOPrintedFMove": "",
    "TNMPDOBNTFusionIdentity": "",
    "TNMPDOUnweightedZipperReconstruction": "",
    "TNMPDOFusionTracePower": "",
    "TNMPDORecursiveStructureOperator": "",
    "TNAppendixBAdjacentBondProjectors": "",
    "TNAppendixBPhysicalSupportTransport": "",
    "TNAppendixBChainTransport": "",
    "TNRFPKrausIsometry": "",
    "TNRFPKrausIsometryReverse": "",
    "TNRFPIsometryCanonicalForm": "",
    "TNRFPIsometryCanonicalFormBlocks": "",
    "TNMPDOTwoSiteBlocking": "",
    "TNMPDOBNTVerticalProduct": "",
    "TNMPDOBlockClosureMap": "",
    "TNMPDOBNTOperatorTraceClosure": "",
    "TNMPDOFirstSiteInsertionHypothesis": "",
    "TNMPDOFirstSiteInsertionBlockwise": "",
    "TNMPDOInsertionTracePairing": "",
    "TNMPDOHorizontalCanonicalForm": "",
    "TNMPDOBlockInjectiveInverse": "",
    "TNMPDOInverseRecovery": "",
    "TNMPDOProjectorAbsorption": "",
    "TNGaugeConjugation": "left physical right",
    "TNPhysicalRealization": "virtual physical",
    "TNLinearTwist": "twist label",
    "TNPermutationTwistLabeled": "left right permutation",
    "TNPermutationTwist": "left right",
    "TNTwistedTransfer": "twist",
    "TNCondCOne": "twist virtual label",
    "TNCondCTwo": "virtual",
    "TNStringOrderParameter": "twist length",
    "TNInternalTraceInsertion": "left right virtual",
    "TNExternalTraceInsertion": "left right virtual",
    "TNBoundaryRegrow": "virtual left right length",
    "TNLocalEqualityStep": "left_virtual right_virtual physical",
    "TNGroundSpaceMap": "tensor left right length virtual",
    "TNPEPSEdgeBlockingReduction": "",
    "TNPEPSEdgeInsertedCoeff": "",
    "TNPEPSThreeSiteInsertionComparison": "",
    "TNPEPSInsertionPhysicalRealization": "",
    "TNPEPSPhysicalToVirtualInsertion": "",
    "TNPEPSEdgeInsertionEquality": "",
    "TNPEPSEdgeGaugeAbsorption": "",
    "TNPEPSTwoInjectiveTensorInsertionComparison": "",
    "TNPEPSTwoInjectiveGaugeScalarReduction": "",
    "TNPEPSOneVertexComplementComparison": "",
    "TNPEPSInjectiveRegionUnion": "",
    "TNPEPSInjectiveRegionUnionProof": "",
    "TNPEPSNormalRegionsRS": "",
    "TNPEPSNormalRegionT": "",
    "TNPEPSNormalRectangleCover": "",
    "TNPEPSNormalEdgeComplementTopCollar": "",
    "TNPEPSNormalOneSiteSeparation": "",
    "TNPEPSNormalEdgeBlockingReduction": "",
    "TNPEPSNormalEdgeBlockingHypotheses": "",
    "TNPEPSNormalBlockingHypotheses": "",
    "TNPEPSTINormalGaugeAbsorption": "",
    "TNPEPSEdgeGaugeOrientation": "",
    "TNPEPSGaugeVertexAction": "",
    "TNPEPSGaugeCancellation": "",
    "TNPEPSBlockedMiddleLocalGaugeFormula": "",
    "TNPEPSLocalGaugeExtraction": "",
    "TNPEPSGlobalConsistency": "",
    "TNPEPSLatticeState": "",
    "TNPEPSLocalTensorStar": "",
    "TNPEPSVertexInjectivityMap": "",
    "TNPEPSStateContraction": "",
    "TNPEPSTorusGeometry": "",
    "TNPEPSVertexScalarBalance": "",
    "TNKrausMap": "",
    "TNStinespring": "",
    "TNChoiMatrix": "",
    "TNTransferMapTracePairing": "",
    "TNTwoPointCorrelator": "",
}


def _diagram_arity(args: str) -> int:
    return len(args.split())


def _sample_arg_value(name: str) -> str:
    values = {
        "tensor": "A",
        "label": "i",
        "left": "i",
        "middle": "j",
        "right": "k",
        "length": "L",
        "top": "i",
        "bottom": "j",
        "top_left": "i_1",
        "bottom_left": "j_1",
        "top_right": "i_N",
        "bottom_right": "j_N",
        "physical": "i",
        "virtual": "X",
        "twist": "u",
        "permutation": "\\sigma",
        "left_virtual": "X",
        "right_virtual": "Y",
        "rendered": "\\TNPEPSNormalRegionT",
        "body": "\\TNMPSLocal{A}{i}",
    }
    return values.get(name, "x")


def _sample_tex_call(name: str) -> str:
    args = _DIAGRAM_ARGS[name].split()
    return rf"\{name}" + "".join("{" + _sample_arg_value(arg) + "}" for arg in args)


def _assert_diagram_args_match_print_macros() -> None:
    pattern = re.compile(r"\\newcommand\{\\(TN(?!@)\w+)\}(?:\[(\d+)\])?")
    source = (_SRC_DIR / "macros/tn_print.tex").read_text(encoding="utf-8")
    print_arities = {
        name: int(arity) if arity else 0
        for name, arity in pattern.findall(source)
    }
    expected_arities = {
        name: _diagram_arity(args)
        for name, args in _DIAGRAM_ARGS.items()
    }
    if print_arities != expected_arities:
        missing = sorted(set(print_arities) - set(expected_arities))
        stale = sorted(set(expected_arities) - set(print_arities))
        mismatched = sorted(
            name
            for name in set(print_arities) & set(expected_arities)
            if print_arities[name] != expected_arities[name]
        )
        raise RuntimeError(
            "Tensor-network diagram arities are out of sync with macros/tn_print.tex "
            f"(missing={missing}, stale={stale}, mismatched={mismatched})."
        )


def _assert_diagram_templates_cover_registered_macros() -> None:
    pattern = re.compile(r"^name:\s+(.+)$", re.MULTILINE)
    template = _TEMPLATE_FILE.read_text(encoding="utf-8")
    rendered_names = {
        name
        for line in pattern.findall(template)
        for name in line.split()
    }
    registered_names = set(_DIAGRAM_ARGS)
    missing = sorted(registered_names - rendered_names)
    stale = sorted(rendered_names - registered_names)
    if missing or stale:
        raise RuntimeError(
            "Tensor-network diagram HTML templates are out of sync with "
            f"registered macros (missing={missing}, stale={stale})."
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
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and characters[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2:
            index += 1
            continue
        cursor = index
        while cursor < len(characters) and characters[cursor] != "\n":
            characters[cursor] = " "
            cursor += 1
        index = cursor
    return "".join(characters)


def _pattern_locations(path: Path, pattern: re.Pattern[str]) -> list[str]:
    text = _mask_tex_comments(path.read_text(encoding="utf-8"))
    return [_source_line(path, match.start()) for match in pattern.finditer(text)]


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


def _assert_typed_port_syntax() -> None:
    """Require typed compositions to use symbolic ports and typed constructors."""

    sources = (_SRC_DIR / "macros/tn_print.tex", _TN_LIBRARY_FILE, _SLIDE_LIBRARY)
    command_names = frozenset(_TYPED_PORT_COMMAND_ARITIES)
    malformed: list[str] = []
    untyped: list[str] = []
    forbidden_options = re.compile(
        r"(?:^|,)\s*(?:<?-+>?|dashed|densely dashed|tn (?:grouping|factor) region|"
        r"tn (?:morphism|comparison) arrow)\s*(?:,|$)"
    )
    for path in sources:
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
    for path in (_SRC_DIR / "macros/tn_print.tex", _TN_LIBRARY_FILE, _SLIDE_LIBRARY):
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
    if counts != _EXPECTED_SLIDE_DIAGRAM_CALLS:
        raise RuntimeError(
            "Slide tensor-network diagram calls differ from the audited collection "
            f"(actual={counts}, expected={_EXPECTED_SLIDE_DIAGRAM_CALLS})."
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
    required_shared_inputs = (
        r"\input{../../tex/tn/tn_core}",
        r"\input{../../tex/tn/tn_library}",
    )
    missing_inputs = [
        path for path in required_shared_inputs if path not in library_source
    ]
    if missing_inputs:
        raise RuntimeError(
            "The slide tensor-network theme must load the universal core and "
            "library: " + ", ".join(missing_inputs)
        )

    core_source = _TN_CORE_FILE.read_text(encoding="utf-8")
    core_theme_keys = set(
        re.findall(r"^\s*(tn theme [^/]+?)/\.style", core_source, re.MULTILINE)
    )
    slide_tn_style_keys = set(
        re.findall(r"^\s*(tn [^/]+?)/\.style", library_source, re.MULTILINE)
    )
    invalid_theme_keys = sorted(slide_tn_style_keys - core_theme_keys)
    if invalid_theme_keys:
        raise RuntimeError(
            "The slide theme may replace only declared tn theme slots: "
            + ", ".join(invalid_theme_keys)
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

    raw_slide_draw = re.compile(
        r"^[ \t]*\\(?:draw|path|coordinate|fill|filldraw|shade|shadedraw)\b",
        re.MULTILINE,
    )
    if raw_slide_draw.search(library_source):
        raise RuntimeError(
            "Complete slide tensor networks must compose universal TN commands, "
            "not contain raw TikZ paths or coordinates."
        )

    dashed_contraction = re.compile(
        r"\\TN@(?:v|p)(?:connect|open|trace)[A-Za-z@]*"
        r"(?:\[[^\]]*(?:dashed|densely dashed)[^\]]*\])"
    )
    if dashed_contraction.search(library_source):
        raise RuntimeError(
            "A slide contraction or trace is dashed; dashed strokes are reserved "
            "for grouping regions."
        )

    macro_pattern = re.compile(
        r"^\\newcommand\{\\(SlideTN[A-Z]\w*)\}\[(\d+)\]", re.MULTILINE
    )
    matches = list(macro_pattern.finditer(library_source))
    ignored: dict[str, list[int]] = {}
    for index, match in enumerate(matches):
        body_end = matches[index + 1].start() if index + 1 < len(matches) else len(
            library_source
        )
        body = library_source[match.end() : body_end]
        arity = int(match.group(2))
        missing = [argument for argument in range(1, arity + 1) if f"#{argument}" not in body]
        if missing:
            ignored[match.group(1)] = missing
    if ignored:
        raise RuntimeError(f"Slide tensor-network macros ignore arguments: {ignored}")


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


def _public_macro_bodies(source: str) -> list[tuple[str, int, str]]:
    matches = list(_PUBLIC_MACRO_PATTERN.finditer(source))
    return [
        (
            match.group(1),
            int(match.group(2) or 0),
            source[match.end() : matches[index + 1].start()]
            if index + 1 < len(matches)
            else source[match.end() :],
        )
        for index, match in enumerate(matches)
    ]


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
        escaped = index > 0 and source[index - 1] == "\\"
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


def _tex_macro_definitions(source: str) -> list[tuple[str, str, int]]:
    """Return complete ``newcommand`` bodies with their source offsets."""

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
    """Locate semantic wires that bypass the atomic named-port vocabulary.

    Coordinate-only lattice edges and region boundaries remain legitimate
    geometric paths.  Explicit anchors such as ``object.east`` and
    ``object.30`` are exact boundary ports and remain valid for curved or
    multi-segment contractions.  Debt consists of bare semantic nodes and of
    endpoints obtained by shifting an anchor, endpoints at an object centre,
    and traces whose endpoints are only numerical coordinates.  The same
    exact-attachment condition applies to point connectors.
    """

    inexact_path_endpoints: list[dict[str, object]] = []
    bare_node_connectors: list[dict[str, object]] = []
    for macro_name, body, body_offset in _tex_macro_definitions(source):
        semantic_names = _semantic_node_names(body)
        for command, arguments, call_offset, option in _tex_command_calls(
            body, _GENERAL_WIRE_COMMANDS
        ):
            if not arguments:
                continue
            if option and re.search(r"\btn (?:factor|grouping) region\b", option):
                continue
            path_body = arguments[0]
            references = {
                name
                for name in semantic_names
                if re.search(r"\(\s*" + re.escape(name) + r"\s*\)", path_body)
            }
            stripped_path = path_body.strip().removesuffix(";").rstrip()
            references.update(
                match.group("reference") + " (offset)"
                for match in _OFFSET_ANCHOR_POINT_PATTERN.finditer(stripped_path)
                if match.start() == 0 or match.end() == len(stripped_path)
            )
            references.update(
                name + ".center"
                for name in semantic_names
                for match in re.finditer(
                    r"\(\s*" + re.escape(name) + r"\.center\s*\)", stripped_path
                )
                if match.start() == 0 or match.end() == len(stripped_path)
            )
            if command in _TRACE_PATH_COMMANDS and not re.search(
                r"\(\s*(?:\$\([^)]*\)\s*)?[#A-Za-z\\]", stripped_path
            ):
                references.add("coordinate-only trace")
            if references:
                inexact_path_endpoints.append(
                    {
                        "location": _source_line(path, body_offset + call_offset),
                        "macro": macro_name,
                        "command": command,
                        "references": sorted(references),
                    }
                )

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

    return {
        "inexact_path_endpoints": inexact_path_endpoints,
        "bare_node_point_connectors": bare_node_connectors,
    }


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


def _semantic_audit_counts() -> dict[str, object]:
    """Collect migration measures without assigning mathematical meaning to them."""

    print_path = _SRC_DIR / "macros/tn_print.tex"
    core_path = _TN_CORE_FILE
    print_source = print_path.read_text(encoding="utf-8")
    core_source = core_path.read_text(encoding="utf-8")
    library_path = _TN_LIBRARY_FILE
    library_source = (
        library_path.read_text(encoding="utf-8") if library_path.exists() else ""
    )
    private_source = core_source + "\n" + library_source
    public_macros = _public_macro_bodies(print_source)
    chapter_paths = sorted((_SRC_DIR / "chapter").rglob("*.tex"))
    chapter_sources = [path.read_text(encoding="utf-8") for path in chapter_paths]
    chapter_source = "\n".join(chapter_sources)

    chapter_calls = re.findall(r"\\(TN[A-Z]\w+)", chapter_source)
    ignored_arguments = {
        name: [index for index in range(1, arity + 1) if f"#{index}" not in body]
        for name, arity, body in public_macros
        if arity > 0 and name != "TNTikZDiagram"
    }
    ignored_arguments = {
        name: indices for name, indices in ignored_arguments.items() if indices
    }
    unused_diagrams = sorted(
        name
        for name, _, _ in public_macros
        if name != "TNTikZDiagram" and name not in chapter_calls
    )

    audited_sources = {
        "macros/tn_print.tex": _source_semantic_debt(print_path, print_source),
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
        "registered": len(_DIAGRAM_ARGS),
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
        "literal_coordinates": len(_LITERAL_COORDINATE_PATTERN.findall(print_source)),
        "draw_commands": len(re.findall(r"\\draw\b", print_source)),
        "node_commands": len(re.findall(r"\\node\b", print_source)),
        "raw_glyph_counts": raw_glyph_counts,
        "direct_wire_commands": direct_wire_commands,
        "legacy_wire_commands": legacy_wire_commands,
        "raw_wire_commands": direct_wire_commands + legacy_wire_commands,
        "named_port_debt": named_port_debt,
        "audited_sources": audited_sources,
        "noncore_style_locations": _noncore_tikz_style_locations(),
        "ignored_arguments": ignored_arguments,
        "unused_diagrams": unused_diagrams,
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

    _assert_diagram_args_match_print_macros()
    _assert_diagram_templates_cover_registered_macros()
    _assert_no_chapter_local_tikz()
    _assert_typed_port_syntax()
    _assert_no_raw_glyph_nodes()

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

    if machine_readable:
        print(json.dumps(counts, indent=2, sort_keys=True))
    else:
        print(
            "tensor-network semantic audit: "
            f"{counts['concrete']} concrete diagrams, {counts['registered']} registrations, "
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
                "raw glyph aliases or tensor-network draws in macros/tn_print.tex "
                "and tex/tn/tn_library.tex "
                f"(glyphs={raw_glyph_total}, wires={raw_wire_total}) at "
                + _abbreviate_locations(raw_locations)
            )
        named_port_total = int(counts["named_port_debt"])
        if named_port_total:
            port_locations = _debt_locations(
                audited_sources,
                ("inexact_path_endpoints", "bare_node_point_connectors"),
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
    pattern = re.compile(r"\\newcommand\{\\(TNPEPS\w+)\}(?:\[\d+\])?")
    source = (_SRC_DIR / "macros/tn_print.tex").read_text(encoding="utf-8")
    peps_macros = sorted(set(pattern.findall(source)))
    chapter = _read_chapter_with_includes(_SRC_DIR / "chapter/ch24_peps_ft.tex")
    stale_records = sorted(intentionally_unused - set(peps_macros))
    if stale_records:
        raise RuntimeError(
            "Recorded intentionally unused PEPS diagram macros are not public "
            f"macros in tn_print.tex: {stale_records}"
        )
    unused = [
        name
        for name in peps_macros
        if (
            rf"\{name}" not in chapter
            and rf"\TNTikZDiagram{{{name}}}" not in chapter
            and name not in intentionally_unused
        )
    ]
    if unused:
        raise RuntimeError(
            "Public PEPS diagram macros must be used in the PEPS chapter or recorded "
            f"as intentionally unused: {unused}"
        )


_assert_diagram_args_match_print_macros()


def _tex_call(obj: Command) -> str:
    if obj.macroName == "TNTikZDiagram":
        rendered = stringify_tex_item(obj.attributes.get("rendered", "")).strip()
        if rendered:
            if rendered.startswith("\\"):
                return rendered
            return "\\" + rendered

    source = getattr(obj, "source", "").strip()
    if source.startswith(rf"\{obj.macroName}"):
        return source

    args = _DIAGRAM_ARGS[obj.macroName].split()
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
    digest.update(tex.encode("utf-8"))
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
    return rf"""\documentclass[tikz,border=2pt]{{standalone}}
\usepackage{{amssymb,amsthm,amsmath,mathtools}}
\usepackage{{tikz}}
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
        if name not in _DIAGRAM_ARGS:
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


class _TNTikZDiagram(Command):
    blockType = False

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

        return (
            '<img class="tn-svg" '
            f'src="{escape(src, quote=True)}" '
            f'alt="{escape(tex_call, quote=True)}">'
        )


for _macro_name, _args in _DIAGRAM_ARGS.items():
    globals()[_macro_name] = type(
        _macro_name,
        (_TNTikZDiagram,),
        {"args": _args, "macroName": _macro_name},
    )


def _main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check TNLean tensor-network diagram TeX/Python synchronization."
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="check that Python arities match public TeX macros",
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
        _assert_diagram_args_match_print_macros()
        _assert_diagram_templates_cover_registered_macros()
        print(f"checked {len(_DIAGRAM_ARGS)} tensor-network diagram registrations")

    if args.check_peps_usage:
        _assert_peps_macros_used_in_chapter()
        print("checked public PEPS diagram usage in the PEPS chapter")

    if args.check_slides:
        _assert_slide_diagram_contract()
        slide_calls = sum(_EXPECTED_SLIDE_DIAGRAM_CALLS.values())
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
        names = args.smoke_render or list(_DIAGRAM_ARGS)
        rendered = _smoke_render(names)
        print(f"rendered {len(rendered)} tensor-network diagram SVGs")

    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
