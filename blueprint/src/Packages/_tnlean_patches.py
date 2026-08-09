r"""TNLean-specific plasTeX monkey patches.

This module is loaded from ``web.tex`` as ``\usepackage{_tnlean_patches}``.
Because plasTeX searches ``packages-dirs=Packages`` before its built-in/plugin
package implementations, this single helper can monkey-patch the exact
upstream methods that TNLean still needs without shadowing the full ``natbib``,
``blueprint``, or ``depgraph`` modules.

The remaining local fixes are:

* ``plasTeX.Packages.natbib.bibliography.loadBibliographyFile``:
  skip the spurious missing-``web.aux`` warning during HTML builds, while also
  re-exposing natbib's ``bibitem`` as a module-level macro on *this* patches
  module so ``\bibitem`` is registered in the global plasTeX context.  When
  ``\usepackage{_tnlean_patches}`` is processed, plasTeX scans
  ``vars(package_module)`` for classes with a ``macroName`` attribute and
  installs them on the document context; assigning ``bibitem`` onto the
  already-imported ``plasTeX.Packages.natbib`` module would be a no-op because
  that scan has already run.
* ``leanblueprint.Packages.blueprint.lean.digest``:
  coerce plasTeX list items to plain strings, merge multiple ``\lean`` tags on
  one parent node, and deduplicate ``lean_decls`` output.
* ``plastexdepgraph.Packages.depgraph.{uses, alsoIn, proves}.digest``:
  normalize label tokens and defer/fallback label resolution so ``\uses``,
  ``\alsoIn``, and ``\proves`` survive plasTeX timing quirks.
* ``plasTeX.Base.LaTeX.Crossref.{label, ref, pageref}`` and
  ``plasTeX.Packages.amsmath.eqref``: read the key of a cross-reference with
  the underscore, superscript, alignment, and dollar characters demoted to
  ordinary characters, so a key written inside a display survives.  ``\path``
  reads its argument the same way, over a wider set of characters.
* ``plasTeX.Base.LaTeX.Arrays.Array.EndRow``: a bracketed expression opening
  the row after a line break is mathematics, not a line-spacing length.
* ``plasTeX.Base.LaTeX.Arrays.Array.ArrayRow``: a row with no table around it
  -- a line break inside a braced argument, taken for a row break -- prints
  the entries it holds and no environment around them.

It also declares the constructions the web document meets but neither plasTeX
nor its packages define: ``\path`` from ``url``, the small matrices with
delimiters of ``mathtools``, the ``samepage`` grouping, and the inert
tensor-network surface selector ``\tenkzkernel``.
"""

from __future__ import annotations

import io
import os
import pickle
from pathlib import Path
from typing import Any, Callable

from _tnlean_utils import CONTROL_WORD as _CONTROL_WORD
from _tnlean_utils import ROW_BREAK_LENGTH as _ROW_BREAK_LENGTH
from _tnlean_utils import stringify_tex_item as _stringify_tex_item
from leanblueprint.Packages import blueprint as _blueprint
import plasTeX.Packages.amsmath as _amsmath
import plasTeX.Packages.natbib as _natbib
from plasTeX import Base, Command, DimenCommand, Environment, Token
from plasTeX import sourceChildren as _source_children
from plasTeX.Base.LaTeX import Crossref as _crossref
from plasTeX.Base.LaTeX.Arrays import Array as _Array
from plastexdepgraph.Packages import depgraph as _depgraph


_HISTORICAL_DECL_REPLACEMENTS = {
    # These names were observed in #398 with underscores stripped by a
    # plasTeX parsing corner case. The generic string coercion below avoids the
    # common failure mode; this mapping is kept as a narrow last-resort guard.
    "MPSTensor.exponentialconvergenceofprimitive":
        "MPSTensor.exponential_convergence_of_primitive",
}


# --- natbib patch ---------------------------------------------------------


def _patched_load_bibliography_file(self, tex):
    doc = self.ownerDocument
    doc.userdata.setPath("bibliography/bibcites", {})

    working_dir = Path(doc.userdata.get("working-dir", "."))
    jobname = doc.userdata.get("jobname", getattr(tex, "jobname", "web"))
    aux_path = working_dir / f"{jobname}.aux"
    if aux_path.exists():
        self.ownerDocument.context.push(self)
        self.ownerDocument.context["setcounter"] = self.setcounter
        tex.loadAuxiliaryFile()
        self.ownerDocument.context.pop(self)

    Base.bibliography.loadBibliographyFile(self, tex)


_natbib.bibliography.loadBibliographyFile = _patched_load_bibliography_file

# Re-expose natbib's nested ``thebibliography.bibitem`` class at module level
# so plasTeX's ``loadPythonPackage`` hook (which imports macros via
# ``importMacros(vars(imported))``) registers ``\bibitem`` in the global
# document context when this patches package is loaded. Assigning onto
# ``_natbib`` directly is ineffective because plasTeX has already scanned
# ``natbib`` by the time this file executes.
bibitem = _natbib.thebibliography.bibitem


def _fallback_citation(self, *, parenthetical: bool, include_prenote: bool):
    """Render unresolved natbib citations without producing bare ``()``.

    The ordering mirrors the corresponding natbib citation shape for the
    citation forms used here: natbib's prenote object, citation text, and
    natbib's postnote object. The note objects already include their configured
    spacing and separator.
    """

    keys = [_stringify_tex_item(key) for key in self.attributes.get("bibkeys", [])]
    if os.environ.get("TNLEAN_FAIL_ON_CITATION_FALLBACK"):
        raise RuntimeError(f"unexpected unresolved natbib citation fallback: {keys}")

    res = self.ownerDocument.createDocumentFragment()
    punctuation = getattr(self, "punctuation", {}) or {}
    citesep = punctuation.get("citesep", punctuation.get("sep", ", "))
    text = citesep.join(keys) if keys else "unresolved citation"

    if parenthetical:
        res.append(punctuation.get("open", "("))
    if include_prenote:
        res.append(self.prenote)
    res.append(text)
    res.append(self.postnote)
    if parenthetical:
        res.append(punctuation.get("close", ")"))
    return res


def _cite_uses_parenthetical_fallback(self) -> bool:
    return bool(self.prenote or self.postnote)


def _has_unresolved_bibitems(self) -> bool:
    bibitems = self.bibitems
    if not bibitems:
        return True
    if self.isNumeric():
        return any(getattr(item, "bibcite", None) is None for item in bibitems)
    return any(
        getattr(item, "bibcite", None) is None
        or getattr(item.bibcite, "attributes", None) is None
        for item in bibitems
    )


def _wrap_natbib_citation(
    cls, *, parenthetical: bool | Callable[[Any], bool], include_prenote: bool = True
) -> None:
    original = cls.citation

    def citation(self, *args, **kwargs):
        if _has_unresolved_bibitems(self):
            use_parentheses = (
                parenthetical(self) if callable(parenthetical) else parenthetical
            )
            return _fallback_citation(
                self,
                parenthetical=use_parentheses,
                include_prenote=include_prenote,
            )
        return original(self, *args, **kwargs)

    cls.citation = citation


# Capitalized, ``*full``, and alias variants delegate to these patched
# ``citation`` methods.
for _cls, _parenthetical, _include_prenote in (
    (_natbib.cite, _cite_uses_parenthetical_fallback, True),
    (_natbib.citep, True, True),
    (_natbib.citet, False, True),
    (_natbib.citealt, False, True),
    (_natbib.citealp, False, True),
    (_natbib.citeauthor, False, False),
    (_natbib.citeyear, False, False),
    (_natbib.citeyearpar, True, True),
):
    _wrap_natbib_citation(
        _cls, parenthetical=_parenthetical, include_prenote=_include_prenote
    )


# --- leanblueprint patch --------------------------------------------------


def _normalize_decl(self, obj: Any) -> str:
    decl = _stringify_tex_item(obj)
    normalized = _HISTORICAL_DECL_REPLACEMENTS.get(decl, decl)
    if normalized != decl:
        logged = self.ownerDocument.userdata.setdefault(
            "_tnlean_logged_decl_replacements", set()
        )
        if (decl, normalized) not in logged:
            _blueprint.log.warning(
                "Normalizing mangled \\lean declaration %r to %r.",
                decl,
                normalized,
            )
            logged.add((decl, normalized))
    return normalized



def _patched_lean_digest(self, tokens):
    Command.digest(self, tokens)

    raw_decls = self.attributes.get("decls", [])
    decls = []
    for raw_decl in raw_decls:
        decl = _normalize_decl(self, raw_decl)
        if decl and decl not in decls:
            decls.append(decl)

    existing = list(self.parentNode.userdata.get("leandecls", []))
    for decl in decls:
        if decl not in existing:
            existing.append(decl)
    self.parentNode.setUserData("leandecls", existing)

    all_decls = self.ownerDocument.userdata.setdefault("lean_decls", [])
    for decl in decls:
        if decl not in all_decls:
            all_decls.append(decl)


_blueprint.lean.digest = _patched_lean_digest


# --- plastexdepgraph patch ------------------------------------------------


def _normalize_label(obj: Any) -> str:
    return _stringify_tex_item(obj)



def _find_label_node(node, label: str):
    node_id = getattr(node, "id", None)
    if node_id == label:
        return node

    attrs = getattr(node, "attributes", None)
    if attrs:
        for key in ("id", "label"):
            if attrs.get(key) == label:
                return node

    for child in getattr(node, "childNodes", []):
        found = _find_label_node(child, label)
        if found is not None:
            return found

    return None



def _lookup_label(labels_dict, label: str):
    target = labels_dict.get(label)
    if target is not None:
        return target

    for raw_key, candidate in labels_dict.items():
        if _normalize_label(raw_key) == label:
            return candidate

        candidate_id = getattr(candidate, "id", None)
        if candidate_id is not None and _normalize_label(candidate_id) == label:
            return candidate

        attrs = getattr(candidate, "attributes", None)
        if attrs:
            for key in ("id", "label"):
                value = attrs.get(key)
                if value is not None and _normalize_label(value) == label:
                    return candidate

    return None


class _LabelProxy:
    def __init__(self, *, label: str, url: str, caption: str, ref: str, title: str, userdata: dict):
        self.id = label
        self.url = url
        self.caption = caption
        self.ref = ref
        self.title = title
        self.userdata = userdata
        self.parentNode = None

    def __hash__(self):
        return hash((self.id, self.url))

    def __eq__(self, other):
        return isinstance(other, _LabelProxy) and (self.id, self.url) == (other.id, other.url)



# Class allowlist for deserializing plasTeX ``.paux`` files.  plasTeX's
# ``Context.persist`` / ``Node.persist`` writes a dict-of-dicts of string-coerced
# ``refAttributes`` (``macroName``, ``ref``, ``title``, ``captionName``, ``id``,
# ``url``).  The built-in container and scalar types never go through
# ``Unpickler.find_class``; the only custom class we expect is the
# ``plasTeX.Renderers.URL`` wrapper, which is a thin ``str`` subclass used to
# store node URLs.  Everything else is rejected.
_SAFE_PAUX_CLASSES: frozenset[tuple[str, str]] = frozenset({
    ("plasTeX.Renderers", "URL"),
})


class _SafePauxUnpickler(pickle.Unpickler):
    """Restricted unpickler for plasTeX ``*.paux`` files.

    Denies every ``find_class`` lookup except for an explicit allowlist of
    plasTeX value-object classes.  This prevents arbitrary-code execution
    from a stale or tampered ``web.paux`` left in the working directory.
    """

    def find_class(self, module: str, name: str):  # type: ignore[override]
        if (module, name) in _SAFE_PAUX_CLASSES:
            return super().find_class(module, name)
        raise pickle.UnpicklingError(
            f"Refusing to deserialize class {module}.{name} from .paux file; "
            "only plain built-in containers, strings, and safelisted plasTeX "
            "value classes are permitted."
        )


def _safe_paux_loads(raw: bytes) -> dict:
    """Safely unpickle a ``.paux`` payload, returning ``{}`` on any failure."""

    try:
        obj = _SafePauxUnpickler(io.BytesIO(raw)).load()
    except (pickle.UnpicklingError, EOFError, AttributeError, ImportError,
            IndexError, KeyError, TypeError, ValueError):
        return {}
    return obj if isinstance(obj, dict) else {}


def _load_paux_labels(doc):
    cache = doc.userdata.get("_tnlean_paux_labels")
    if cache is not None:
        return cache

    working_dir = Path(doc.userdata.get("working-dir", "."))
    paux_path = working_dir / f"{doc.userdata.get('jobname', 'web')}.paux"
    labels: dict = {}
    if paux_path.exists():
        try:
            raw = paux_path.read_bytes()
        except OSError:
            raw = b""
        if raw:
            data = _safe_paux_loads(raw)
            entry = data.get("HTML5", {})
            if isinstance(entry, dict):
                labels = entry

    doc.userdata["_tnlean_paux_labels"] = labels
    return labels



def _label_status_from_source(doc, label: str):
    cache = doc.userdata.setdefault("_tnlean_label_status", {})
    if label in cache:
        return cache[label]

    working_dir = Path(doc.userdata.get("working-dir", "."))
    needle = rf"\label{{{label}}}"
    status = {"leanok": False, "notready": False}

    for tex_path in working_dir.rglob("*.tex"):
        try:
            # plasTeX sources are UTF-8 by convention; pinning the encoding
            # keeps this scan stable across locales and avoids silently
            # disabling \leanok / \notready detection on systems with a
            # non-UTF-8 default encoding.
            text = tex_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue

        idx = text.find(needle)
        if idx == -1:
            continue

        begin = text.rfind(r"\begin{", 0, idx)
        end = text.find(r"\end{", idx)
        if begin == -1:
            begin = max(0, idx - 400)
        if end == -1:
            end = min(len(text), idx + 800)
        chunk = text[begin:end]
        status = {
            "leanok": r"\leanok" in chunk,
            "notready": r"\notready" in chunk,
        }
        break

    cache[label] = status
    return status



def _proxy_from_paux(doc, label: str):
    entry = _load_paux_labels(doc).get(label)
    if not entry:
        return None

    status = dict(_label_status_from_source(doc, label))
    return _LabelProxy(
        label=label,
        url=entry.get("url", ""),
        caption=entry.get("captionName", ""),
        ref=entry.get("ref", ""),
        title=entry.get("title", ""),
        userdata=status,
    )



def _resolve_label(doc, label: str, *, report_missing: bool = False):
    if not label:
        return None

    labels_dict = doc.context.labels
    target = _lookup_label(labels_dict, label)
    if target is None:
        target = _find_label_node(doc, label)
        if target is not None:
            labels_dict[label] = target
    if target is None:
        target = _proxy_from_paux(doc, label)
        if target is not None:
            labels_dict[label] = target
    if target is None and report_missing:
        _depgraph.log.error("Label %r could not be resolved", label)
    return target



def _patched_uses_digest(self, tokens):
    Command.digest(self, tokens)
    node = self.parentNode
    doc = self.ownerDocument
    labels = [
        label
        for label in (_normalize_label(label) for label in self.attributes.get("labels", []))
        if label
    ]

    def update_used() -> None:
        used = []
        for label in labels:
            target = _resolve_label(doc, label, report_missing=True)
            if target is not None:
                used.append(target)
        node.setUserData("uses", used)

    doc.addPostParseCallbacks(10, update_used)



def _patched_also_in_digest(self, tokens):
    Command.digest(self, tokens)
    node = self.parentNode
    doc = self.ownerDocument
    labels = [
        label
        for label in (_normalize_label(label) for label in self.attributes.get("labels", []))
        if label
    ]

    def update_incls() -> None:
        also_in = []
        for label in labels:
            target = _resolve_label(doc, label)
            if target is not None:
                also_in.append(target)
        incls = doc.userdata.setdefault("graph_includes", {})
        for decl in also_in:
            incls.setdefault(decl, []).append(node)

    doc.addPostParseCallbacks(10, update_incls)



def _patched_proves_digest(self, tokens):
    Command.digest(self, tokens)
    node = self.parentNode
    doc = self.ownerDocument
    label = _normalize_label(self.attributes.get("label", ""))

    def update_proved() -> None:
        proved = _resolve_label(doc, label, report_missing=True)
        if proved is not None:
            node.setUserData("proves", proved)
            proved.userdata["proved_by"] = node

    doc.addPostParseCallbacks(10, update_proved)


_depgraph.uses.digest = _patched_uses_digest
_depgraph.alsoIn.digest = _patched_also_in_digest
_depgraph.proves.digest = _patched_proves_digest


# --- cross-reference keys read inside a display ---------------------------

# Inside a display, the underscore opens a subscript, the caret a superscript,
# the ampersand a column break, and the dollar a mode switch.  A cross-
# reference key is none of those: it is a name.  While the key of a
# cross-reference is being read these four characters are demoted to ordinary
# characters, so ``\label{eq:block_diagonal}`` written inside an ``align``
# yields the key it spells rather than a parse fragment.  Left unhandled, the
# fragment reaches the page as the identifier of the display and as ``??`` at
# every reference to it.
_REFERENCE_KEY_CHARACTERS = "_^&$"

# A file path is a name too, and one written with more of TeX's characters in
# it: a comment mark would discard the rest of the line, and a tie would print
# as a space where the path has none.
_PATH_CHARACTERS = "_^&$~#%"


def _read_argument_as_written(macro_class, characters: str) -> None:
    """Read one macro's argument with the given characters demoted."""

    original = macro_class.invoke

    def invoke(self, tex):
        context = self.ownerDocument.context
        # A copy, so the characters come back however plasTeX chooses to
        # record the change: whether it replaces the table or edits it, what
        # is put back is what was read.
        categories = context.categories[:]
        for character in characters:
            context.catcode(character, Token.CC_OTHER)
        try:
            return original(self, tex)
        finally:
            context.contexts[-1].categories = context.categories = categories

    macro_class.invoke = invoke


for _macro_class in (
    _crossref.label,
    _crossref.ref,
    _crossref.pageref,
    _amsmath.eqref,
):
    _read_argument_as_written(_macro_class, _REFERENCE_KEY_CHARACTERS)


# --- a bracket opening a row is mathematics -------------------------------

# After a line break an array row may take a length in brackets that widens
# the gap to the next row.  A row that opens with a commutator carries
# brackets of its own, and those brackets are mathematics.  LaTeX reads them
# as mathematics; plasTeX and MathJax both read them as the length, which
# turns the row into an error box.  The length is kept when the brackets
# really hold one, and returned to the row otherwise; ``ROW_BREAK_LENGTH``
# states which brackets hold one by their spelling, and the generated-page
# regression reads that rule from there.  A dimension the document declares
# for itself has no telling spelling, so the document is asked directly:
# plasTeX records a dimension as a ``DimenCommand``, and \alpha is not one.


def _names_a_dimension(node, written: str) -> bool:
    control_word = _CONTROL_WORD.match(written)
    if control_word is None:
        return False
    declared = node.ownerDocument.context.get(control_word.group(4))
    return declared is not None and issubclass(declared, DimenCommand)


# --- a line break inside a braced argument is not a row of the display ----

# TeX reads an alignment with braces balanced: a line break inside a braced
# argument belongs to that argument, not to the alignment around it.  plasTeX
# ends the row anyway, which leaves a row hanging inside the brace group; the
# row then prints itself wrapped in a table named after the group, and the
# reader meets ``\begin{bgroup}`` in the middle of a formula.  A row with no
# table around it prints the entries it holds and nothing more, which is how
# a stacked limit such as ``\substack`` reaches MathJax as it was written.
_original_array_row_source = _Array.ArrayRow.source


def _patched_array_row_source(self) -> str:
    if isinstance(self.parentNode, _Array):
        return _original_array_row_source.fget(self)

    written = []
    for cell in self:
        written.append(_source_children(cell, par=False))
        if cell.endToken is not None:
            written.append(cell.endToken.source)
    if self.endToken is not None:
        written.append(self.endToken.source)
    return "".join(written)


_Array.ArrayRow.source = property(_patched_array_row_source)


_original_end_row_source = _Array.EndRow.source


def _patched_end_row_source(self) -> str:
    written = _original_end_row_source.fget(self)
    opening = written.find("[")
    if opening != -1 and written.endswith("]"):
        bracketed = written[opening + 1:-1]
        if not (_ROW_BREAK_LENGTH.match(bracketed)
                or _names_a_dimension(self, bracketed)):
            return "%s {}%s" % (written[:opening], written[opening:])
    return written


_Array.EndRow.source = property(_patched_end_row_source)


# --- constructions the web document meets but plasTeX does not define -----


class path(Command):
    r"""``\path`` from ``url``, which ``hyperref`` loads for the printed volume.

    plasTeX leaves the command undefined, and the HTML5 renderer then matches
    the bare name against the link template of ``url``, so every file path in
    the prose became an empty link followed by its own unstyled text.  The
    path is read as written: a comment mark inside it would otherwise discard
    the rest of the line, and a tie would print as a space the path has not.
    """

    args = "self"


_read_argument_as_written(path, _PATH_CHARACTERS)


class samepage(Environment):
    r"""``samepage`` keeps a statement and its proof on one printed page.

    A page is a notion of the printed volume alone, so on the web the grouping
    carries its contents and nothing else.  It stands between paragraphs, as
    the statements it holds together do.
    """

    blockType = True


class tenkzkernel(Command):
    r"""``\tenkzkernel`` selects the tensor-network kernel surface.

    The surface is bound when the tensor-network package loads, so the
    selector sets nothing and prints nothing.
    """


class _MathtoolsSmallMatrix(_amsmath.smallmatrix):
    r"""A small matrix with delimiters, as ``mathtools`` defines it.

    The printed volume loads ``mathtools``; on the web MathJax loads it on
    first sight of the environment, which is what the request in front of the
    opening marker asks for.  Without the declaration plasTeX closes the
    environment before its entries and leaves the closing marker adrift, which
    reaches the page as an empty display beside the unset entries.
    """

    macroName = None
    mathMode = True

    @property
    def source(self) -> str:
        written = _amsmath.smallmatrix.source.fget(self)
        if self.macroMode == Command.MODE_BEGIN:
            return r"\require{mathtools}" + written
        return written


class psmallmatrix(_MathtoolsSmallMatrix):
    r"""``psmallmatrix``: a small matrix in parentheses."""


class bsmallmatrix(_MathtoolsSmallMatrix):
    r"""``bsmallmatrix``: a small matrix in square brackets."""


class vsmallmatrix(_MathtoolsSmallMatrix):
    r"""``vsmallmatrix``: a small matrix between single bars."""


class Vsmallmatrix(_MathtoolsSmallMatrix):
    r"""``Vsmallmatrix``: a small matrix between double bars."""


class Bsmallmatrix(_MathtoolsSmallMatrix):
    r"""``Bsmallmatrix``: a small matrix in braces."""
