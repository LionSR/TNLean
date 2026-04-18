r"""TNLean-specific plasTeX monkey patches.

This module is loaded from ``web.tex`` as ``\usepackage{_tnlean_patches}``.
Because plasTeX searches ``packages-dirs=Packages`` before its built-in/plugin
package implementations, this single helper can monkey-patch the exact
upstream methods that TNLean still needs without shadowing the full ``natbib``,
``blueprint``, or ``depgraph`` modules.

The remaining local fixes are:

* ``plasTeX.Packages.natbib.bibliography.loadBibliographyFile``:
  skip the spurious missing-``web.aux`` warning during HTML builds, while still
  exposing natbib's ``bibitem`` globally so generated ``web.bbl`` entries parse
  reliably when present.
* ``leanblueprint.Packages.blueprint.lean.digest``:
  coerce plasTeX list items to plain strings, merge multiple ``\lean`` tags on
  one parent node, and deduplicate ``lean_decls`` output.
* ``plastexdepgraph.Packages.depgraph.{uses, alsoIn, proves}.digest``:
  normalize label tokens and defer/fallback label resolution so ``\uses``,
  ``\alsoIn``, and ``\proves`` survive plasTeX timing quirks.
"""

from __future__ import annotations

from pathlib import Path
import pickle
from typing import Any

from leanblueprint.Packages import blueprint as _blueprint
import plasTeX.Packages.natbib as _natbib
from plasTeX import Base, Command
from plastexdepgraph.Packages import depgraph as _depgraph


_HISTORICAL_DECL_REPLACEMENTS = {
    # These two names were observed in #398 with underscores stripped by a
    # plasTeX parsing corner case. The generic string coercion below avoids the
    # common failure mode; this mapping is kept as a narrow last-resort guard.
    "MPSTensor.weakFundamentalTheoremconditional":
        "MPSTensor.weakFundamentalTheorem_conditional",
    "MPSTensor.exponentialconvergenceofprimitive":
        "MPSTensor.exponential_convergence_of_primitive",
}


def _stringify_tex_item(obj: Any) -> str:
    """Extract a stable string from a plasTeX token/list item."""

    return getattr(obj, "source", getattr(obj, "textContent", str(obj))).strip()


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
_natbib.bibitem = _natbib.thebibliography.bibitem


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



def _load_paux_labels(doc):
    cache = doc.userdata.get("_tnlean_paux_labels")
    if cache is not None:
        return cache

    working_dir = Path(doc.userdata.get("working-dir", "."))
    paux_path = working_dir / f"{doc.userdata.get('jobname', 'web')}.paux"
    labels = {}
    if paux_path.exists():
        try:
            data = pickle.loads(paux_path.read_bytes())
            labels = data.get("HTML5", {})
        except Exception:
            labels = {}

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
            text = tex_path.read_text()
        except Exception:
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
