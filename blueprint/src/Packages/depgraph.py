"""Local override for the plasTeX depgraph package.

This hardens label-list parsing for ``\\uses``, ``\\alsoIn``, and
``\\proves``. plasTeX can hand back TeXFragment objects or padded strings for
list arguments; the upstream package uses them directly as dictionary keys,
which can make otherwise valid labels appear unresolved.
"""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import pickle

import plastexdepgraph
from plasTeX import Command


_UPSTREAM = Path(plastexdepgraph.__file__).parent / "Packages" / "depgraph.py"
_SPEC = spec_from_file_location("_tnlean_upstream_depgraph", _UPSTREAM)
assert _SPEC is not None and _SPEC.loader is not None
_MODULE = module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)

for _name in dir(_MODULE):
    if _name.startswith("__") or _name in {"uses", "alsoIn", "proves"}:
        continue
    globals()[_name] = getattr(_MODULE, _name)


def _normalize_label(obj) -> str:
    return getattr(obj, "source", getattr(obj, "textContent", str(obj))).strip()


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
        _MODULE.log.error("Label '" + label + "' could not be resolved")
    return target


class uses(_MODULE.uses):
    r"""\uses{labels list}"""

    def digest(self, tokens):
        Command.digest(self, tokens)
        node = self.parentNode
        doc = self.ownerDocument
        labels = [_normalize_label(label) for label in self.attributes["labels"]]

        def update_used():
            used = []
            for label in labels:
                target = _resolve_label(doc, label, report_missing=True)
                if target is not None:
                    used.append(target)
            node.setUserData("uses", used)

        doc.addPostParseCallbacks(10, update_used)


class alsoIn(_MODULE.alsoIn):
    r"""\alsoIn{labels list}"""

    def digest(self, tokens):
        Command.digest(self, tokens)
        node = self.parentNode
        doc = self.ownerDocument
        labels = [_normalize_label(label) for label in self.attributes["labels"]]

        def update_incls():
            alsoin = []
            for label in labels:
                target = _resolve_label(doc, label)
                if target is not None:
                    alsoin.append(target)
            incls = doc.userdata.setdefault("graph_includes", dict())
            for decl in alsoin:
                incls.setdefault(decl, []).append(node)

        doc.addPostParseCallbacks(10, update_incls)


class proves(_MODULE.proves):
    r"""\proves{label}"""

    def digest(self, tokens):
        Command.digest(self, tokens)
        node = self.parentNode
        doc = self.ownerDocument
        label = _normalize_label(self.attributes["label"])

        def update_proved() -> None:
            proved = _resolve_label(doc, label, report_missing=True)
            if proved:
                node.setUserData("proves", proved)
                proved.userdata["proved_by"] = node

        doc.addPostParseCallbacks(10, update_proved)
