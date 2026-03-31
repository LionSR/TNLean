"""Local override for the leanblueprint plasTeX package.

This keeps the upstream behaviour but hardens `\\lean{...}` parsing:
plasTeX can sometimes hand back TeXFragment objects instead of plain
strings for list items, and the stock package calls `.strip()` directly.
"""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

from plasTeX import Command


_UPSTREAM = Path(
    "/Users/siruilu/miniforge3/lib/python3.13/site-packages/leanblueprint/Packages/blueprint.py"
)
_SPEC = spec_from_file_location("_tnlean_upstream_blueprint", _UPSTREAM)
_MODULE = module_from_spec(_SPEC)
assert _SPEC is not None and _SPEC.loader is not None
_SPEC.loader.exec_module(_MODULE)

for _name in dir(_MODULE):
    if _name.startswith("__") or _name == "lean":
        continue
    globals()[_name] = getattr(_MODULE, _name)


class lean(_MODULE.lean):
    r"""\lean{decl list}"""

    def digest(self, tokens):
        Command.digest(self, tokens)
        raw_decls = self.attributes["decls"]
        decls = [getattr(dec, "textContent", str(dec)).strip() for dec in raw_decls]
        self.parentNode.setUserData("leandecls", decls)
        all_decls = self.ownerDocument.userdata.setdefault("lean_decls", [])
        all_decls.extend(decls)
