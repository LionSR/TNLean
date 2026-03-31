"""Local override for the leanblueprint plasTeX package.

This keeps the upstream behaviour but hardens `\\lean{...}` parsing:
plasTeX can sometimes hand back TeXFragment objects instead of plain
strings for list items, and the stock package calls `.strip()` directly.
"""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

import leanblueprint
from plasTeX import Command


_UPSTREAM = Path(leanblueprint.__file__).parent / "Packages" / "blueprint.py"
_SPEC = spec_from_file_location("_tnlean_upstream_blueprint", _UPSTREAM)
assert _SPEC is not None and _SPEC.loader is not None
_MODULE = module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)

for _name in dir(_MODULE):
    if _name.startswith("__") or _name == "lean":
        continue
    globals()[_name] = getattr(_MODULE, _name)


class lean(_MODULE.lean):
    r"""\lean{decl list}"""

    def digest(self, tokens):
        replacements = {
            "MPSTensor.weakFundamentalTheoremconditional":
                "MPSTensor.weakFundamentalTheorem_conditional",
            "MPSTensor.exponentialconvergenceofprimitive":
                "MPSTensor.exponential_convergence_of_primitive",
        }

        def normalize_decl(decl: str) -> str:
            normalized = replacements.get(decl, decl)
            if normalized != decl:
                logged = self.ownerDocument.userdata.setdefault(
                    "_tnlean_logged_replacements", set()
                )
                if (decl, normalized) not in logged:
                    _MODULE.log.warning(
                        "Normalizing mangled \\lean declaration '%s' to '%s'; "
                        "this works around a plasTeX underscore-parsing bug.",
                        decl,
                        normalized,
                    )
                    logged.add((decl, normalized))
            return normalized

        Command.digest(self, tokens)
        raw_decls = self.attributes["decls"]
        decls = [
            normalize_decl(
                getattr(dec, "source", getattr(dec, "textContent", str(dec))).strip()
            )
            for dec in raw_decls
        ]
        existing = list(self.parentNode.userdata.get("leandecls", []))
        for decl in decls:
            if decl and decl not in existing:
                existing.append(decl)
        self.parentNode.setUserData("leandecls", existing)
        all_decls = self.ownerDocument.userdata.setdefault("lean_decls", [])
        for decl in decls:
            if decl and decl not in all_decls:
                all_decls.append(decl)
