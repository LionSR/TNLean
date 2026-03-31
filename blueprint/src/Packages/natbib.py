"""Local override for plasTeX's natbib package.

This keeps the upstream behaviour but avoids a noisy missing-``web.aux``
warning during HTML builds and exposes ``\\bibitem`` globally so entries from
the generated ``.bbl`` file are recognized reliably while it is being loaded.
"""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

import plasTeX
from plasTeX import Base


_UPSTREAM = Path(plasTeX.__file__).parent / "Packages" / "natbib.py"
_SPEC = spec_from_file_location("_tnlean_upstream_natbib", _UPSTREAM)
_MODULE = module_from_spec(_SPEC)
assert _SPEC is not None and _SPEC.loader is not None
_SPEC.loader.exec_module(_MODULE)

for _name in dir(_MODULE):
    if _name.startswith("__") or _name in {"bibliography", "bibitem"}:
        continue
    globals()[_name] = getattr(_MODULE, _name)


class bibliography(_MODULE.bibliography):
    def loadBibliographyFile(self, tex):
        doc = self.ownerDocument
        doc.userdata.setPath("bibliography/bibcites", {})

        aux_path = Path(f"{tex.jobname}.aux")
        if aux_path.exists():
            self.ownerDocument.context.push(self)
            self.ownerDocument.context["setcounter"] = self.setcounter
            tex.loadAuxiliaryFile()
            self.ownerDocument.context.pop(self)

        Base.bibliography.loadBibliographyFile(self, tex)


bibitem = _MODULE.thebibliography.bibitem
