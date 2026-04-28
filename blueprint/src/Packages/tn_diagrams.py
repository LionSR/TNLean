r"""plasTeX renderers for TNLean tensor-network diagrams.

The PDF blueprint renders the chapter-facing ``\TN...`` macros with TikZ from
``macros/tn_print.tex``.  The web blueprint uses the same macro calls and asks
this package for a cached SVG.  Thus TikZ remains the single source of truth.
"""

from __future__ import annotations

import hashlib
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
_CACHE_DIR = _SRC_DIR / ".tn_svg_cache"
_SVG_SUBDIR = "tn_svg"
_RENDER_SOURCE_FILES = (
    _SRC_DIR / "macros/common.tex",
    _SRC_DIR / "macros/tn_print.tex",
)


_DIAGRAM_ARGS: dict[str, str] = {
    "TNMPSLocal": "tensor label",
    "TNMPSWord": "tensor left right length",
    "TNMPV": "tensor left right length",
    "TNTransferMap": "tensor",
    "TNMPOCell": "tensor top bottom",
    "TNMPOChain": "tensor top_left bottom_left top_right bottom_right length",
    "TNLPDO": "upper lower bond top bottom",
    "TNGaugeConjugation": "left physical right",
    "TNPhysicalRealization": "virtual physical",
    "TNLinearTwist": "twist label",
    "TNPermutationTwistLabeled": "left right permutation",
    "TNPermutationTwist": "left right",
    "TNTwistedTransfer": "twist",
    "TNCondCOne": "twist virtual label",
    "TNCondCTwo": "virtual",
    "TNStringOrderParameter": "twist length",
    "TNVirtualInsertion": "left middle right virtual",
    "TNInternalTraceInsertion": "left right virtual",
    "TNExternalTraceInsertion": "left right virtual",
    "TNBoundaryRegrow": "virtual left right length",
    "TNLocalEqualityStep": "left_virtual right_virtual physical",
    "TNPeriodicGauge": "left virtual right",
    "TNGroundSpaceMap": "tensor left right length virtual",
    "TNPEPSEdgeGaugeOrientation": "",
    "TNPEPSGaugeVertexAction": "",
    "TNPEPSGaugeCancellation": "",
    "TNPEPSLocalGaugeExtraction": "",
    "TNPEPSGlobalConsistency": "",
    "TNMPOCellDiagram": "tensor top bottom",
    "TNMPOChainDiagram": "",
    "TNLPDODiagram": "",
}


def _diagram_arity(args: str) -> int:
    return len(args.split())


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


_assert_diagram_args_match_print_macros()


def _tex_call(obj: Command) -> str:
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
    (_CACHE_DIR / f"{stem}.tex").write_text(_latex_document(tex_call), encoding="utf-8")

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

    return svg_path.name


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
