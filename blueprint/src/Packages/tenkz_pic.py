r"""plasTeX renderers for tenkz tensor-network pictures (spec §1.5, §5.1).

The tenkz environments (``tenkz``, ``tenkzlattice``, ``tenkzplanes``,
``tenkzfree`` — the spec's three sub-languages plus the Phase-1 bra-ket
double-layer environment that lives in the lattice layer),
the plain ``tikzcd`` environment that carries the blueprint's commutative
diagrams, and the bridge command ``\tnpic`` are registered here as
**verbatim-captured units**: plasTeX never tokenizes a picture body.  Each
captured unit is compiled **standalone** against ``TEXINPUTS=tex/tenkz//``
and converted to one SVG, cached by a per-body content hash, so editing one
figure invalidates exactly one SVG (spec §1.5: "one edited figure
invalidates one SVG, not 114").

Design decisions
----------------

1. **Verbatim round trip, no Python-side grammar.**  The TeX library in
   ``tex/tenkz/`` is the single authority on the picture grammar.  This
   module captures the raw characters between ``\begin{tenkz}[...]`` and
   ``\end{tenkz}`` (the optional key list included — with verbatim catcodes
   it is simply the first characters of the body) and re-emits them
   unchanged into a standalone document.  Print and web therefore compile
   byte-identical picture sources, which is what makes the cross-engine
   drift check (spec §5.5, G12) meaningful.

2. **Engine route: xelatex → .xdv → dvisvgm, with a probed fallback.**
   The spec pins the web pipeline to ``xelatex -no-pdf`` → ``.xdv`` →
   ``dvisvgm`` (§1.5).  That route has a silent failure mode: under
   xelatex, PGF emits xdvipdfmx ``pdf:code``/``pdf:bcontent`` specials,
   which dvisvgm can only interpret through a Ghostscript (or mutool) PDF
   interpreter.  Without one — or with dvisvgm < 3.2 against Ghostscript
   >= 10.1, whose PostScript-based PDF interpreter was removed — dvisvgm
   exits 0 and emits an SVG containing the text glyphs but **none of the
   TikZ ink** (observed with dvisvgm 3.0.3 + Ghostscript 10.06 on macOS).
   ``dvisvgm --pdf`` fails for the same reason.  We therefore compile a
   one-time ink canary (a bare TikZ ``\draw``, no text, so any ``<path>``
   in the output must be ink) through the xdv route; if the route fails —
   dvisvgm missing, xelatex or dvisvgm exiting non-zero, no SVG produced,
   or an SVG that lost its ink — every unit in this process falls back to
   ``xelatex`` → PDF → ``pdftocairo -svg`` (poppler; no Ghostscript
   dependency), and the fallback warning names the observed failure mode.  Both routes rasterize nothing — text becomes outlined
   paths either way (``--no-fonts`` / cairo).  The pdf→svg fallback uses
   pdftocairo rather than ``dvisvgm --pdf`` because the latter depends on
   exactly the Ghostscript facility whose absence triggers the fallback.

3. **Cache key.**  ``sha256(library digest ‖ standalone document)[:16]``.
   The library digest folds in every file of ``tex/tenkz/`` plus
   ``macros/common.tex``: a library edit re-renders everything (correct —
   every picture may look different), a body edit re-renders one SVG.

4. **Standalone preamble.**  Units are compiled with ``macros/common`` in
   scope so picture labels may use blueprint macros, with the same
   ``\newcounter{chapter}`` shim required because standalone is article-based
   and lacks the chapter counter that common's theorem numbering expects.

5. **Equation rows (G20).**  Blueprint source marks a display-adjacent
   diagram equation with ``tenkzequation``.  The wrapper keeps every captured
   picture as its own SVG outside MathJax and lays the sibling pictures and
   operator text out as one responsive row.  Equality signs and arrows remain
   selectable instead of becoming part of one whole-equation image.  A bare
   ``\tnpic`` inside ``$...$`` or ``\[...\]`` is still unsupported because
   MathJax cannot typeset the emitted ``<img>``; ordinary TeX retains that
   running-math capability.
"""

from __future__ import annotations

import hashlib
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

log = logging.getLogger(__name__)

_SRC_DIR = Path(__file__).resolve().parents[1]
_REPO_ROOT = _SRC_DIR.parents[1]
_TENKZ_DIR = _REPO_ROOT / "tex/tenkz"
_CACHE_DIR = _SRC_DIR / ".tenkz_svg_cache"
_SVG_SUBDIR = "tenkz_svg"
MISSING_SVG_SENTINEL = "tenkz SVG unavailable"

# Every file that participates in rendering a unit.  All of them are folded
# into the content hash: editing the library or the shared macros re-renders
# every picture, editing one picture body re-renders exactly one SVG.
_RENDER_SOURCE_FILES = (
    _SRC_DIR / "macros/common.tex",
    _SRC_DIR / "macros/diagrams.tex",
    *sorted(_TENKZ_DIR.glob("*.sty")),
    *sorted(_TENKZ_DIR.glob("*.code.tex")),
)

# The .tnlog dialect tag of each environment (the ``\tenkz@beginpicture``
# argument in tex/tenkz/, spec §5.1); reused as the CSS modifier class of
# the emitted <img>.
_ENVIRONMENT_LANGS = {
    "tenkz": "grid",
    "tenkzlattice": "lattice",
    "tenkzplanes": "planes",
    "tenkzfree": "free",
    "tikzcd": "cd",
    "tnpic": "grid",
}

# Ink canary for the route probe: a pure \draw, no text.  Any <path> in its
# SVG is necessarily TikZ ink, so "no <path>" identifies the silent
# dvisvgm-without-Ghostscript failure mode described in the module docstring.
_CANARY_DOCUMENT = r"""\documentclass[border=2pt]{standalone}
\usepackage{tikz}
\begin{document}
\begin{tikzpicture}\draw[line width=1pt] (0,0) -- (12pt,12pt);\end{tikzpicture}
\end{document}
"""


def _latex_document(unit_source: str) -> str:
    """Wrap one verbatim picture unit in the standalone compile document."""

    return rf"""\documentclass[varwidth,border=2pt]{{standalone}}
\usepackage{{amssymb,amsthm,amsmath,mathtools}}
% standalone is based on article, which already supplies section and
% subsection; only chapter is absent, so define it before loading
% macros/common (its theorem numbering references the chapter counter).
\newcounter{{chapter}}
\input{{macros/common}}
\usepackage{{tenkz}}
\input{{macros/diagrams}}
\begin{{document}}
{unit_source}
\end{{document}}
"""


@lru_cache(maxsize=1)
def _render_source_digest() -> str:
    digest = hashlib.sha256()
    for source_file in _RENDER_SOURCE_FILES:
        if not source_file.is_file():
            raise RuntimeError(f"Missing tenkz render source: {source_file}")
        digest.update(source_file.name.encode("utf-8"))
        digest.update(b"\0")
        digest.update(source_file.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def unit_hash(unit_source: str) -> str:
    """Content hash of one picture unit (library digest + full document)."""

    digest = hashlib.sha256()
    digest.update(_render_source_digest().encode("ascii"))
    digest.update(b"\0")
    digest.update(_latex_document(unit_source).encode("utf-8"))
    return digest.hexdigest()[:16]


@lru_cache(maxsize=1)
def _tex_env() -> dict[str, str]:
    """Compile environment: tex/tenkz// on TEXINPUTS (spec §1.5)."""

    env = os.environ.copy()
    env["TEXINPUTS"] = str(_TENKZ_DIR) + "//:" + env.get("TEXINPUTS", "")
    kpsewhich = shutil.which("kpsewhich")
    if kpsewhich is None:
        return env
    # When invoked from plasTeX the caller's environment can lack the TeX
    # variables a Homebrew/TeX Live split needs; resolve them once here.
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


def _run(cmd: Iterable[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(cmd),
        cwd=cwd,
        env=_tex_env(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=120,
        check=False,
    )


@dataclass(frozen=True)
class Toolchain:
    """The engine route chosen for this process (see module docstring §2)."""

    xelatex: str
    route: str  # "xdv" (spec primary) or "pdf" (probed fallback)
    converter: str  # dvisvgm for "xdv", pdftocairo for "pdf"


def _xelatex_command(xelatex: str, stem: str, *, xdv: bool) -> list[str]:
    cmd = [xelatex]
    if xdv:
        cmd.append("-no-pdf")
    cmd += [
        "-interaction=nonstopmode",
        "-halt-on-error",
        "-output-directory",
        str(_CACHE_DIR),
        str(_CACHE_DIR / f"{stem}.tex"),
    ]
    return cmd


def _dvisvgm_command(dvisvgm: str, stem: str, svg_path: Path) -> list[str]:
    # --no-fonts: text as outlined paths (web-safe, matches the fallback);
    # --exact --bbox=3pt: tight crop, same knobs as the old pipeline.
    return [
        dvisvgm,
        "--no-fonts",
        "--exact",
        "--bbox=3pt",
        f"--output={svg_path}",
        str(_CACHE_DIR / f"{stem}.xdv"),
    ]


def _svg_has_ink(svg_path: Path) -> bool:
    if not svg_path.is_file():
        return False
    return "<path" in svg_path.read_text(encoding="utf-8", errors="replace")


def _xdv_route_failure(xelatex: str, dvisvgm: str) -> str | None:
    """One-time canary through the spec's primary route (module docstring §2).

    Returns None when the route renders ink, otherwise the observed failure
    mode — the fallback warning must name what actually broke (a failed
    compile or conversion is not the ink-stripping Ghostscript problem).
    """

    _CACHE_DIR.mkdir(parents=True, exist_ok=True)
    stem = "tenkz-route-probe"
    (_CACHE_DIR / f"{stem}.tex").write_text(_CANARY_DOCUMENT, encoding="utf-8")
    svg_path = _CACHE_DIR / f"{stem}.svg"
    svg_path.unlink(missing_ok=True)
    engine = _run(_xelatex_command(xelatex, stem, xdv=True), cwd=_SRC_DIR)
    if engine.returncode != 0:
        return f"xelatex exited {engine.returncode} compiling the canary"
    converter = _run(_dvisvgm_command(dvisvgm, stem, svg_path), cwd=_SRC_DIR)
    if converter.returncode != 0:
        return f"dvisvgm exited {converter.returncode} converting the canary"
    if not svg_path.is_file():
        return "dvisvgm exited 0 but produced no canary SVG"
    if not _svg_has_ink(svg_path):
        return (
            "dvisvgm dropped the TikZ ink of the canary SVG "
            "(Ghostscript/mutool unavailable to it?)"
        )
    return None


@lru_cache(maxsize=1)
def toolchain() -> Toolchain | None:
    """Probe and cache the SVG toolchain; None when no usable route exists."""

    xelatex = shutil.which("xelatex")
    if xelatex is None:
        return None
    dvisvgm = shutil.which("dvisvgm")
    if dvisvgm is None:
        xdv_failure = "dvisvgm is not on PATH"
    else:
        xdv_failure = _xdv_route_failure(xelatex, dvisvgm)
        if xdv_failure is None:
            return Toolchain(xelatex=xelatex, route="xdv", converter=dvisvgm)
    pdftocairo = shutil.which("pdftocairo")
    if pdftocairo is not None:
        log.warning(
            "tenkz: xdv route unusable (%s); falling back to "
            "xelatex -> PDF -> pdftocairo.",
            xdv_failure,
        )
        return Toolchain(xelatex=xelatex, route="pdf", converter=pdftocairo)
    return None


def _compile_unit(unit_source: str, stem: str, svg_path: Path) -> bool:
    """Compile one unit to ``svg_path``; False when no toolchain exists."""

    chain = toolchain()
    if chain is None:
        return False
    svg_path.parent.mkdir(parents=True, exist_ok=True)
    _CACHE_DIR.mkdir(parents=True, exist_ok=True)
    tex_path = _CACHE_DIR / f"{stem}.tex"
    tex_path.write_text(_latex_document(unit_source), encoding="utf-8")

    engine = _run(
        _xelatex_command(chain.xelatex, stem, xdv=chain.route == "xdv"),
        cwd=_SRC_DIR,
    )
    if engine.returncode != 0:
        log_path = _CACHE_DIR / f"{stem}.compile.log"
        log_path.write_text(engine.stdout, encoding="utf-8")
        raise RuntimeError(
            f"tenkz picture compilation failed for {unit_source!r}; see {log_path}"
        )

    if chain.route == "xdv":
        converter_cmd = _dvisvgm_command(chain.converter, stem, svg_path)
    else:
        converter_cmd = [
            chain.converter,
            "-svg",
            str(_CACHE_DIR / f"{stem}.pdf"),
            str(svg_path),
        ]
    converter = _run(converter_cmd, cwd=_SRC_DIR)
    if converter.returncode != 0 or not svg_path.is_file():
        log_path = _CACHE_DIR / f"{stem}.convert.log"
        log_path.write_text(converter.stdout, encoding="utf-8")
        raise RuntimeError(
            f"tenkz SVG conversion failed for {unit_source!r}; see {log_path}"
        )

    tex_path.unlink(missing_ok=True)
    return True


def render_unit(unit_source: str, svg_dir: Path) -> tuple[Path | None, bool]:
    """Render one verbatim unit to a content-addressed SVG under ``svg_dir``.

    Returns ``(svg_path, cache_hit)``; ``(None, False)`` when the SVG
    toolchain is unavailable.  The cache is the SVG's existence: the file
    name is the content hash, so a body edit produces a new name (miss)
    while an untouched body finds its previous SVG (hit) — per-figure
    invalidation with no manifest to maintain.
    """

    stem = f"tenkz-{unit_hash(unit_source)}"
    svg_path = svg_dir / f"{stem}.svg"
    if svg_path.exists():
        return svg_path, True
    if not _compile_unit(unit_source, stem, svg_path):
        return None, False
    return svg_path, False


# --------------------------------------------------------------------------
# plasTeX layer.  Deferred import so scripts/test_tenkz_pic.py can exercise
# the compile+cache core above without a plasTeX installation.
# --------------------------------------------------------------------------

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


def _svg_src(obj: object, svg_path: Path, output_dir: Path) -> str:
    output_url = _nearest_output_url(obj)
    if output_url is None:
        return posixpath.join(_SVG_SUBDIR, svg_path.name)
    html_path = Path(output_url)
    if not html_path.is_absolute():
        html_path = output_dir / html_path
    return Path(os.path.relpath(svg_path, start=html_path.parent)).as_posix()


def _missing_tools_html(unit_source: str) -> str:
    return (
        '<span class="tenkz-svg-missing">'
        f"{MISSING_SVG_SENTINEL}: install xelatex plus dvisvgm (with "
        "Ghostscript/mutool) or pdftocairo to render "
        f"<code>{escape(unit_source)}</code>."
        "</span>"
    )


try:
    from plasTeX import Command, Environment, VerbatimEnvironment
except ImportError:  # standalone harness use; see the section comment above
    pass
else:

    class tenkzkernel(Command):
        r"""The kernel switch (spec §2).  It draws nothing; it stands in
        the tree so a picture can read whether the switch reaches it."""

        args = ""

    class tenkzequation(Environment):
        """A responsive text-mode row of independent SVG picture units."""

        blockType = True
        templateName = "TenkzEquation"

    def _holds_kernel_switch(node) -> bool:
        r"""Whether this preceding sibling carries \tenkzkernel in force.

        A paragraph break is not a TeX group, so a switch inside a
        preceding ``par`` wrapper still governs what follows; the search
        descends through ``par`` nodes and nothing else, since every
        other container opens a group that ends the declaration.
        """
        name = getattr(node, "nodeName", "")
        if name == "tenkzkernel":
            return True
        if name != "par":
            return False
        return any(
            _holds_kernel_switch(child)
            for child in getattr(node, "childNodes", [])
        )

    def _kernel_switch_reaches(node) -> bool:
        r"""Whether \tenkzkernel is in force where this picture stands.

        The switch is an ordinary TeX declaration, so a group ends it: a
        switch inside one ``center`` block does not reach a picture in the
        next.  Reading the preceding siblings at each level up from the
        picture answers exactly that question, and it keeps a chapter that
        has migrated one figure from claiming the ones it has not.
        """
        current = node
        while current is not None:
            parent = getattr(current, "parentNode", None)
            if parent is None:
                return False
            for sibling in getattr(parent, "childNodes", []):
                if sibling is current:
                    break
                if _holds_kernel_switch(sibling):
                    return True
            current = parent
        return False

    class _TenkzSvgMixin:
        """Shared rendering: compile the captured unit, emit one <img>."""

        # plasTeX's renderer reads ``templateName`` as a string attribute of
        # the node; the template lives in plastex_templates/
        # TenkzPictures.jinja2s and expands to ``tenkz_svg_html``.
        templateName = "TenkzPicture"

        def tenkzUnitSource(self) -> str:
            raise NotImplementedError

        @property
        def tenkz_svg_html(self) -> str:
            unit_source = self.tenkzUnitSource()
            if _kernel_switch_reaches(self):
                unit_source = "\\tenkzkernel\n" + unit_source
            output_dir = _output_dir(self.ownerDocument)
            svg_path, _ = render_unit(unit_source, output_dir / _SVG_SUBDIR)
            if svg_path is None:
                logged = self.ownerDocument.userdata.setdefault(
                    "_tenkz_svg_missing_tools", False
                )
                if not logged:
                    log.warning(
                        "tenkz SVG rendering needs xelatex and dvisvgm or "
                        "pdftocairo on PATH."
                    )
                    self.ownerDocument.userdata["_tenkz_svg_missing_tools"] = True
                if os.environ.get("CI") == "true":
                    raise RuntimeError(
                        "tenkz SVG rendering needs xelatex and dvisvgm or "
                        f"pdftocairo on PATH for {unit_source!r}."
                    )
                return _missing_tools_html(unit_source)
            src = _svg_src(self, svg_path, output_dir)
            lang = _ENVIRONMENT_LANGS[self.nodeName]
            # The verbatim unit source is the per-picture alternative text;
            # tenkzequation keeps operators outside the image and selectable.
            return (
                f'<img class="tenkz-pic tenkz-pic-{lang}" '
                f'src="{escape(src, quote=True)}" '
                f'alt="{escape(unit_source, quote=True)}">'
            )

    class _TenkzVerbatimEnvironment(_TenkzSvgMixin, VerbatimEnvironment):
        r"""Base of the four picture environments.

        VerbatimEnvironment switches to verbatim catcodes right after
        parsing the (empty) argument spec, so everything between
        ``\begin{X}`` and ``\end{X}`` — the optional ``[keys]`` included —
        is captured as raw characters and round-trips into the standalone
        document byte-identically.  No tenkz key ever gets parsed in
        Python; the TeX library is the single grammar authority.
        """

        def tenkzUnitSource(self) -> str:
            name = self.nodeName
            return rf"\begin{{{name}}}{self.textContent}\end{{{name}}}"

    class tenkz(_TenkzVerbatimEnvironment):
        pass

    class tenkzlattice(_TenkzVerbatimEnvironment):
        pass

    class tenkzplanes(_TenkzVerbatimEnvironment):
        pass

    class tenkzfree(_TenkzVerbatimEnvironment):
        pass

    class tikzcd(_TenkzVerbatimEnvironment):
        pass

    class tnpic(_TenkzSvgMixin, Command):
        r"""The bridge object ``\tnpic[keys]{grid body}`` (spec §2.3).

        The optional key list and the mandatory body are read with
        verbatim catcodes and balanced-brace scanning, mirroring how
        ``\verb`` captures its argument, so cell separators (``&``),
        comments, and math inside the body survive untouched.

        In blueprint source this command is supported at top level, including
        as a child of ``tenkzequation``.  It must not appear inside MathJax
        input: the explicit equation wrapper is the G20 web contract, while
        ordinary TeX may continue to use the atom in running mathematics.
        """

        blockType = False

        def invoke(self, tex):
            self.ownerDocument.context.push(self)
            self.parse(tex)
            self.ownerDocument.context.setVerbatimCatcodes()
            try:
                self.tenkzCaptured = self._capture_call(tex)
            finally:
                self.ownerDocument.context.pop(self)
            return [self]

        @staticmethod
        def _next_nonspace(tokens) -> str | None:
            for tok in tokens:
                if str(tok) not in " \t\r\n":
                    return tok
            return None

        def _capture_call(self, tex) -> str:
            tokens = iter(tex)
            parts: list[str] = []
            head = self._next_nonspace(tokens)
            if head == "[":
                # Optional key list: keys may contain braced values
                # (``bond label={$D$ at 1-2}``), so ``]`` closes only at
                # brace depth zero.
                option = ["["]
                depth = 0
                for tok in tokens:
                    option.append(str(tok))
                    if tok == "{":
                        depth += 1
                    elif tok == "}":
                        depth -= 1
                    elif tok == "]" and depth == 0:
                        break
                else:
                    raise ValueError(r"unterminated \tnpic optional argument")
                parts.append("".join(option))
                head = self._next_nonspace(tokens)
            if head != "{":
                raise ValueError(r"\tnpic requires a braced grid body")
            body = ["{"]
            depth = 1
            for tok in tokens:
                body.append(str(tok))
                if tok == "{":
                    depth += 1
                elif tok == "}":
                    depth -= 1
                    if depth == 0:
                        break
            else:
                raise ValueError(r"unterminated \tnpic body")
            parts.append("".join(body))
            return "".join(parts)

        def tenkzUnitSource(self) -> str:
            return r"\tnpic" + self.tenkzCaptured

        @property
        def source(self) -> str:
            return self.tenkzUnitSource()
