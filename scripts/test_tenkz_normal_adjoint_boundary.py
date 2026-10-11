#!/usr/bin/env python3
"""Check the normal-adjoint diagrams, virtual order, and boundary conjugation."""

from __future__ import annotations

import argparse
import itertools
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

from tenkz_paths import ensure_pythonpath, tenkz_tex

ensure_pythonpath()
from tenkz_audit import Audit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch30_mpo_normal_adjoint_boundary.tex"
PARTS = {
    "LETTERS": [("W.0", "T.180"), ("T.0", "V.180")],
    "BOUNDARY": [("V.0", "X.180"), ("X.0", "W.180")],
}
EXPECTED_PANELS = [
    ("open:e, open:w, phys:n, phys:s", 1, 4),
    ("open:e, open:w, phys:n, phys:s", 3, 6),
    ("open:e, open:w", 1, 2),
    ("open:e, open:w", 3, 4),
]
EXPECTED_LABELS = [
    [("180", r"\alpha"), ("0", r"\beta"), ("90", "i"), ("270", "j")],
    [("180", r"\alpha"), ("0", r"\beta"), ("90", "i"), ("270", "j")],
    [("180", "p"), ("0", "q")],
    [("180", "p"), ("0", "q")],
]
EXPECTED_TENSORS = [
    [("S", r"T_a^\sharp")],
    [("W", r"W_a"), ("T", r"T_{a^\vee}"), ("V", r"V_a")],
    [("B", "B")],
    [("V", r"V_a"), ("X", r"\overline X"), ("W", r"W_a")],
]


def label_tokens(label: str) -> tuple[str, ...]:
    """Ignore TeX spacing without conflating control words with their arguments."""
    return tuple(re.findall(r"\\[A-Za-z]+|\\.|[^\s]", label))


def assert_tensor_labels(actual, expected) -> None:
    normalize = lambda items: [(name, label_tokens(label)) for name, label in items]
    assert normalize(actual) == normalize(expected), (actual, expected)


def source_tensor_labels(body: str) -> list[tuple[str, str]]:
    """Read actual named node glyphs, including nested TeX braces in labels."""
    result = []
    for match in re.finditer(r"\\tn\[([^]]*)\]\{", body, re.DOTALL):
        name = re.search(r"(?:^|,)\s*name=([^,\s]+)", match[1])
        assert name is not None, "Every diagram tensor must have a pinned name"
        start, end, depth = match.end(), match.end(), 1
        while depth:
            assert end < len(body), "Unclosed tensor glyph label"
            if body[end] == "\\":
                end += 2
                continue
            depth += (body[end] == "{") - (body[end] == "}")
            end += 1
        result.append((name[1], body[start:end - 1]))
    return result


def check_contractions() -> None:
    """Use exact small Gaussian integers, including a nonunitary similarity."""
    def mul(a, b):
        return [[sum(a[i][k] * b[k][j] for k in range(2))
                 for j in range(2)] for i in range(2)]

    def conjugate(a):
        return [[z.conjugate() for z in row] for row in a]

    def transpose(a):
        return [[a[j][i] for j in range(2)] for i in range(2)]

    def trace(a):
        return a[0][0] + a[1][1]

    identity = [[1, 0], [0, 1]]
    v, w = [[1, 1], [0, 1]], [[1, -1], [0, 1]]
    x = [[1 + 2j, 3 - 1j], [2 + 4j, -1 + 1j]]
    a = {(i, j): [[1 + i + 1j * j, 2 + j - 1j * i],
                  [i - j + 2j, -1 + j + 1j * (i + 1)]]
         for i in range(2) for j in range(2)}
    b = {(i, j): mul(mul(v, conjugate(a[j, i])), w)
         for i in range(2) for j in range(2)}
    assert mul(v, w) == mul(w, v) == identity
    for pair in a:
        assert conjugate(a[pair[1], pair[0]]) == mul(mul(w, b[pair]), v)
    boundary = mul(mul(v, conjugate(x)), w)
    wrong = mul(mul(v, transpose(conjugate(x))), w)

    def close(tensor, boundary_matrix, sigma, tau):
        product = identity
        for pair in zip(sigma, tau, strict=True):
            product = mul(product, tensor[pair])
        return trace(mul(boundary_matrix, product))

    wrong_detected = False
    count = 0
    for n in range(3):
        configurations = list(itertools.product(range(2), repeat=n))
        for sigma, tau in itertools.product(configurations, repeat=2):
            expected = close(a, x, tau, sigma).conjugate()
            assert expected == close(b, boundary, sigma, tau)
            wrong_detected |= expected != close(b, wrong, sigma, tau)
            count += 1
    assert wrong_detected, "The test must detect an erroneous virtual transpose"
    print(f"PASS: {count} exact boundary coefficients at lengths 0, 1, 2; "
          "the virtual-transpose mutation is detected")


def check(work: Path) -> None:
    engine = shutil.which("xelatex")
    if engine is None:
        raise SystemExit("FAIL: xelatex is required")
    source = CHAPTER.read_text(encoding="utf-8")
    bodies, rendered_bodies = [], []
    for part_index, (tag, expected_wires) in enumerate(PARTS.items()):
        begin = f"% TENKZ-NORMAL-ADJOINT-{tag}-BEGIN"
        end = f"% TENKZ-NORMAL-ADJOINT-{tag}-END"
        assert source.count(begin) == source.count(end) == 1
        body = source.split(begin, 1)[1].split(end, 1)[0]
        assert re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", body) == expected_wires
        assert body.count("bonds=none") == 2
        assert "West ports are matrix rows; east ports are columns." in body
        assert r"\dagger" not in body and r"\mathsf T" not in body
        expected_tensors = (EXPECTED_TENSORS[2 * part_index]
                            + EXPECTED_TENSORS[2 * part_index + 1])
        assert_tensor_labels(source_tensor_labels(body), expected_tensors)
        if tag == "BOUNDARY":
            mutant = body.replace(r"]{\overline X}", "]{X}")
            assert mutant != body, "The actual conjugated boundary glyph is missing"
            try:
                assert_tensor_labels(source_tensor_labels(mutant), expected_tensors)
            except AssertionError:
                pass
            else:
                raise AssertionError("Removing the boundary bar escaped the source check")
        rendered_bodies.append(body)
        body = body.replace(r"\begin{tenkzequation}", r"\begin{tenkzeq}[check={signature}]")
        body = body.replace(r"\end{tenkzequation}", r"\end{tenkzeq}")
        bodies.append(body.replace("$=$", "="))
    assert "Conjugation is entrywise, with no virtual transpose." in source
    assert "Fin chi_{a^vee}" in bodies[0] and "Fin chi_a" in bodies[1]
    tex = work / "normal-adjoint-boundary.tex"
    tex.write_text(
        "\\documentclass{article}\n\\usepackage{amsmath,amssymb,tenkz}\n"
        "\\pagestyle{empty}\n\\begin{document}\n"
        + "\n".join(bodies) + "\n\\end{document}\n", encoding="utf-8",
    )
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
    run = subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    (work / "compile.log").write_text(run.stdout, encoding="utf-8")
    if run.returncode:
        raise SystemExit(f"FAIL: diagram did not compile; see {work / 'compile.log'}")
    audit = Audit(work / "normal-adjoint-boundary.tnlog", tex)
    audit.run()
    assert not audit.findings, audit.findings
    panels, atoms, wires = [], [], []
    for event in audit.events():
        if event.kind == "atom":
            atoms.append(event)
        elif event.kind == "wire":
            wires.append(event)
        elif event.kind == "kernel-boundary":
            assert_tensor_labels(
                [(atom.attrs["name"], atom.attrs["label"]) for atom in atoms],
                EXPECTED_TENSORS[len(panels)],
            )
            labels = [(w.attrs["port-face"], w.attrs["port-label"].strip())
                      for w in wires if w.attrs.get("origin") == "port-open"]
            assert sorted(labels) == sorted(EXPECTED_LABELS[len(panels)]), labels
            panels.append((event.attrs["signature"], len(atoms), len(wires)))
            assert not any(w.attrs.get("origin") in {"grid", "trace"} for w in wires)
            atoms, wires = [], []
    assert panels == EXPECTED_PANELS, panels
    checks = [event.attrs for event in audit.log_events if event.kind == "check"]
    assert len(checks) == 2 and all(c.get("result") == "equal" for c in checks), checks
    # The blueprint's wrapper is a center environment, not a native equation.
    # Check that its standalone panel sizing also keeps every tensor name inside.
    wrapper = work / "rendered-wrapper.tex"
    wrapper.write_text(
        "\\documentclass{article}\n\\usepackage{amsmath,amssymb,tenkz}\n"
        "\\newenvironment{tenkzequation}{\\center}{\\endcenter}\n"
        "\\pagestyle{empty}\n\\begin{document}\n"
        + "\n".join(rendered_bodies) + "\n\\end{document}\n", encoding="utf-8",
    )
    rendered = subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error", wrapper.name],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    (work / "wrapper-compile.log").write_text(rendered.stdout, encoding="utf-8")
    assert rendered.returncode == 0, "The blueprint wrapper did not compile"
    wrapper_audit = Audit(work / "rendered-wrapper.tnlog", wrapper)
    wrapper_audit.run()
    assert not wrapper_audit.findings, wrapper_audit.findings
    wrapper_atoms, wrapper_panels = [], 0
    for event in wrapper_audit.events():
        if event.kind == "atom":
            wrapper_atoms.append((event.attrs["name"], event.attrs["label"]))
        elif event.kind == "kernel-boundary":
            assert_tensor_labels(wrapper_atoms, EXPECTED_TENSORS[wrapper_panels])
            wrapper_atoms = []
            wrapper_panels += 1
    assert wrapper_panels == len(EXPECTED_TENSORS)
    outside = [event.attrs for event in wrapper_audit.log_events
               if event.kind == "bbox" and event.attrs.get("class") == "label"
               and event.attrs.get("owner") not in {None, "0"}]
    assert not outside, f"Tensor labels moved outside their glyphs: {outside}"
    check_contractions()
    print("PASS: four panels; exact virtual matrix-product order; matching "
          "native signatures; physical output/input orientation; no audit findings")
    print("PASS: every named tensor glyph pinned in source and both event streams; "
          "removing the actual boundary conjugation bar is rejected")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, help="retain rendered regression artifacts")
    args = parser.parse_args()
    if args.output_dir is not None:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        check(args.output_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_normal_adjoint_") as tmp:
            check(Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
