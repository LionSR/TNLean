# Dependent microscopic parent-to-seam diagrams

Date: 2026-10-05.

## Sources and scope

The companion is
[`ch24_peps_dependent_parent_seam_diagrams.tex`](../../blueprint/src/chapter/ch24_peps_dependent_parent_seam_diagrams.tex).
Declaration ownership remains in the native parent-seam theorem fragment.

The local source passage is SCP10, `Papers/1001.3807/paper_v3.tex`, lines
1526–1566, Theorem 5.7 and its use of the intersection and closure theorems.
The source figures `figs3/close-out-out.pdf` and
`figs3/close-AAAA-ug-uh.pdf` were rasterized and inspected.
The mathematical comparison used the complete statements and proofs in
`TorusDependentParentSeamCuts.lean`, `TorusNonuniformParentSeamCuts.lean`,
`GraphPhysicalPadding.lean`, and `PaddedPhysicalParent.lean`, together with
the literal `cutCoeff` definition in `DependentBondCut.lean`.

The proved implication concerns the existing positive microscopic plaquette
parent, every native seam, independently dimensioned and represented virtual
bonds, and independent finite physical alphabets. Both torus periods are at
least three. It does not assert the full microscopic commuting-closure
classification.

## Exact meaning of the four displays

1. One arbitrary joint boundary contracts with the original network.
   The two displayed virtual wires are the complete tail and head tuples,
   each in the dependent product of cut-edge alphabets. They are independent.
   The box is defined by summing one common index on each uncut bond and
   multiplying all original site tensors. It is not a replacement 2×2 lattice.
2. Product physical padding commutes with this contraction and preserves the
   same joint boundary coefficients. The original physical tuple is summed
   into the product padding map; the ambient tuple remains open.
3. Product restriction after padding recovers every original physical vector.
4. Padding after restriction recovers every ambient parent-kernel vector.
   This equality follows from the parent constraints, without an assumed
   local-image condition. On the ambient space the composition is a coordinate
   projection, not an assumed identity or unitary.

Every panel has typed exterior signature `(0 virtual, 1 physical)`. The one
physical wire always denotes an explicitly specified full-site tuple. The
source comments state each formula, index correspondence, and contraction.

## Verification

With XeLaTeX, pdftoppm and the Tenkz checkout pinned by `tenkz.toml`:

```sh
python3 scripts/test_tenkz_peps_parent_seams.py
python3 scripts/test_tenkz_peps_parent_seams.py --output-dir /tmp/parent-seam-review
```

Verified with pinned Tenkz `08a6493f3605dcf2ca5b512823ccb2698dfc027b`:

- Four displays / seven panels render separately and together with the actual
  native theorem fragment and the print preamble.
- Exact source atoms, glyphs, port kinds, wire incidences and tuple labels match
  the expected contractions; emitted atom/wire types and all seven exact
  `phys:e` boundary signatures also match.
- Seven negative mutations are rejected: merged incidences, incorrect tail/head
  labels, a virtual-to-physical type change, changed boundary coefficients,
  a changed padded tensor, an incorrect recovery map, and a wrong output alphabet.
- An exact integer fixture checks grouped contraction against the literal
  endpoint sum with bond dimensions 2, 3, 3 and physical sizes 2, 1, 3.
  Tagged-coordinate padding has exact left-inverse recovery; its reverse
  composition is not the identity on the entire ambient space.
- Tenkz topology, bounding-box, overlap, and equation-boundary audits pass.
  The two-pass combined document has no LaTeX warnings or overfull boxes.
- Individual PNGs and the combined diagram page were inspected. The companion
  occupies one printed page; indices and equations are legible without overlap.
- An exported-tree smoke test passes with no `.git` directory or private refs.
  Python syntax and whitespace checks pass. ChkTeX was unavailable locally.

No Lean proof, router, workflow, package dependency, or repository rendering
cache was changed by this diagram work. The regression test checks the diagram
contract and fixture algebra; it does not replace Lean's parent theorem.
