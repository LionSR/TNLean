# Nonzero bond-dimension convention: torus uniqueness clauses

This audit continues `docs/audits/2026-10-13_peps_nonzero_bond_fixed_lattice.md`,
which carried the convention that every virtual bond space is nonzero through
the fixed-lattice normal corollaries of arXiv:1804.04964 and left four torus
uniqueness clauses that paired a region hypothesis with explicit positivity.
This note records the fourth and last pass: the moved declarations, the changed
signatures, and the steps that keep explicit positivity. No compatibility alias
is provided and no theorem is renamed.

## Moved declarations

The uniqueness module `TNLean/PEPS/TorusGaugeUniqueness.lean` sits below the
module that defined the tensor hypothesis of Theorem 3, so the hypothesis moved
to a new module `TNLean/PEPS/NormalTorusRectanglePEPS.lean`, imported by both
`TorusGaugeUniqueness.lean` and
`TorusUnconditionalFundamentalTheorem.lean`.

- `TNLean.PEPS.IsNormalTorusRectanglePEPS`
- `TNLean.PEPS.IsNormalTorusRectanglePEPS.unionClosure`

Both fully qualified names, their binders and their statements are unchanged.
No parallel structure was introduced.

## Signature changes

Source: Theorem 3, "X and Y are unique up to a multiplicative constant",
`Papers/1804.04964/paper_normal.tex:1471`, and the uniqueness clause of the
window corollary, lines 2297-2318.

- `torusAbsorbedGauge_unique_scalar`: `hAr`, `hBr`, `hposA` and `hposB` are
  replaced by `hAn hBn : IsNormalTorusRectanglePEPS _`.
- `torusCovariantAbsorbedGauge_unique_classScalar`: the same replacement.
- `torusGauge_unique_scalar_of_perVertex`: the same replacement.
- `torusGauge_unique_scalar_of_normalArcWindows`: the window hypothesis of the
  second tensor and `hposB` are replaced by
  `hB : IsNormalTorusArcWindowPEPS L K B`. The statement only ever assumed the
  second tensor's positivity, and the field `bondDim_pos` of the structure
  gives it; the first tensor still enters only through `hbond` and the
  per-vertex relations. Its private helper
  `exists_injective_region_boundary_of_normalArcWindows` takes the same
  structure.

The hypotheses `hbond` (the bond spaces of `A` and `B` agree) and `hd`
(positive physical dimension) are kept: `hbond` appears in the statement's
types, and neither was touched by this pass.

Caller updated: `fundamentalTheorem_normalTorusArcWindowPEPS` passes its tensor
hypothesis directly.

## Explicit positivity kept

- `torusAbsorbedGauge_unique_scalar_of_region` sees `B` only through
  injectivity of one region and its complement, which does not force nonzero
  bonds; its callers supply positivity from the tensor hypotheses.
- The internal region, blocking and chain steps listed in the previous notes,
  including `physical_to_virtual_insertion`.

## Markers

Each touched Lean module carries one self-contained
`**Local fix (nonzero virtual spaces):**` marker citing
`docs/paper-gaps/peps_injective_ft_section3_route.tex`:
`NormalTorusRectanglePEPS.lean` (new), `TorusGaugeUniqueness.lean`,
`TorusWindowGaugeUniqueness.lean` and `TorusArcWindowFundamentalTheorem.lean`
(added), and `TorusUnconditionalFundamentalTheorem.lean` (kept).

## Counterexample module

`TNLean/PEPS/PhysicalToVirtualCounterexample.lean` is kept. The hypothesis of
`physical_to_virtual_insertion` is still the edge-blocked three-site chain,
which its witness satisfies.

## End state

The theorem and corollary statements of arXiv:1804.04964 that the earlier
notes listed state no separate positivity hypothesis. These are Theorem 2 and
its uniqueness clause, the general normal theorem, Theorem 3 with its
bond-dimension, existence and uniqueness statements, the closed-chain
corollary with its uniqueness clause, the open-square-lattice reading of
Theorem 3, and the window corollary with its bond-dimension, existence and
uniqueness statements. They carry the convention through
`Tensor.IsInjective`, `NormalPEPSPairHypotheses`, `IsNormalCycleArcMPS`,
`IsNormalTorusRectanglePEPS`, `IsNormalSquareLatticeRectanglePEPS` and
`IsNormalTorusArcWindowPEPS`.

Lemmas on the generic tensor keep explicit positivity, because the generic
tensor admits zero-dimensional bonds and the proofs apply these lemmas to
blocked, coarse and transported tensors. Examples are the overlapping union
lemma `regionInjectivityUnionClosure_of_overlap` (the source's Lemma
`injective_union`) and the internal proof steps that see a tensor only through
region, blocking or chain data.
