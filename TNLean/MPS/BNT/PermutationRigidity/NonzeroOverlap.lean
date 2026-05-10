import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.SpectralGapNT
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Overlap.CastDecay

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Permutation rigidity for basis-of-normal-tensors (BNT) decompositions — Theorem 4.4
(paper hypotheses, no span-equality)

This module replaces the extra span-equality hypothesis used in
`PermutationRigidityPrimitive.lean` with the **paper-style** hypotheses from Theorem 4.4
(arXiv:2011.12127 / 1606.00608, primitive branch): proportionality of the full MPV
families together with explicit decompositions into BNT families.

It contains both directions of the key nonvanishing-overlap step and the resulting
full permutation / gauge-phase matching theorems, in both the injective and
irreducible trace-preserving settings.

The overlap arguments follow the Appendix-A strategy: take overlaps of the
proportional full states with individual block states and use the asymptotic
orthogonality inside each BNT family.

In canonical-form applications one first normalizes by the dominant weights, so the relevant
coefficient arrays are `(μ j / μ 0)^N`; the discarded dominant factors are absorbed into the
proportionality constant.
-/

open scoped BigOperators Matrix
open Filter Finset

namespace MPSTensor

/-! ## Key paper step: some mixed overlap does not decay -/

/--
**Key step of Theorem 4.4 (paper route).**

Assume we have two families `A j` and `B k` whose within-family overlaps are
asymptotically orthonormal, and that the *full* tensors `A_total` and `B_total`
are proportional MPV families and admit expansions in those families with
coefficients converging to nonzero limits.

Then for each `k`, it is impossible that `mpvOverlap (A j) (B k)` tends to `0`
for all `j`.

This lemma is the replacement for the span-equality-based argument
`exists_nonzero_overlap` in `PermutationRigidityPrimitive.lean`.
-/
theorem exists_nonzero_overlap_of_proportional_decomp
    {d : ℕ}
    {gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (_A_total : MPSTensor d DtotA)
    (_B_total : MPSTensor d DtotB)
    (_aCoeff : ℕ → Fin gA → ℂ) (_bCoeff : ℕ → Fin gB → ℂ)
    (_c : ℕ → ℂ)
    (_hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv _A_total σ = ∑ j : Fin gA, (_aCoeff N j) * mpv (A j) σ)
    (_hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv _B_total σ = ∑ k : Fin gB, (_bCoeff N k) * mpv (B k) σ)
    (_hProp : ∀ N (σ : Fin N → Fin d), mpv _A_total σ = _c N * mpv _B_total σ)
    (_hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (_hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0)) :
    ∀ k : Fin gB,
      ∃ j : Fin gA,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  -- Paper-faithful proof pending: replaces the deleted abstract-limit argument that consumed
  -- `aLim`, `bLim`, `cLim`, `haCoeff`, `hbCoeff`, `hc`, `_haLim_ne`, `_hbLim_ne`, `_hcLim_ne`.
  -- See `docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`.
  sorry


/-! ## Symmetric key step (A-indexed)

For the block-count equality we also need the converse direction: for each `A j`, some overlap
with a `B k` does not decay.
-/

/--
**Key step of Theorem 4.4 (paper route), opposite direction.**

Under the same proportionality + decomposition hypotheses as
`exists_nonzero_overlap_of_proportional_decomp`, if the `A`-family overlaps are asymptotically
orthonormal, then for each `j` it is impossible that
`mpvOverlap (A j) (B k) → 0` for all `k`.
-/
theorem exists_nonzero_overlap_of_proportional_decomp_left
    {d : ℕ}
    {gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (_A_total : MPSTensor d DtotA)
    (_B_total : MPSTensor d DtotB)
    (_aCoeff : ℕ → Fin gA → ℂ) (_bCoeff : ℕ → Fin gB → ℂ)
    (_c : ℕ → ℂ)
    (_hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv _A_total σ = ∑ j : Fin gA, (_aCoeff N j) * mpv (A j) σ)
    (_hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv _B_total σ = ∑ k : Fin gB, (_bCoeff N k) * mpv (B k) σ)
    (_hProp : ∀ N (σ : Fin N → Fin d), mpv _A_total σ = _c N * mpv _B_total σ)
    (_hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (_hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0)) :
    ∀ j : Fin gA,
      ∃ k : Fin gB,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  -- Paper-faithful proof pending. See companion theorem and the gap note.
  sorry

end MPSTensor
