/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.CanonicalForm.PhaseClassSectorData
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Spectral.SpectralGapNT

open scoped Matrix BigOperators
open Filter

/-!
# Equal-norm overlap bridge for phase-class BNT data

This file records the overlap/spectral bridge used before the phase-class BNT
construction: if two trace-preserving irreducible blocks have a non-decaying
cross-overlap, then they are gauge-phase equivalent after identifying bond
dimensions.

## Background

The canonical-form reduction produces TP + primitive blocks with
nonzero weights. Equal-modulus blocks are not automatically one BNT sector:
the source BNT construction keeps minimal gauge-phase representatives and
records repeated copies through sector weights. The phase-class construction in
`PhaseClassSectorData.lean` is the source-facing route for that step.

## Important: equal-norm blocks are NOT automatically gauge-phase equivalent

The BNT of a tensor (Cirac--Perez-Garcia--Schuch--Verstraete 2017,
Proposition A.6) is constructed so that all pairs of BNT elements have
*decaying* cross-overlaps. In particular, two BNT elements can
share the same weight norm while being completely independent (non-GPE).  The BNT
already groups gauge-equivalent blocks together; remaining blocks are pairwise
non-gauge-equivalent.  A counter-example shows that the
MPV-level hypothesis `hFullTensor` alone cannot force non-decaying cross-overlaps.

To obtain GPE for equal-norm blocks, one must derive the non-decay property from
structural properties of the decomposition (cyclic-sector origin, Fundamental
Theorem matching, etc.).

## Main local result

* `gaugePhaseEquiv_of_nonDecaying_overlap` — Non-decaying cross-overlap between two
  TP + irreducible blocks implies equal bond dimensions and gauge-phase equivalence.
  Uses the spectral dichotomy from `SpectralGap.lean`.  **Fully proved.**

The BNT sector constructors formerly summarized here now live in
`PhaseClassSectorData.lean`.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017, Lemma A.2]: Overlap dichotomy for Normal Tensors.
- [Cirac--Perez-Garcia--Schuch--Verstraete 2017, Proposition A.6]: BNT construction and minimality.
- [Cirac--Perez-Garcia--Schuch--Verstraete 2017, Definition 2.6, Proposition 2.7]:
  BNT minimality and grouping.
-/

namespace MPSTensor

variable {d : ℕ}

/-! ### Auxiliary cast lemma -/

/-- Casting the bond dimension preserves the primitivity of the transfer map. -/
private lemma isPrimitive_transferMap_cast_dim {d D₁ D₂ : ℕ} (h : D₁ = D₂)
    (A : MPSTensor d D₁) :
    _root_.IsPrimitive (transferMap (d := d) (D := D₂)
      (cast (congr_arg (MPSTensor d) h) A)) ↔
    _root_.IsPrimitive (transferMap (d := d) (D := D₁) A) := by
  subst h; rfl

/-! ### Section 1. Gauge-phase equivalence from non-decaying overlaps -/

/-- **Gauge-phase equivalence from non-decaying cross-overlap.**

If two TP + irreducible blocks have a cross-overlap that does not decay to zero,
then they must have equal bond dimensions and be gauge-phase equivalent.

The proof uses the **spectral dichotomy** (proved in `SpectralGap.lean` and
`SpectralGapNT.lean`): for injective TP-normalized blocks, either
- `spectralRadius(F_{AB}) < 1`, which forces `mpvOverlap A B N → 0`, or
- `spectralRadius(F_{AB}) ≥ 1`, which forces `GaugePhaseEquiv A B`.

If the overlap does NOT decay, we are in the second case. Dimension equality
follows from `mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP` (contrapositive).

This factored-out lemma replaces the previous monolithic placeholder proof in
`gaugePhaseEquiv_of_equal_norm_blocks`. -/
theorem gaugePhaseEquiv_of_nonDecaying_overlap
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_TP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_TP : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hNonDecay : ¬ Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds 0)) :
    ∃ hdim : D₁ = D₂,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- Step 1: Dimension equality (contrapositive of dim-mismatch decay).
  have hdim : D₁ = D₂ := by
    by_contra hne
    exact hNonDecay
      (mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B hA_irr hB_irr hA_TP hB_TP hne)
  refine ⟨hdim, ?_⟩
  -- Step 2: Gauge-phase equivalence (contrapositive of non-GPE decay).
  by_contra hNotGPE
  exact hNonDecay
    (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      hdim A B hA_irr hB_irr hA_TP hB_TP hNotGPE)

end MPSTensor
