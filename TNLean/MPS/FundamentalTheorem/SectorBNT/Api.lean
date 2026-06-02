/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.BNT.Basic
import TNLean.MPS.Overlap.CastDecay

/-!
# Auxiliary lemmas for the BNT canonical-form predicate `IsBNTCanonicalForm`

Elementary lemmas for the predicate `IsBNTCanonicalForm` introduced in
`SectorBNT/Basic.lean`.  All lemmas here use the **raw** sector coefficients
`P.weight j q` and `P.coeff N j = ∑_q (P.weight j q)^N`; no equal-modulus
factorisation is assumed.  The optional `HasEqualModulusWeightLayer`
specialisation lives in `SectorBNT/EqualModulus.lean` and is intentionally
not imported here.

## Contents

* `SectorDecomposition.coeff_eq_sum_weight_pow` — definitional unfolding
  `P.coeff N j = ∑_q (P.weight j q)^N`
  (CPSV16 lines 287–301; CPSV21 lines 1864–1884).
* `IsBNTCanonicalForm.cross_overlap_basis_tendsto_zero` — cross-overlap
  between distinct basis blocks decays, dispatched by bond-dimension equality
  (CPSV16 lines 1080–1091; CPSV16 lines 264–279).
* `IsBNTCanonicalForm.combined_family_eventually_li` — combined-family
  eventual linear independence for two BNT canonical forms
  with mutually vanishing cross-overlaps (CPSV16 corollary Lem1,
  lines 1121–1132; CPSV21 line 1850 BNT linear-independence input).
* `IsBNTCanonicalForm.weight_unit_exists_of_struct` — the global
  unit-modulus witness re-stated for direct access by downstream callers
  (CPSV16 line 246).

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608.
  Lines 217–246 (optional global modulus normalization), 264–279
  (gauge-phase sector grouping), 287–301 (raw two-layer BNT display),
  349–352 (thm1), 1080–1091 (normal-tensor overlap dichotomy),
  1121–1132 (Lem1, combined-family eventual linear independence).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127.
  Lines 1846–1884 (BNT and two-layer BNT decomposition with raw
  `μ_{j,q}` and per-block spectral-radius-one normalization).
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

namespace SectorDecomposition

/-- **Raw two-layer sector coefficient identity** (definitional).

CPSV16 lines 287–301 and CPSV21 lines 1864–1884 specify the BNT sector
coefficient as the raw power sum `∑_q (μ_{j,q})^N` over the copies of
the `j`-th basis block.  In our formalisation `P.coeff N j` is exactly
this sum, so the identity is by `rfl` after unfolding the abbreviations. -/
lemma coeff_eq_sum_weight_pow (P : SectorDecomposition d)
    (N : ℕ) (j : Fin P.basisCount) :
    P.coeff N j = ∑ q : Fin (P.copies j), (P.weight j q) ^ N := rfl

end SectorDecomposition

namespace IsBNTCanonicalForm

variable {P Q : SectorDecomposition d}

/-- **Cross-overlap between distinct basis blocks decays.**

For any two distinct basis indices `j ≠ k` of a BNT canonical form
satisfying `IsBNTCanonicalForm`, the MPV overlap
`mpvOverlap (P.basis j) (P.basis k) N` tends to `0` as `N → ∞`.

The dispatch follows CPSV16 lines 1080–1091 (the normal-tensor overlap
dichotomy):

* if `P.basisDim j ≠ P.basisDim k`, decay follows from
  `mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`;
* if the bond dimensions agree, the `basis_distinct` field of
  `IsBNTCanonicalForm` rules out gauge-phase equivalence in the
  cast-compatible shape, and decay follows from
  `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`
  (CPSV16 lines 264–279 gauge-phase sector grouping). -/
lemma cross_overlap_basis_tendsto_zero
    (h : IsBNTCanonicalForm P) {j k : Fin P.basisCount} (hjk : j ≠ k) :
    Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j) (P.basis k) N)
      atTop (𝓝 0) := by
  haveI hjpos : NeZero (P.basisDim j) := ⟨(h.basis_dim_pos j).ne'⟩
  haveI hkpos : NeZero (P.basisDim k) := ⟨(h.basis_dim_pos k).ne'⟩
  by_cases hdim : P.basisDim j = P.basisDim k
  · exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      (hdim := hdim) (A := P.basis j) (B := P.basis k)
      (hA_irr := h.basis_irreducible j)
      (hB_irr := h.basis_irreducible k)
      (hA_norm := h.basis_left_canonical j)
      (hB_norm := h.basis_left_canonical k)
      (hNot := h.basis_distinct j k hjk hdim)
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
      (P.basis j) (P.basis k)
      (h.basis_irreducible j) (h.basis_irreducible k)
      (h.basis_left_canonical j) (h.basis_left_canonical k)
      hdim

/-- **Combined-family eventual linear independence** for two BNT canonical
forms with mutually vanishing cross-overlaps.

This is the instantiation of corollary Lem1 (CPSV16 lines 1121–1132): once the
cross-overlaps between the two BNT families vanish, the union of basis MPV
states is linearly independent for all sufficiently large lengths.  CPSV21
line 1850 states the same linear-independence input as part of the BNT
definition.

The proof feeds the per-family normalised self-overlaps, the
within-family cross-decay from `cross_overlap_basis_tendsto_zero`, and
the inter-family decay hypothesis into
`eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal`
(`TNLean.MPS.BNT.Basic`, line 195). -/
lemma combined_family_eventually_li
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hAB : ∀ (j : Fin P.basisCount) (k : Fin Q.basisCount),
      Tendsto (fun N : ℕ =>
        mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0)) :
    ∀ᶠ N in atTop,
      LinearIndependent ℂ
        (Sum.elim
          (fun j : Fin P.basisCount => mpvState (d := d) (P.basis j) N)
          (fun k : Fin Q.basisCount => mpvState (d := d) (Q.basis k) N)) :=
  eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal
    (A := P.basis) (B := Q.basis)
    (hA_self := hP.basis_normalized_self_overlap)
    (hA_off := fun _ _ hij => hP.cross_overlap_basis_tendsto_zero hij)
    (hB_self := hQ.basis_normalized_self_overlap)
    (hB_off := fun _ _ hk => hQ.cross_overlap_basis_tendsto_zero hk)
    (hAB := hAB)

/-- **Global unit-modulus weight witness from the canonical-form normalization.**

Re-states the structural field `weight_unit_exists` (CPSV16 §II.C
line 246) for direct access by downstream callers that want to extract a
global unit-modulus weight without depending on the structure layout. -/
lemma weight_unit_exists_of_struct (h : IsBNTCanonicalForm P) :
    ∃ (j : Fin P.basisCount) (q : Fin (P.copies j)),
      ‖P.weight j q‖ = 1 := h.weight_unit_exists

end IsBNTCanonicalForm

end MPSTensor
