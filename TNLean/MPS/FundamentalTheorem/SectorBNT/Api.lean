/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.FundamentalTheorem.SectorBNT.CesaroNonDecay
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
* `SectorDecomposition.norm_coeff_le_copies_of_norm_weight_le_one` — bound
  the sector coefficient by the multiplicity when every copy has unit-or-less
  modulus (CPSV16 lines 287–301 with the optional normalization convention
  of lines 217–246).
* `IsBNTCanonicalForm.cross_overlap_basis_tendsto_zero` — cross-overlap
  between distinct basis blocks decays, dispatched by bond-dimension equality
  (CPSV16 lines 1080–1091; CPSV16 lines 264–279).
* `IsBNTCanonicalForm.combined_family_eventually_li` — combined-family
  eventual linear independence for two BNT canonical forms
  with mutually vanishing cross-overlaps (CPSV16 corollary Lem1,
  lines 1121–1132; CPSV21 line 1850 BNT linear-independence input).
* `IsBNTCanonicalForm.norm_coeff_le_copies` — the structural-field reading
  of the multiplicity bound (CPSV16 line 246 via `weight_norm_le_one`).
* `IsBNTCanonicalForm.weight_unit_exists_of_struct` — the global
  unit-modulus witness re-stated for direct access by downstream callers (CPSV16 line 246).
* `IsBNTCanonicalForm.coeff_not_tendsto_zero_at_block` — the Cesàro
  non-decay reading of the line 1182 projection step, with the per-block
  unit-modulus witness supplied as an explicit theorem-level hypothesis
  `hUnit : ∃ q, ‖μ_{j₀,q}‖ = 1`.

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

/-- **Sector coefficient bound by multiplicity** under a unit-or-less
modulus hypothesis on every copy weight.

CPSV16 lines 287–301 give the raw coefficient `∑_q (μ_{j,q})^N`.  When
the optional global normalization of CPSV16 lines 217–246 (or any
other unit-bound on the raw weights) is in force, `‖μ_{j,q}‖ ≤ 1` for
every `q`, and the triangle inequality bounds the norm of the
coefficient by the multiplicity `r_j`.  This lemma does not require the
full `HasEqualModulusWeightLayer` factorisation; it only consumes a
direct bound on the raw weights. -/
lemma norm_coeff_le_copies_of_norm_weight_le_one
    (P : SectorDecomposition d) (N : ℕ) (j : Fin P.basisCount)
    (hWeightLe : ∀ q : Fin (P.copies j), ‖P.weight j q‖ ≤ 1) :
    ‖P.coeff N j‖ ≤ (P.copies j : ℝ) := by
  classical
  have hsum :
      ‖∑ q : Fin (P.copies j), (P.weight j q) ^ N‖
        ≤ ∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖ :=
    norm_sum_le _ _
  have hPow : ∀ q : Fin (P.copies j),
      ‖(P.weight j q) ^ N‖ ≤ 1 := by
    intro q
    have hbound := hWeightLe q
    have hnn : (0 : ℝ) ≤ ‖P.weight j q‖ := norm_nonneg _
    have hpow : ‖P.weight j q‖ ^ N ≤ 1 ^ N :=
      pow_le_pow_left₀ hnn hbound N
    simpa [norm_pow, one_pow] using hpow
  have hSumBound :
      (∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖)
        ≤ ∑ _q : Fin (P.copies j), (1 : ℝ) :=
    Finset.sum_le_sum (fun q _ => hPow q)
  have hCard :
      (∑ _q : Fin (P.copies j), (1 : ℝ)) = (P.copies j : ℝ) := by
    simp
  calc
    ‖P.coeff N j‖
        = ‖∑ q : Fin (P.copies j), (P.weight j q) ^ N‖ := by
          rw [coeff_eq_sum_weight_pow]
    _ ≤ ∑ q : Fin (P.copies j), ‖(P.weight j q) ^ N‖ := hsum
    _ ≤ ∑ _q : Fin (P.copies j), (1 : ℝ) := hSumBound
    _ = (P.copies j : ℝ) := hCard

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

/-- **Coefficient norm bound under the line-246 normalization.**

A direct consequence of the structural field `weight_norm_le_one`
(CPSV16 §II.C line 246): the sector coefficient
`P.coeff N j = ∑_q (P.weight j q)^N` is bounded in modulus by the
multiplicity `P.copies j`.  This is the structural-field reading of the
prior explicit-hypothesis lemma
`SectorDecomposition.norm_coeff_le_copies_of_norm_weight_le_one`. -/
lemma norm_coeff_le_copies
    (h : IsBNTCanonicalForm P) (N : ℕ) (j : Fin P.basisCount) :
    ‖P.coeff N j‖ ≤ (P.copies j : ℝ) :=
  P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j)
    (hWeightLe := h.weight_norm_le_one j)

/-- **Global unit-modulus weight witness from the canonical-form normalization.**

Re-states the structural field `weight_unit_exists` (CPSV16 §II.C
line 246) for direct access by downstream callers that want to extract a
global unit-modulus weight without depending on the structure layout. -/
lemma weight_unit_exists_of_struct (h : IsBNTCanonicalForm P) :
    ∃ (j : Fin P.basisCount) (q : Fin (P.copies j)),
      ‖P.weight j q‖ = 1 := h.weight_unit_exists

/-- **Per-block coefficient non-decay.**

For a user-supplied sector `j₀ : Fin P.basisCount` carrying a unit-modulus
copy witness `hUnit : ∃ q, ‖P.weight j₀ q‖ = 1`, the power-sum coefficient
`P.coeff N j₀ = ∑_q (P.weight j₀ q)^N` does **not** tend to `0` as
`N → ∞`.

The per-block unit-modulus hypothesis `hUnit` is taken as an explicit
theorem-level argument rather than a structural field of
`IsBNTCanonicalForm`: CPSV16 §II.C line 246 records only the *global*
normalization $\exists j, \exists q, |\mu_{j,q}| = 1$, while CPSV21
Section IV.A uses Definition 4.2 (lines 1846–1850) for the BNT basis and
the display at lines 1864–1884 for the two-layer expansion.  It normalizes
the spectral radius of the *basis* tensors, not the copy coefficients
$\mu_{j,q}$.  The per-block witness is implicit in CPSV16 Appendix MPV proof,
line 1182's projection step and is
therefore exposed here as a per-theorem hypothesis.

Paper anchor: CPSV16 appendix power-sum lemma, lines 1155--1163, and
CPSV16 Appendix MPV proof, line 1182 (per-block
projection step). -/
theorem coeff_not_tendsto_zero_at_block
    (h : IsBNTCanonicalForm P) (j₀ : Fin P.basisCount)
    (hUnit : ∃ q : Fin (P.copies j₀), ‖P.weight j₀ q‖ = 1) :
    ¬ Tendsto (fun N : ℕ => P.coeff N j₀) atTop (𝓝 0) := by
  have h_le : ∀ q : Fin (P.copies j₀), ‖P.weight j₀ q‖ ≤ 1 :=
    h.weight_norm_le_one j₀
  have hAnal := CesaroNonDecay.sum_pow_not_tendsto_zero_of_unit_modulus
    (P.weight j₀) h_le hUnit
  intro hTend
  exact hAnal hTend

/-- **Cesàro converse: coefficient decays when every weight is strictly subnormal.**

For any sector `j : Fin P.basisCount` such that every copy weight satisfies
`‖P.weight j q‖ < 1` (strictly), the power-sum coefficient
`P.coeff N j = ∑_q (P.weight j q)^N` tends to `0` as `N → ∞`.

This is the **converse** of `coeff_not_tendsto_zero_at_block`: under the
CPSV16 §II.C line-246 normalization (`weight_norm_le_one`), if **no** copy of
sector `j` carries a unit-modulus weight, then the sector's coefficient
decays exponentially.  The argument is elementary: each summand
`(P.weight j q)^N` tends to `0` because the closed-unit-disk strict
inequality `‖w‖ < 1` makes the geometric sequence vanish, and a finite sum
of vanishing sequences vanishes.

Paper anchor: CPSV16 §II.C line 246 + line 1244 (the convergence half of
the line-246 dichotomy: unit-modulus weights survive; subnormal weights
decay).  After the Phase D per-block normalization this lemma is no longer
on the FT critical path, but it remains a useful peripheral/subnormal-sector
estimate. -/
theorem coeff_tendsto_zero_of_all_weights_subnorm
    (_h : IsBNTCanonicalForm P) (j : Fin P.basisCount)
    (hSubnorm : ∀ q : Fin (P.copies j), ‖P.weight j q‖ < 1) :
    Tendsto (fun N : ℕ => P.coeff N j) atTop (𝓝 0) := by
  classical
  -- Unfold `P.coeff N j = ∑_q (P.weight j q)^N` and apply `tendsto_finset_sum`.
  have hEq : ∀ N : ℕ, P.coeff N j
      = ∑ q : Fin (P.copies j), (P.weight j q) ^ N := fun N => rfl
  refine Filter.Tendsto.congr (fun N => (hEq N).symm) ?_
  -- Each term `(P.weight j q)^N → 0` by `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`.
  have hSumZero :
      Tendsto (fun N : ℕ => ∑ q : Fin (P.copies j), (P.weight j q) ^ N)
        atTop (𝓝 (∑ _q : Fin (P.copies j), (0 : ℂ))) := by
    refine tendsto_finset_sum (Finset.univ : Finset (Fin (P.copies j))) ?_
    intro q _
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hSubnorm q)
  simpa using hSumZero

end IsBNTCanonicalForm

end MPSTensor
