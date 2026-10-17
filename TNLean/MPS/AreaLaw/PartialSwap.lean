/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Dist
import TNLean.MPS.AreaLaw.DoubledHamiltonian
import TNLean.MPS.AreaLaw.BoundaryCounting
import TNLean.PEPS.Approximation.SheetSwapConjugateSupport

/-!
# The partial-swap perturbation on a chain

Keep the two replica labels of every interaction. Each conjugation difference
has the original support and norm at most `2J`. The interior terms cancel in
pairs; the remaining labels number at most `N_R` times the boundary cardinality,
where `N_R = 2 * 2^(2R)`. Zero local dimension and empty boundaries are included.

## Main results

* `ChainHamiltonian.partialSwap_term_difference_spec`: support, Hermiticity
  and the `2J` bound for each separately labelled replica difference.
* `ChainHamiltonian.partialSwap_difference_eq_sum_crossing`: the exact global
  decomposition and the number of retained labels.
* `ChainHamiltonian.partialSwap_boundary_spec`: support near actual boundary
  edges and the global norm bound with the original interaction coefficient.

**Scope restriction (contiguous chains):** The physical sites are `Fin L`.
The broader source domain may have gaps; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines
355–363, with the crossing count from `part1_arealaw.tex`, `eq:count`.
No spectral or ground-state transport is asserted here.
-/

open Matrix QuantumCircuit
open TNLean.PEPS.EncodedFrame
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Each labelled replica difference is Hermitian, supported on its original
interaction support, and of norm at most `2J`. Source: TNLean note,
`part2a_mps_information.tex`, lines 359–362. -/
theorem ChainHamiltonian.partialSwap_term_difference_spec
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J)
    (D : Finset (Fin L)) (X : ChainSupport L R) (b : Bool) :
    let e := QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (TNLean.PEPS.EncodedFrame.sheetSwapOp q D)
    let T := Matrix.reindex e e
      (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
        else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
    let K := F * T * Fᴴ - T
    Entropy.IsSupportedOn (n := fun _ ↦ q * q) K X.1 ∧ K.IsHermitian ∧ ‖K‖ ≤ 2 * J := by
  classical
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  have hterm := mem_supportedOperators_of_isSupportedOn (h.supported X)
  have hone := one_mem_supportedOperators (d := q) (X.1 : Set (Fin L))
  have hF : ‖F‖ ≤ 1 := by
    simpa only [F, Matrix.l2_opNorm_reindex_equiv] using norm_sheetSwapOp_le_one (q := q) D
  have hgeneral (U V : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hU : U ∈ supportedOperators q (X.1 : Set (Fin L)))
      (hV : V ∈ supportedOperators q (X.1 : Set (Fin L)))
      (hUVherm : (U ⊗ₖ V).IsHermitian) (hUVnorm : ‖U ⊗ₖ V‖ ≤ J) :
      let T := Matrix.reindex e e (U ⊗ₖ V)
      let K := F * T * Fᴴ - T
      Entropy.IsSupportedOn (n := fun _ ↦ q * q) K X.1 ∧ K.IsHermitian ∧ ‖K‖ ≤ 2 * J := by
    have hT : Matrix.reindex e e (U ⊗ₖ V) ∈
        supportedOperators (q * q) (X.1 : Set (Fin L)) := by
      simpa only [Set.union_self] using reindex_kronecker_mem_supportedOperators hU hV
    refine ⟨isSupportedOn_of_mem_supportedOperators
      ((supportedOperators (q * q) (X.1 : Set (Fin L))).sub_mem
        (reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators D X.1 hU hV) hT), ?_, ?_⟩
    · have hTherm := hUVherm.reindex e
      exact (Matrix.isHermitian_mul_mul_conjTranspose F hTherm).sub hTherm
    · have hTnorm : ‖Matrix.reindex e e (U ⊗ₖ V)‖ ≤ J := by
        simpa only [Matrix.l2_opNorm_reindex_equiv] using hUVnorm
      have hconj : ‖F * Matrix.reindex e e (U ⊗ₖ V) * Fᴴ‖ ≤ J := by
        simpa only [one_mul, mul_one] using
          norm_mul_le_of_le (norm_mul_le_of_le hF hTnorm)
            ((Matrix.l2_opNorm_conjTranspose F).trans_le hF)
      exact (norm_sub_le _ _).trans ((add_le_add hconj hTnorm).trans_eq (by ring))
  cases b
  · apply hgeneral (h.term X) 1 hterm hone
    · change (h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))ᴴ = _
      rw [conjTranspose_kronecker, h.hermitian X, conjTranspose_one]
    · exact (Matrix.l2_opNorm_kronecker_one_le _).trans (h.norm_le X)
  · apply hgeneral 1 (h.term X) hone hterm
    · change ((1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X)ᴴ = _
      rw [conjTranspose_kronecker, h.hermitian X, conjTranspose_one]
    · exact (Matrix.l2_opNorm_one_kronecker_le _).trans (h.norm_le X)

/-- The actual partial-swap perturbation is the sum of its crossing replica
differences, with the printed boundary count. Source: TNLean note,
`part2a_mps_information.tex`, lines 355–363. -/
theorem ChainHamiltonian.partialSwap_difference_eq_sum_crossing
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J) (D : Finset (Fin L)) :
    let e := QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (TNLean.PEPS.EncodedFrame.sheetSwapOp q D)
    let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
      (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
        else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
    let C := Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
    (F * h.doubled.operator * Fᴴ - h.doubled.operator =
      ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b)) ∧
      C.card * 2 ≤ chainCrossConst R * (boundaryEdges L D).card := by
  classical
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  let C := Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
  change (F * h.doubled.operator * Fᴴ - h.doubled.operator =
    ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b)) ∧
      C.card * 2 ≤ chainCrossConst R * (boundaryEdges L D).card
  have hpair (X : ChainSupport L R) : h.doubled.term X = ∑ b : Bool, T X b := by
    rw [Fintype.sum_bool]
    change Matrix.reindex e e (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X) =
      Matrix.reindex e e (1 ⊗ₖ h.term X) + Matrix.reindex e e (h.term X ⊗ₖ 1)
    simpa only [Matrix.coe_reindexAddEquiv] using
      ((Matrix.reindexAddEquiv ℂ e e).map_add (h.term X ⊗ₖ 1) (1 ⊗ₖ h.term X)).trans
        (add_comm _ _)
  have hsum : h.doubled.operator = ∑ X, ∑ b : Bool, T X b :=
    Finset.sum_congr rfl (fun X _ ↦ hpair X)
  let δ : Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ →ₗ[ℂ]
      Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ :=
    LinearMap.mulLeftRight ℂ (F, Fᴴ) - LinearMap.id
  have hcancel (X : ChainSupport L R) (hX : X ∉ C) : δ (∑ b : Bool, T X b) = 0 := by
    have hnot : ¬ ((∃ v ∈ X.1, v ∈ D) ∧ ∃ v ∈ X.1, v ∉ D) := by
      simpa only [C, Entropy.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]
        using hX
    have hside : (X.1 : Set (Fin L)) ⊆ (D : Set (Fin L)) ∨
        Disjoint (X.1 : Set (Fin L)) (D : Set (Fin L)) := by
      rcases not_and_or.mp hnot with hi | ho
      · exact Or.inr (Finset.disjoint_coe.mpr
          (Finset.disjoint_left.mpr (fun x hx hxD ↦ hi ⟨x, hx, hxD⟩)))
      · exact Or.inl (Finset.coe_subset.mpr (by
          intro x hx
          by_contra hxD
          exact ho ⟨x, hx, hxD⟩))
    rw [← hpair X]
    change F * Matrix.reindex e e (doubledHamiltonian (h.term X)) * Fᴴ -
      Matrix.reindex e e (doubledHamiltonian (h.term X)) = 0
    apply sub_eq_zero.mpr
    simpa only [F, Matrix.conjTranspose_submatrix, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv] using
      congrArg (Matrix.reindex e e)
        (sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
          (mem_supportedOperators_of_isSupportedOn (h.supported X)) hside)
  refine ⟨?_, ?_⟩
  · change δ h.doubled.operator = ∑ X ∈ C, ∑ b : Bool, δ (T X b)
    rw [hsum, map_sum]
    simp only [map_sum]
    symm
    apply Finset.sum_subset (Finset.subset_univ C)
    intro X _ hX
    simpa only [map_sum] using hcancel X hX
  · calc
      C.card * 2 ≤ (2 ^ (2 * R) * (boundaryEdges L D).card) * 2 :=
        Nat.mul_le_mul_right 2 (card_crossingTerms_le_mul_card_boundaryEdges L R D)
      _ = chainCrossConst R * (boundaryEdges L D).card := by
        unfold chainCrossConst
        ring

/-- The actual perturbation is supported in the union of crossing supports,
which lies within range of an actual boundary edge, with the original `J`
coefficient in its norm bound. Source: TNLean note,
`part2a_mps_information.tex`, lines 355–363. -/
theorem ChainHamiltonian.partialSwap_boundary_spec
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J)
    (D : Finset (Fin L)) :
    let e := QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (TNLean.PEPS.EncodedFrame.sheetSwapOp q D)
    let C := Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
    let Z := C.biUnion (fun X ↦ X.1)
    let K := F * h.doubled.operator * Fᴴ - h.doubled.operator
    Entropy.IsSupportedOn (n := fun _ ↦ q * q) K Z ∧
      (∀ x ∈ Z, ∃ p ∈ boundaryEdges L D, Nat.dist x.val p ≤ R) ∧
      ‖K‖ ≤ 2 * J * (chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ) := by
  classical
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  let C := Entropy.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
  let Z := C.biUnion (fun X ↦ X.1)
  let K := F * h.doubled.operator * Fᴴ - h.doubled.operator
  change Entropy.IsSupportedOn (n := fun _ ↦ q * q) K Z ∧
    (∀ x ∈ Z, ∃ p ∈ boundaryEdges L D, Nat.dist x.val p ≤ R) ∧
      ‖K‖ ≤ 2 * J * (chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ)
  have hzone : ∀ x ∈ Z, ∃ p ∈ boundaryEdges L D, Nat.dist x.val p ≤ R := by
    intro x hx
    obtain ⟨X, hXC, hxX⟩ := Finset.mem_biUnion.mp hx
    have hsplit : (∃ v ∈ X.1, v ∈ D) ∧ ∃ v ∈ X.1, v ∉ D := by
      simpa only [C, Entropy.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]
        using hXC
    obtain ⟨p, hp, hwin⟩ := X.2.exists_boundary_window_of_split hsplit
    refine ⟨p, hp, ?_⟩
    have hxwin := mem_interval.mp (hwin hxX)
    simp only [Nat.dist]
    omega
  let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  obtain ⟨hsum, hcount⟩ := h.partialSwap_difference_eq_sum_crossing D
  change K = ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b) at hsum
  have hsupp : Entropy.IsSupportedOn (n := fun _ ↦ q * q) K Z := by
    apply isSupportedOn_of_mem_supportedOperators
    rw [hsum]
    apply Submodule.sum_mem
    intro X hXC
    apply Submodule.sum_mem
    intro b _
    apply supportedOperators_mono
      (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem (fun X ↦ X.1) hXC))
    exact mem_supportedOperators_of_isSupportedOn
      (h.partialSwap_term_difference_spec D X b).1
  have hnorm : ‖K‖ ≤ (C.card : ℝ) * (2 * (2 * J)) := by
    rw [hsum]
    calc
      _ ≤ ∑ X ∈ C, ‖∑ b : Bool, (F * T X b * Fᴴ - T X b)‖ := norm_sum_le _ _
      _ ≤ ∑ X ∈ C, ∑ b : Bool, ‖F * T X b * Fᴴ - T X b‖ :=
        Finset.sum_le_sum (fun X _ ↦ norm_sum_le _ _)
      _ ≤ ∑ _X ∈ C, ∑ _b : Bool, 2 * J := by
        apply Finset.sum_le_sum
        intro X _
        exact Finset.sum_le_sum (fun b _ ↦ (h.partialSwap_term_difference_spec D X b).2.2)
      _ = _ := by simp
  refine ⟨hsupp, hzone, ?_⟩
  by_cases hL : L = 0
  · have hb : boundaryEdges L D = ∅ := by simp [boundaryEdges, hL]
    have hc : C.card = 0 := by
      change C.card * 2 ≤ chainCrossConst R * (boundaryEdges L D).card at hcount
      rw [hb] at hcount
      simp only [Finset.card_empty, mul_zero] at hcount
      omega
    simpa only [hc, Nat.cast_zero, zero_mul, hb, Finset.card_empty, mul_zero] using hnorm
  · let x : Fin L := ⟨0, Nat.pos_of_ne_zero hL⟩
    let X₀ : ChainSupport L R := ⟨{x}, by simp [IsChainSupport]⟩
    have hJ : 0 ≤ J := (norm_nonneg (h.term X₀)).trans (h.norm_le X₀)
    have hc : (C.card : ℝ) * 2 ≤
        (chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ) := by
      exact_mod_cast hcount
    calc
      ‖K‖ ≤ (C.card : ℝ) * (2 * (2 * J)) := hnorm
      _ = (2 * J) * ((C.card : ℝ) * 2) := by ring
      _ ≤ (2 * J) * ((chainCrossConst R : ℝ) * ((boundaryEdges L D).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring

end TNLean.MPS.AreaLaw
