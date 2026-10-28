/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.FilterPolynomial
import TNLean.MPS.AreaLaw.Huang.ApproximateEnergyFilter
import TNLean.MPS.AreaLaw.Huang.PhysicalGaussian

/-!
# A finite family of ground filters from a positive nearest-neighbour chain

Choose energy estimates throughout the interval `[-L,L]` and construct the finite
Gaussian approximation at each estimate. The family depends only on the physical
Hamiltonian, gap parameter and precision, before the ground energy or ground vector
is supplied. All its members satisfy one simultaneous operator-Schmidt bound.
For every unit ground vector with the prescribed gap, one member approximates a
positive multiple of its ground projection with amplitude between one half and one.

The precision and rank budgets are the conservative polynomial bounds from
`FilterPolynomial`. No printed sharper dependence on the inverse gap is asserted.
The construction uses Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19,
in place of the energy-dependent power sampler of LVV; see
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A finite family of Gaussian approximants chosen before ground-state data.
Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. -/
theorem exists_positive_chain_filter_family {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) :
    ∃ Q : Fin (huangEnergyCount c Delta L) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (∀ j cut, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (Q j)) ≤
          huangFilterRankBound q c Delta L) ∧
      ∀ j, ‖GaussianFilter.gaussianIntertwiner (huangFilterVariance c Delta L)
        ((∑ i, h i) - (timeMeshNode L (huangEnergyMesh c Delta L) j : ℂ) • 1) 0 1 - Q j‖ ≤
          3 * huangFilterEta c L := by
  classical
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hη := (huangFilterEta_bounds hc L).1
  have hT := (huangFilterTime_pos hc hDelta L).le
  have hδ := (huangEnergyMesh_bounds hc hDelta L).1
  have hex (j : Fin (huangEnergyCount c Delta L)) :
      ∃ Q : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
        (∀ cut, operatorSchmidtRank
          (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) Q) ≤
            huangFilterRankBound q c Delta L) ∧
        ‖GaussianFilter.gaussianIntertwiner (huangFilterVariance c Delta L)
          ((∑ i, h i) - (timeMeshNode L (huangEnergyMesh c Delta L) j : ℂ) • 1) 0 1 - Q‖ ≤
            3 * huangFilterEta c L := by
    obtain ⟨N, Q, -, hN, herror, hrank⟩ := exists_positive_chain_gaussian_approximation
      hq h hs h0 h1 (huangFilterVariance c Delta L)
      (timeMeshNode L (huangEnergyMesh c Delta L) j) hT hη hη
    have hE : |timeMeshNode L (huangEnergyMesh c Delta L) j| ≤ (L : ℝ) :=
      abs_le.mpr (timeMeshNode_mem hL hδ j)
    have hNbound : N ≤ huangFilterSampleCount c Delta L := by
      apply (Nat.cast_le (α := ℝ)).mp
      exact (hN.trans (by gcongr; linarith)).trans (Nat.le_ceil _)
    refine ⟨Q, fun cut ↦ (hrank cut).trans (Nat.mul_le_mul_right _ hNbound), ?_⟩
    have htail := huangFilterTime_tail_le hc hDelta L
    linarith
  choose Q hQ using hex
  exact ⟨Q, fun j ↦ (hQ j).1, fun j ↦ (hQ j).2⟩

/-- An energy eigenvalue of a sum of positive contractions lies in the length window.
Supporting estimate for Huang, arXiv:1406.6355v6, Section 5.4, Lemma 18. -/
theorem abs_eigenvalue_positive_chain_le_length {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1) {E₀ : ℝ}
    (hHΓ : (∑ i, h i) *ᵥ WithLp.ofLp Γ = (E₀ : ℂ) • WithLp.ofLp Γ) :
    |E₀| ≤ (L : ℝ) := by
  have hnorm (i) : ‖h i‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i)
  have hHnorm : ‖∑ i, h i‖ ≤ (L : ℝ) := by
    calc
      _ ≤ ∑ i, ‖h i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin (L - 1), (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hnorm i
      _ = ((L - 1 : ℕ) : ℝ) := by simp
      _ ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 1
  have heig : toEuclideanLin (∑ i, h i) Γ = (E₀ : ℂ) • Γ := by
    apply WithLp.ofLp_injective
    exact hHΓ
  have hn := Entropy.norm_toEuclideanLin_le (∑ i, h i) Γ
  rw [heig, norm_smul, hΓ, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at hn
  exact hn.trans hHnorm

/-- One member of the finite family approximates a positive multiple of the ground
projection, with amplitude at least one half. The family is chosen before the eigenvalue
and ground vector. Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. -/
theorem exists_positive_chain_ground_filter_family {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) :
    ∃ Q : Fin (huangEnergyCount c Delta L) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      (∀ j cut, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) (Q j)) ≤
          huangFilterRankBound q c Delta L) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)), ‖Γ‖ = 1 →
        (∑ i, h i) *ᵥ WithLp.ofLp Γ = (E₀ : ℂ) • WithLp.ofLp Γ →
        ((∑ i, h i) - (E₀ : ℂ) • 1 - (Delta : ℂ) •
          (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef →
        ∃ (j : Fin (huangEnergyCount c Delta L)) (a : ℝ),
          1 / 2 ≤ a ∧ a ≤ 1 ∧
          ‖Q j - (a : ℂ) • vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
            4 * huangFilterEta c L := by
  obtain ⟨Q, hQrank, hQerror⟩ := exists_positive_chain_filter_family hq h hs h0 h1 hc hDelta
  refine ⟨Q, hQrank, ?_⟩
  intro E₀ Γ hΓ hHΓ hgap
  have hE₀ := abs_eigenvalue_positive_chain_le_length h h0 h1 hΓ hHΓ
  obtain ⟨j, hj⟩ := exists_timeMeshNode_abs_sub_le (Nat.cast_nonneg L)
    (huangEnergyMesh_bounds hc hDelta L).1 (abs_le.mp hE₀)
  have haccuracy := huangEnergyMesh_accuracy (E := timeMeshNode L (huangEnergyMesh c Delta L) j)
    (E₀ := E₀) hc hDelta L (by simpa [abs_sub_comm] using hj)
  let E := timeMeshNode L (huangEnergyMesh c Delta L) j
  let a := Real.exp (-(huangFilterVariance c Delta L : ℝ) * (E₀ - E) ^ 2 / 2)
  have hamp := gaussian_ground_amplitude_bounds (E₀ := E₀) (E := E)
    (huangFilterVariance c Delta L) haccuracy.2
  have ha : 1 / 2 ≤ a := by
    exact (by linarith [Real.one_sub_le_exp_neg (1 / 2 : ℝ)] :
      (1 / 2 : ℝ) ≤ Real.exp (-(1 : ℝ) / 2)).trans hamp.1
  refine ⟨j, a, ha, hamp.2, ?_⟩
  have hHerm : (∑ i, h i).IsHermitian :=
    Matrix.isHermitian_sum _ fun i _ ↦ (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian
  have hspec := norm_gaussianIntertwiner_shift_sub_rankOne_le
    (huangFilterVariance c Delta L) hHerm hΓ hHΓ hgap hDelta haccuracy.1
  have hsuppression := huangFilterVariance_suppression_le hc hDelta L
  have hfirst := hQerror j
  rw [norm_sub_rev] at hfirst
  have htriangle := (norm_sub_le_norm_sub_add_norm_sub (Q j)
    (GaussianFilter.gaussianIntertwiner (huangFilterVariance c Delta L)
      ((∑ i, h i) - (E : ℂ) • 1) 0 1)
    ((a : ℂ) • vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).trans
      (add_le_add hfirst (hspec.trans hsuppression))
  simpa only [show 3 * huangFilterEta c L + huangFilterEta c L =
    4 * huangFilterEta c L by ring] using htriangle

end TNLean.MPS.AreaLaw
