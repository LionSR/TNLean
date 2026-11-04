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
`docs/paper-gaps/lvv13_runtime_ground_energy.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- **The Gaussian filter approximants of Huang's construction.** At each node of the
energy mesh, the Gaussian approximant of the positive chain with Huang's variance, time
window and accuracy. Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. -/
noncomputable def huangFilterApproximant {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (h0 : ∀ i, 0 ≤ h i)
    (c Delta : ℝ) (j : Fin (huangEnergyCount c Delta L)) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  positiveChainGaussianApproximant hq h h0 (huangFilterVariance c Delta L)
    (timeMeshNode L (huangEnergyMesh c Delta L) j) (huangFilterTime c Delta L)
    (huangFilterEta c L) (huangFilterEta c L)

/-- Each Huang approximant has cut rank at most the uniform filter rank bound at every
cut, and lies within `3 η` of the Gaussian filter at its mesh node. Huang,
arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. -/
theorem huangFilterApproximant_spec {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) (j : Fin (huangEnergyCount c Delta L)) :
    (∀ cut, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut)
        (huangFilterApproximant hq h h0 c Delta j)) ≤ huangFilterRankBound q c Delta L) ∧
    ‖GaussianFilter.gaussianIntertwiner (huangFilterVariance c Delta L)
      ((∑ i, h i) - (timeMeshNode L (huangEnergyMesh c Delta L) j : ℂ) • 1) 0 1 -
        huangFilterApproximant hq h h0 c Delta j‖ ≤ 3 * huangFilterEta c L := by
  classical
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hη := (huangFilterEta_bounds hc L).1
  have hT := (huangFilterTime_pos hc hDelta L).le
  have hδ := (huangEnergyMesh_bounds hc hDelta L).1
  obtain ⟨-, hN, herror, hrank⟩ := positiveChainGaussianApproximant_spec
    hq h hs h0 h1 (huangFilterVariance c Delta L)
    (timeMeshNode L (huangEnergyMesh c Delta L) j) hT hη hη
  have hE : |timeMeshNode L (huangEnergyMesh c Delta L) j| ≤ (L : ℝ) :=
    abs_le.mpr (timeMeshNode_mem hL hδ j)
  have hNbound : positiveChainGaussianSampleCount h (timeMeshNode L (huangEnergyMesh c Delta L) j)
      (huangFilterTime c Delta L) (huangFilterEta c L) ≤ huangFilterSampleCount c Delta L := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact (hN.trans (by gcongr; linarith)).trans (Nat.le_ceil _)
  refine ⟨fun cut ↦ (hrank cut).trans (Nat.mul_le_mul_right _ hNbound), ?_⟩
  have htail := huangFilterTime_tail_le hc hDelta L
  unfold huangFilterApproximant
  linarith

/-- A finite family of approximate Gaussian filters over the energy mesh, with uniform
cut-rank bounds: the existence form of `huangFilterApproximant_spec`. Huang,
arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. -/
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
          3 * huangFilterEta c L :=
  ⟨huangFilterApproximant hq h h0 c Delta,
    fun j ↦ (huangFilterApproximant_spec hq h hs h0 h1 hc hDelta j).1,
    fun j ↦ (huangFilterApproximant_spec hq h hs h0 h1 hc hDelta j).2⟩

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

/-- For every gapped ground pair, one Huang approximant is within `4 η` of a positive
multiple `a |Γ⟩⟨Γ|`, `1/2 ≤ a ≤ 1`, of the ground projection. Huang, arXiv:1406.6355v6,
Section 5.4, Lemmas 18--19. -/
theorem exists_huangFilterApproximant_near_ground {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta)
    (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (hΓ : ‖Γ‖ = 1)
    (hHΓ : (∑ i, h i) *ᵥ WithLp.ofLp Γ = (E₀ : ℂ) • WithLp.ofLp Γ)
    (hgap : ((∑ i, h i) - (E₀ : ℂ) • 1 - (Delta : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef) :
    ∃ (j : Fin (huangEnergyCount c Delta L)) (a : ℝ),
      1 / 2 ≤ a ∧ a ≤ 1 ∧
      ‖huangFilterApproximant hq h h0 c Delta j -
        (a : ℂ) • vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
          4 * huangFilterEta c L := by
  have hQerror (j : Fin (huangEnergyCount c Delta L)) :=
    (huangFilterApproximant_spec hq h hs h0 h1 hc hDelta j).2
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
  have htriangle := (norm_sub_le_norm_sub_add_norm_sub (huangFilterApproximant hq h h0 c Delta j)
    (GaussianFilter.gaussianIntertwiner (huangFilterVariance c Delta L)
      ((∑ i, h i) - (E : ℂ) • 1) 0 1)
    ((a : ℂ) • vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).trans
      (add_le_add hfirst (hspec.trans hsuppression))
  simpa only [show 3 * huangFilterEta c L + huangFilterEta c L =
    4 * huangFilterEta c L by ring] using htriangle


/-- A finite family of approximate Gaussian filters, one of which is close to a multiple
of the ground projection for every gapped ground pair: the existence form of
`huangFilterApproximant_spec` and `exists_huangFilterApproximant_near_ground`. Huang,
arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. -/
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
            4 * huangFilterEta c L :=
  ⟨huangFilterApproximant hq h h0 c Delta,
    fun j ↦ (huangFilterApproximant_spec hq h hs h0 h1 hc hDelta j).1,
    fun E₀ Γ hΓ hHΓ hgap ↦
      exists_huangFilterApproximant_near_ground hq h hs h0 h1 hc hDelta E₀ Γ hΓ hHΓ hgap⟩

end TNLean.MPS.AreaLaw
