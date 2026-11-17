/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.PhysicalPropagation
import TNLean.MPS.AreaLaw.Huang.UnitaryQuadrature
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Finite Gaussian approximation from the original positive interactions

Quadrature samples of an energy-centered Gaussian filter are approximated using the
constructed propagators of the original positive Hamiltonian. The scalar energy phase
is incorporated in the coefficients; no shifted local interaction is required to be
positive. The resulting single finite sum has an explicit sample count, operator-norm
error and simultaneous operator-Schmidt bound at every cut.

Source: Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19, equations (19)--(22), using
Osborne, arXiv:quant-ph/0508031v2, Figure 2 and equations (12)--(13).
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder NNReal

namespace TNLean.MPS.AreaLaw

private theorem norm_weighted_sum_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (w : Fin N → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j ≤ 1)
    (X Y : Fin N → E) {rho : ℝ} (hrho : 0 ≤ rho) (hXY : ∀ j, ‖X j - Y j‖ ≤ rho) :
    ‖(∑ j, w j • X j) - ∑ j, w j • Y j‖ ≤ rho := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖w j • X j - w j • Y j‖ := norm_sum_le _ _
    _ ≤ ∑ j, w j * rho := by
      apply Finset.sum_le_sum
      intro j _
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hw j)]
      exact mul_le_mul_of_nonneg_left (hXY j) (hw j)
    _ = rho * ∑ j, w j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    _ ≤ rho := mul_le_of_le_one_right hrho hsum

/-- The number of quadrature nodes of the Gaussian approximant: the time mesh of accuracy
`eta / (‖H - E‖ + 1)` on the window `[-T, T]`. Huang, arXiv:1406.6355v6, Section 5.4,
equation (22). -/
noncomputable def positiveChainGaussianSampleCount {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (energy T eta : ℝ) : ℕ :=
  timeMeshCount T (eta / (‖(∑ i, h i) - (energy : ℂ) • 1‖ + 1))

/-- **The Gaussian approximant of a positive chain.** The Gaussian quadrature, over the
time mesh, of the phase-shifted positive-chain propagators at the mesh nodes: an
approximation to the Gaussian filter `exp(-variance (H - E)² / 2)` with simultaneous
cut-rank bounds. Huang, arXiv:1406.6355v6, Section 5.4, equation (22) and Lemma 19. -/
noncomputable def positiveChainGaussianApproximant {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (h0 : ∀ i, 0 ≤ h i)
    (variance : ℝ≥0) (energy T eta rho : ℝ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  let delta := eta / (‖(∑ i, h i) - (energy : ℂ) • 1‖ + 1)
  ∑ j : Fin (timeMeshCount T delta), timeMeshWeight variance T delta j •
    (Complex.exp (((-energy * timeMeshNode T delta j : ℝ) : ℂ) * Complex.I) •
      positiveChainPropagator hq h h0 T rho (-timeMeshNode T delta j))

/-- The Gaussian approximant has at least one and at most polynomially many nodes,
approximates the Gaussian filter to accuracy `2 exp(-T²/(2 variance)) + eta + rho`, and
has cut rank at most the number of nodes times the propagator rank at every cut. Huang,
arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. -/
theorem positiveChainGaussianApproximant_spec {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (variance : ℝ≥0) (energy : ℝ) {T eta rho : ℝ}
    (hT : 0 ≤ T) (heta : 0 < eta) (hrho : 0 < rho) :
    let H := ∑ i, h i
    let r := chainPropagationRadius L T rho
    let N := positiveChainGaussianSampleCount h energy T eta
    let Q := positiveChainGaussianApproximant hq h h0 variance energy T eta rho
    1 ≤ N ∧ (N : ℝ) ≤ 2 * T * ((L : ℝ) + |energy| + 1) / eta + 2 ∧
      ‖GaussianFilter.gaussianIntertwiner variance (H - (energy : ℂ) • 1) 0 1 - Q‖ ≤
        2 * Real.exp (-T ^ 2 / (2 * (variance : ℝ))) + eta + rho ∧
      ∀ cut : ℕ, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) Q) ≤
          N * q ^ (8 * r + 8) := by
  classical
  let : NeZero q := ⟨by omega⟩
  intro H r N Q
  let Hcenter := H - (energy : ℂ) • 1
  have hHerm : H.IsHermitian :=
    Matrix.isHermitian_sum _ fun i _ ↦ (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian
  have hcenter : Hcenter.IsHermitian :=
    hHerm.sub (isHermitian_one.smul
      (by simp [IsSelfAdjoint, Complex.conj_ofReal] : IsSelfAdjoint (energy : ℂ)))
  have hnorm (i) : ‖h i‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i)
  have hHnorm : ‖H‖ ≤ (L : ℝ) := by
    calc
      _ ≤ ∑ i, ‖h i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin (L - 1), (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hnorm i
      _ = ((L - 1 : ℕ) : ℝ) := by simp
      _ ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 1
  have hcenterNorm : ‖Hcenter‖ ≤ (L : ℝ) + |energy| := by
    calc
      _ ≤ ‖H‖ + ‖(energy : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)‖ :=
        norm_sub_le _ _
      _ = ‖H‖ + |energy| := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one]
      _ ≤ (L : ℝ) + |energy| := by linarith
  let delta := eta / (‖Hcenter‖ + 1)
  have hdelta : 0 < delta := div_pos heta (by positivity)
  have hNdef : N = timeMeshCount T delta := rfl
  let times := timeMeshNode T delta
  let weights := timeMeshWeight variance T delta
  let phase := fun t : ℝ ↦ Complex.exp (((-energy * t : ℝ) : ℂ) * Complex.I)
  have hphase (t : ℝ) : ‖phase t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hshift (t : ℝ) : hermitianUnitaryPath Hcenter t = phase t • hermitianUnitaryPath H t := by
    calc
      _ = Complex.exp ((t : ℂ) * Complex.I * (-energy)) • hermitianUnitaryPath H t := by
        simpa only [Hcenter, sub_eq_add_neg, Complex.ofReal_neg, neg_smul] using
          hermitianUnitaryPath_add_smul_one H (-energy) t
      _ = phase t • hermitianUnitaryPath H t := by
        congr 1
        congr 1
        push_cast
        ring
  obtain ⟨hKerror, hKrank⟩ := positiveChainPropagator_spec hq h hs h0 h1 hT hrho
  let K := positiveChainPropagator hq h h0 T rho
  have hQdef : Q = ∑ j : Fin N, weights j • (phase (times j) • K (-times j)) := rfl
  have hsamples (j : Fin N) :
      ‖hermitianUnitaryPath Hcenter (times j) - phase (times j) • K (-times j)‖ ≤ rho := by
    rw [hshift, ← smul_sub, norm_smul, hphase, one_mul]
    have htime : |-times j| ≤ T := by
      rw [abs_neg]
      exact abs_le.mpr (timeMeshNode_mem hT hdelta j)
    simpa only [neg_neg] using hKerror (-times j) htime
  have hreplace := norm_weighted_sum_sub_le weights (timeMeshWeight_nonneg variance T delta)
    (sum_timeMeshWeight_le_one variance hT hdelta)
    (fun j ↦ hermitianUnitaryPath Hcenter (times j))
    (fun j ↦ phase (times j) • K (-times j)) hrho.le hsamples
  have hquad := norm_gaussianIntertwiner_sub_unitary_timeMesh_sum_le variance hcenter hT heta
  have hN : (N : ℝ) ≤ 2 * T * ((L : ℝ) + |energy| + 1) / eta + 2 :=
    (timeMeshCount_accuracy_le hT (norm_nonneg Hcenter) heta).trans (by gcongr)
  refine ⟨by rw [hNdef, timeMeshCount]; omega, hN, ?_, ?_⟩
  · rw [hQdef]
    exact (norm_sub_le_norm_sub_add_norm_sub _
      (∑ j : Fin N, weights j • hermitianUnitaryPath Hcenter (times j)) _).trans
        (add_le_add hquad hreplace)
  · have hQ : Q = ∑ j : Fin N, ((weights j : ℂ) * phase (times j)) • K (-times j) := by
      rw [hQdef]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      rfl
    rw [hQ]
    intro cut
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (operatorSchmidtRank_weighted_chain_sum_le Finset.univ
        (fun j : Fin N ↦ (weights j : ℂ) * phase (times j))
        (fun j ↦ K (-times j)) (q ^ (8 * r + 8)) (fun j _ ↦ hKrank (-times j)) cut)


/-- A finite-node Gaussian approximant of a positive chain: the existence form of
`positiveChainGaussianApproximant_spec`. Huang, arXiv:1406.6355v6, Section 5.4,
Lemmas 18--19. -/
theorem exists_positive_chain_gaussian_approximation {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (variance : ℝ≥0) (energy : ℝ) {T eta rho : ℝ}
    (hT : 0 ≤ T) (heta : 0 < eta) (hrho : 0 < rho) :
    let H := ∑ i, h i
    let r := chainPropagationRadius L T rho
    ∃ (N : ℕ) (Q : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      1 ≤ N ∧ (N : ℝ) ≤ 2 * T * ((L : ℝ) + |energy| + 1) / eta + 2 ∧
      ‖GaussianFilter.gaussianIntertwiner variance (H - (energy : ℂ) • 1) 0 1 - Q‖ ≤
        2 * Real.exp (-T ^ 2 / (2 * (variance : ℝ))) + eta + rho ∧
      ∀ cut : ℕ, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L cut) Q) ≤
          N * q ^ (8 * r + 8) :=
  ⟨positiveChainGaussianSampleCount h energy T eta,
    positiveChainGaussianApproximant hq h h0 variance energy T eta rho,
    positiveChainGaussianApproximant_spec hq h hs h0 h1 variance energy hT heta hrho⟩

end TNLean.MPS.AreaLaw
