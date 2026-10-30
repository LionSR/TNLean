/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathGaussianCorrelation
import TNLean.Lattice.GaussianFrequencyClusteringRate

/-!
# Ordinary exponential clustering from the actual physical MPS gap

The actual uniform physical gap and finite-ring propagation bound imply one
positive exponential rate for ordinary connected correlations at every
parameter and ring length. The Gaussian frequency comparison, observable
centering and regularizer limit are derived, not supplied as estimates.
The original periodic MPS vector is normalized only through its explicit
expectation quotient.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3; applied to
SPC11, arXiv:1010.3732, Section II.F, lines 929–953. Passing these finite
correlations to limiting minimal transfer contractions remains separate.
-/

noncomputable section

open TNLean.Lattice Matrix QuantumCircuit MPSPreparation GaussianFilter
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- A physical uniform gap gives ordinary connected exponential clustering
for the actual periodic MPS vectors, uniformly in the parameter and ring
length. There is no clustering, transfer-gap, chosen minimal gauge or
frequency-separation premise. The displayed separation starts at one;
this is the range required for the limiting-correlation rate argument.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3;
SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_connected_exponential_clustering
    (Q : ExactMPSGroundPath P) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) [NeZero N] (_hN : 2 ≤ N),
      ∀ (A B : MPOTensor.ChainOperator d N) (X Y : Finset (Fin N)),
      ∀ (hX : X.Nonempty) (hY : Y.Nonempty),
      A ∈ supportedOperators d X → B ∈ supportedOperators d Y →
      Disjoint (X : Set (Fin N)) (Y : Set (Fin N)) →
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ℓ ≤ ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY →
        let ψ := mpvState (Q.tensor γ) N
        ‖normalizedVectorExpectation ψ (A * B) -
          normalizedVectorExpectation ψ A * normalizedVectorExpectation ψ B‖ ≤
            K * ((X.card : ℝ) + 1) * ‖A‖ * ‖B‖ * Real.exp (-κ * ℓ) := by
  obtain ⟨Δ, hΔ, hEst⟩ := Q.exists_uniform_connected_correlation_gaussian_bound
  let v := 8 * Real.exp (1 : ℝ)
  have hv : 0 < v := by dsimp only [v]; positivity
  obtain ⟨C, κ, hC, hκ, hRate⟩ := exists_gaussianFrequencyClusteringRate Δ v hΔ hv
  refine ⟨2 * C, κ, mul_pos (by norm_num) hC, hκ, ?_⟩
  intro γ hγ N _ hN A B X Y hX hY hA hB hXY ℓ hℓ hDist
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  let T := ℓ / (2 * v)
  let q := T * Δ
  let s := (q / Δ ^ 2).toNNReal
  have hT : 0 < T := div_pos hℓpos (by positivity)
  have hq : 0 < q := mul_pos hT hΔ
  have hs : (s : ℝ) = T / Δ := by
    dsimp only [s]
    rw [Real.coe_toNNReal _ (div_nonneg hq.le (sq_nonneg Δ))]
    dsimp only [q]
    field_simp [hΔ.ne']
  have htime : v * T = ℓ / 2 := by
    dsimp only [T]
    field_simp [hv.ne']
  have hqexp : Real.exp (-q / 2) = Real.exp (-ℓ * Δ / (4 * v)) := by
    congr 1
    dsimp only [q, T]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have htail : Real.exp (-T ^ 2 / (2 * (s : ℝ))) = Real.exp (-q / 2) := by
    rw [hs]
    congr 1
    dsimp only [q]
    field_simp [hT.ne', hΔ.ne']
  have hc : kernel s⁻¹ 0 = Real.sqrt (ℓ / (4 * Real.pi * v * Δ)) := by
    rw [kernel_inv_zero_eq_sqrt, hs]
    congr 1
    dsimp only [T]
    field_simp [hv.ne', hΔ.ne', Real.pi_ne_zero]
    ring
  have hrecip : 2 / T = 4 * v / ℓ := by
    dsimp only [T]
    field_simp [hℓpos.ne', hv.ne']
    ring
  have hshort :
      (2 * (X.card : ℝ) * Real.exp (-ℓ)) * v * Real.exp (v * T) =
        2 * X.card * v * Real.exp (-ℓ / 2) := by
    rw [htime]
    calc
      _ = (2 * X.card * v) * (Real.exp (-ℓ) * Real.exp (ℓ / 2)) := by ring
      _ = _ := by
        rw [← Real.exp_add, show -ℓ + ℓ / 2 = -ℓ / 2 by ring]
  have hBracket :
      2 * Real.exp (-q / 2) + kernel s⁻¹ 0 *
        ((2 * X.card *
          Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) *
          v * Real.exp (v * T) + (2 / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ)))) ≤
      2 * Real.exp (-ℓ * Δ / (4 * v)) +
        Real.sqrt (ℓ / (4 * Real.pi * v * Δ)) *
          (2 * X.card * v * Real.exp (-ℓ / 2) +
            (4 * v / ℓ) * Real.exp (-ℓ * Δ / (4 * v))) := by
    simp only [hc, htail, hqexp, hrecip]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply add_le_add _ le_rfl
    calc
      _ ≤ (2 * (X.card : ℝ) * Real.exp (-ℓ)) * v * Real.exp (v * T) := by
        have hDecay :
            Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) ≤
              Real.exp (-ℓ) := Real.exp_le_exp.mpr (by linarith)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDecay (by positivity)) hv.le) (Real.exp_pos _).le
      _ = _ := hshort
  have h := hEst γ hγ N hN A B X Y hX hY hA hB hXY q T 1 hq hT (by norm_num)
  apply h.trans
  calc
    _ ≤ (2 * ‖A‖ * ‖B‖) *
        (C * ((X.card : ℝ) + 1) * Real.exp (-κ * ℓ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hBracket.trans (hRate X.card (by positivity) ℓ hℓ)
    _ = _ := by ring

end MPSTensor
