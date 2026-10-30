/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathGaussianFilter
import TNLean.Lattice.GaussianConnectedCorrelation
import TNLean.Lattice.ObservableCentering

/-!
# Ordinary centered correlations derived from the physical MPS gap

One physical gap gives one positive Gaussian spectral constant at every
parameter and ring length. The actual finite-ring Lieb–Robinson estimate
and actual Gaussian/Cauchy frequency separation then bound the ordinary
centered correlation of the periodic MPS vector. No filtered-to-ordinary
comparison, transfer-gap condition or continuous canonical gauge is given
as input.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3; applied to the
exact MPS path of SPC11, arXiv:1010.3732, Section II.F, lines 929–953.
-/

open TNLean.Lattice Matrix QuantumCircuit MPSPreparation GaussianFilter
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- The actual physical gap implies an ordinary centered-correlation
bound with uniform Gaussian/propagation parameters. Both the spectral and
propagation estimates are derived from the actual physical path, so no
ordinary clustering or transfer conclusion is hidden as a premise.
The original unnormalized periodic MPS vector is retained.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3;
SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_centered_correlation_gaussian_bound
    (Q : ExactMPSGroundPath P) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) [NeZero N] (_hN : 2 ≤ N),
      ∀ (A B : MPOTensor.ChainOperator d N) (X Y : Finset (Fin N)),
      ∀ (hX : X.Nonempty) (hY : Y.Nonempty),
      A ∈ supportedOperators d X → B ∈ supportedOperators d Y →
      Disjoint (X : Set (Fin N)) (Y : Set (Fin N)) →
      ⟪mpvState (Q.tensor γ) N,
        toEuclideanCLM (𝕜 := ℂ) A (mpvState (Q.tensor γ) N)⟫_ℂ = 0 →
      ∀ (q T a : ℝ), 0 < q → 0 < T → 0 ≤ a →
        let ψ := mpvState (Q.tensor γ) N
        let s := (q / Δ ^ 2).toNNReal
        let C := 2 * ‖A‖ * ‖B‖ * X.card *
          Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)
        let v := 8 * Real.exp a
        ‖⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A * B) ψ⟫_ℂ‖ ≤
          (2 * Real.exp (-q / 2) * ‖A‖ * ‖B‖ +
            kernel s⁻¹ 0 * (C * v * Real.exp (v * T) +
              (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ))))) * ‖ψ‖ ^ 2 := by
  obtain ⟨Δ, hΔ, hdata⟩ := Q.exists_uniform_ground_line_spectral_gap
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ N _ hN A B X Y hX hY hA hB hXY hcenter q T a hq hT ha
  obtain ⟨E₀, hH, hline, hgap⟩ := hdata γ hγ N hN
  have hψ : mpvState (Q.tensor γ) N ∈
      groundEigenspace (interactionHamiltonian (P.interaction γ) hN) E₀ := by
    rw [hline]
    exact Submodule.mem_span_singleton_self _
  apply norm_centered_ground_correlation_le_gaussian hq hΔ hT (by positivity)
    (by positivity) hH hgap hψ hline A B hcenter
  intro t
  exact norm_interactionHamiltonian_commutator_le_exp_abs_of_disjoint hN (P.interaction γ)
    (P.hermitian γ hγ) (P.norm_le_one γ hγ) A B X Y hX hY hA hB hXY a ha t

/-- The physical gap bounds ordinary connected correlations of arbitrary
supported observables. Centering, its norm bound and support preservation
are derived from the actual periodic MPS vector; no centering condition
is added to the public physical hypotheses.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3;
SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_connected_correlation_gaussian_bound
    (Q : ExactMPSGroundPath P) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) [NeZero N] (_hN : 2 ≤ N),
      ∀ (A B : MPOTensor.ChainOperator d N) (X Y : Finset (Fin N)),
      ∀ (hX : X.Nonempty) (hY : Y.Nonempty),
      A ∈ supportedOperators d X → B ∈ supportedOperators d Y →
      Disjoint (X : Set (Fin N)) (Y : Set (Fin N)) →
      ∀ (q T a : ℝ), 0 < q → 0 < T → 0 ≤ a →
        let ψ := mpvState (Q.tensor γ) N
        let s := (q / Δ ^ 2).toNNReal
        let v := 8 * Real.exp a
        ‖normalizedVectorExpectation ψ (A * B) -
          normalizedVectorExpectation ψ A * normalizedVectorExpectation ψ B‖ ≤
          2 * ‖A‖ * ‖B‖ * (2 * Real.exp (-q / 2) +
            kernel s⁻¹ 0 *
              ((2 * X.card *
                Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) *
                v * Real.exp (v * T) +
                (2 / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ))))) := by
  obtain ⟨Δ, hΔ, hEst⟩ := Q.exists_uniform_centered_correlation_gaussian_bound
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ N _ hN A B X Y hX hY hA hB hXY q T a hq hT ha
  let ψ := mpvState (Q.tensor γ) N
  have hψne : ψ ≠ 0 := by
    exact ((EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm.map_eq_zero_iff).not.mpr
      (Q.nonzero γ hγ N (by omega))
  let A₀ := centeredObservable ψ A
  have hA₀ : A₀ ∈ supportedOperators d X :=
    centeredObservable_mem ψ (one_mem_supportedOperators _) hA
  have hcenter : ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A₀ ψ⟫_ℂ = 0 :=
    inner_centeredObservable_eq_zero hψne A
  have hNormA : ‖A₀‖ ≤ 2 * ‖A‖ := norm_centeredObservable_le hψne A
  let s := (q / Δ ^ 2).toNNReal
  let v := 8 * Real.exp a
  let B₀ := 2 * Real.exp (-q / 2) + kernel s⁻¹ 0 *
    ((2 * X.card *
      Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) *
      v * Real.exp (v * T) + (2 / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ))))
  have hB₀ : 0 ≤ B₀ := by
    have hk := kernel_nonneg s⁻¹ 0
    dsimp only [B₀, v]
    positivity
  have hraw : ‖⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A₀ * B) ψ⟫_ℂ‖ ≤
      (‖A₀‖ * ‖B‖ * B₀) * ‖ψ‖ ^ 2 := by
    have h := hEst γ hγ N hN A₀ B X Y hX hY hA₀ hB hXY hcenter q T a hq hT ha
    convert h using 1
    dsimp only [B₀, s, v]
    ring
  have hcov : normalizedVectorExpectation ψ (A * B) -
      normalizedVectorExpectation ψ A * normalizedVectorExpectation ψ B =
        ⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A₀ * B) ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    dsimp only [A₀]
    rw [inner_centeredObservable_mul]
    simp only [normalizedVectorExpectation, sub_div, mul_div_assoc]
  show ‖normalizedVectorExpectation ψ (A * B) -
      normalizedVectorExpectation ψ A * normalizedVectorExpectation ψ B‖ ≤
    2 * ‖A‖ * ‖B‖ * B₀
  rw [hcov, norm_div, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hψne) 2)).mpr
  apply hraw.trans
  apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right ?_ hB₀
  exact mul_le_mul_of_nonneg_right hNormA (norm_nonneg B)

end MPSTensor
