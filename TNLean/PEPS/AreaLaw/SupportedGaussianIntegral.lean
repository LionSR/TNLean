/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Dynamics.SupportedGaussianIntegral
import TNLean.PEPS.AreaLaw.RegionOperatorLocalization

/-!
# A supported Gaussian approximation between two Hamiltonians

Project both the evolved observable and the relative-evolution generator
onto the same graph neighbourhood. The projected differential equation
constructs a unitary path on this neighbourhood. Integrating the product
against the original restricted Gaussian measure gives a supported
operator, with norm and approximation bounds uniform in the variance.

The path is chosen before the variance and time cutoff. Neither a
propagator nor an approximating operator is supplied as a hypothesis.
Only the actual supports of the input observable and Hamiltonian
difference enter. No spectral gap or information assumption is used.

## References

OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
September 24, 2026, Section 2, lines 513–562, in the proof of
eq:info-local-two-sided. Source revision:
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The common projection region is the neighbourhood of the union of the
two input supports, as in the support conclusion of that argument.
Independently formalized; no upstream Lean proof text is reused.
-/

open ManyBody (PlaneInteraction)

open MeasureTheory ProbabilityTheory QuantumCircuit
open scoped Matrix Matrix.Norms.L2Operator NNReal
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- The supported Gaussian approximation from a region localization bound with constants
`C, v ≥ 0` and decay `c`, for one finite-range Hamiltonian `g`. The constants of the
localization bound pass unchanged to the approximation error. -/
private theorem supported_gaussian_integral_of_localization {q : ℕ} (hq : 1 ≤ q) {R : ℕ}
    {J C v c : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v) {Λ : Finset (ℤ × ℤ)} (g : PlaneInteraction Λ q R)
        (hg : ∀ X, (g.term X).IsHermitian) (hgJ : ∀ X, ‖g.term X‖ ≤ J)
    (hlocal : ∀ (S : Finset (Site Λ)) (A : Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
      A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S → ∀ (l : ℕ) (t : ℝ),
      ‖ManyBody.heisenbergEvolution g.hamiltonian t A -
          ManyBody.regionExpectation (graphNeighborhood Λ l S) (ManyBody.heisenbergEvolution
              g.hamiltonian t
              A)‖ ≤
        ‖A‖ * min 2 (C * (Λ.card : ℝ) * Real.exp (v * |t| - c * l)))
    (H W : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) (hH : H.IsHermitian)
    (Q Z : Finset (Site Λ)) (hW : W ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Q)
    (hD : g.hamiltonian - H ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Z) (l : ℕ) :
    let B := graphNeighborhood Λ l (Q ∪ Z)
    ∃ U : ℝ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
      U 0 = 1 ∧
      (∀ t, HasDerivAt U
        ((Complex.I • ManyBody.regionExpectation B
          (ManyBody.heisenbergEvolution g.hamiltonian t (g.hamiltonian - H))) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup (Configuration Λ q) ℂ) ∧
      (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B) ∧
      ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
        let M := ∫ t : ℝ in Set.Icc (-T) T,
          ManyBody.regionExpectation B (ManyBody.heisenbergEvolution g.hamiltonian t W) * U t
            ∂gaussianReal 0 η
        M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B ∧
        ‖M‖ ≤ ‖W‖ ∧
        ‖M - GaussianFilter.gaussianIntertwinerTruncated η T g.hamiltonian H W‖ ≤
          ‖W‖ * C * (Λ.card : ℝ) * (1 + ‖g.hamiltonian - H‖ * T) *
            Real.exp (v * T - c * l) := by
  classical
  intro B
  have : NeZero q := ⟨by omega⟩
  obtain ⟨U, hU0, hU, hunit, hsupport, haverage⟩ :=
    ManyBody.exists_supported_gaussian_integral_of_projection_bounds
        (ManyBody.Interaction.isHermitian_hamiltonian hg) hH B
  refine ⟨U, hU0, hU, hunit, fun t ↦ (hsupport t),
    fun η T hT ↦ ?_⟩
  have hnear (A : Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
      (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (Q ∪ Z : Finset (Site Λ)))
      (t : ℝ) (ht : |t| ≤ T) :
      ‖ManyBody.heisenbergEvolution g.hamiltonian t A -
        ManyBody.regionExpectation B (ManyBody.heisenbergEvolution g.hamiltonian t A)‖ ≤
        ‖A‖ * (C * (Λ.card : ℝ) * Real.exp (v * T - c * l)) :=
    (hlocal (Q ∪ Z) A hA l t).trans
      (mul_le_mul_of_nonneg_left
        ((min_le_right _ _).trans
          (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr
              (sub_le_sub_right (mul_le_mul_of_nonneg_left ht hv) _))
            (mul_nonneg hC (Nat.cast_nonneg _))))
        (norm_nonneg A))
  obtain ⟨hMsupport, hMnorm, hMerror⟩ := haverage B B
    (fun _ hx ↦ hx) (fun _ hx ↦ hx) W η T hT
    (C * (Λ.card : ℝ) * Real.exp (v * T - c * l))
    (‖g.hamiltonian - H‖ * (C * (Λ.card : ℝ) * Real.exp (v * T - c * l)))
    (by positivity) (by positivity)
    (hnear W (ManyBody.supportedOperators_mono (fun _ hx ↦ Finset.mem_union_left Z hx) hW))
    (hnear (g.hamiltonian - H)
      (ManyBody.supportedOperators_mono (fun _ hx ↦ Finset.mem_union_right Q hx) hD))
  refine ⟨ hMsupport, hMnorm, hMerror.trans_eq ?_⟩
  ring


/-- **The supported Gaussian approximation, with explicit constants.** For a Hamiltonian of
range `R` and term-norm bound `J ≥ 0`, the approximation error of the supported Gaussian
integral is at most `‖W‖ 2 C₀(R) |Λ| (1 + ‖D‖ T) e^{v(R, J) T - l/2}`, with
`C₀(R) = graphBallLocalizationPrefactor R` and `v(R, J) = graphBallLocalizationVelocity R J`
the constants of `TNLean.PEPS.AreaLaw.quasilocal_region_localization`.
Source: polynomial-PEPS, Section 2, eq:info-local-two-sided, lines 513–562. -/
theorem supported_gaussian_integral (q : ℕ) (hq : 1 ≤ q) (R : ℕ) {J : ℝ} (hJ : 0 ≤ J)
    (Λ : Finset (ℤ × ℤ)) (g : PlaneInteraction Λ q R) (hg : ∀ X, (g.term X).IsHermitian)
        (hgJ : ∀ X, ‖g.term X‖ ≤ J)
    (H W : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) (hH : H.IsHermitian)
    (Q Z : Finset (Site Λ)) (hW : W ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Q)
    (hD : g.hamiltonian - H ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Z) (l : ℕ) :
    let B := graphNeighborhood Λ l (Q ∪ Z)
    ∃ U : ℝ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
      U 0 = 1 ∧
      (∀ t, HasDerivAt U
        ((Complex.I • ManyBody.regionExpectation B
          (ManyBody.heisenbergEvolution g.hamiltonian t (g.hamiltonian - H))) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup (Configuration Λ q) ℂ) ∧
      (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B) ∧
      ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
        let M := ∫ t : ℝ in Set.Icc (-T) T,
          ManyBody.regionExpectation B (ManyBody.heisenbergEvolution g.hamiltonian t W) * U t
            ∂gaussianReal 0 η
        M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B ∧
        ‖M‖ ≤ ‖W‖ ∧
        ‖M - GaussianFilter.gaussianIntertwinerTruncated η T g.hamiltonian H W‖ ≤
          ‖W‖ * (2 * graphBallLocalizationPrefactor R) * (Λ.card : ℝ) *
            (1 + ‖g.hamiltonian - H‖ * T) *
            Real.exp (graphBallLocalizationVelocity R J * T - 1 / 2 * l) :=
  supported_gaussian_integral_of_localization hq
    (mul_pos two_pos (graphBallLocalizationPrefactor_pos R)).le
    (graphBallLocalizationVelocity_nonneg R hJ) g hg hgJ
    (quasilocal_region_localization q hq R J Λ g hg hgJ) H W hH Q Z hW hD l

/-- The actual projected relative evolution constructs a supported
approximation to every truncated two-Hamiltonian Gaussian filter.
The same path works for all variances and nonnegative time cutoffs.
Source: polynomial-PEPS, Section 2, eq:info-local-two-sided,
lines 513–562. -/
theorem exists_supported_gaussian_integral (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (J : ℝ) :
    ∃ C v c : ℝ, 0 < C ∧ 0 < v ∧ 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (g : PlaneInteraction Λ q R) (_ : ∀ X, (g.term X).IsHermitian)
          (_ : ∀ X, ‖g.term X‖ ≤ J)
        (H W : Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
        H.IsHermitian →
        ∀ Q Z : Finset (Site Λ),
          W ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Q →
          g.hamiltonian - H ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Z →
          ∀ l : ℕ,
            let B := graphNeighborhood Λ l (Q ∪ Z)
            ∃ U : ℝ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
              U 0 = 1 ∧
              (∀ t, HasDerivAt U
                ((Complex.I • ManyBody.regionExpectation B
                  (ManyBody.heisenbergEvolution g.hamiltonian t (g.hamiltonian - H))) * U t) t) ∧
              (∀ t, U t ∈ Matrix.unitaryGroup (Configuration Λ q) ℂ) ∧
              (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B) ∧
              ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
                let M := ∫ t : ℝ in Set.Icc (-T) T,
                  ManyBody.regionExpectation B
                      (ManyBody.heisenbergEvolution g.hamiltonian t W) * U t
                    ∂gaussianReal 0 η
                M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B ∧
                ‖M‖ ≤ ‖W‖ ∧
                ‖M - GaussianFilter.gaussianIntertwinerTruncated η T g.hamiltonian H W‖ ≤
                  ‖W‖ * C * (Λ.card : ℝ) * (1 + ‖g.hamiltonian - H‖ * T) *
                    Real.exp (v * T - c * l)  := by
  obtain ⟨C, v, c, hC, hv, hc, hlocal⟩ :=
    exists_quasilocal_region_localization q hq R J
  exact ⟨C, v, c, hC, hv, hc, fun Λ g hg hgJ H W hH Q Z hW hD l ↦
    supported_gaussian_integral_of_localization hq hC.le hv.le g hg hgJ (hlocal Λ g hg hgJ) H W
        hH Q Z hW hD l⟩

end TNLean.PEPS.AreaLaw
