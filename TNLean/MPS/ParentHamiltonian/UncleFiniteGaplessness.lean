/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleGroundSpace
import TNLean.MPS.ParentHamiltonian.UncleGroundGram
import TNLean.MPS.ParentHamiltonian.UncleTrialGroundProjection
import TNLean.MPS.ParentHamiltonian.UncleVariationalAsymptotics
import TNLean.MPS.ParentHamiltonian.UncleEndpointEnergyBound

/-!
# Generic finite-volume gaplessness of the actual uncle Hamiltonian

For almost every pair of perturbation walls satisfying the source full-span
condition, the actual periodic uncle Hamiltonians on \(6N+1\) sites have
positive eigenvalues tending to zero. The actual quadratic norm growth,
linear energy bound and ground-space projection decay are derived from the
canonical block data. No norm, overlap, energy or transfer-gap estimate is
supplied as a premise.

Source: arXiv:1210.6613, thm:gapless and its proof, lines 1154–1314.
The injective-perturbation standing assumption is explicit at lines
1017–1018 and 1041–1042. This is the finite-volume conclusion; constructing
an infinite-volume operator and its full spectrum is a separate result.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open scoped InnerProductSpace
open MeasureTheory Filter

namespace MPSTensor

variable {d a b : ℕ}

private theorem ker_uncleHamiltonianES_eq_span_mpvState
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L))
    (M : ℕ) (hM : 2 ≤ M) :
    LinearMap.ker (uncleHamiltonianES A B R L M).toLinearMap =
      Submodule.span ℂ ({mpvState A M, mpvState B M} :
        Set (EuclideanSpace ℂ (Cfg d M))) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, M = n + 2 := ⟨M - 2, by omega⟩
  rw [ker_uncleHamiltonianES_eq_span_mpv A B R L hPert n]
  rfl

/-- Generic finite-volume gaplessness for the actual two-block uncle
Hamiltonians in the source canonical normalization. For almost every wall
pair, if its boundary letters span the full matrix algebra, then every
positive threshold eventually bounds an actual positive eigenvalue on
\(6N+1\) sites. The full-span condition is the source's standing
injective-perturbation assumption, not an assumed variational estimate.

Source: arXiv:1210.6613, thm:gapless, lines 1154–1314; injective
perturbations at lines 1017–1018 and 1041–1042. -/
theorem uncleHamiltonianES_ae_eventually_exists_pos_eigenvalue_lt
    (A : MPSTensor d a) (B : MPSTensor d b)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef) (htrA : Matrix.trace ρA = 1)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef) (htrB : Matrix.trace ρB = 1)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB)
    (μ : Measure ((Fin d → Matrix (Fin a) (Fin b) ℂ) ×
      (Fin d → Matrix (Fin b) (Fin a) ℂ))) [μ.IsAddHaarMeasure] :
    ∀ᵐ P ∂μ, Kraus.IsInjective (uncleBoundaryLetter A B P.1 P.2) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∃ η : ℝ, 0 < η ∧ η < ε ∧
          Module.End.HasEigenvalue
            (uncleHamiltonianES A B P.1 P.2 (6 * N + 1)).toLinearMap (η : ℂ) := by
  classical
  by_cases hExists : ∃ (R₀ : Fin d → Matrix (Fin a) (Fin b) ℂ)
      (L₀ : Fin d → Matrix (Fin b) (Fin a) ℂ),
      Kraus.IsInjective (uncleBoundaryLetter A B R₀ L₀)
  · obtain ⟨R₀, L₀, hPert₀⟩ := hExists
    have ha : a ≠ 0 := by
      intro ha
      subst a
      simp at htrA
    have hb : b ≠ 0 := by
      intro hb
      subst b
      simp at htrB
    let : NeZero a := ⟨ha⟩
    let : NeZero b := ⟨hb⟩
    have hAB := uncleBoundaryLetter_mixedMapSpectralRadius_lt_one
      A B R₀ L₀ hPert₀ hUA hUB ρA hρA ρB hρB hFA hFB
    have hBA := uncleBoundaryLetter_mixedMapSpectralRadius_reverse_lt_one
      A B R₀ L₀ hPert₀ hUA hUB ρA hρA ρB hρB hFA hFB
    have hGram := uncleGroundGram_tendsto
      A B R₀ L₀ hPert₀ hUA hUB ρA hρA htrA ρB hρB htrB hFA hFB
    have hNorm := uncleTwoWallTrialSource_ae_quadratic_norm_growth
      A B R₀ L₀ hPert₀ hUA hUB ρA hρA htrA ρB hρB htrB hFA hFB μ
    filter_upwards [hNorm] with P hP
    intro hPert
    obtain ⟨c, C, hc, _hC, hBounds⟩ := hP
    let v : (N : ℕ) → EuclideanSpace ℂ (Cfg d (6 * N + 1)) := fun N ↦
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B P.1 P.2 N)
    have hNormLower : ∀ᶠ N : ℕ in atTop,
        c * ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ‖v N‖ ^ 2 :=
      hBounds.mono fun _ hN ↦ hN.1
    have hSpan := uncleTwoWallTrialSource_span_projection_tendsto_zero
      A B P.1 P.2 hUA hUB hGram hAB hBA
    have hProjection : Tendsto (fun N : ℕ ↦
        ‖(LinearMap.ker (uncleHamiltonianES A B P.1 P.2
          (6 * N + 1)).toLinearMap).starProjection (v N)‖ ^ 2) atTop (nhds (0 : ℝ)) := by
      apply hSpan.congr'
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hK := ker_uncleHamiltonianES_eq_span_mpvState A B P.1 P.2 hPert
        (6 * N + 1) (by omega)
      have key : ∀ (K₁ K₂ : Submodule ℂ (EuclideanSpace ℂ (Cfg d (6 * N + 1))))
          [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection], K₁ = K₂ →
          ∀ x, K₁.starProjection x = K₂.starProjection x := by
        rintro K₁ K₂ _ _ rfl x
        rfl
      rw [key _ _ hK]
    obtain ⟨CE, hCE, hEnergy⟩ := re_inner_uncleHamiltonianES_trial_le_mul
      A B P.1 P.2 hUA hUB ρA hρA ρB hρB hFA hFB hAB hBA
    apply eventually_exists_pos_eigenvalue_uncleHamiltonianES_lt_of_trial_bounds
      A B P.1 P.2 v c hc hNormLower hProjection
    exact ⟨CE, hCE, (eventually_gt_atTop 0).mono fun N hN ↦ hEnergy N hN⟩
  · exact Filter.Eventually.of_forall fun P hPert ↦
      False.elim (hExists ⟨P.1, P.2, hPert⟩)

end MPSTensor
