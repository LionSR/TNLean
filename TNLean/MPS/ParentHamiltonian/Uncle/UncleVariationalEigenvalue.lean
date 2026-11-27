/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Uncle.UncleKernelConditions
import TNLean.MPS.Tensor.Overlap
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TNLean.MPS.ParentHamiltonian.Uncle.UncleTrialOverlap
import QICLean.Spectral.Eigenvalue.PositiveRayleighEigenvalue

/-!
# The finite variational spectral step for the uncle Hamiltonian

A positive operator with a vector orthogonal to its kernel and Rayleigh
quotient below epsilon has a positive eigenvalue below epsilon (QICLean,
`LinearMap.IsPositive.exists_pos_eigenvalue_lt_of_rayleigh`).
Applied to the Hamiltonian of the translates of the uncle interaction, this is the spectral step
in arXiv:1210.6613, proof of Theorem thm:gapless, lines 1302–1314.
The preceding norm, energy, and ground-overlap estimates must still supply
such a vector; they are not assumed as a gaplessness conclusion here.

## Vanishing projection of the actual two-wall trial onto the periodic sectors

The derived trial overlaps and the asymptotic Gram matrix of the two periodic
vectors force the actual projected squared norm to vanish. This supplies the
projection-removal step for arXiv:1210.6613, proof of Theorem thm:gapless,
lines 1302–1314. The separate canonical Gram theorem discharges the explicit
Gram-limit input; the exact uncle kernel theorem identifies this span with
the full kernel for injective perturbations and sufficiently large lengths.

## The asymptotic finite variational step for the uncle Hamiltonian

A quadratic lower bound for an actual trial's squared norm, a vanishing
actual kernel projection and a linear energy upper bound give arbitrarily
small positive eigenvalues on the chains of length 6N+1. This is the purely
analytic step after the source tensor and genericity estimates; those
estimates remain explicit inputs here.

Source: arXiv:1210.6613, proof of Theorem thm:gapless, lines 1302–1314.
-/

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace MPSTensor

private theorem norm_span_pair_projection_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (u v φ : E) (hu : (1 / 2 : ℝ) ≤ ‖u‖ ^ 2) (hv : (1 / 2 : ℝ) ≤ ‖v‖ ^ 2)
    (huv : ‖inner ℂ u v‖ ≤ 1 / 4) :
    ‖(Submodule.span ℂ ({u, v} : Set E)).starProjection φ‖ ^ 2 ≤
      4 * (‖inner ℂ u φ‖ ^ 2 + ‖inner ℂ v φ‖ ^ 2) := by
  classical
  let K := Submodule.span ℂ ({u, v} : Set E)
  let w := K.starProjection φ
  obtain ⟨α, β, hw⟩ := Submodule.mem_span_pair.mp (K.starProjection_apply_mem φ)
  have hw' : w = α • u + β • v := hw.symm
  have hcross : |(inner ℂ (α • u) (β • v)).re| ≤ ‖α‖ * ‖β‖ / 4 := by
    calc
      _ ≤ ‖inner ℂ (α • u) (β • v)‖ := Complex.abs_re_le_norm _
      _ = ‖α‖ * ‖β‖ * ‖inner ℂ u v‖ := by
        simp only [inner_smul_left, inner_smul_right, norm_mul, starRingEnd_apply, norm_star]
        ring
      _ ≤ ‖α‖ * ‖β‖ * (1 / 4) :=
        mul_le_mul_of_nonneg_left huv (mul_nonneg (norm_nonneg α) (norm_nonneg β))
      _ = _ := by ring
  have hexpand : ‖w‖ ^ 2 = ‖α‖ ^ 2 * ‖u‖ ^ 2 +
      2 * (inner ℂ (α • u) (β • v)).re + ‖β‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [hw', norm_add_sq (𝕜 := ℂ), RCLike.re_eq_complex_re,
      norm_smul, norm_smul, mul_pow, mul_pow]
  have hcoefs : ‖α‖ ^ 2 + ‖β‖ ^ 2 ≤ 4 * ‖w‖ ^ 2 := by
    have hα := mul_le_mul_of_nonneg_left hu (sq_nonneg ‖α‖)
    have hβ := mul_le_mul_of_nonneg_left hv (sq_nonneg ‖β‖)
    have hlow := (abs_le.mp hcross).1
    nlinarith [sq_nonneg (‖α‖ - ‖β‖)]
  have hinner : ‖w‖ ^ 2 ≤
      ‖α‖ * ‖inner ℂ u φ‖ + ‖β‖ * ‖inner ℂ v φ‖ := by
    calc
      _ = (inner ℂ w φ).re := (K.re_inner_starProjection_eq_normSq φ).symm
      _ ≤ ‖inner ℂ w φ‖ := Complex.re_le_norm _
      _ ≤ _ := by
        rw [hw', inner_add_left, inner_smul_left, inner_smul_left]
        simpa only [norm_mul, starRingEnd_apply, norm_star] using
          norm_add_le (star α * inner ℂ u φ) (star β * inner ℂ v φ)
  have hCS : (‖α‖ * ‖inner ℂ u φ‖ + ‖β‖ * ‖inner ℂ v φ‖) ^ 2 ≤
      (‖α‖ ^ 2 + ‖β‖ ^ 2) * (‖inner ℂ u φ‖ ^ 2 + ‖inner ℂ v φ‖ ^ 2) := by
    nlinarith [sq_nonneg (‖α‖ * ‖inner ℂ v φ‖ - ‖β‖ * ‖inner ℂ u φ‖)]
  have hsquare : (‖w‖ ^ 2) ^ 2 ≤
      4 * ‖w‖ ^ 2 * (‖inner ℂ u φ‖ ^ 2 + ‖inner ℂ v φ‖ ^ 2) := by
    calc
      _ ≤ (‖α‖ * ‖inner ℂ u φ‖ + ‖β‖ * ‖inner ℂ v φ‖) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg ‖w‖) (by positivity)).mpr hinner
      _ ≤ _ := hCS.trans (mul_le_mul_of_nonneg_right hcoefs (by positivity))
  change ‖w‖ ^ 2 ≤ _
  by_cases hwzero : ‖w‖ ^ 2 = 0
  · rw [hwzero]
    positivity
  have hwpos : 0 < ‖w‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hwzero)
  apply (mul_le_mul_iff_left₀ hwpos).mp
  nlinarith only [hsquare]

/-- The two periodic MPS sectors give a controlled ground-space
projection once their Gram matrix is close to the identity. The hypotheses
are finite scalar inequalities, to be supplied by the canonical transfer
limits and the mixed-overlap decay. Source application:
arXiv:1210.6613, proof of thm:gapless, lines 1302–1314. -/
theorem norm_mpv_span_projection_sq_le
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b) (N : ℕ)
    (φ : EuclideanSpace ℂ (Cfg d N))
    (hA : (1 / 2 : ℝ) ≤ ‖mpvState A N‖ ^ 2)
    (hB : (1 / 2 : ℝ) ≤ ‖mpvState B N‖ ^ 2)
    (hAB : ‖inner ℂ (mpvState A N) (mpvState B N)‖ ≤ 1 / 4) :
    ‖(Submodule.span ℂ ({mpvState A N, mpvState B N} :
        Set (EuclideanSpace ℂ (Cfg d N)))).starProjection φ‖ ^ 2 ≤
      4 * (‖inner ℂ (mpvState A N) φ‖ ^ 2 + ‖inner ℂ (mpvState B N) φ‖ ^ 2) :=
  norm_span_pair_projection_sq_le _ _ _ hA hB hAB

end MPSTensor
end

end

section

open scoped InnerProductSpace Topology
open Filter

namespace MPSTensor

/-- The actual source trial has vanishing squared projection onto the two
periodic ground sectors. The actual overlap limits are derived from unital
normalization and mixed damping, rather than supplied as an orthogonality
premise. Source: arXiv:1210.6613, proof of Theorem thm:gapless. -/
theorem uncleTwoWallTrialSource_span_projection_tendsto_zero
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (hGram :
      Tendsto (fun M ↦ ‖mpvState A M‖ ^ 2) atTop (nhds (1 : ℝ)) ∧
        Tendsto (fun M ↦ ‖mpvState B M‖ ^ 2) atTop (nhds (1 : ℝ)) ∧
        Tendsto (fun M ↦ inner ℂ (mpvState A M) (mpvState B M)) atTop (nhds (0 : ℂ)))
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    Tendsto (fun N : ℕ ↦
      ‖(Submodule.span ℂ ({mpvState A (6 * N + 1), mpvState B (6 * N + 1)} :
          Set (EuclideanSpace ℂ (Cfg d (6 * N + 1))))).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace (Fin d) (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N))‖ ^ 2) atTop (nhds (0 : ℝ)) := by
  have hlen : Tendsto (fun N : ℕ ↦ 6 * N + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    exact eventually_atTop.mpr ⟨M, fun N hN ↦ by omega⟩
  have hA := (hGram.1.comp hlen).eventually
    (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hB := (hGram.2.1.comp hlen).eventually
    (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hcrossNorm : Tendsto (fun N : ℕ ↦
      ‖inner ℂ (mpvState A (6 * N + 1)) (mpvState B (6 * N + 1))‖)
      atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_apply, norm_zero] using (hGram.2.2.comp hlen).norm
  have hcross := hcrossNorm.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hleft := inner_mpvState_left_uncleTwoWallTrialSource_tendsto_zero A B R L hUA hBA
  have hright := inner_mpvState_right_uncleTwoWallTrialSource_tendsto_zero A B R L hUB hAB
  have hbound := ((hleft.norm.pow 2).add (hright.norm.pow 2)).const_mul 4
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ sq_nonneg _)
  · filter_upwards [hA, hB, hcross] with N hAN hBN hcrossN
    exact norm_mpv_span_projection_sq_le A B (6 * N + 1) _ hAN.le hBN.le hcrossN.le
  · simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero] using hbound

end MPSTensor

end

section

noncomputable section

open Filter
open scoped InnerProductSpace Topology

namespace MPSTensor

open ManyBody.Interaction (translationInvariant)

/-- The actual uncle Hamiltonians have eventually a positive eigenvalue
below every positive threshold when the actual trial family has quadratic
squared norm, vanishing kernel projection and linear energy. The kernel
complement vector is derived by subtracting its actual orthogonal projection.
This is the analytic step of arXiv:1210.6613, proof of thm:gapless,
lines 1302–1314; no source tensor estimate is asserted by this lemma alone. -/
theorem eventually_exists_pos_eigenvalue_hamiltonian_uncleInteraction_lt_of_trial_bounds
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : (N : ℕ) → EuclideanSpace ℂ (Cfg d (6 * N + 1)))
    (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ᶠ N : ℕ in atTop, c * ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ‖v N‖ ^ 2)
    (hProj : Tendsto (fun N : ℕ ↦
      ‖(LinearMap.ker (Matrix.toEuclideanLin
          (translationInvariant (6 * N + 1) (uncleInteraction A B R L)).hamiltonian)).starProjection
        (v N)‖ ^ 2) atTop (𝓝 0))
    (hEnergy : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (⟪Matrix.toEuclideanLin
          (translationInvariant (6 * N + 1) (uncleInteraction A B R L)).hamiltonian (v N), v
            N⟫_ℂ).re ≤ C * N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧
        Module.End.HasEigenvalue
          (Matrix.toEuclideanLin
              (translationInvariant (6 * N + 1) (uncleInteraction A B R L)).hamiltonian) (μ : ℂ) :=
                by
  obtain ⟨C, hC, hEnergy⟩ := hEnergy
  intro ε hε
  let k : ℝ := ε * c / 2
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (C / k)
  have hMpos : 0 < M := Nat.cast_pos.mp ((div_pos hC hk).trans hM)
  have hProjSmall : ∀ᶠ N : ℕ in atTop,
      ‖(LinearMap.ker (Matrix.toEuclideanLin
          (translationInvariant (6 * N + 1) (uncleInteraction A B R L)).hamiltonian)).starProjection
        (v N)‖ ^ 2 < c / 2 :=
    hProj.eventually (eventually_lt_nhds (half_pos hc))
  filter_upwards [hNorm, hEnergy, hProjSmall, eventually_ge_atTop M]
    with N hNormN hEnergyN hProjN hMN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (hMpos.trans_le hMN)
  have hNormN' : c * ((N : ℝ) + 1) ^ 2 ≤ ‖v N‖ ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hNormN
  have hMass : (c / 2) * (N : ℝ) ^ 2 ≤ ‖v N‖ ^ 2 -
      ‖(LinearMap.ker (Matrix.toEuclideanLin
          (translationInvariant (6 * N + 1) (uncleInteraction A B R L)).hamiltonian)).starProjection
        (v N)‖ ^ 2 := by
    have hlinear : 0 ≤ c * (N : ℝ) := mul_nonneg hc.le hNpos.le
    have hquadratic : 0 ≤ c * (N : ℝ) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
    nlinarith only [hNormN', hProjN.le, hc, hlinear, hquadratic]
  have hLarge : C < k * (N : ℝ) := by
    have hdiv : C / k < (N : ℝ) := hM.trans_le (Nat.cast_le.mpr hMN)
    simpa only [mul_comm] using (div_lt_iff₀ hk).mp hdiv
  have hRayleigh : C * (N : ℝ) < ε * ((c / 2) * (N : ℝ) ^ 2) := by
    calc
      C * (N : ℝ) < (k * (N : ℝ)) * (N : ℝ) :=
        mul_lt_mul_of_pos_right hLarge hNpos
      _ = _ := by dsimp [k]; ring
  apply (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_uncleInteraction
    A B R L (6 * N + 1))).exists_pos_eigenvalue_lt_of_projection_bound (v N) ε
  exact hEnergyN.trans_lt
    (hRayleigh.trans_le (mul_le_mul_of_nonneg_left hMass hε.le))

end MPSTensor
end

end
