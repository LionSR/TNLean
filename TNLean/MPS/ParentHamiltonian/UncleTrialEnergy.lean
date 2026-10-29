/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTrialLocalization

/-!
# Exact quadratic energy of the two-wall uncle trial

The actual local uncle projector is a positive contraction. Its quadratic
form is the squared norm of its image. Combined with the derived global
four-bond localization, this gives an exact finite sum of nonnegative
endpoint energies and a contraction bound on that sum. No asymptotic
energy estimate or energy-support premise is supplied.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

/-- The actual local uncle projector contracts every two-site vector.
This is the local projector used in the source variational energy,
arXiv:1210.6613, lines 1289–1296. -/
theorem norm_uncleInteractionES_apply_le
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) :
    ‖uncleInteractionES A B R L v‖ ≤ ‖v‖ := by
  let e := blockedConfigLinearIsometryEquiv d 1 2
  let K := (groundSpaceES (uncleTensor A B R L) 1)ᗮ
  change ‖e (K.starProjection (e.symm v))‖ ≤ ‖v‖
  rw [e.norm_map]
  simpa only [e.symm.norm_map] using K.norm_starProjection_apply_le (e.symm v)

/-- The actual two-site uncle interaction has operator norm at most one. -/
theorem norm_uncleInteractionES_le_one
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    ‖uncleInteractionES A B R L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul] using norm_uncleInteractionES_apply_le A B R L v

/-- The actual uncle local quadratic form is the squared projected norm.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem re_inner_uncleInteractionES_eq_norm_sq
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) :
    (⟪uncleInteractionES A B R L v, v⟫_ℂ).re =
      ‖uncleInteractionES A B R L v‖ ^ 2 := by
  let e := blockedConfigLinearIsometryEquiv d 1 2
  let K := (groundSpaceES (uncleTensor A B R L) 1)ᗮ
  have hact (w : EuclideanSpace ℂ (Cfg d 2)) :
      uncleInteractionES A B R L w = e (K.starProjection (e.symm w)) := rfl
  calc
    _ = (⟪K.starProjection (e.symm v), e.symm v⟫_ℂ).re := by
      rw [hact, e.inner_map_eq_flip]
    _ = ‖K.starProjection (e.symm v)‖ ^ 2 := by
      exact K.re_inner_starProjection_eq_normSq (e.symm v)
    _ = _ := by rw [hact, e.norm_map]

/-- Each actual local quadratic energy is nonnegative and bounded by the
squared input norm. No positivity or contraction premise is supplied. -/
theorem re_inner_uncleInteractionES_bounds
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) :
    0 ≤ (⟪uncleInteractionES A B R L v, v⟫_ℂ).re ∧
      (⟪uncleInteractionES A B R L v, v⟫_ℂ).re ≤ ‖v‖ ^ 2 := by
  rw [re_inner_uncleInteractionES_eq_norm_sq]
  exact ⟨sq_nonneg _, (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_uncleInteractionES_apply_le A B R L v)⟩

/-- The actual trial energy is exactly the nonnegative four-endpoint sum
of squared local projected norms. This is a finite identity, before the
source's asymptotic endpoint estimates. Source: arXiv:1210.6613,
proof of Lemma lowenergystates, lines 1289–1296. -/
theorem re_inner_uncleHamiltonianES_trial_eq_sum_endpoints
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) :
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    (⟪uncleHamiltonianES A B R L (6 * N + 1) φ, φ⟫_ℂ).re =
      (((d ^ 2 : ℕ) : ℝ)⁻¹) * ∑ i ∈ uncleTrialEndpointBonds N hN,
        ∑ τ : Cfg d (6 * N + 1),
          ‖uncleInteractionES A B R L (cyclicRestrictES (Fin.pos i) 2 i τ φ)‖ ^ 2 := by
  let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
    (uncleTwoWallTrialSource A B R L N)
  let c : ℝ := ((d ^ 2 : ℕ) : ℝ)⁻¹
  have hc : (((d ^ 2 : ℕ) : ℂ)⁻¹) = (c : ℂ) := by simp [c]
  dsimp only
  rw [uncleHamiltonianES_trial_eq_sum_endpoints A B R L N hN]
  simp only [hc, sum_inner, inner_smul_left, Complex.conj_ofReal,
    LinearMap.adjoint_inner_left]
  change Complex.reCLM (∑ i ∈ uncleTrialEndpointBonds N hN, c •
    ∑ τ : Cfg d (6 * N + 1),
      inner ℂ (uncleInteractionES A B R L (cyclicRestrictES (Fin.pos i) 2 i τ φ))
        (cyclicRestrictES (Fin.pos i) 2 i τ φ)) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [re_inner_uncleInteractionES_eq_norm_sq]
  rw [Finset.mul_sum]

/-- A finite endpoint-energy bound derived from the actual local
contraction. The endpoint restricted norms still require source estimates;
this is not the asymptotic bound in Lemma lowenergystates. -/
theorem re_inner_uncleHamiltonianES_trial_le_endpoint_norms
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (N : ℕ) (hN : 0 < N) :
    let φ := (WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)
    (⟪uncleHamiltonianES A B R L (6 * N + 1) φ, φ⟫_ℂ).re ≤
      (((d ^ 2 : ℕ) : ℝ)⁻¹) * ∑ i ∈ uncleTrialEndpointBonds N hN,
        ∑ τ : Cfg d (6 * N + 1), ‖cyclicRestrictES (Fin.pos i) 2 i τ φ‖ ^ 2 := by
  dsimp only
  rw [re_inner_uncleHamiltonianES_trial_eq_sum_endpoints A B R L N hN]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro τ _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_uncleInteractionES_apply_le A B R L _)

end MPSTensor
