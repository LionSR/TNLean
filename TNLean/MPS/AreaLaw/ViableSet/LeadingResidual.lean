/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ViableLeadingBounds
import TNLean.MPS.AreaLaw.AKLV.ResidualPhase

/-!
# Residual certification for the LVV leading vector

The trace-one constraint separates a density matrix eigenvalue above one half from the
rest of the spectrum.  This file combines that separation with the abstract residual
estimate to certify an approximate leading eigenvector.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`,
lines 493--505.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- The shifted positive operator `μ I - σ` has gap `2μ - 1` above its kernel on the
orthogonal complement of a unit `μ`-eigenvector of the trace-one density matrix `σ`.
Consequently its residual controls the orthogonal component of any vector. -/
theorem Matrix.PosSemidef.norm_orthogonal_component_le_shifted_residual
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) (z : EuclideanSpace ℂ n) :
    let K := toEuclideanLin (((μ : ℂ) • (1 : Matrix n n ℂ)) - σ)
    ‖z - ⟪u, z⟫_ℂ • u‖ ≤ ‖K z‖ / (2 * μ - 1) := by
  let K := toEuclideanLin (((μ : ℂ) • (1 : Matrix n n ℂ)) - σ)
  have hone : (((μ : ℂ) • (1 : Matrix n n ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have hK : K.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr
    (hone.sub hσ.isHermitian)
  have huL : toEuclideanLin σ u = (μ : ℂ) • u := by
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
  have heig : K u = (0 : ℂ) • u := by
    have h1 : toEuclideanLin (1 : Matrix n n ℂ) u = u := by simp [toLpLin_one]
    dsimp only [K]
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, h1, huL,
      sub_self, zero_smul]
  have hsep : (0 : ℝ) < 2 * μ - 1 := by linarith only [hμ]
  have horth : ∀ w : EuclideanSpace ℂ n, ⟪u, w⟫_ℂ = 0 →
      (2 * μ - 1) * ‖w‖ ^ 2 ≤ (⟪w, K w⟫_ℂ).re := by
    intro w hw
    have hh := Matrix.PosSemidef.re_inner_le_one_sub_eigenvalue_of_orthogonal
      hσ htr hu huσ hμ hw
    have h1 : toEuclideanLin (1 : Matrix n n ℂ) w = w := by simp [toLpLin_one]
    have hscalar : (⟪w, (μ : ℂ) • w⟫_ℂ).re = μ * ‖w‖ ^ 2 := by
      rw [inner_smul_right, Complex.re_ofReal_mul,
        show (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) w]
    dsimp only [K]
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, h1, inner_sub_right,
      Complex.sub_re, hscalar]
    linarith
  let P : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    1 - InnerProductSpace.rankOne ℂ u u
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hu).one_sub
  have hPapply (x : EuclideanSpace ℂ n) : P x = x - ⟪u, x⟫_ℂ • u := rfl
  have hself : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    simp
  have hinner (x : EuclideanSpace ℂ n) : ⟪u, K x⟫_ℂ = 0 := by
    have hsym := hK u x
    rw [heig, zero_smul, inner_zero_left] at hsym
    exact hsym.symm
  have hcomm (x : EuclideanSpace ℂ n) : K (P x) = P (K x) := by
    simp only [hPapply, map_sub, map_smul, heig, zero_smul, smul_zero, sub_zero,
      hinner]
  let w := P z
  have hw : ⟪u, w⟫_ℂ = 0 := by
    rw [show w = P z from rfl, hPapply, inner_sub_right, inner_smul_right,
      hself, mul_one, sub_self]
  have hres : K w = P (K z) := by
    rw [show w = P z from rfl, hcomm]
  have hlow : (2 * μ - 1) * ‖w‖ ^ 2 ≤ (⟪w, K w⟫_ℂ).re := horth w hw
  have hupper : (⟪w, K w⟫_ℂ).re ≤ ‖w‖ * ‖K z‖ := by
    calc
      _ ≤ ‖w‖ * ‖K w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        rw [hres]
        exact ContinuousLinearMap.IsStarProjection.norm_apply_le hP _) (norm_nonneg _)
  change ‖w‖ ≤ _
  by_cases hw0 : ‖w‖ = 0
  · rw [hw0]
    exact div_nonneg (norm_nonneg _) hsep.le
  apply (le_div_iff₀ hsep).mpr
  have hmul : ‖w‖ * ((2 * μ - 1) * ‖w‖) ≤ ‖w‖ * ‖K z‖ := by
    nlinarith
  have hh := le_of_mul_le_mul_left hmul
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0))
  nlinarith

/-- The shifted residual is the usual eigenpair residual, up to a harmless sign. -/
theorem Matrix.PosSemidef.norm_orthogonal_component_le_leading_residual
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) (z : EuclideanSpace ℂ n) :
    ‖z - ⟪u, z⟫_ℂ • u‖ ≤
      ‖toEuclideanLin σ z - (μ : ℂ) • z‖ / (2 * μ - 1) := by
  have hh := Matrix.PosSemidef.norm_orthogonal_component_le_shifted_residual
    hσ htr hu huσ hμ z
  change ‖z - ⟪u, z⟫_ℂ • u‖ ≤
    ‖toEuclideanLin (((μ : ℂ) • (1 : Matrix n n ℂ)) - σ) z‖ / (2 * μ - 1) at hh
  have h1 : toEuclideanLin (1 : Matrix n n ℂ) z = z := by simp [toLpLin_one]
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, h1,
    show (μ : ℂ) • z - toEuclideanLin σ z =
      -(toEuclideanLin σ z - (μ : ℂ) • z) by abel, norm_neg] at hh
  exact hh

/-- For a unit numerical vector, the eigenpair residual gives a phase-aligned squared
distance to the exact leading vector. -/
theorem Matrix.PosSemidef.exists_phase_sq_distance_le_leading_residual
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) :
    ∃ θ : ℝ, ‖z - Complex.exp (θ * Complex.I) • u‖ ^ 2 ≤
      2 * (‖toEuclideanLin σ z - (μ : ℂ) • z‖ / (2 * μ - 1)) ^ 2 := by
  let P : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    1 - InnerProductSpace.rankOne ℂ u u
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hu).one_sub
  have hPapply (x : EuclideanSpace ℂ n) : P x = x - ⟪u, x⟫_ℂ • u := rfl
  have hnorm : ‖P z‖ ≤
      ‖toEuclideanLin σ z - (μ : ℂ) • z‖ / (2 * μ - 1) := by
    rw [hPapply]
    exact Matrix.PosSemidef.norm_orthogonal_component_le_leading_residual
      hσ htr hu huσ hμ z
  have hdeficit : 1 - ‖⟪u, z⟫_ℂ‖ ^ 2 = ‖P z‖ ^ 2 := by
    have hh := ContinuousLinearMap.IsStarProjection.norm_sq_eq
      (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hu) z
    simp only [hz, one_pow, InnerProductSpace.rankOne_apply, norm_smul, hu, mul_one] at hh
    change 1 = ‖⟪u, z⟫_ℂ‖ ^ 2 + ‖P z‖ ^ 2 at hh
    linarith
  have hbound : 1 * (1 - ‖⟪u, z⟫_ℂ‖ ^ 2) ≤
      (‖toEuclideanLin σ z - (μ : ℂ) • z‖ / (2 * μ - 1)) ^ 2 := by
    rw [one_mul, hdeficit]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  obtain ⟨θ, _, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap
    (by norm_num : (0 : ℝ) < 1) hz hu hbound
  exact ⟨θ, by simpa only [div_one] using hθ⟩

/-- At the LVV scale `μ ≥ 23 / 24`, the residual-to-distance estimate has the
uniform conditioning factor `12 / 11`. -/
theorem Matrix.PosSemidef.exists_phase_sq_distance_le_twelve_div_eleven_residual
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) :
    ∃ θ : ℝ, ‖z - Complex.exp (θ * Complex.I) • u‖ ^ 2 ≤
      2 * ((12 / 11) * ‖toEuclideanLin σ z - (μ : ℂ) • z‖) ^ 2 := by
  have hhalf : 1 / 2 < μ := by linarith only [hμ]
  obtain ⟨θ, hθ⟩ := Matrix.PosSemidef.exists_phase_sq_distance_le_leading_residual
    hσ htr hu hz huσ hhalf
  refine ⟨θ, hθ.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (by linarith only [hhalf]))
  exact leading_residual_div_separation_le (norm_nonneg _) hμ

/-- A residual at most `11 / 24` times a target vector tolerance suffices for that
phase-aligned tolerance.  The factor is a convenient rational consequence of the
uniform `12 / 11` conditioning and the squared-distance estimate. -/
theorem Matrix.PosSemidef.exists_phase_distance_le_of_residual_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ ζ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) (hζ : 0 ≤ ζ)
    (hres : ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ (11 / 24) * ζ) :
    ∃ θ : ℝ, ‖z - Complex.exp (θ * Complex.I) • u‖ ≤ ζ := by
  obtain ⟨θ, hθ⟩ :=
    Matrix.PosSemidef.exists_phase_sq_distance_le_twelve_div_eleven_residual
      hσ htr hu hz huσ hμ
  refine ⟨θ, ?_⟩
  have hscaled : (12 / 11) * ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ ζ / 2 := by
    nlinarith only [hres]
  have hsq : ‖z - Complex.exp (θ * Complex.I) • u‖ ^ 2 ≤ ζ ^ 2 := by
    calc
      _ ≤ 2 * ((12 / 11) * ‖toEuclideanLin σ z - (μ : ℂ) • z‖) ^ 2 := hθ
      _ ≤ 2 * (ζ / 2) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) (norm_nonneg _)) hscaled 2) (by norm_num)
      _ ≤ ζ ^ 2 := by nlinarith only [sq_nonneg ζ]
  nlinarith only [hsq, hζ, norm_nonneg (z - Complex.exp (θ * Complex.I) • u),
    sq_nonneg (‖z - Complex.exp (θ * Complex.I) • u‖ - ζ)]

/-- A sufficiently accurate residual certificate produces an exact unit leading
eigenvector within the prescribed tolerance.  The exact vector differs from the
chosen leading eigenvector only by a complex phase. -/
theorem Matrix.PosSemidef.exists_nearby_unit_eigenvector_of_residual_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ ζ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) (hζ : 0 ≤ ζ)
    (hres : ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ (11 / 24) * ζ) :
    ∃ v : EuclideanSpace ℂ n,
      ‖v‖ = 1 ∧
      σ *ᵥ WithLp.ofLp v = (μ : ℂ) • WithLp.ofLp v ∧
      ‖z - v‖ ≤ ζ ∧
      ∃ θ : ℝ, v = Complex.exp (θ * Complex.I) • u := by
  obtain ⟨θ, hθ⟩ := Matrix.PosSemidef.exists_phase_distance_le_of_residual_le
    hσ htr hu hz huσ hμ hζ hres
  refine ⟨Complex.exp (θ * Complex.I) • u, ?_, ?_, hθ, θ, rfl⟩
  · rw [norm_smul, Complex.norm_exp, hu]
    norm_num
  · rw [WithLp.ofLp_smul, mulVec_smul, huσ]
    simp only [smul_smul, mul_comm]

/-- At the LVV vector tolerance `Δ / (16224 L)`, the sufficient residual tolerance
`11 / 24` times the vector tolerance is `11 Δ / (389376 L)`. -/
theorem residual_precision_of_lvv_vector_tolerance
    {L : ℕ} (hL : 0 < L) {Δ r : ℝ}
    (hr : r ≤ 11 * Δ / (389376 * L)) :
    r ≤ (11 / 24) * (Δ / (16224 * L)) := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have heq :
      (11 : ℝ) * Δ / (389376 * L) = (11 / 24) * (Δ / (16224 * L)) := by
    field_simp [hL0]
    ring
  rwa [← heq]

/-- The explicit LVV spectral tolerance: for a positive chain length, a residual at
most `11 Δ / (389376 L)` produces an exact unit leading eigenvector within
`Δ / (16224 L)` of the numerical unit vector. -/
theorem Matrix.PosSemidef.exists_nearby_unit_eigenvector_of_lvv_residual
    {n : Type*} [Fintype n] [DecidableEq n]
    {L : ℕ} (hL : 0 < L) {Δ : ℝ} (hΔ : 0 < Δ)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ)
    (hres : ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ 11 * Δ / (389376 * L)) :
    ∃ v : EuclideanSpace ℂ n,
      ‖v‖ = 1 ∧
      σ *ᵥ WithLp.ofLp v = (μ : ℂ) • WithLp.ofLp v ∧
      ‖z - v‖ ≤ Δ / (16224 * L) ∧
      ∃ θ : ℝ, v = Complex.exp (θ * Complex.I) • u := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hζ : 0 ≤ Δ / (16224 * L) :=
    (div_pos hΔ (mul_pos (by norm_num) hLreal)).le
  apply Matrix.PosSemidef.exists_nearby_unit_eigenvector_of_residual_le
    hσ htr hu hz huσ hμ hζ
  exact residual_precision_of_lvv_vector_tolerance hL hres

end TNLean.MPS.AreaLaw
