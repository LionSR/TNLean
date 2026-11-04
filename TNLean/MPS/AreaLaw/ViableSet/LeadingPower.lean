/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.LeadingResidual
import QICLean.Channel.FilterNormalization

/-!
# Power iteration for the LVV compressed density

The dominant eigenvalue of the compressed LVV density is at least `23 / 24`, while the
remaining spectral mass is at most `1 / 24`.  This file develops the corresponding power
iteration.  Its first ingredient is a deterministic choice among the coordinate vectors:
one of the `n` standard basis vectors has squared overlap at least `1 / n` with the unit
dominant eigenvector.

Source context: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, lines
477--478 and 493--505.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Matrix powers act on Euclidean vectors by iterating the associated linear map. -/
theorem Matrix.toEuclideanLin_pow_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (t : ℕ) (x : EuclideanSpace ℂ n) :
    toEuclideanLin (A ^ t) x = ((toEuclideanLin A)^[t]) x := by
  change (toLpLin 2 2 (A ^ t)) x = _
  rw [toLpLin_pow]
  induction t with
  | zero => simp
  | succ t ih =>
      simp only [pow_succ', Function.iterate_succ_apply']
      change toEuclideanLin A (((toLpLin 2 2 A) ^ t) x) = _
      rw [ih]

/-- A unit vector in `ℂⁿ` has squared overlap at least `1 / n` with one of the standard
basis vectors.  Hence trying all `n` coordinate vectors supplies a power-method starting
vector with inverse-polynomial leading component. -/
theorem exists_basisVector_sq_overlap_ge_inv
    {n : ℕ} (hn : 0 < n) (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1) :
    ∃ i : Fin n,
      1 / (n : ℝ) ≤ ‖⟪EuclideanSpace.basisFun (Fin n) ℂ i, u⟫_ℂ‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  have hsum : ∑ i, ‖⟪b i, u⟫_ℂ‖ ^ 2 = 1 := by
    rw [b.sum_sq_norm_inner_right, hu, one_pow]
  by_contra h
  push Not at h
  have hlt : (∑ i, ‖⟪b i, u⟫_ℂ‖ ^ 2) < ∑ _ : Fin n, 1 / (n : ℝ) := by
    apply Finset.sum_lt_sum
    · exact fun i _ ↦ (h i).le
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _, h ⟨0, hn⟩⟩
  have hconst : (∑ _ : Fin n, 1 / (n : ℝ)) = 1 := by
    simp [ne_of_gt hn]
  rw [hsum, hconst] at hlt
  exact (lt_irrefl 1) hlt

/-- A trace-one positive matrix is a contraction in the Euclidean norm. -/
theorem Matrix.PosSemidef.norm_toEuclideanLin_apply_le_of_trace_eq_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (z : EuclideanSpace ℂ n) : ‖toEuclideanLin σ z‖ ≤ ‖z‖ := by
  have hop : ‖σ‖ ≤ 1 := by
    simpa only [htr, Complex.one_re] using hσ.l2_opNorm_le_trace_re
  calc
    ‖toEuclideanLin σ z‖ = ‖WithLp.toLp 2 (σ *ᵥ WithLp.ofLp z)‖ := rfl
    _ ≤ ‖σ‖ * ‖z‖ := σ.l2_opNorm_mulVec z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg z)
    _ = ‖z‖ := one_mul _

/-- Every real eigenvalue of a trace-one positive matrix is at most one. -/
theorem Matrix.PosSemidef.eigenvalue_le_one_of_trace_eq_one
    {n : Type*} [Fintype n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u) : μ ≤ 1 := by
  classical
  have happly := Matrix.PosSemidef.norm_toEuclideanLin_apply_le_of_trace_eq_one hσ htr u
  have heig : toEuclideanLin σ u = (μ : ℂ) • u := by
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
  rw [heig, norm_smul, Complex.norm_real, Real.norm_eq_abs, hu, mul_one] at happly
  exact le_trans (le_abs_self μ) happly

/-- On the orthogonal complement of a unit eigenvector with eigenvalue above one half,
a trace-one positive matrix contracts by at most the remaining spectral mass `1 - μ`. -/
theorem Matrix.PosSemidef.norm_toEuclideanLin_apply_le_one_sub_eigenvalue_of_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) {w : EuclideanSpace ℂ n} (huw : ⟪u, w⟫_ℂ = 0) :
    ‖toEuclideanLin σ w‖ ≤ (1 - μ) * ‖w‖ := by
  let L : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    toEuclideanCLM (n := n) (𝕜 := ℂ) σ
  let P : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    1 - InnerProductSpace.rankOne ℂ u u
  let T := P.comp (L.comp P)
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hu).one_sub
  have hLsym : L.IsSymmetric := by
    simpa only [L, coe_toEuclideanCLM_eq_toEuclideanLin] using
      (isSymmetric_toEuclideanLin_iff.mpr hσ.isHermitian)
  have hTsym : T.IsSymmetric := by
    intro x y
    change ⟪P (L (P x)), y⟫_ℂ = ⟪x, P (L (P y))⟫_ℂ
    calc
      ⟪P (L (P x)), y⟫_ℂ = ⟪L (P x), P y⟫_ℂ :=
        ContinuousLinearMap.IsStarProjection.inner_apply_left hP _ _
      _ = ⟪P x, L (P y)⟫_ℂ := hLsym _ _
      _ = ⟪x, P (L (P y))⟫_ℂ :=
        ContinuousLinearMap.IsStarProjection.inner_apply_left hP _ _
  have hμ1 : μ ≤ 1 :=
    Matrix.PosSemidef.eigenvalue_le_one_of_trace_eq_one hσ htr hu huσ
  have hnonneg : 0 ≤ 1 - μ := sub_nonneg.mpr hμ1
  have hTnorm : ‖T‖ ≤ 1 - μ := by
    rw [T.norm_eq_iSup_rayleighQuotient hTsym]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · subst x
      simpa [ContinuousLinearMap.rayleighQuotient] using hnonneg
    have hPxorth : ⟪u, P x⟫_ℂ = 0 := by
      change ⟪u, x - ⟪u, x⟫_ℂ • u⟫_ℂ = 0
      rw [inner_sub_right, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hu]
      simp
    have hupper := Matrix.PosSemidef.re_inner_le_one_sub_eigenvalue_of_orthogonal
      hσ htr hu huσ hμ hPxorth
    have hlower : 0 ≤ (⟪P x, toEuclideanLin σ (P x)⟫_ℂ).re :=
      hσ.re_inner_toEuclideanLin_self_nonneg (P x)
    have hPnorm : ‖P x‖ ≤ ‖x‖ :=
      ContinuousLinearMap.IsStarProjection.norm_apply_le hP x
    have hform : (⟪T x, x⟫_ℂ).re =
        (⟪P x, toEuclideanLin σ (P x)⟫_ℂ).re := by
      change (⟪P (L (P x)), x⟫_ℂ).re = _
      rw [ContinuousLinearMap.IsStarProjection.inner_apply_left hP]
      calc
        (⟪L (P x), P x⟫_ℂ).re = (⟪P x, L (P x)⟫_ℂ).re :=
          congrArg Complex.re (hLsym _ _)
        _ = (⟪P x, toEuclideanLin σ (P x)⟫_ℂ).re := rfl
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
    change |(⟪T x, x⟫_ℂ).re / ‖x‖ ^ 2| ≤ 1 - μ
    rw [hform, abs_div, abs_of_nonneg hlower, abs_of_nonneg (sq_nonneg ‖x‖),
      div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))]
    exact hupper.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hPnorm) hnonneg)
  have hPw : P w = w := by
    simp [P, huw]
  have hLworth : ⟪u, L w⟫_ℂ = 0 := by
    have huL : L u = (μ : ℂ) • u := by
      change toEuclideanLin σ u = (μ : ℂ) • u
      apply WithLp.ofLp_injective 2
      simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
    calc
      ⟪u, L w⟫_ℂ = ⟪L u, w⟫_ℂ := (hLsym u w).symm
      _ = 0 := by rw [huL, inner_smul_left, huw, mul_zero]
  have hPLw : P (L w) = L w := by
    simp [P, hLworth]
  calc
    ‖toEuclideanLin σ w‖ = ‖L w‖ := rfl
    _ = ‖T w‖ := by
      change ‖L w‖ = ‖P (L (P w))‖
      rw [hPw, hPLw]
    _ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
    _ ≤ (1 - μ) * ‖w‖ := mul_le_mul_of_nonneg_right hTnorm (norm_nonneg w)

/-- At the LVV leading-eigenvalue threshold `23 / 24`, one application of the density
matrix suppresses every orthogonal component by the factor `1 / 24`. -/
theorem Matrix.PosSemidef.norm_toEuclideanLin_apply_le_one_div_twentyFour_of_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) {w : EuclideanSpace ℂ n} (huw : ⟪u, w⟫_ℂ = 0) :
    ‖toEuclideanLin σ w‖ ≤ (1 / 24 : ℝ) * ‖w‖ := by
  have hhalf : 1 / 2 < μ := lt_of_lt_of_le (by norm_num) hμ
  have hcontract :=
    Matrix.PosSemidef.norm_toEuclideanLin_apply_le_one_sub_eigenvalue_of_orthogonal
      hσ htr hu huσ hhalf huw
  exact hcontract.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg w))

/-- After `t` power iterations at the LVV threshold, every component orthogonal to the
leading eigenvector is suppressed by `(1 / 24) ^ t`. -/
theorem Matrix.PosSemidef.norm_iterate_toEuclideanLin_le_one_div_twentyFour_pow_of_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) {w : EuclideanSpace ℂ n} (huw : ⟪u, w⟫_ℂ = 0)
    (t : ℕ) :
    ‖((toEuclideanLin σ)^[t]) w‖ ≤ (1 / 24 : ℝ) ^ t * ‖w‖ := by
  let L := toEuclideanLin σ
  have hLsym : L.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hσ.isHermitian
  have huL : L u = (μ : ℂ) • u := by
    apply WithLp.ofLp_injective 2
    simpa only [L, toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
  have horth : ∀ k : ℕ, ⟪u, (L^[k]) w⟫_ℂ = 0 := by
    intro k
    induction k with
    | zero => simpa using huw
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        calc
          ⟪u, L ((L^[k]) w)⟫_ℂ = ⟪L u, (L^[k]) w⟫_ℂ := (hLsym _ _).symm
          _ = 0 := by rw [huL, inner_smul_left, ih, mul_zero]
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply', pow_succ]
      calc
        ‖L ((L^[t]) w)‖ ≤ (1 / 24 : ℝ) * ‖(L^[t]) w‖ :=
          Matrix.PosSemidef.norm_toEuclideanLin_apply_le_one_div_twentyFour_of_orthogonal
            hσ htr hu huσ hμ (horth t)
        _ ≤ (1 / 24 : ℝ) * ((1 / 24 : ℝ) ^ t * ‖w‖) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 24 : ℝ) ^ t * (1 / 24 : ℝ) * ‖w‖ := by ring

/-- Scaling by the inverse leading eigenvalue turns the LVV power step into a map that
fixes the leading vector and contracts its orthogonal complement by `1 / 23`. -/
theorem Matrix.PosSemidef.inv_eigenvalue_scaled_action
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) {w : EuclideanSpace ℂ n} (huw : ⟪u, w⟫_ℂ = 0) :
    toEuclideanLin ((μ : ℂ)⁻¹ • σ) u = u ∧
      ⟪u, toEuclideanLin ((μ : ℂ)⁻¹ • σ) w⟫_ℂ = 0 ∧
      ‖toEuclideanLin ((μ : ℂ)⁻¹ • σ) w‖ ≤ (1 / 23 : ℝ) * ‖w‖ := by
  have hμpos : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  have huL : toEuclideanLin σ u = (μ : ℂ) • u := by
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
  have hLsym : (toEuclideanLin σ).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hσ.isHermitian
  have horth : ⟪u, toEuclideanLin σ w⟫_ℂ = 0 := by
    calc
      ⟪u, toEuclideanLin σ w⟫_ℂ = ⟪toEuclideanLin σ u, w⟫_ℂ :=
        (hLsym u w).symm
      _ = 0 := by rw [huL, inner_smul_left, huw, mul_zero]
  have hcontract :=
    Matrix.PosSemidef.norm_toEuclideanLin_apply_le_one_div_twentyFour_of_orthogonal
      hσ htr hu huσ hμ huw
  constructor
  · rw [map_smul, LinearMap.smul_apply, huL, smul_smul]
    simp [ne_of_gt hμpos]
  constructor
  · rw [map_smul, LinearMap.smul_apply, inner_smul_right, horth, mul_zero]
  · rw [map_smul, LinearMap.smul_apply, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμpos]
    calc
      μ⁻¹ * ‖toEuclideanLin σ w‖ ≤ μ⁻¹ * ((1 / 24 : ℝ) * ‖w‖) :=
        mul_le_mul_of_nonneg_left hcontract (inv_nonneg.mpr hμpos.le)
      _ ≤ (24 / 23 : ℝ) * ((1 / 24 : ℝ) * ‖w‖) := by
        gcongr
        rw [inv_eq_one_div, div_le_iff₀ hμpos]
        nlinarith only [hμ]
      _ = (1 / 23 : ℝ) * ‖w‖ := by ring

/-- The scaled LVV power fixes the leading vector and contracts every orthogonal vector
by `(1 / 23) ^ t`. -/
theorem Matrix.PosSemidef.inv_eigenvalue_scaled_power
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) {w : EuclideanSpace ℂ n} (huw : ⟪u, w⟫_ℂ = 0)
    (t : ℕ) :
    let A := (μ : ℂ)⁻¹ • σ
    toEuclideanLin (A ^ t) u = u ∧
      ⟪u, toEuclideanLin (A ^ t) w⟫_ℂ = 0 ∧
      ‖toEuclideanLin (A ^ t) w‖ ≤ (1 / 23 : ℝ) ^ t * ‖w‖ := by
  let A := (μ : ℂ)⁻¹ • σ
  obtain ⟨huA, _, _⟩ := Matrix.PosSemidef.inv_eigenvalue_scaled_action
    hσ htr hu huσ hμ huw
  have hstep : ∀ v : EuclideanSpace ℂ n, ⟪u, v⟫_ℂ = 0 →
      ⟪u, toEuclideanLin A v⟫_ℂ = 0 ∧
        ‖toEuclideanLin A v‖ ≤ (1 / 23 : ℝ) * ‖v‖ := by
    intro v huv
    exact (Matrix.PosSemidef.inv_eigenvalue_scaled_action
      hσ htr hu huσ hμ huv).2
  change toEuclideanLin (A ^ t) u = u ∧
    ⟪u, toEuclideanLin (A ^ t) w⟫_ℂ = 0 ∧
    ‖toEuclideanLin (A ^ t) w‖ ≤ (1 / 23 : ℝ) ^ t * ‖w‖
  induction t with
  | zero => simp [huw]
  | succ t ih =>
      obtain ⟨hiu, hiorth, hinorm⟩ := ih
      obtain ⟨hnextorth, hnextnorm⟩ := hstep _ hiorth
      have hsucc (x : EuclideanSpace ℂ n) :
          toEuclideanLin (A ^ (t + 1)) x =
            toEuclideanLin A (toEuclideanLin (A ^ t) x) := by
        rw [Matrix.toEuclideanLin_pow_apply, Function.iterate_succ_apply',
          ← Matrix.toEuclideanLin_pow_apply]
      refine ⟨?_, ?_, ?_⟩
      · rw [hsucc, hiu, huA]
      · rw [hsucc]
        exact hnextorth
      · rw [hsucc, pow_succ]
        exact hnextnorm.trans <| by
          calc
            (1 / 23 : ℝ) * ‖toEuclideanLin (A ^ t) w‖
                ≤ (1 / 23 : ℝ) * ((1 / 23 : ℝ) ^ t * ‖w‖) :=
                  mul_le_mul_of_nonneg_left hinorm (by norm_num)
            _ = (1 / 23 : ℝ) ^ t * (1 / 23 : ℝ) * ‖w‖ := by ring

/-- Normalizing the scaled power output gives a phase-aligned approximation to the
leading eigenvector.  The squared error is controlled by the initial orthogonal-to-leading
ratio and the geometric factor `(1 / 23) ^ (2t)`. -/
theorem Matrix.PosSemidef.exists_phase_normalized_inv_eigenvalue_scaled_power
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) (x : EuclideanSpace ℂ n) (hx : ⟪u, x⟫_ℂ ≠ 0)
    (t : ℕ) :
    let K := ((μ : ℂ)⁻¹ • σ) ^ t
    toEuclideanLin K x ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
      let ψ := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
      ‖ψ‖ = 1 ∧
        ‖ψ - u‖ ^ 2 ≤ 2 * (1 / 23 : ℝ) ^ (2 * t) *
          ‖x - ⟪u, x⟫_ℂ • u‖ ^ 2 / ‖⟪u, x⟫_ℂ‖ ^ 2 := by
  let A := (μ : ℂ)⁻¹ • σ
  let K := A ^ t
  have hfix : toEuclideanLin K u = u :=
    (Matrix.PosSemidef.inv_eigenvalue_scaled_power
      hσ htr hu huσ hμ (w := 0) (by simp) t).1
  have hperp : ∀ v : EuclideanSpace ℂ n, ‖v‖ = 1 → ⟪u, v⟫_ℂ = 0 →
      ⟪u, toEuclideanLin K v⟫_ℂ = 0 ∧
        ‖toEuclideanLin K v‖ ^ 2 ≤ (1 / 23 : ℝ) ^ (2 * t) := by
    intro v hv huv
    obtain ⟨_, horth, hnorm⟩ := Matrix.PosSemidef.inv_eigenvalue_scaled_power
      hσ htr hu huσ hμ huv t
    refine ⟨horth, ?_⟩
    have hnorm' : ‖toEuclideanLin K v‖ ≤ (1 / 23 : ℝ) ^ t := by
      simpa only [K, A, hv, mul_one] using hnorm
    calc
      ‖toEuclideanLin K v‖ ^ 2 ≤ ((1 / 23 : ℝ) ^ t) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
      _ = (1 / 23 : ℝ) ^ (2 * t) := by rw [← pow_mul]; congr 1; omega
  exact Matrix.exists_phase_normalized_filter_output K u x hu hfix
    ((1 / 23 : ℝ) ^ (2 * t)) hperp hx

/-- Among the `n` coordinate starts, one has both inverse-polynomial leading overlap and
the phase-aligned normalized power estimate.  Thus the power method needs no search over
an exponentially large vector net. -/
theorem Matrix.PosSemidef.exists_basisVector_phase_normalized_scaled_power
    {n : ℕ} (hn : 0 < n) {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ (Fin n)} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) (t : ℕ) :
    ∃ i : Fin n,
      1 / (n : ℝ) ≤ ‖⟪EuclideanSpace.basisFun (Fin n) ℂ i, u⟫_ℂ‖ ^ 2 ∧
      let e := EuclideanSpace.basisFun (Fin n) ℂ i
      let K := ((μ : ℂ)⁻¹ • σ) ^ t
      toEuclideanLin K e ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
        let ψ := c • (‖toEuclideanLin K e‖⁻¹ : ℂ) • toEuclideanLin K e
        ‖ψ‖ = 1 ∧
          ‖ψ - u‖ ^ 2 ≤ 2 * (1 / 23 : ℝ) ^ (2 * t) *
            ‖e - ⟪u, e⟫_ℂ • u‖ ^ 2 / ‖⟪u, e⟫_ℂ‖ ^ 2 := by
  obtain ⟨i, hi⟩ := exists_basisVector_sq_overlap_ge_inv hn u hu
  let e := EuclideanSpace.basisFun (Fin n) ℂ i
  have hpositive : 0 < 1 / (n : ℝ) := one_div_pos.mpr (by exact_mod_cast hn)
  have hie : ⟪u, e⟫_ℂ ≠ 0 := by
    intro hie
    have hzero : ‖⟪e, u⟫_ℂ‖ ^ 2 = 0 := by
      rw [norm_inner_symm, hie, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    rw [hzero] at hi
    exact (not_lt_of_ge hi) hpositive
  refine ⟨i, hi, ?_⟩
  exact Matrix.PosSemidef.exists_phase_normalized_inv_eigenvalue_scaled_power
    hσ htr hu huσ hμ e hie t

/-- Removing the component parallel to a unit vector cannot increase the norm. -/
theorem norm_sub_inner_smul_le_of_norm_eq_one
    {n : Type*} [Fintype n] {u x : EuclideanSpace ℂ n} (hu : ‖u‖ = 1) :
    ‖x - ⟪u, x⟫_ℂ • u‖ ≤ ‖x‖ := by
  have horth : ⟪x - ⟪u, x⟫_ℂ • u, ⟪u, x⟫_ℂ • u⟫_ℂ = 0 := by
    have hucomp : ⟪u, x - ⟪u, x⟫_ℂ • u⟫_ℂ = 0 := by
      rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
      simp
    rw [inner_smul_right, inner_eq_zero_symm.mpr hucomp, mul_zero]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (𝕜 := ℂ) (x - ⟪u, x⟫_ℂ • u) (⟪u, x⟫_ℂ • u) horth
  rw [sub_add_cancel] at hpyth
  nlinarith [norm_nonneg (x - ⟪u, x⟫_ℂ • u), norm_nonneg x,
    sq_nonneg ‖⟪u, x⟫_ℂ • u‖]

/-- One of the `n` normalized coordinate-start power sequences has squared phase-aligned
error at most `2 n / 23^(2t)`. -/
theorem Matrix.PosSemidef.exists_basisVector_scaled_power_sq_distance_le
    {n : ℕ} (hn : 0 < n) {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ (Fin n)} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) (t : ℕ) :
    ∃ i : Fin n,
      let e := EuclideanSpace.basisFun (Fin n) ℂ i
      let K := ((μ : ℂ)⁻¹ • σ) ^ t
      toEuclideanLin K e ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
        let ψ := c • (‖toEuclideanLin K e‖⁻¹ : ℂ) • toEuclideanLin K e
        ‖ψ‖ = 1 ∧ ‖ψ - u‖ ^ 2 ≤ 2 * (n : ℝ) * (1 / 23 : ℝ) ^ (2 * t) := by
  obtain ⟨i, hi, hKi, c, hc, hunit, herror⟩ :=
    Matrix.PosSemidef.exists_basisVector_phase_normalized_scaled_power
      hn hσ htr hu huσ hμ t
  let e := EuclideanSpace.basisFun (Fin n) ℂ i
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℂ).orthonormal.1 i
  have hperp : ‖e - ⟪u, e⟫_ℂ • u‖ ^ 2 ≤ 1 := by
    have hh := norm_sub_inner_smul_le_of_norm_eq_one hu (x := e)
    rw [he] at hh
    nlinarith [norm_nonneg (e - ⟪u, e⟫_ℂ • u)]
  have hden : 1 / (n : ℝ) ≤ ‖⟪u, e⟫_ℂ‖ ^ 2 := by
    simpa only [e, norm_inner_symm] using hi
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨i, hKi, c, hc, hunit, herror.trans ?_⟩
  calc
    2 * (1 / 23 : ℝ) ^ (2 * t) * ‖e - ⟪u, e⟫_ℂ • u‖ ^ 2 /
          ‖⟪u, e⟫_ℂ‖ ^ 2
        ≤ 2 * (1 / 23 : ℝ) ^ (2 * t) * 1 / (1 / (n : ℝ)) := by
          gcongr
    _ = 2 * (n : ℝ) * (1 / 23 : ℝ) ^ (2 * t) := by
      field_simp [ne_of_gt hnreal]

/-- A completely elementary polynomial iteration count suffices for the coordinate-start
power method.  Taking `ceil (n / ζ²)` steps makes `2 n / 23^(2t)` at most `ζ²`. -/
theorem scaledPower_error_le_of_ceil_iterationCount
    (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    let t := ⌈(n : ℝ) / ζ ^ 2⌉₊
    2 * (n : ℝ) * (1 / 23 : ℝ) ^ (2 * t) ≤ ζ ^ 2 := by
  let t := ⌈(n : ℝ) / ζ ^ 2⌉₊
  have hζsq : 0 < ζ ^ 2 := sq_pos_of_pos hζ
  have hceil : (n : ℝ) / ζ ^ 2 ≤ (t : ℝ) := Nat.le_ceil _
  have hnle : (n : ℝ) ≤ (t : ℝ) * ζ ^ 2 := (div_le_iff₀ hζsq).mp hceil
  have hbase : 2 * (t : ℝ) + 1 ≤ (23 : ℝ) ^ (2 * t) := by
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [Nat.cast_succ, Nat.mul_succ, pow_add]
        norm_num
        nlinarith [show 0 ≤ (t : ℝ) by positivity]
  have htden : 0 < 2 * (t : ℝ) + 1 := by positivity
  have hpow : (1 / 23 : ℝ) ^ (2 * t) ≤ 1 / (2 * (t : ℝ) + 1) := by
    rw [_root_.one_div_pow]
    exact one_div_le_one_div_of_le htden hbase
  calc
    2 * (n : ℝ) * (1 / 23 : ℝ) ^ (2 * t)
        ≤ 2 * (n : ℝ) * (1 / (2 * (t : ℝ) + 1)) := by gcongr
    _ = (2 * (n : ℝ)) / (2 * (t : ℝ) + 1) := by ring
    _ ≤ ζ ^ 2 := (div_le_iff₀ htden).mpr (by nlinarith)

/-- At the LVV residual tolerance, the elementary power-iteration count is bounded by an
explicit polynomial in the compressed dimension, the chain length, and the inverse gap.
This is the counting part of the leading-vector runtime estimate in LVV13,
`algo53.tex`, lines 477--478 and 493--505. -/
theorem lvvPower_iterationCount_lt (n L : ℕ) (hL : 0 < L)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    let η := 11 * Δ / (778752 * L)
    let t := ⌈(n : ℝ) / η ^ 2⌉₊
    (t : ℝ) < (n : ℝ) * (778752 * L : ℝ) ^ 2 / (11 * Δ) ^ 2 + 1 := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hη : 0 < 11 * Δ / (778752 * L) := by positivity
  have harg : 0 ≤ (n : ℝ) / (11 * Δ / (778752 * L)) ^ 2 := by positivity
  calc
    (⌈(n : ℝ) / (11 * Δ / (778752 * L)) ^ 2⌉₊ : ℝ)
        < (n : ℝ) / (11 * Δ / (778752 * L)) ^ 2 + 1 :=
          Nat.ceil_lt_add_one harg
    _ = (n : ℝ) * (778752 * L : ℝ) ^ 2 / (11 * Δ) ^ 2 + 1 := by
      field_simp

/-- Trying all `n` deterministic coordinate starts uses fewer than `n` times the explicit
single-start iteration budget.  Thus the number of dense matrix-vector applications in
the LVV leading-vector stage is polynomial once a compressed density is given. -/
theorem lvvPower_totalIterationCount_lt (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    let η := 11 * Δ / (778752 * L)
    let t := ⌈(n : ℝ) / η ^ 2⌉₊
    ((n * t : ℕ) : ℝ) <
      (n : ℝ) * ((n : ℝ) * (778752 * L : ℝ) ^ 2 / (11 * Δ) ^ 2 + 1) := by
  have ht := lvvPower_iterationCount_lt n L hL hΔ
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  simpa only [Nat.cast_mul] using mul_lt_mul_of_pos_left ht hnreal

/-- With `ceil (n / ζ²)` iterations, one of the `n` normalized coordinate-start power
sequences lies within distance `ζ` of the leading eigenvector, up to a unit phase. -/
theorem Matrix.PosSemidef.exists_basisVector_scaled_power_distance_le
    {n : ℕ} (hn : 0 < n) {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ (Fin n)} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) {ζ : ℝ} (hζ : 0 < ζ) :
    let t := ⌈(n : ℝ) / ζ ^ 2⌉₊
    ∃ i : Fin n,
      let e := EuclideanSpace.basisFun (Fin n) ℂ i
      let K := ((μ : ℂ)⁻¹ • σ) ^ t
      toEuclideanLin K e ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
        let ψ := c • (‖toEuclideanLin K e‖⁻¹ : ℂ) • toEuclideanLin K e
        ‖ψ‖ = 1 ∧ ‖ψ - u‖ ≤ ζ := by
  let t := ⌈(n : ℝ) / ζ ^ 2⌉₊
  obtain ⟨i, hKi, c, hc, hunit, hsq⟩ :=
    Matrix.PosSemidef.exists_basisVector_scaled_power_sq_distance_le
      hn hσ htr hu huσ hμ t
  refine ⟨i, hKi, c, hc, hunit, ?_⟩
  have htarget := scaledPower_error_le_of_ceil_iterationCount n hζ
  change ‖c • (‖toEuclideanLin (((μ : ℂ)⁻¹ • σ) ^ t)
    (EuclideanSpace.basisFun (Fin n) ℂ i)‖⁻¹ : ℂ) •
      toEuclideanLin (((μ : ℂ)⁻¹ • σ) ^ t)
        (EuclideanSpace.basisFun (Fin n) ℂ i) - u‖ ≤ ζ
  change 2 * (n : ℝ) * (1 / 23 : ℝ) ^ (2 * t) ≤ ζ ^ 2 at htarget
  nlinarith [norm_nonneg (c • (‖toEuclideanLin (((μ : ℂ)⁻¹ • σ) ^ t)
    (EuclideanSpace.basisFun (Fin n) ℂ i)‖⁻¹ : ℂ) •
      toEuclideanLin (((μ : ℂ)⁻¹ • σ) ^ t)
        (EuclideanSpace.basisFun (Fin n) ℂ i) - u)]

/-- For a trace-one positive matrix, distance from an exact eigenvector controls the
residual with factor two. -/
theorem Matrix.PosSemidef.norm_eigenresidual_le_two_mul_distance
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ η : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ0 : 0 ≤ μ) (hdist : ‖z - u‖ ≤ η) :
    ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ 2 * η := by
  have huL : toEuclideanLin σ u = (μ : ℂ) • u := by
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
  have hμ1 := Matrix.PosSemidef.eigenvalue_le_one_of_trace_eq_one hσ htr hu huσ
  have hcontract := Matrix.PosSemidef.norm_toEuclideanLin_apply_le_of_trace_eq_one
    hσ htr (z - u)
  have hrewrite : toEuclideanLin σ z - (μ : ℂ) • z =
      toEuclideanLin σ (z - u) - (μ : ℂ) • (z - u) := by
    rw [map_sub, huL, smul_sub]
    module
  rw [hrewrite]
  calc
    ‖toEuclideanLin σ (z - u) - (μ : ℂ) • (z - u)‖
        ≤ ‖toEuclideanLin σ (z - u)‖ + ‖(μ : ℂ) • (z - u)‖ := norm_sub_le _ _
    _ ≤ ‖z - u‖ + μ * ‖z - u‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ0]
      gcongr
    _ ≤ η + 1 * η := by gcongr
    _ = 2 * η := by ring

/-- The explicit coordinate-start power method discharges any conclusion whose numerical
interface asks for a unit vector with residual at most `2η`. -/
theorem Matrix.PosSemidef.exists_basisVector_scaled_power_of_residual_certificate
    {n : ℕ} (hn : 0 < n) {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ (Fin n)} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) {η : ℝ} (hη : 0 < η)
    (P : EuclideanSpace ℂ (Fin n) → Prop)
    (hcert : ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ = 1 →
      ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ 2 * η → P z) :
    let t := ⌈(n : ℝ) / η ^ 2⌉₊
    ∃ i : Fin n,
      let e := EuclideanSpace.basisFun (Fin n) ℂ i
      let K := ((μ : ℂ)⁻¹ • σ) ^ t
      toEuclideanLin K e ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
        let ψ := c • (‖toEuclideanLin K e‖⁻¹ : ℂ) • toEuclideanLin K e
        ‖ψ‖ = 1 ∧ P ψ := by
  obtain ⟨i, hKi, c, hc, hunit, hdist⟩ :=
    Matrix.PosSemidef.exists_basisVector_scaled_power_distance_le
      hn hσ htr hu huσ hμ hη
  refine ⟨i, hKi, c, hc, hunit, hcert _ hunit ?_⟩
  exact Matrix.PosSemidef.norm_eigenresidual_le_two_mul_distance
    hσ htr hu huσ (by linarith only [hμ]) hdist

end TNLean.MPS.AreaLaw
