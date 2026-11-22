/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChebyshevAGSP.SequenceParameters
import TNLean.MPS.AreaLaw.ChebyshevAGSP.ChangingTargetStep
import TNLean.MPS.AreaLaw.ChebyshevAGSP.CenteredWindow

/-!
# Accuracy-dependent window and polynomial parameters

The window is enlarged by twice the rounded fourth root of the cube of the
accuracy logarithm divided by the gap. The polynomial degree retains the
source square-root spectral-ceiling dependence.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517. The exact logarithmic
rank expression is retained; its fourth-root comparison is a separate
estimate from the shrinking and physical approximation statements.

## Actual accuracy-dependent filtering at the same physical cut

A fitting enlarged window also admits the initial favorable window at the
same cut. Filter the actual initialized vector with the actual polynomial
for the enlarged window. If the enlarged window does not fit, use the
original vector and its exact finite-dimensional cut-rank bound.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517.

**Scope restriction (physical gap and rank expression):** Local dimension
at least two and an actual first excited energy remain explicit. The
fitting-window construction derives the upper gap bound one from the physical
interaction; the boundary alternative needs no upper gap bound. The theorem
retains the exact selected sharp rank expression;
its uniform fourth-root logarithmic comparison and final sequential MPS
assembly remain separate. See
`docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

section

open Real

namespace TNLean.MPS.AreaLaw

/-- Logarithmic accuracy scale for a requested squared error. -/
noncomputable def aklvAccuracyLog (rho : ℝ) : ℝ := log (128 / rho)

/-- Rounded fourth-root increment in the accuracy-dependent window. -/
noncomputable def aklvAccuracyIncrement (g rho : ℝ) : ℕ :=
  ⌈sqrt (sqrt (aklvAccuracyLog rho ^ 3 / g))⌉₊

/-- The enlarged width preserves the parity of the initial physical window. -/
noncomputable def aklvAccuracyWidth (s0 : ℕ) (g rho : ℝ) : ℕ :=
  s0 + 2 * aklvAccuracyIncrement g rho

/-- Threshold making the clipped target accurate at the requested scale. -/
noncomputable def aklvAccuracyThreshold (g rho : ℝ) : ℝ :=
  aklvLogarithmicThreshold g + 16 * aklvAccuracyLog rho

/-- Degree for the actual polynomial at the enlarged width. -/
noncomputable def aklvAccuracyDegree (g rho : ℝ) (s : ℕ) : ℕ :=
  ⌈aklvAccuracyLog rho * sqrt ((2 * aklvAccuracyThreshold g rho + s) / g)⌉₊

/-- Exact common rank budget for the filtered and boundary alternatives. -/
noncomputable def aklvAccuracyRankBound (q s0 : ℕ) (g rho : ℝ) : ℕ :=
  let s := aklvAccuracyWidth s0 g rho
  let ell := aklvAccuracyDegree g rho s
  max ((q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) *
    (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))) (q ^ (s - s / 2))

/-- The logarithmic scale is at least one and its negative exponential is
exactly the requested squared error divided by 128. -/
theorem aklvAccuracyLog_bounds {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    1 ≤ aklvAccuracyLog rho ∧ exp (-aklvAccuracyLog rho) = rho / 128 := by
  have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have h128 : (1 : ℝ) ≤ log 128 := by
    have hid : log (128 : ℝ) = 7 * log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow]
      norm_num
    rw [hid]
    linarith
  constructor
  · apply h128.trans
    apply log_le_log (by norm_num)
    exact (le_div_iff₀ hrho).mpr (by nlinarith)
  · rw [aklvAccuracyLog, exp_neg, exp_log (by positivity)]
    field_simp

/-- The accuracy threshold is above the physical threshold and positive. -/
theorem aklvAccuracyThreshold_bounds {g rho : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    aklvLogarithmicThreshold g ≤ aklvAccuracyThreshold g rho ∧
      0 < aklvAccuracyThreshold g rho ∧
      exp (-aklvAccuracyThreshold g rho / 16) ≤ rho / 128 := by
  have hz := (aklvAccuracyLog_bounds hrho hrho1).1
  have hT : 0 ≤ aklvLogarithmicThreshold g := by
    have hlog := log_nonneg ((one_le_div hg).mpr hg1)
    unfold aklvLogarithmicThreshold
    positivity
  have ht : aklvLogarithmicThreshold g ≤ aklvAccuracyThreshold g rho := by
    unfold aklvAccuracyThreshold
    linarith
  refine ⟨ht, by unfold aklvAccuracyThreshold; linarith, ?_⟩
  have hid : -aklvAccuracyThreshold g rho / 16 =
      -aklvLogarithmicThreshold g / 16 - aklvAccuracyLog rho := by
    unfold aklvAccuracyThreshold
    ring
  rw [hid, exp_sub, div_eq_mul_inv, ← exp_neg,
    (aklvAccuracyLog_bounds hrho hrho1).2]
  have hexp : exp (-aklvLogarithmicThreshold g / 16) ≤ 1 :=
    exp_le_one_iff.mpr (by linarith)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ rho / 128)

/-- The selected actual degree makes the squared shrinking factor quadratic
in the requested squared error. -/
theorem aklvAccuracyDegree_shrink_le {g rho : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (s : ℕ) :
    (2 * exp (-2 * (aklvAccuracyDegree g rho s : ℝ) *
      sqrt ((9 * g / 10) / (2 * aklvAccuracyThreshold g rho + s)))) ^ 2 ≤
        rho ^ 2 / 4096 := by
  let z := aklvAccuracyLog rho
  let W := 2 * aklvAccuracyThreshold g rho + s
  let ell := aklvAccuracyDegree g rho s
  have hz : 0 ≤ z := by linarith [(aklvAccuracyLog_bounds hrho hrho1).1]
  have hW : 0 < W := by
    have ht := (aklvAccuracyThreshold_bounds hg hg1 hrho hrho1).2.1
    dsimp only [W]
    positivity
  have hproduct : sqrt (W / g) * sqrt ((9 * g / 10) / W) = sqrt (9 / 10) := by
    rw [← sqrt_mul (div_nonneg hW.le hg.le)]
    congr 1
    field_simp
  have hroot : (1 : ℝ) / 2 ≤ sqrt (9 / 10) := le_sqrt_of_sq_le (by norm_num)
  have hdegree : z * sqrt (W / g) ≤ (ell : ℝ) := Nat.le_ceil _
  have hscaled : 2 * z ≤ 4 * (ell : ℝ) * sqrt ((9 * g / 10) / W) := by
    have hmul := mul_le_mul_of_nonneg_right hdegree (sqrt_nonneg ((9 * g / 10) / W))
    have hzroot := mul_le_mul_of_nonneg_left hroot hz
    nlinarith [hproduct]
  have hexp : exp (-(2 * z)) = rho ^ 2 / 16384 := by
    have heq : -(2 * z) = (2 : ℕ) * (-z) := by push_cast; ring
    rw [heq, exp_nat_mul, (aklvAccuracyLog_bounds hrho hrho1).2]
    ring
  change (2 * exp (-2 * (ell : ℝ) * sqrt ((9 * g / 10) / W))) ^ 2 ≤ _
  calc
    _ = 4 * exp (-(4 * (ell : ℝ) * sqrt ((9 * g / 10) / W))) := by
      rw [mul_pow, ← exp_nat_mul]
      congr 2 <;> norm_num
      ring
    _ ≤ 4 * exp (-(2 * z)) := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num)
    _ = rho ^ 2 / 4096 := by rw [hexp]; ring

/-- The physical refinement's two actual error terms fit within the request. -/
theorem aklvAccuracy_refinement_error_le {g rho : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (s : ℕ) :
    16 * (2 * exp (-2 * (aklvAccuracyDegree g rho s : ℝ) *
      sqrt ((9 * g / 10) / (2 * aklvAccuracyThreshold g rho + s)))) ^ 2 +
      exp (-aklvAccuracyThreshold g rho / 16) / 50 ≤ rho := by
  have hdelta := aklvAccuracyDegree_shrink_le hg hg1 hrho hrho1 s
  have htarget := (aklvAccuracyThreshold_bounds hg hg1 hrho hrho1).2.2
  have hsquare : rho ^ 2 ≤ rho := by nlinarith
  nlinarith

/-- The integer increment retains the exact fourth-root scale. -/
theorem aklvAccuracyIncrement_bounds (g rho : ℝ) :
    sqrt (sqrt (aklvAccuracyLog rho ^ 3 / g)) ≤
        (aklvAccuracyIncrement g rho : ℝ) ∧
      (aklvAccuracyIncrement g rho : ℝ) <
        sqrt (sqrt (aklvAccuracyLog rho ^ 3 / g)) + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (sqrt_nonneg _)⟩

/-- The common rank budget retains exactly the sharp logarithmic expression
and the exact boundary cost. No exponential-in-degree estimate is substituted. -/
theorem aklvAccuracyRankBound_log {q : ℕ} (hq : 1 ≤ q) (s0 : ℕ) (g rho : ℝ) :
    let s := aklvAccuracyWidth s0 g rho
    let ell := aklvAccuracyDegree g rho s
    let D0 : ℕ := (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
    log (aklvAccuracyRankBound q s0 g rho : ℝ) =
      max (log (D0 : ℝ) + ((32 * (ell / s + Nat.sqrt ell + 1) : ℕ) : ℝ) *
        log ((q * (ell + 1) : ℕ) : ℝ))
        (((s - s / 2 : ℕ) : ℝ) * log (q : ℝ)) := by
  intro s ell D0
  let D : ℕ := (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1))
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hD0 : 0 < (D0 : ℝ) := by dsimp only [D0]; positivity
  have hD : 0 < (D : ℝ) := by dsimp only [D]; positivity
  have hlog : log ((D0 * D : ℕ) : ℝ) =
      log (D0 : ℝ) + ((32 * (ell / s + Nat.sqrt ell + 1) : ℕ) : ℝ) *
        log ((q * (ell + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, log_mul (ne_of_gt hD0) (ne_of_gt hD)]
    simp only [D, Nat.cast_pow, log_pow]
  have hboundary : log ((q ^ (s - s / 2) : ℕ) : ℝ) =
      (((s - s / 2 : ℕ) : ℝ) * log (q : ℝ)) := by
    rw [Nat.cast_pow, log_pow]
  change log ((max (D0 * D) (q ^ (s - s / 2)) : ℕ) : ℝ) = _
  rcases le_total (D0 * D) (q ^ (s - s / 2)) with hle | hle
  · have hlogle : log ((D0 * D : ℕ) : ℝ) ≤ log ((q ^ (s - s / 2) : ℕ) : ℝ) :=
      log_le_log (by rw [Nat.cast_mul]; exact mul_pos hD0 hD) (by exact_mod_cast hle)
    rw [hlog, hboundary] at hlogle
    rw [max_eq_right hle, hboundary, max_eq_right hlogle]
  · have hlogle : log ((q ^ (s - s / 2) : ℕ) : ℝ) ≤ log ((D0 * D : ℕ) : ℝ) :=
      log_le_log (by rw [Nat.cast_pow]; exact pow_pos hqpos _) (by exact_mod_cast hle)
    rw [hboundary, hlog] at hlogle
    rw [max_eq_left hle, hlog, max_eq_left hlogle]

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)
open ManyBody (cutMatrix)

open Matrix Polynomial
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- In the fitting-window alternative the output is the actual polynomial
image of the actual initialized vector, with both windows at the same cut.
AKLV, arXiv:1301.1162v1, lines 1503--1517. -/
def IsAKLVAccuracyFilteredOutput {L q : ℕ} (k s0 : ℕ)
    (Φ : ManyBody.BondInteraction L q)
    (g rho : ℝ) (Ω y : EuclideanSpace ℂ (Fin L → Fin q)) : Prop :=
  let s := aklvAccuracyWidth s0 g rho
  let t := aklvAccuracyThreshold g rho
  let ell := aklvAccuracyDegree g rho s
  ∃ (a a0 : ℕ) (e0 e : Fin 3 → ℝ) (x : EuclideanSpace ℂ (Fin L → Fin q))
      (E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)) (p : Polynomial ℝ) (c : ℂ),
    a + s / 2 = k ∧ a + s + 1 ≤ L ∧ a0 + s0 / 2 = k ∧
    (∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a0 s0 Φ j *ᵥ z = (e0 j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a0 s0 Φ j - (e0 j : ℂ) • 1).PosSemidef) ∧
    (∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a s Φ j *ᵥ z = (e j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a s Φ j - (e j : ℂ) • 1).PosSemidef) ∧
    IsAKLVSequenceInitialization a0 s0 Φ e0 g Ω x ∧ ‖x‖ = 1 ∧ ‖x - Ω‖ ^ 2 ≤ 1 / 16 ∧
    let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) Φ e t Finset.univ
    B.PosSemidef ∧ ‖B‖ ≤ 2 * t + s ∧ 0 ≤ E ∧ ‖φ‖ = 1 ∧
    toEuclideanLin B φ = (E : ℂ) • φ ∧
    (B - (E : ℂ) • 1 - ((9 * g / 10 : ℝ) : ℂ) •
      (1 - vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
    ‖φ - Ω‖ ^ 2 ≤ rho / 12800 ∧ p.natDegree = ell ∧ p.eval E = 1 ∧
    let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
    toEuclideanLin K φ = φ ∧ toEuclideanLin K x ≠ 0 ∧ ‖c‖ = 1 ∧
    y = c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x

/-- Every cut has an actual unit approximant at the selected sharp rank
budget. It is either exact at a boundary or an actual same-cut filter of
the favorable initialization. No area-law approximation is supplied. -/
theorem exists_aklv_physical_accuracy_window :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q k : ℕ) (_hq : 2 ≤ q) (_hk : k ≤ L)
        (Φ : ManyBody.BondInteraction L q)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ j, 0 ≤ Φ.term j) → (∀ j, Φ.term j ≤ 1) → ‖Ω‖ = 1 →
      Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      (Φ.hamiltonian - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ Φ.hamiltonian →
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
      ∃ y : EuclideanSpace ℂ (Fin L → Fin q), ‖y‖ = 1 ∧ ‖y - Ω‖ ^ 2 ≤ rho ∧
        (cutMatrix (leftBlock L k) y).rank ≤ aklvAccuracyRankBound q s0 g rho ∧
        (y = Ω ∨ IsAKLVAccuracyFilteredOutput k s0 Φ g rho Ω y) := by
  classical
  obtain ⟨A, hA, hA21, hsequence⟩ := exists_aklv_physical_changing_target_sequence
  refine ⟨A, hA, hA21, ?_⟩
  intro L q k hq hk Φ mu g Ω h0 h1 hΩ hground hgap hg hexcited rho hrho hrho1 u s0
  let s := aklvAccuracyWidth s0 g rho
  let m := aklvAccuracyIncrement g rho
  rcases aklv_centered_window_or_exact_rank (by omega) hk Ω (s := s) with hfit | hexact
  · obtain ⟨a, hcenter, ha⟩ := hfit
    have hsmall := aklv_initial_window_of_enlarged (s := s0) (m := m) ha
    let a0 := a + m
    obtain ⟨_hq, hg1, hs0, _hlogD0, e0, _E0, seq,
        hregional, _hEeq, _hE0, _hE6, hinvariant, hinitial, _hedges⟩ :=
      hsequence L q a0 Φ mu g Ω h0 h1 hΩ hground hgap hg hexcited hsmall.2
    let x := seq 0
    have hcenter0 : a0 + s0 / 2 = k := hsmall.1.trans hcenter
    have hx : ‖x‖ = 1 := (hinvariant 0).1
    have hxΩ : ‖x - Ω‖ ^ 2 ≤ 1 / 16 := by
      simpa only [(aklvSequenceWeight_zero_succ 0).1] using (hinvariant 0).2.1
    have hxrank : schmidtRank (WithLp.ofLp (ManyBody.cutVector (leftBlock L k) x)) ≤
        (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) := by
      have hr := (hinvariant 0).2.2
      rw [(aklvSequenceRankBound_zero_succ q g s0 0).1, hcenter0] at hr
      exact hr
    have hs : 6 ≤ s := by
      change 21 ≤ s0 at hs0
      dsimp only [s, aklvAccuracyWidth]
      omega
    obtain ⟨_hq', _hg1', e, _E0', hregional', _hEeq', _hE0', _hE6', hfilter⟩ :=
      exists_aklv_variable_window_filtered_output hs ha Φ h0 h1
        mu g Ω hΩ hground hgap hg hexcited x hx hxΩ
    let t := aklvAccuracyThreshold g rho
    let ell := aklvAccuracyDegree g rho s
    let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) Φ e t Finset.univ
    obtain ⟨hBpos, hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose,
        _hxφ, _hoverlap, hpoly⟩ :=
      hfilter t (aklvAccuracyThreshold_bounds hg hg1 hrho hrho1).1
    obtain ⟨p, hdegree, hpE, hfix, _hrankK, hKx, c, hc, hyunit, hyrank, _hcontract, hyΩ⟩ :=
      hpoly ell
    let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
    let y := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
    refine ⟨y, hyunit, hyΩ.trans (aklvAccuracy_refinement_error_le hg hg1 hrho hrho1 s),
      ?_, Or.inr ?_⟩
    · have hxrank' : (cutMatrix (leftBlock L (a + s / 2)) x).rank ≤
          (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) := by
        rw [hcenter]
        exact hxrank
      change (cutMatrix (leftBlock L (a + s / 2)) y).rank ≤
        _ * (cutMatrix (leftBlock L (a + s / 2)) x).rank at hyrank
      have hr := hyrank.trans (Nat.mul_le_mul_left _ hxrank')
      rw [hcenter] at hr
      apply hr.trans
      apply le_trans (le_of_eq (Nat.mul_comm _ _))
      exact le_max_left _ _
    · have htarget : ‖φ - Ω‖ ^ 2 ≤ rho / 12800 := by
        have ht := (aklvAccuracyThreshold_bounds hg hg1 hrho hrho1).2.2
        linarith
      exact ⟨a, a0, e0, e, x, E, φ, p, c, hcenter, ha, hcenter0, hregional, hregional', hinitial,
        hx, hxΩ, hBpos, hBnorm, hE, hφ, heigen, hprojector, htarget,
        hdegree, hpE, hfix, hKx, hc, rfl⟩
  · refine ⟨Ω, hΩ, by simpa using hrho.le, ?_, Or.inl rfl⟩
    exact hexact.trans (le_max_right _ _)

end TNLean.MPS.AreaLaw

end
