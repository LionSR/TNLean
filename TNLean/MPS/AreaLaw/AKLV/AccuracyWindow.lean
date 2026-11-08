/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.ChangingTargets
import TNLean.MPS.AreaLaw.AKLV.CenteredWindow
import TNLean.MPS.AreaLaw.AKLV.OptimizedTailParameters

/-!
# Actual accuracy-dependent filtering at the same physical cut

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

open Matrix Polynomial
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- In the fitting-window alternative the output is the actual polynomial
image of the actual initialized vector, with both windows at the same cut.
AKLV, arXiv:1301.1162v1, lines 1503--1517. -/
def IsAKLVAccuracyFilteredOutput {L q : ℕ} (k s0 : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (g rho : ℝ) (Ω y : EuclideanSpace ℂ (Fin L → Fin q)) : Prop :=
  let s := aklvAccuracyWidth s0 g rho
  let t := aklvAccuracyThreshold g rho
  let ell := aklvAccuracyDegree g rho s
  ∃ (a a0 : ℕ) (e0 e : Fin 3 → ℝ) (x : EuclideanSpace ℂ (Fin L → Fin q))
      (E : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)) (p : Polynomial ℝ) (c : ℂ),
    a + s / 2 = k ∧ a + s + 1 ≤ L ∧ a0 + s0 / 2 = k ∧
    (∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a0 s0 h j *ᵥ z = (e0 j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a0 s0 h j - (e0 j : ℂ) • 1).PosSemidef) ∧
    (∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
      (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ z = (e j : ℂ) • z) ∧
      ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef) ∧
    IsAKLVSequenceInitialization a0 s0 h e0 g Ω x ∧ ‖x‖ = 1 ∧ ‖x - Ω‖ ^ 2 ≤ 1 / 16 ∧
    let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ
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
        (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h j) (interval L j.val (j.val + 2))) →
      (∀ j, 0 ≤ h j) → (∀ j, h j ≤ 1) → ‖Ω‖ = 1 →
      (∑ j, h j) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      ((∑ j, h j) - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ (∑ j, h j) →
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
      ∃ y : EuclideanSpace ℂ (Fin L → Fin q), ‖y‖ = 1 ∧ ‖y - Ω‖ ^ 2 ≤ rho ∧
        (cutMatrix y k).rank ≤ aklvAccuracyRankBound q s0 g rho ∧
        (y = Ω ∨ IsAKLVAccuracyFilteredOutput k s0 h g rho Ω y) := by
  classical
  obtain ⟨A, hA, hA21, hsequence⟩ := exists_aklv_physical_changing_target_sequence
  refine ⟨A, hA, hA21, ?_⟩
  intro L q k hq hk h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited rho hrho hrho1 u s0
  let s := aklvAccuracyWidth s0 g rho
  let m := aklvAccuracyIncrement g rho
  rcases aklv_centered_window_or_exact_rank (by omega) hk Ω (s := s) with hfit | hexact
  · obtain ⟨a, hcenter, ha⟩ := hfit
    have hsmall := aklv_initial_window_of_enlarged (s := s0) (m := m) ha
    let a0 := a + m
    obtain ⟨_hq, hg1, hs0, _hlogD0, e0, _E0, seq,
        hregional, _hEeq, _hE0, _hE6, hinvariant, hinitial, _hedges⟩ :=
      hsequence L q a0 h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited hsmall.2
    let x := seq 0
    have hcenter0 : a0 + s0 / 2 = k := hsmall.1.trans hcenter
    have hx : ‖x‖ = 1 := (hinvariant 0).1
    have hxΩ : ‖x - Ω‖ ^ 2 ≤ 1 / 16 := by
      simpa only [(aklvSequenceWeight_zero_succ 0).1] using (hinvariant 0).2.1
    have hxrank : schmidtRank (WithLp.ofLp (Entropy.cutVector (leftBlock L k) x)) ≤
        (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) := by
      have hr := (hinvariant 0).2.2
      rw [(aklvSequenceRankBound_zero_succ q g s0 0).1, hcenter0] at hr
      exact hr
    have hs : 6 ≤ s := by
      change 21 ≤ s0 at hs0
      dsimp only [s, aklvAccuracyWidth]
      omega
    obtain ⟨_hq', _hg1', e, _E0', hregional', _hEeq', _hE0', _hE6', hfilter⟩ :=
      exists_aklv_variable_window_filtered_output hs ha h hsupp h0 h1
        mu g Ω hΩ hground hgap hg hexcited x hx hxΩ
    let t := aklvAccuracyThreshold g rho
    let ell := aklvAccuracyDegree g rho s
    let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e t Finset.univ
    obtain ⟨hBpos, hBnorm, E, φ, hE, hφ, heigen, hprojector, hclose,
        _hxφ, _hoverlap, hpoly⟩ :=
      hfilter t (aklvAccuracyThreshold_bounds hg hg1 hrho hrho1).1
    obtain ⟨p, hdegree, hpE, hfix, _hrankK, hKx, c, hc, hyunit, hyrank, _hcontract, hyΩ⟩ :=
      hpoly ell
    let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
    let y := c • (‖toEuclideanLin K x‖⁻¹ : ℂ) • toEuclideanLin K x
    refine ⟨y, hyunit, hyΩ.trans (aklvAccuracy_refinement_error_le hg hg1 hrho hrho1 s),
      ?_, Or.inr ?_⟩
    · have hxrank' : (cutMatrix x (a + s / 2)).rank ≤
          (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) := by
        rw [hcenter]
        exact hxrank
      change (cutMatrix y (a + s / 2)).rank ≤
        _ * (cutMatrix x (a + s / 2)).rank at hyrank
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
