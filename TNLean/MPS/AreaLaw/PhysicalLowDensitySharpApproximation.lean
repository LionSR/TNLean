/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalLowDensityApproximation
import TNLean.MPS.AreaLaw.SharpRankCount

/-!
# Sharp logarithmic rank for an original low-energy band

The same initial viable space is refined by the actual polynomial family at
independent truncation and window scales. Its actual dimension contributes
exactly one logarithm of the original full-band dimension. The remaining
accuracy dependence has power three quarters of the logarithmic accuracy,
as in ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105.

**Scope restriction (physical intervals and fixed bandwidth):** The theorem
retains `q ≥ 2` and a coefficient for each fixed positive bandwidth. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`. The capped width is
explicit; comparison with the source variable uses its stated range
`0 < v ≤ etaLD`. No original-band gap or invariance is assumed.
-/

open scoped BigOperators TensorProduct ComplexOrder MatrixOrder InnerProductSpace
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- A normalized fixed-cut approximation has the sharp logarithmic rank bound,
with coefficient one on the logarithm of the original low-energy dimension.
ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_fixed_bandwidth_interval_low_energy_normalized_approximation
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q p r : ℕ) (v : ℝ) (hq : 2 ≤ q), p ≤ r → r ≤ L → 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ h0 : ∀ i, 0 ≤ h i, (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + c)
      let e := Tm.trans (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm
      let b := min v (etaLD / 2)
      let g := min (b / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let a := 16 + Real.log (1 / g) + Real.log (1 / delta)
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ψ ∈ G (etaLD - v) → ‖ψ‖ = 1 →
      ∃ φ : EuclideanSpace ℂ (Fin L → Fin q), ‖φ‖ = 1 ∧
        1 - delta ≤ ‖⟪φ, ψ⟫_ℂ‖ ∧
        Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
          Real.log (Module.finrank ℂ (G etaLD) : ℝ) +
          K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
            (1 + Real.log a) := by
  classical
  obtain ⟨Kb, C, hKb, hC, hactual⟩ :=
    exists_fixed_bandwidth_normalized_low_energy_approximation_of_independent_scales etaLD hLD
  let beta : ℝ := (7 * C) ^ (1 / 4 : ℝ)
  let kappa : ℝ := 44 * (1 + Real.log (11 + beta))
  let K : ℝ := 8 * Kb + 2 * kappa * (11 + beta)
  have hbeta : 0 ≤ beta := Real.rpow_nonneg (by linarith only [hC]) _
  have hlogbeta : 0 ≤ Real.log (11 + beta) := Real.log_nonneg (by linarith only [hbeta])
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro L q p r v hq hpr hrL hv h hs h0 h1 config H hRaw
    J betaCoord tau U Phi Tm G e b g u
  let : Nonempty (Fin L → Fin q) := config
  have hb : 0 < b := lt_min hv (by positivity)
  have hg : 0 < g := lt_min (by dsimp only [b]; positivity) (by norm_num)
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgb : g ≤ b / 2 := (min_le_left _ _).trans (by linarith only [hb])
  have hinv : 1 ≤ 1 / g := (one_le_div hg).2 hg1
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg hinv
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hu : 1 ≤ u := by dsimp only [u]; linarith only [hlogq, hlogg]
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hcost : Kb / (b / 2) *
      (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3 ≤
      8 * Kb / g * u ^ 3 := by
    have hinvb : 1 / (b / 2) ≤ 1 / g := one_div_le_one_div_of_le hg hgb
    have hlogb : Real.log (1 + 1 / (b / 2)) ≤ 1 + Real.log (1 / g) := by
      calc
        _ ≤ Real.log (2 * (1 / g)) :=
          Real.log_le_log (by positivity) (by linarith only [hinv, hinvb])
        _ = Real.log 2 + Real.log (1 / g) :=
          Real.log_mul (by norm_num) (by positivity)
        _ ≤ 1 + Real.log (1 / g) := by
          linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hbase : 1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2)) ≤ 2 * u := by
      dsimp only [u]
      linarith only [hlogb, hlogq, hlogg]
    have hbase0 : 0 ≤ 1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2)) := by
      have hn := Real.log_nonneg (show 1 ≤ 1 + 1 / (b / 2) by
        linarith only [one_div_pos.mpr (show 0 < b / 2 by positivity)])
      linarith only [hlogq, hn]
    calc
      _ ≤ Kb / g * (2 * u) ^ 3 := mul_le_mul
        (div_le_div_of_nonneg_left hKb.le hg hgb)
        (pow_le_pow_left₀ hbase0 hbase 3) (by positivity) (by positivity)
      _ = _ := by ring
  obtain ⟨W0, hWdim, _hW0, happ⟩ := hactual L q p r v hq hpr hrL hv h hs h0 h1
  intro delta hdelta hdelta1 a ψ hψG hψ
  obtain ⟨ell, hell, hwindow, hvec⟩ := happ delta hdelta hdelta1
  let D1 : ℕ := (q * ell ^ 2) ^ (22 * ell)
  obtain ⟨φ, hφ, hoverlap, hrank⟩ := hvec ψ hψG hψ
  have ha : 1 ≤ a := by
    have hl := Real.log_nonneg ((one_le_div hdelta).2 hdelta1)
    dsimp only [a]
    linarith only [hlogg, hl]
  let X := u ^ 3 / g
  let Y := (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u
  let P := 1 + Real.log a
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hP : 1 ≤ P := by dsimp only [P]; linarith only [Real.log_nonneg ha]
  have hXgrow : X ≤ (X + Y) * P := by
    nlinarith only [hY, mul_nonneg (add_nonneg hX hY) (sub_nonneg.mpr hP)]
  have hwindow' : (ell : ℝ) ≤
      10 / g + beta * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) := by
    change (ell : ℝ) ≤ 8 / g + beta * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) at hwindow
    have hdiv : 8 / g ≤ 10 / g :=
      div_le_div_of_nonneg_right (by norm_num) hg.le
    linarith only [hwindow, hdiv]
  have hcount : Real.log (D1 : ℝ) ≤ kappa *
      (10 / g + beta * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * u * P :=
    Real.sharp_polynomial_family_log_count q ell g a beta
      (by omega) hell hg hg1 ha hbeta hwindow'
  have hucube : u ≤ u ^ 3 := by
    have hsq : 1 ≤ u ^ 2 := one_le_pow₀ hu
    nlinarith only [mul_le_mul_of_nonneg_left hsq hu0]
  have hpoly : (10 / g + beta * (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) * u ≤
      (11 + beta) * (X + Y) := by
    have hux : u / g ≤ X := div_le_div_of_nonneg_right hucube hg.le
    calc
      _ = 10 * (u / g) + beta * Y := by dsimp only [Y]; ring
      _ ≤ 10 * X + beta * Y := by linarith only [hux]
      _ ≤ (11 + beta) * (X + Y) := by
        nlinarith only [hX, hY, mul_nonneg hbeta hX]
  have hcountgrow : 2 * Real.log (D1 : ℝ) ≤
      2 * kappa * (11 + beta) * (X + Y) * P := by
    have hscale := mul_le_mul_of_nonneg_left hpoly hkappa.le
    have hscaleP := mul_le_mul_of_nonneg_right hscale (zero_le_one.trans hP)
    nlinarith only [hcount, hscaleP]
  refine ⟨φ, hφ, hoverlap, ?_⟩
  change Real.log (Matrix.schmidtRank (WithLp.ofLp (e φ)) : ℝ) ≤
    Real.log (Module.finrank ℂ (G etaLD) : ℝ) + K * (X + Y) * P
  by_cases hzero : Matrix.schmidtRank (WithLp.ofLp (e φ)) = 0
  · rw [hzero, Nat.cast_zero, Real.log_zero]
    exact add_nonneg (Real.log_natCast_nonneg _) (by positivity)
  · have hWpos : (0 : ℝ) < (Module.finrank ℂ W0 : ℝ) := by
      have hm : 0 < Module.finrank ℂ W0 * D1 ^ 2 :=
        (Nat.pos_of_ne_zero hzero).trans_le hrank
      exact_mod_cast Nat.pos_of_mul_pos_right hm
    have hrpos : (0 : ℝ) < (Module.finrank ℂ (G etaLD) : ℝ) :=
      pos_of_mul_pos_left (hWpos.trans_le hWdim) (Real.exp_pos _).le
    have hlogW : Real.log (Module.finrank ℂ W0 : ℝ) ≤
        Real.log (Module.finrank ℂ (G etaLD) : ℝ) + 8 * Kb * X := by
      have hl := Real.log_le_log hWpos hWdim
      rw [Real.log_mul hrpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
      have hc : Kb / (b / 2) *
          (1 + Real.log (q : ℝ) + Real.log (1 + 1 / (b / 2))) ^ 3 ≤ 8 * Kb * X := by
        calc
          _ ≤ 8 * Kb / g * u ^ 3 := hcost
          _ = _ := by dsimp only [X]; ring
      linarith only [hl, hc]
    have hbudget : Real.log ((Module.finrank ℂ W0 * D1 ^ 2 : ℕ) : ℝ) ≤
        Real.log (Module.finrank ℂ (G etaLD) : ℝ) + K * (X + Y) * P := by
      have hDpos : (0 : ℝ) < (D1 : ℝ) := by dsimp only [D1]; positivity
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hWpos.ne' (pow_pos hDpos 2).ne', Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      have hbasegrow := mul_le_mul_of_nonneg_left hXgrow (by positivity : 0 ≤ 8 * Kb)
      dsimp only [K]
      nlinarith only [hlogW, hcountgrow, hbasegrow]
    exact (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hzero)
      (by exact_mod_cast hrank)).trans hbudget

end TNLean.MPS.AreaLaw
