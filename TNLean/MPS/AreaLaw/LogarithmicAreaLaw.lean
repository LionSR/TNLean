/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ComponentReduction

/-!
# Logarithmic dimension dependence and polynomial range dependence

For fixed interaction range, the logarithmic interaction-energy estimate gives
an area-law coefficient bounded by a range-dependent multiple of `log q ^ 3`.
The coefficient is evaluated at local dimension two and is chosen before the
chain length, Hamiltonian, ground vector and region.

Source: the TNLean one-dimensional note, `part1_arealaw.tex`, Remark `rem:sharper`,
lines 711–745. The two general dimension-logarithmic bounds use the finite-range interaction model
without a consecutive-window hypothesis. The polynomial-range bound additionally
requires every nonzero interaction to occupy a full contained consecutive window.
Its absolute coefficient is fixed before the local dimension, interaction range,
term norm bound, gap, chain length, Hamiltonian, ground vector and region.
Range zero and local dimension one are handled by their zero-entropy conclusions.

**Scope restriction (full windows):** `chainAreaLaw_of_consecutive_terms_polynomial_range`
and `domainAreaLaw_of_consecutive_terms_polynomial_range` assume that every nonzero
interaction occupies a full window of `R + 1` consecutive sites contained in the chain or
domain; recorded in `docs/paper-gaps/tnlean_one_dimensional_discount_constants.tex`,
section "Full consecutive windows".
-/

open TNLean.Lattice

namespace TNLean.MPS.AreaLaw

variable {L q R : ℕ} {J Δ : ℝ}

/-- The coefficient `K_R` of `log³ q` in the area-law constant at fixed range: `C₀(2, R)`
with the energy entry of `C₁(2, R)` replaced by its logarithmic entry, divided by
`log³ 2`. Source: the note, Remark `rem:sharper`, `part1_arealaw.tex`, lines 711–745. -/
noncomputable def chainLogCubeConst (R : ℕ) : ℝ :=
  ((8 * R * Real.log 2 + Real.log 2) *
      (5 + 64 * Real.exp 1 * chainCrossConst R *
          Real.log (Real.exp 1 * (2 : ℝ) ^ (R + 1)) ^ 2 + 128 * chainBudgetConst 2 R) +
      1024 * Real.exp 1 * chainBudgetConst 2 R) / Real.log 2 ^ 3

/-- The area-law coefficient grows at most cubically in the logarithm of the local
dimension, with the range fixed. The energy entry of `C₁(q, R)` is bounded by its logarithmic
entry `64 e N_R log² (e q^{R + 1})`, so the coefficient of `log³ q` is `C₀(2, R)` with the
energy entry replaced by that logarithmic entry at `q = 2`. Source: the note, Remark
`rem:sharper`, `part1_arealaw.tex`, lines 711–745. -/
theorem chainAreaLawConst_le_mul_log_cube (hq : 2 ≤ q) :
    chainAreaLawConst q R ≤ chainLogCubeConst R * Real.log (q : ℝ) ^ 3 := by
  unfold chainLogCubeConst
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcx : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hx : 0 ≤ Real.log (q : ℝ) := hc.le.trans hcx
  let t : ℝ := Real.log (q : ℝ) / Real.log 2
  have ht : 1 ≤ t := (one_le_div hc).mpr hcx
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have ht23 : t ^ 2 ≤ t ^ 3 := by
    calc t ^ 2 = t ^ 2 * 1 := by ring
         _ ≤ t ^ 2 * t := mul_le_mul_of_nonneg_left ht (sq_nonneg t)
         _ = t ^ 3 := by ring
  have hlog : Real.log (q : ℝ) = Real.log 2 * t := by
    dsimp only [t]
    field_simp [hc.ne']
  have hℓ (d : ℝ) (hd : 0 < d) :
      Real.log (Real.exp 1 * d ^ (R + 1)) = 1 + ((R : ℝ) + 1) * Real.log d := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (pow_ne_zero _ hd.ne'), Real.log_exp, Real.log_pow,
      Nat.cast_add, Nat.cast_one]
  set ℓ₂ : ℝ := Real.log (Real.exp 1 * (2 : ℝ) ^ (R + 1))
  have hℓ₂ : ℓ₂ = 1 + ((R : ℝ) + 1) * Real.log 2 := hℓ 2 (by norm_num)
  have hℓq : Real.log (Real.exp 1 * (q : ℝ) ^ (R + 1)) ≤ ℓ₂ * t := by
    rw [hℓ (q : ℝ) (by exact_mod_cast (show 0 < q by omega)), hℓ₂, hlog]
    have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith only [ht, hR, hc]
  have hℓq0 : 0 ≤ Real.log (Real.exp 1 * (q : ℝ) ^ (R + 1)) := by
    rw [hℓ (q : ℝ) (by exact_mod_cast (show 0 < q by omega))]
    positivity
  have hℓsq : Real.log (Real.exp 1 * (q : ℝ) ^ (R + 1)) ^ 2 ≤ ℓ₂ ^ 2 * t ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hℓq0 hℓq 2
  have hN : (0 : ℝ) ≤ chainCrossConst R := Nat.cast_nonneg _
  have hB : chainBudgetConst q R ≤ chainBudgetConst 2 R * t ^ 2 := by
    calc chainBudgetConst q R
        ≤ (chainBudgetConst 2 R / Real.log 2 ^ 2) * Real.log (q : ℝ) ^ 2 :=
          chainBudgetConst_le_mul_log_sq hq
      _ = chainBudgetConst 2 R * t ^ 2 := by simp only [t, div_pow]; ring
  have hB2 : 1 ≤ chainBudgetConst 2 R := one_le_chainBudgetConst 2 R
  have hE : min (32 * chainCrossConst R * (q : ℝ) ^ (2 * (R + 1)))
      (64 * Real.exp 1 * chainCrossConst R *
        Real.log (Real.exp 1 * (q : ℝ) ^ (R + 1)) ^ 2) ≤
      64 * Real.exp 1 * chainCrossConst R * ℓ₂ ^ 2 * t ^ 2 :=
    (min_le_right _ _).trans (by
      rw [show 64 * Real.exp 1 * chainCrossConst R * ℓ₂ ^ 2 * t ^ 2 =
        64 * Real.exp 1 * chainCrossConst R * (ℓ₂ ^ 2 * t ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hℓsq (by positivity))
  set C₁' : ℝ := 5 + 64 * Real.exp 1 * chainCrossConst R * ℓ₂ ^ 2 +
    128 * chainBudgetConst 2 R
  have hC : chainShellConst q R ≤ C₁' * t ^ 2 := by
    rw [chainShellConst, cutShellConst, ← chainBudgetConst]
    nlinarith only [hE, hB, ht2]
  have hC0 : 0 ≤ chainShellConst q R := cutShellConst_nonneg _ q R
  have hpre : 8 * R * Real.log (q : ℝ) + Real.log 2 ≤ (8 * R * Real.log 2 + Real.log 2) * t := by
    rw [hlog]
    have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith only [ht, hR, hc]
  have hpre0 : 0 ≤ 8 * R * Real.log (q : ℝ) + Real.log 2 := by positivity
  have hfirst : (8 * R * Real.log (q : ℝ) + Real.log 2) * chainShellConst q R ≤
      ((8 * R * Real.log 2 + Real.log 2) * C₁') * t ^ 3 := by
    calc (8 * R * Real.log (q : ℝ) + Real.log 2) * chainShellConst q R
        ≤ ((8 * R * Real.log 2 + Real.log 2) * t) * (C₁' * t ^ 2) :=
          mul_le_mul hpre hC hC0 (by positivity)
      _ = ((8 * R * Real.log 2 + Real.log 2) * C₁') * t ^ 3 := by ring
  have hlast : 1024 * Real.exp 1 * chainBudgetConst q R ≤
      (1024 * Real.exp 1 * chainBudgetConst 2 R) * t ^ 3 := by
    have hB3 := hB.trans (mul_le_mul_of_nonneg_left ht23 (zero_le_one.trans hB2))
    calc 1024 * Real.exp 1 * chainBudgetConst q R
        ≤ 1024 * Real.exp 1 * (chainBudgetConst 2 R * t ^ 3) :=
          mul_le_mul_of_nonneg_left hB3 (by positivity)
      _ = (1024 * Real.exp 1 * chainBudgetConst 2 R) * t ^ 3 := by ring
  calc chainAreaLawConst q R
      = (8 * R * Real.log (q : ℝ) + Real.log 2) * chainShellConst q R +
          1024 * Real.exp 1 * chainBudgetConst q R := rfl
    _ ≤ ((8 * R * Real.log 2 + Real.log 2) * C₁') * t ^ 3 +
          (1024 * Real.exp 1 * chainBudgetConst 2 R) * t ^ 3 := add_le_add hfirst hlast
    _ = _ := by
      simp only [C₁', ℓ₂, t, div_pow]
      field_simp

/-- For fixed interaction range, the original gapped chain satisfies an area law
with explicit coefficient proportional to `(1 + J/Δ) log³ q`.
Source: the note, Remark `rem:sharper`, `part1_arealaw.tex`, lines 711–745. -/
theorem regionEntropy_le_log_cube_mul_card_boundaryEdges (hq : 1 ≤ q)
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (h : ChainHamiltonian L q R J)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (A : Finset (Fin L)) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) A Ω ≤
      chainLogCubeConst R * (1 + J / Δ) *
        Real.log (q : ℝ) ^ 3 * (boundaryEdges L A).card := by
  by_cases hq2 : 2 ≤ q
  · have hθ : 0 ≤ 1 + J / Δ := by positivity
    have hbound := (chainIntervalEntropyBound_le (q := q) (R := R) hq hJ hΔ).trans
      (mul_le_mul_of_nonneg_right (chainAreaLawConst_le_mul_log_cube (R := R) hq2) hθ)
    refine (regionEntropy_le_mul_card_boundaryEdges hq hJ hΔ h hgs A).trans
      ((mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)).trans_eq ?_)
    ring
  · have hqeq : q = 1 := by omega
    subst q
    rw [regionEntropy_eq_zero_of_localDimension_one hgs.1 A]
    norm_num

/-- Scalar window-budget bound after normalizing by a positive logarithmic lower
bound. Source: the one-dimensional note, Remark `rem:sharper`, lines 706–745. -/
private theorem consecutive_window_budget_le_range_log_sq (c y r : ℝ)
    (hc : 0 < c) (hy : c ≤ y) (hr : 1 ≤ r) :
    1 + 2 * r * (1 + (r + 1) * y) ^ 2 ≤
      ((c⁻¹) ^ 2 + 2 * (c⁻¹ + 2) ^ 2) * r * (r * y) ^ 2 := by
  have hy0 : 0 ≤ y := hc.le.trans hy
  have hcx : c ≤ r * y := hy.trans (le_mul_of_one_le_left hy0 hr)
  have hu : 1 ≤ c⁻¹ * (r * y) := by
    simpa only [div_eq_mul_inv, mul_comm] using (one_le_div hc).mpr hcx
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hlin : 1 + (r + 1) * y ≤ (c⁻¹ + 2) * (r * y) := by
    nlinarith only [hu, mul_nonneg (sub_nonneg.mpr hr) hy0]
  have hsq : (1 + (r + 1) * y) ^ 2 ≤ ((c⁻¹ + 2) * (r * y)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hlin
  have hu2 : 1 ≤ (c⁻¹) ^ 2 * (r * y) ^ 2 := by
    simpa only [mul_pow] using (one_le_pow₀ hu (n := 2))
  have huR : 1 ≤ (c⁻¹) ^ 2 * r * (r * y) ^ 2 := by
    calc 1 ≤ (c⁻¹) ^ 2 * (r * y) ^ 2 := hu2
         _ ≤ r * ((c⁻¹) ^ 2 * (r * y) ^ 2) :=
           le_mul_of_one_le_left (by positivity) hr
         _ = _ := by ring
  calc
    _ ≤ (c⁻¹) ^ 2 * r * (r * y) ^ 2 +
        2 * r * ((c⁻¹ + 2) * (r * y)) ^ 2 :=
      add_le_add huR (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = _ := by ring

/-- Absorb the additive entropy coefficient using a positive lower bound on the
range times the dimension logarithm. Source: Remark `rem:sharper`, lines 706–745. -/
private theorem area_law_coefficient_le_budget_mul_log (c x B E : ℝ) (hc : 0 < c)
    (hx : c ≤ x) (hB : 1 ≤ B) (hE0 : 0 ≤ E) (hE : E ≤ 64 * Real.exp 1 * B) :
    (8 * x + c) * (5 + E + 128 * B) + 1024 * Real.exp 1 * B ≤
      (1197 + 576 * Real.exp 1 + 1024 * Real.exp 1 / c) * B * x := by
  have hx0 : 0 ≤ x := hc.le.trans hx
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hfirst : 5 + E + 128 * B ≤ (133 + 64 * Real.exp 1) * B := by
    nlinarith only [hB, hE]
  have hfirst0 : 0 ≤ 5 + E + 128 * B := by positivity
  have hpre : 8 * x + c ≤ 9 * x := by linarith
  have hprod : (8 * x + c) * (5 + E + 128 * B) ≤ 9 * x * ((133 + 64 * Real.exp 1) * B) :=
    mul_le_mul hpre hfirst hfirst0 (by positivity)
  have htail : 1024 * Real.exp 1 * B ≤ (1024 * Real.exp 1 / c) * B * x := by
    calc
      _ = (1024 * Real.exp 1 / c) * B * c := by
        field_simp [hc.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  nlinarith only [hprod, htail]

/-- A scalar estimate for the consecutive-window budget. The constants are
absolute and are fixed before the local dimension and interaction range.
Source: the one-dimensional note, Remark rem:sharper, lines 706–745. -/
private theorem consecutive_window_coefficient_le_range_log_cube :
    let c : ℝ := Real.log 2
    let C : ℝ := 1197 + 576 * Real.exp 1 + 1024 * Real.exp 1 / c
    let K : ℝ := (c⁻¹) ^ 2 + 2 * (c⁻¹ + 2) ^ 2
    0 < C ∧ 0 < K ∧ ∀ (q R : ℕ), 2 ≤ q → 1 ≤ R →
      windowAreaLawConst q R ≤ C * K * (R : ℝ) * Real.log ((q : ℝ) ^ R) ^ 3 := by
  dsimp only
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨by positivity, by positivity, ?_⟩
  intro q R hq hR
  have hB := one_le_windowBudgetConst q R
  unfold windowAreaLawConst windowBudgetConst cutAreaLawConst cutShellConst cutBudgetConst at *
  push_cast at hB ⊢
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hy : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hr : 1 ≤ (R : ℝ) := by exact_mod_cast hR
  have hlog : Real.log (Real.exp 1 * (q : ℝ) ^ (R + 1)) =
      1 + ((R : ℝ) + 1) * Real.log (q : ℝ) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (pow_ne_zero _ hq0.ne'),
      Real.log_exp, Real.log_pow, Nat.cast_add, Nat.cast_one]
  set ℓ : ℝ := Real.log (Real.exp 1 * (q : ℝ) ^ (R + 1))
  let B : ℝ := 1 + 2 * (R : ℝ) * ℓ ^ 2
  let C : ℝ := 1197 + 576 * Real.exp 1 + 1024 * Real.exp 1 / Real.log 2
  let K : ℝ := ((Real.log 2)⁻¹) ^ 2 + 2 * ((Real.log 2)⁻¹ + 2) ^ 2
  have hbudget : B ≤ K * (R : ℝ) * ((R : ℝ) * Real.log (q : ℝ)) ^ 2 := by
    dsimp only [B, K]
    rw [hlog]
    exact consecutive_window_budget_le_range_log_sq (Real.log 2) (Real.log (q : ℝ)) (R : ℝ) hc hy hr
  replace hB : 1 ≤ B := hB
  have hx : Real.log 2 ≤ (R : ℝ) * Real.log (q : ℝ) :=
    hy.trans (le_mul_of_one_le_left (hc.le.trans hy) hr)
  have hE : min (32 * (2 * (R : ℝ)) * (q : ℝ) ^ (2 * (R + 1)))
      (64 * Real.exp 1 * (2 * (R : ℝ)) * ℓ ^ 2) ≤ 64 * Real.exp 1 * B := by
    refine (min_le_right _ _).trans ?_
    dsimp only [B]
    nlinarith only [Real.exp_pos 1]
  have hE0 : 0 ≤ min (32 * (2 * (R : ℝ)) * (q : ℝ) ^ (2 * (R + 1)))
      (64 * Real.exp 1 * (2 * (R : ℝ)) * ℓ ^ 2) := by positivity
  have hcoef := area_law_coefficient_le_budget_mul_log (Real.log 2)
    ((R : ℝ) * Real.log (q : ℝ)) B _ hc hx hB hE0 hE
  have hcombine : C * B * ((R : ℝ) * Real.log (q : ℝ)) ≤
      C * (K * (R : ℝ) * ((R : ℝ) * Real.log (q : ℝ)) ^ 2) *
        ((R : ℝ) * Real.log (q : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbudget (by dsimp only [C]; positivity))
      (hc.le.trans hx)
  calc
    _ = (8 * ((R : ℝ) * Real.log (q : ℝ)) + Real.log 2) *
          (5 + min (32 * (2 * (R : ℝ)) * (q : ℝ) ^ (2 * (R + 1)))
            (64 * Real.exp 1 * (2 * (R : ℝ)) * ℓ ^ 2) + 128 * B) +
        1024 * Real.exp 1 * B := by ring
    _ ≤ C * B * ((R : ℝ) * Real.log (q : ℝ)) := by
      simpa only [C, mul_assoc] using hcoef
    _ ≤ C * (K * (R : ℝ) * ((R : ℝ) * Real.log (q : ℝ)) ^ 2) *
        ((R : ℝ) * Real.log (q : ℝ)) := hcombine
    _ = _ := by rw [Real.log_pow]; ring

/-- On-site interactions give zero entropy on every region of a gapped ground state.
Source: the one-dimensional note, Section 2 (`sec:setting`), component reduction. -/
theorem ChainHamiltonian.regionEntropy_eq_zero_of_range_zero
    {L q : ℕ} {J Δ : ℝ} (h : ChainHamiltonian L q 0 J)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΔ : 0 < Δ) (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ)
    (A : Finset (Fin L)) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) A Ω = 0 := by
  refine regionEntropy_eq_zero_of_forall_subset_or_disjoint
    h.supported h.hermitian hΔ hgs A ?_
  intro X
  have hcard := X.property.card_le
  grind [Finset.card_le_one_iff, Finset.disjoint_left]

/-- Absolute polynomial dependence on the interaction range for full contained
consecutive-window interactions. Source: the one-dimensional note, Remark
`rem:sharper`, `part1_arealaw.tex`, lines 706–745. -/
theorem chainAreaLaw_of_consecutive_terms_polynomial_range :
    ∃ Cabs : ℝ, 0 < Cabs ∧
      Cabs = (1197 + 576 * Real.exp 1 + 1024 * Real.exp 1 / Real.log 2) *
        (((Real.log 2)⁻¹) ^ 2 + 2 * ((Real.log 2)⁻¹ + 2) ^ 2) ∧
      ∀ (q R : ℕ) (J Δ : ℝ), 1 ≤ q → 0 ≤ J → 0 < Δ →
        ∀ L : ℕ, ∀ h : ChainHamiltonian L q R J,
          (∀ X : ChainSupport L R, h.term X ≠ 0 →
            ∃ a : ℕ, a + R + 1 ≤ L ∧ X.1 = interval L a (a + R + 1)) →
          ∀ E₀ : ℝ, ∀ Ω : EuclideanSpace ℂ (Fin L → Fin q),
            Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
            ∀ A : Finset (Fin L),
              Entropy.regionEntropy (n := fun _ : Fin L ↦ q) A Ω ≤
                Cabs * (1 + J / Δ) * (R : ℝ) * Real.log ((q : ℝ) ^ R) ^ 3 *
                  (boundaryEdges L A).card := by
  obtain ⟨hC, hK, hscalar⟩ := consecutive_window_coefficient_le_range_log_cube
  refine ⟨_, mul_pos hC hK, rfl, ?_⟩
  intro q R J Δ hq hJ hΔ L h hwindow E₀ Ω hgs A
  by_cases hpos : 2 ≤ q ∧ 1 ≤ R
  · obtain ⟨Cphys, hCphys, hCeq, hbound⟩ :=
      chainAreaLaw_of_consecutive_terms q R J Δ hq hJ hΔ
    have hscalar' := hscalar q R hpos.1 hpos.2
    have hphysical := hbound L h hwindow E₀ Ω hgs A
    have hθ : 0 ≤ 1 + J / Δ := by positivity
    have hlast := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscalar' hθ)
      (Nat.cast_nonneg (boundaryEdges L A).card)
    rw [hCeq] at hphysical
    exact hphysical.trans (by convert hlast using 1; ring)
  · by_cases hR0 : R = 0
    · subst R
      rw [h.regionEntropy_eq_zero_of_range_zero hΔ hgs A]
      simp
    · have hq1 : q = 1 := by omega
      subst q
      rw [regionEntropy_eq_zero_of_localDimension_one hgs.1 A]
      simp

/-- Full physical windows remain full windows after increasing relabelling.
Source: the one-dimensional note, part1_arealaw.tex, lines 64–93 and 706–748. -/
private theorem DomainHamiltonian.toChain_consecutive_terms
    {Λ : Finset ℤ} {q R : ℕ} {J : ℝ}
    (h : DomainHamiltonian Λ q R J) (hJ : 0 ≤ J)
    (hwindow : ∀ X : DomainSupport Λ R, h.term X ≠ 0 →
      ∃ a : ℤ, X.1.image (sitePos Λ) = Finset.Ico a (a + (R : ℤ) + 1)) :
    ∀ Y : ChainSupport Λ.card R, (h.toChain hJ).term Y ≠ 0 →
      ∃ a : ℕ, a + R + 1 ≤ Λ.card ∧ Y.1 = interval Λ.card a (a + R + 1) := by
  classical
  intro Y hY
  change (if hdom : IsDomainSupport Λ R Y.1 then h.term ⟨Y.1, hdom⟩ else 0) ≠ 0 at hY
  split_ifs at hY with hdom
  · obtain ⟨a, ha⟩ := hwindow ⟨Y.1, hdom⟩ hY
    have hc := congrArg Finset.card ha
    rw [Finset.card_image_of_injective _ (sitePos Λ).injective, Int.card_Ico] at hc
    have hlen : a + (R : ℤ) + 1 - a = ((R + 1 : ℕ) : ℤ) := by omega
    rw [hlen, Int.toNat_natCast] at hc
    exact Y.2.exists_eq_interval_of_card_eq hc
  · exact (hY rfl).elim

/-- The absolute polynomial-range bound on a finite subset of the integers.
Only nonzero interactions are required to be full contained windows in the original sites.
Source: the one-dimensional note, part1_arealaw.tex, lines 64–93 and 706–748. -/
theorem domainAreaLaw_of_consecutive_terms_polynomial_range :
    ∃ Cabs : ℝ, 0 < Cabs ∧
      Cabs = (1197 + 576 * Real.exp 1 + 1024 * Real.exp 1 / Real.log 2) *
        (((Real.log 2)⁻¹) ^ 2 + 2 * ((Real.log 2)⁻¹ + 2) ^ 2) ∧
      ∀ (q R : ℕ) (J Δ : ℝ), 1 ≤ q → 0 ≤ J → 0 < Δ →
        ∀ Λ : Finset ℤ, ∀ h : DomainHamiltonian Λ q R J,
          (∀ X : DomainSupport Λ R, h.term X ≠ 0 →
            ∃ a : ℤ,
              X.1.image (sitePos Λ) = Finset.Ico a (a + (R : ℤ) + 1)) →
          ∀ E₀ : ℝ, ∀ Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q),
            Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
            ∀ A : Finset ℤ,
              Entropy.regionEntropy (n := fun _ : Fin Λ.card ↦ q)
                (domainRegion Λ A) Ω ≤
                Cabs * (1 + J / Δ) * (R : ℝ) * Real.log ((q : ℝ) ^ R) ^ 3 *
                  (domainBoundaryEdges Λ A).card := by
  obtain ⟨Cabs, hCabs, hCeq, hchain⟩ :=
    chainAreaLaw_of_consecutive_terms_polynomial_range
  refine ⟨Cabs, hCabs, hCeq, ?_⟩
  intro q R J Δ hq hJ hΔ Λ h hwindow E₀ Ω hgs A
  obtain ⟨A', hS, hB⟩ := h.exists_regionEntropy_eq_card_boundaryEdges_eq hΔ hgs A
  have hgs' : Matrix.IsGappedGroundState (h.toChain hJ).operator E₀ Ω Δ := by
    rwa [DomainHamiltonian.toChain_operator]
  have hbound := hchain q R J Δ hq hJ hΔ Λ.card (h.toChain hJ)
    (h.toChain_consecutive_terms hJ hwindow) E₀ Ω hgs' A'
  simpa only [hS, hB] using hbound

end TNLean.MPS.AreaLaw
