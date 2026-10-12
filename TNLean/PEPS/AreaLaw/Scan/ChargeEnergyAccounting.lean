/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.EnergyBalance

/-!
# Charge energy from finite leaf bounds

The good-old contribution is controlled by Hölder without dividing by the
split-label capacity. The bad-old and new contributions retain their literal
Fourier mass one half and the interpolation factors `1-p` and `p`.
The result applies to a single round and requires no `ScanData` construction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 492–511, at `openai/math@adc7f124`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.ScanRound

open MeasureTheory Set

variable {ι Θ : Type} [Fintype ι] [MeasurableSpace Θ]

open Classical in
/-- Good-old Hölder accounting with a nonnegative capacity, including zero.
The Fourier mass is bounded before the finite weighted Hölder inequality. -/
theorem goodOld_le_capacity (R : ScanRound ι Θ) (k : ℕ) (p : ℝ)
    [∀ h, IsFiniteMeasure (R.μOld k p h)]
    (hw : ∀ h, 0 ≤ R.w h) (hsumw : ∑ h, R.w h = 1)
    (hmass : ∀ h, (R.μOld k p h).real univ = 1 / 2)
    (hη : ∀ i h, Measurable (R.etaOld i h))
    (hη0 : ∀ i h θ, 0 ≤ R.etaOld i h θ) {B N : ℝ}
    (hηB : ∀ i h θ, R.etaOld i h θ ≤ B) (hN : 0 ≤ N)
    (hcard : ∀ h, ((Finset.univ.filter fun i ↦ R.splitOld i h).card : ℝ) ≤ N) :
    (∑ h, if R.good h then R.w h * ∑ i,
        (if R.splitOld i h then
          ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) else 0)
      else 0) ≤ N ^ (7 / 8 : ℝ) * R.chargeDefect k p ^ (1 / 8 : ℝ) := by
  let J : R.H × ι → ℝ := fun x ↦ ∫ θ, R.etaOld x.2 x.1 θ ^ (1 / 8 : ℝ) ∂(R.μOld k p x.1)
  let I : R.H × ι → ℝ := fun x ↦ ∫ θ, R.etaOld x.2 x.1 θ ∂(R.μOld k p x.1)
  let c : R.H × ι → ℝ := fun x ↦ if R.good x.1 ∧ R.splitOld x.2 x.1 then R.w x.1 else 0
  have hc0 : ∀ x, 0 ≤ c x := fun x ↦ by
    simp only [c]; split_ifs
    · exact hw x.1
    · exact le_rfl
  have hJ0 : ∀ x, 0 ≤ J x := fun x ↦ integral_nonneg fun θ ↦ Real.rpow_nonneg (hη0 x.2 x.1 θ) _
  have hI0 : ∀ x, 0 ≤ I x := fun x ↦ integral_nonneg fun θ ↦ hη0 x.2 x.1 θ
  -- Each `J ≤ I^{1/8}`, by Hölder against the mass `1/2`.
  have hJI : ∀ x, J x ≤ I x ^ (1 / 8 : ℝ) := fun x ↦ by
    have h := integral_rpow_le_of_holder (R.μOld k p x.1) (hη x.2 x.1)
      (hη0 x.2 x.1) (hηB x.2 x.1)
    rw [hmass x.1] at h
    have h1 : (1 / 2 : ℝ) ^ (7 / 8 : ℝ) ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num)
      (by norm_num)
    calc J x ≤ _ := h
      _ ≤ 1 * I x ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hI0 x) _)
      _ = _ := one_mul _
  have hJ8 : ∀ x, J x ^ (8 : ℝ) ≤ I x := fun x ↦ by
    calc J x ^ (8 : ℝ) ≤ (I x ^ (1 / 8 : ℝ)) ^ (8 : ℝ) :=
          Real.rpow_le_rpow (hJ0 x) (hJI x) (by norm_num)
      _ = I x := by rw [← Real.rpow_mul (hI0 x)]; norm_num
  have hH := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ (p := 8) (by norm_num) c J hc0
    hJ0
  -- Identify the three sums.
  have hsplit : ∀ f : R.H × ι → ℝ, ∑ x, c x * f x =
      ∑ h, if R.good h then R.w h * ∑ i, (if R.splitOld i h then f (h, i) else 0) else 0 := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    by_cases hg : R.good h
    · simp only [hg, ↓reduceIte, true_and, c, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp
    · simp [hg, c]
  have hsumc : ∑ x, c x ≤ N := by
    have := hsplit fun _ ↦ 1
    simp only [mul_one] at this
    rw [this]
    calc (∑ h, if R.good h then R.w h * ∑ i, (if R.splitOld i h then (1 : ℝ) else 0) else 0)
        ≤ ∑ h, R.w h * N := Finset.sum_le_sum fun h _ ↦ by
          split_ifs
          · refine mul_le_mul_of_nonneg_left ?_ (hw h)
            rw [Finset.sum_boole]; exact hcard h
          · exact mul_nonneg (hw h) hN
      _ = N := by rw [← Finset.sum_mul, hsumw, one_mul]
  have hQ : ∑ x, c x * J x ^ (8 : ℝ) ≤ R.chargeDefect k p := by
    calc ∑ x, c x * J x ^ (8 : ℝ) ≤ ∑ x, c x * I x :=
          Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hJ8 x) (hc0 x)
      _ = R.chargeDefect k p := by rw [hsplit]; rfl
  have hlhs := hsplit J
  rw [hlhs] at hH
  refine hH.trans ?_
  have e1 : (1 - (8 : ℝ)⁻¹) = 7 / 8 := by norm_num
  have e2 : ((8 : ℝ)⁻¹) = 1 / 8 := by norm_num
  rw [e1, e2]
  have hsc0 : 0 ≤ ∑ x, c x := Finset.sum_nonneg fun x _ ↦ hc0 x
  have hcJ0 : 0 ≤ ∑ x, c x * J x ^ (8 : ℝ) :=
    Finset.sum_nonneg fun x _ ↦ mul_nonneg (hc0 x) (Real.rpow_nonneg (hJ0 x) _)
  calc (∑ x, c x) ^ (7 / 8 : ℝ) * (∑ x, c x * J x ^ (8 : ℝ)) ^ (1 / 8 : ℝ)
      ≤ N ^ (7 / 8 : ℝ) * (R.chargeDefect k p) ^ (1 / 8 : ℝ) :=
        mul_le_mul (Real.rpow_le_rpow hsc0 hsumc (by norm_num))
          (Real.rpow_le_rpow hcJ0 hQ (by norm_num)) (Real.rpow_nonneg hcJ0 _)
          (Real.rpow_nonneg hN _)

open Classical in
/-- A single-round energy bound retaining the exact old and new interpolation
factors. All capacities may vanish; the conclusion never divides by them. -/
theorem energySum_le_of_leaf_bounds (R : ScanRound ι Θ) (k : ℕ) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1)
    [∀ h, IsFiniteMeasure (R.μOld k p h)]
    [∀ h c, IsFiniteMeasure (R.μNew k p h c)]
    (hw : ∀ h, 0 ≤ R.w h) (hsumw : ∑ h, R.w h = 1)
    (hq : ∀ h c, 0 ≤ R.q h c) (hsumq : ∀ h, ∑ c, R.q h c = 1)
    (hmassOld : ∀ h, (R.μOld k p h).real univ = 1 / 2)
    (hmassNew : ∀ h c, (R.μNew k p h c).real univ = 1 / 2)
    (hη : ∀ i h, Measurable (R.etaOld i h))
    (hηOld0 : ∀ i h θ, 0 ≤ R.etaOld i h θ)
    (hηNew0 : ∀ i h c θ, 0 ≤ R.etaNew i h c θ)
    {B N d : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N) (hd : 0 ≤ d)
    (hηOldB : ∀ i h θ, R.etaOld i h θ ≤ B)
    (hηNewB : ∀ i h c θ, R.etaNew i h c θ ≤ B)
    (hcardOld : ∀ h, ((Finset.univ.filter fun i ↦ R.splitOld i h).card : ℝ) ≤ N)
    (hcardNew : ∀ h c, ((Finset.univ.filter fun i ↦ R.splitNew i h c).card : ℝ) ≤ N)
    (hsplit : ∀ i, R.splitWeight p i ≤ d) :
    R.energySum k p ≤ d * ((1 - p) * N ^ (7 / 8 : ℝ) *
      R.chargeDefect k p ^ (1 / 8 : ℝ) +
      N * B ^ (1 / 8 : ℝ) / 2 * ((1 - p) * R.badWeight + p)) := by
  have hpOld : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hB8 : 0 ≤ B ^ (1 / 8 : ℝ) / 2 := by positivity
  have hOld0 (i : ι) (h : R.H) :
      0 ≤ ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) :=
    integral_nonneg fun θ ↦ Real.rpow_nonneg (hηOld0 i h θ) _
  have hNew0 (i : ι) (h : R.H) (c : R.Ch h) :
      0 ≤ ∫ θ, R.etaNew i h c θ ^ (1 / 8 : ℝ) ∂(R.μNew k p h c) :=
    integral_nonneg fun θ ↦ Real.rpow_nonneg (hηNew0 i h c θ) _
  have hterm (i : ι) : 0 ≤ R.termEnergy k p i := by
    unfold termEnergy
    refine add_nonneg (Finset.sum_nonneg fun h _ ↦ ?_)
      (Finset.sum_nonneg fun h _ ↦ Finset.sum_nonneg fun c _ ↦ ?_)
    · split_ifs
      · exact mul_nonneg (mul_nonneg hpOld (hw h)) (hOld0 i h)
      · exact le_rfl
    · split_ifs
      · exact mul_nonneg (mul_nonneg (mul_nonneg hp.1 (hw h)) (hq h c)) (hNew0 i h c)
      · exact le_rfl
  have hgood := R.goodOld_le_capacity k p hw hsumw hmassOld hη hηOld0 hηOldB hN hcardOld
  have hnew : (∑ i, ∑ h, ∑ c, if R.splitNew i h c then
      p * R.w h * R.q h c *
        ∫ θ, R.etaNew i h c θ ^ (1 / 8 : ℝ) ∂(R.μNew k p h c) else 0) ≤
      p * (N * (B ^ (1 / 8 : ℝ) / 2)) := by
    rw [Finset.sum_comm]
    calc _ = ∑ h, ∑ c, ∑ i, (if R.splitNew i h c then
          p * R.w h * R.q h c *
            ∫ θ, R.etaNew i h c θ ^ (1 / 8 : ℝ) ∂(R.μNew k p h c) else 0) :=
          Finset.sum_congr rfl fun h _ ↦ Finset.sum_comm
      _ ≤ ∑ h, ∑ c, p * R.w h * R.q h c * (N * (B ^ (1 / 8 : ℝ) / 2)) :=
          Finset.sum_le_sum fun h _ ↦ Finset.sum_le_sum fun c _ ↦
            sum_ite_mul_le _ (mul_nonneg (mul_nonneg hp.1 (hw h)) (hq h c)) _ hB8
              (fun i _ ↦ integral_rpow_le_half _ (hmassNew h c)
                (hηNew0 i h c) (hηNewB i h c)) (hcardNew h c)
      _ = ∑ h, p * (N * (B ^ (1 / 8 : ℝ) / 2)) * R.w h * ∑ c, R.q h c :=
          Finset.sum_congr rfl fun h _ ↦ by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ ↦ by ring
      _ = ∑ h, p * (N * (B ^ (1 / 8 : ℝ) / 2)) * R.w h :=
          Finset.sum_congr rfl fun h _ ↦ by rw [hsumq h, mul_one]
      _ = p * (N * (B ^ (1 / 8 : ℝ) / 2)) := by
          rw [← Finset.mul_sum, hsumw, mul_one]
  have hold (h : R.H) : (∑ i, if R.splitOld i h then
      (1 - p) * R.w h * ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) else 0) ≤
      (1 - p) * (if R.good h then R.w h * ∑ i,
        (if R.splitOld i h then
          ∫ θ, R.etaOld i h θ ^ (1 / 8 : ℝ) ∂(R.μOld k p h) else 0) else 0) +
      (1 - p) * (N * (B ^ (1 / 8 : ℝ) / 2)) * (if R.good h then 0 else R.w h) := by
    by_cases hg : R.good h
    · simp only [hg, ↓reduceIte, mul_zero, add_zero]
      rw [sum_ite_mul_eq]
      exact le_of_eq (_root_.mul_assoc _ _ _)
    · simp only [hg, ↓reduceIte, mul_zero, zero_add]
      calc _ ≤ (1 - p) * R.w h * (N * (B ^ (1 / 8 : ℝ) / 2)) :=
            sum_ite_mul_le _ (mul_nonneg hpOld (hw h)) _ hB8
              (fun i _ ↦ integral_rpow_le_half _ (hmassOld h)
                (hηOld0 i h) (hηOldB i h)) (hcardOld h)
        _ = _ := by ring
  have holdsum := Finset.sum_le_sum (s := Finset.univ) fun h _ ↦ hold h
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at holdsum
  have holdgood := mul_le_mul_of_nonneg_left hgood hpOld
  calc
    R.energySum k p ≤ d * ∑ i, R.termEnergy k p i := by
      rw [energySum, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hsplit i) (hterm i)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hd
      unfold termEnergy
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      dsimp only [badWeight] at *
      linarith

end TNLean.PEPS.AreaLaw.Scan.ScanRound
