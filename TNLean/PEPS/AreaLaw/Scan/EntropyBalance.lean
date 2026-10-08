/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs

/-!
# Integrated entropy balance of the scan

At a charge round every split term of a good old history is sampled with probability at least
`c/(nD)`, so the entropy gain of Proposition 7.4 dominates `(cka/(nD)) 𝒬(p)`
(`scanner:charge-gain`). Integrating over every full round, telescoping the endpoint values of
`log N²`, and bounding the two ends by the initial floor and the terminal rough upper
comparison gives `ScanData.IntegratedChargeBound`.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.sum_integral_le_of_deriv`: telescoped integration of derivative
  lower bounds over a finite chain of intervals.
* `TNLean.PEPS.AreaLaw.Scan.ScanData.chargeDefect_le_choiceGainSum`: `scanner:charge-gain`.
* `TNLean.PEPS.AreaLaw.Scan.ScanData.integratedChargeBound`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`, lines 416–479.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open MeasureTheory Set

/-- Telescoped integration of derivative lower bounds over a chain of `R` unit intervals whose
adjacent endpoint values agree. Rounds in `T` carry a nonnegative gain `coef · Q r` that is
retained only on `[α, β] ⊆ [0, 1]`; every round pays the error `err`
(`08-scanner.tex`, lines 457–475). -/
theorem sum_integral_le_of_deriv {R : ℕ} (f Q : Fin R → ℝ → ℝ) (T : Finset (Fin R))
    {coef err α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) (hcoef : 0 ≤ coef)
    (hR : 0 < R)
    (hcont : ∀ r, ContinuousOn (f r) (Icc 0 1))
    (hdiff : ∀ r, DifferentiableOn ℝ (f r) (Ioo 0 1))
    (hQ_nonneg : ∀ r, ∀ p ∈ Ioo (0 : ℝ) 1, 0 ≤ Q r p)
    (hQ_cont : ∀ r, ContinuousOn (Q r) (Ioo 0 1))
    (hQ_bdd : ∃ B, ∀ r, ∀ p ∈ Ioo (0 : ℝ) 1, Q r p ≤ B)
    (hgainT : ∀ r ∈ T, ∀ p ∈ Ioo (0 : ℝ) 1, coef * Q r p - err ≤ -deriv (f r) p)
    (hgain : ∀ r, ∀ p ∈ Ioo (0 : ℝ) 1, -err ≤ -deriv (f r) p)
    (htele : ∀ (r : Fin R) (hr : r.val + 1 < R), f ⟨r.val + 1, hr⟩ 0 = f r 1) :
    coef * ∑ r ∈ T, ∫ p in α..β, Q r p ≤
      f ⟨0, hR⟩ 0 - f ⟨R - 1, Nat.sub_lt hR one_pos⟩ 1 + R * err := by
  obtain ⟨B, hB⟩ := hQ_bdd
  -- Integrability of every `Q r` on `[0, 1]`.
  have hQint : ∀ r, IntegrableOn (Q r) (Icc 0 1) := by
    intro r
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    refine ⟨(hQ_cont r).aestronglyMeasurable measurableSet_Ioo,
      HasFiniteIntegral.restrict_of_bounded (C := max B 0) (by simp) ?_⟩
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun p hp ↦ ?_)
    rw [Real.norm_of_nonneg (hQ_nonneg r p hp)]
    exact (hB r p hp).trans (le_max_left _ _)
  -- Fundamental theorem of calculus on one round with a lower bound `φ ≤ -f'`.
  have hftc : ∀ r (φ : ℝ → ℝ), IntegrableOn φ (Icc 0 1) →
      (∀ p ∈ Ioo (0 : ℝ) 1, φ p ≤ -deriv (f r) p) → ∫ p in (0 : ℝ)..1, φ p ≤ f r 0 - f r 1 := by
    intro r φ hφ hle
    have := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le (g := fun p ↦ -f r p)
      (g' := fun p ↦ -deriv (f r) p) zero_le_one (hcont r).neg
      (fun x hx ↦ (((hdiff r).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt.neg
        ).hasDerivWithinAt) hφ hle
    linarith
  -- Per-round slack `d r = f r 0 - f r 1 + err`.
  have hd_nonneg : ∀ r, 0 ≤ f r 0 - f r 1 + err := by
    intro r
    have := hftc r (fun _ ↦ -err) (integrableOn_const (by simp)) (hgain r)
    simp at this
    linarith
  have hdT : ∀ r ∈ T, coef * ∫ p in α..β, Q r p ≤ f r 0 - f r 1 + err := by
    intro r hr
    have hii : IntervalIntegrable (Q r) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 (hQint r)
    have hmono : ∫ p in α..β, Q r p ≤ ∫ p in (0 : ℝ)..1, Q r p := by
      refine intervalIntegral.integral_mono_interval hα hαβ hβ ?_ hii
      rw [Filter.EventuallyLE, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
      exact (ae_restrict_iff' measurableSet_Ioo).2
        (Filter.Eventually.of_forall fun p hp ↦ hQ_nonneg r p hp)
    have := hftc r (fun p ↦ coef * Q r p - err)
      (((hQint r).const_mul coef).sub (integrableOn_const (by simp))) (hgainT r hr)
    rw [intervalIntegral.integral_sub (hii.const_mul coef) intervalIntegrable_const,
      intervalIntegral.integral_const_mul] at this
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at this
    nlinarith [mul_le_mul_of_nonneg_left hmono hcoef]
  -- Telescoping over the chain of rounds.
  set F : ℕ → ℝ := fun i ↦ if h : i < R then f ⟨i, h⟩ 0 else f ⟨R - 1, Nat.sub_lt hR one_pos⟩ 1
    with hF
  have hF1 : ∀ r : Fin R, f r 1 = F (r.val + 1) := by
    intro r
    by_cases h : r.val + 1 < R
    · simp only [hF, h, dite_true, ← htele r h]
    · have : r = ⟨R - 1, Nat.sub_lt hR one_pos⟩ := Fin.ext (by simp only; omega)
      rw [this]
      simp [hF, show ¬(R - 1 + 1 < R) by omega]
  have hF0 : ∀ r : Fin R, f r 0 = F r.val := fun r ↦ by simp [hF, r.isLt]
  have htel : ∑ r : Fin R, (f r 0 - f r 1 + err) =
      f ⟨0, hR⟩ 0 - f ⟨R - 1, Nat.sub_lt hR one_pos⟩ 1 + R * err := by
    rw [Finset.sum_add_distrib]
    simp only [hF0, hF1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ F i - F (i + 1)), Finset.sum_range_sub']
    simp only [hF, hR, dite_true, Nat.lt_irrefl, dite_false]
    split_ifs with h
    · omega
    · rfl
  calc coef * ∑ r ∈ T, ∫ p in α..β, Q r p
      = ∑ r ∈ T, coef * ∫ p in α..β, Q r p := Finset.mul_sum _ _ _
    _ ≤ ∑ r ∈ T, (f r 0 - f r 1 + err) := Finset.sum_le_sum hdT
    _ ≤ ∑ r : Fin R, (f r 0 - f r 1 + err) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun r _ _ ↦ hd_nonneg r
    _ = _ := htel

namespace ScanData

variable {X : ScannerExponents} {κ : ScanConstants} {n : ℕ} (S : ScanData X κ n)

/-- A measurable function with values in `[0, b]` is integrable for a finite measure. -/
theorem integrable_of_bounded {Θ : Type} [MeasurableSpace Θ] {μ : Measure Θ}
    [IsFiniteMeasure μ] {g : Θ → ℝ} {b : ℝ} (hg : Measurable g) (h0 : ∀ θ, 0 ≤ g θ)
    (hb : ∀ θ, g θ ≤ b) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable b
    (Filter.Eventually.of_forall fun θ ↦ by rw [Real.norm_of_nonneg (h0 θ)]; exact hb θ)

/-- On a charge round the choice-averaged entropy gain dominates `c/(nD)` times the charge
defect `𝒬(p)`: good old histories sample each split term with probability at least `c/(nD)`
and bad ones contribute nonnegatively (`scanner:charge-gain`, lines 442–451). -/
theorem chargeDefect_le_choiceGainSum (r : Fin (X.rounds n)) (hr : IsChargeRound r)
    (k : ℕ) (p : ℝ) :
    κ.c / (n * X.D n) * (S.round r).chargeDefect k p ≤ (S.round r).choiceGainSum k p := by
  classical
  have hc : 0 ≤ κ.c / (n * X.D n) := div_nonneg κ.c_pos.le (by positivity)
  have := S.isFiniteMeasure_μOld r k p
  unfold ScanRound.chargeDefect ScanRound.choiceGainSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun h _ ↦ ?_
  have hgain_int : Integrable ((S.round r).choiceGain h) ((S.round r).μOld k p h) :=
    integrable_of_bounded (S.measurable_choiceGain r h) (S.choiceGain_nonneg r h)
      (S.choiceGain_le r h)
  split_ifs with hg
  · rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (S.w_nonneg r h)
    have hint : ∀ i, Integrable (fun θ ↦ if (S.round r).splitOld i h then
        (S.round r).etaOld i h θ else 0) ((S.round r).μOld k p h) := by
      intro i
      split_ifs
      · exact integrable_of_bounded (S.measurable_etaOld r i h) (S.etaOld_nonneg r i h)
          (S.etaOld_le r i h)
      · exact integrable_zero _ _ _
    calc κ.c / (n * X.D n) * ∑ i, (if (S.round r).splitOld i h then
            ∫ θ, (S.round r).etaOld i h θ ∂(S.round r).μOld k p h else 0)
        = ∫ θ, κ.c / (n * X.D n) * ∑ i, (if (S.round r).splitOld i h then
            (S.round r).etaOld i h θ else 0) ∂(S.round r).μOld k p h := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint i]
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          split_ifs <;> simp
      _ ≤ ∫ θ, (S.round r).choiceGain h θ ∂(S.round r).μOld k p h :=
          integral_mono ((integrable_finsetSum _ fun i _ ↦ hint i).const_mul _) hgain_int
            fun θ ↦ S.sampling r hr h hg θ
  · rw [mul_zero]
    exact mul_nonneg (S.w_nonneg r h) (integral_nonneg (S.choiceGain_nonneg r h))

/-- The charge defect is nonnegative (lines 437–438). -/
theorem chargeDefect_nonneg (r : Fin (X.rounds n)) (k : ℕ) (p : ℝ) :
    0 ≤ (S.round r).chargeDefect k p := by
  classical
  unfold ScanRound.chargeDefect
  refine Finset.sum_nonneg fun h _ ↦ ?_
  split_ifs
  · refine mul_nonneg (S.w_nonneg r h) (Finset.sum_nonneg fun i _ ↦ ?_)
    split_ifs
    · exact integral_nonneg (S.etaOld_nonneg r i h)
    · exact le_rfl
  · exact le_rfl

/-- The charge defect is bounded at fixed `k` (lines 438–440, 488). -/
theorem chargeDefect_le (r : Fin (X.rounds n)) (k : ℕ) (p : ℝ) :
    (S.round r).chargeDefect k p ≤ κ.C * X.K n * n * X.D n * (κ.C * Real.log n ^ κ.Cl) := by
  classical
  set b : ℝ := κ.C * Real.log n ^ κ.Cl with hb
  have hb0 : 0 ≤ b :=
    mul_nonneg (by linarith [κ.one_le_C]) (Real.rpow_nonneg (Real.log_natCast_nonneg n) _)
  have hN0 : 0 ≤ κ.C * X.K n * n * X.D n := by
    have := κ.one_le_C
    positivity
  have := fun h ↦ S.isFiniteMeasure_μOld r k p h
  have hη : ∀ i h, ∫ θ, (S.round r).etaOld i h θ ∂(S.round r).μOld k p h ≤ b := by
    intro i h
    calc ∫ θ, (S.round r).etaOld i h θ ∂(S.round r).μOld k p h
        ≤ ∫ _θ, b ∂(S.round r).μOld k p h :=
          integral_mono (integrable_of_bounded (S.measurable_etaOld r i h)
            (S.etaOld_nonneg r i h) (S.etaOld_le r i h)) (integrable_const _)
            (S.etaOld_le r i h)
      _ = b / 2 := by rw [integral_const, smul_eq_mul, S.μOld_real_univ]; ring
      _ ≤ b := by linarith
  calc (S.round r).chargeDefect k p
      ≤ ∑ h, (S.round r).w h * (κ.C * X.K n * n * X.D n * b) := by
        unfold ScanRound.chargeDefect
        refine Finset.sum_le_sum fun h _ ↦ ?_
        split_ifs
        · refine mul_le_mul_of_nonneg_left ?_ (S.w_nonneg r h)
          calc ∑ i, (if (S.round r).splitOld i h then
                ∫ θ, (S.round r).etaOld i h θ ∂(S.round r).μOld k p h else 0)
              ≤ ∑ i, (if (S.round r).splitOld i h then b else 0) :=
                Finset.sum_le_sum fun i _ ↦ by split_ifs <;> simp [hη]
            _ = (Finset.univ.filter fun i ↦ (S.round r).splitOld i h).card * b := by
                rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            _ ≤ _ := mul_le_mul_of_nonneg_right (S.card_splitOld_le r h) hb0
        · exact mul_nonneg (S.w_nonneg r h) (mul_nonneg hN0 hb0)
    _ = _ := by rw [← Finset.sum_mul, S.sum_w, one_mul]

/-- The integrated entropy inequality (lines 457–475), for every replica count `k ≥ 1`. -/
theorem integratedChargeBound {C₁ : ℝ} (hn : ScaleFacts X n C₁) (k : ℕ) (hk : 1 ≤ k) :
    S.IntegratedChargeBound k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 ≤ X.a n := div_nonneg (by linarith [X.one_le_W]) (Nat.cast_nonneg _)
  have hc : 0 ≤ κ.c / (n * X.D n) := div_nonneg κ.c_pos.le (by positivity)
  have hR : 0 < X.rounds n := by
    unfold ScannerExponents.rounds
    have := hn.two_le_n
    have := hn.one_le_m
    positivity
  have heps := hn.eps_pos
  have heps1 := hn.eps_lt_one
  set err : ℝ := κ.C * k * X.a n * X.K n * X.a n ^ (1 / 4 : ℝ) * Real.log n ^ κ.Cl + S.β k
  have key := sum_integral_le_of_deriv (fun r ↦ (S.round r).logNormSq k)
    (fun r ↦ (S.round r).chargeDefect k) (X.chargeRounds n)
    (coef := k * X.a n * (κ.c / (n * X.D n))) (err := err) (α := X.eps n / 2)
    (β := X.eps n) (by positivity) (by linarith)
    (by linarith) (by positivity) hR (fun r ↦ S.continuousOn_logNormSq r k)
    (fun r ↦ S.differentiableOn_logNormSq r k) (fun r p _ ↦ S.chargeDefect_nonneg r k p)
    (fun r ↦ S.continuousOn_chargeDefect r k) ⟨_, fun r p _ ↦ S.chargeDefect_le r k p⟩
    (fun r hr p hp ↦ by
      have h1 := S.entropy_gain r k p hp
      have h2 := S.chargeDefect_le_choiceGainSum r (Finset.mem_filter.1 hr).2 k p
      have h3 : k * X.a n * (κ.c / (n * X.D n) * (S.round r).chargeDefect k p) ≤
          k * X.a n * (S.round r).choiceGainSum k p :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      simp only [err]
      linarith)
    (fun r p hp ↦ by
      have h1 := S.entropy_gain r k p hp
      have h2 : 0 ≤ k * X.a n * (S.round r).choiceGainSum k p := by
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun h _ ↦ ?_)
        exact mul_nonneg (S.w_nonneg r h) (integral_nonneg (S.choiceGain_nonneg r h))
      simp only [err]
      linarith)
    (fun r hr ↦ S.logNormSq_succ r hr k)
  have hinit := S.logNormSq_init ⟨0, hR⟩ rfl k
  have hfin := S.logNormSq_final ⟨X.rounds n - 1, Nat.sub_lt hR one_pos⟩
    (by simp only; omega) k hk
  rw [div_le_iff₀ hk0] at hfin
  unfold IntegratedChargeBound terminalBound
  nlinarith

end ScanData

end TNLean.PEPS.AreaLaw.Scan
