/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEndpointRoughBudget

/-!
# The selected density from the actual endpoint budget

The actual endpoint estimate and the accepted logarithmic transport error
give the full normalized numerator of charge selection. The normalization
then cancels the original replica count and physical density factors exactly.
These scalar consequences preserve the selected point and do not replace an
endpoint estimate by a new physical assumption.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 457–490, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- Accumulate the exact `2H` transport errors in the same explicit vanishing
remainder. The endpoint premise is supplied by the actual rough endpoint
theorem, and the logarithmic premise by actual charge selection.
Source: `08-scanner.tex`, lines 457–490. -/
theorem roughSelectionBudget_le_of_endpoint_budget
    {k d K H : ℕ} (hk : 0 < k) (c Ci Cβ endpoint Brough rate β : ℝ)
    (hendpoint : endpoint / (k : ℝ) ≤ Brough + roughEndpointRemainder d c K Ci k)
    (hβ : β ≤ Cβ * Real.log ((k : ℝ) + 2)) :
    (endpoint + (2 * H : ℕ) * ((k : ℝ) * rate + β)) / (k : ℝ) ≤
      Brough + (2 * H : ℕ) * rate +
        roughEndpointRemainder d c K (Ci + (2 * H : ℕ) * Cβ) k := by
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hβ' : ((2 * H : ℕ) : ℝ) * β / (k : ℝ) ≤
      ((2 * H : ℕ) : ℝ) * (Cβ * Real.log ((k : ℝ) + 2)) / (k : ℝ) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hβ (Nat.cast_nonneg _)) hkr.le
  calc
    (endpoint + (2 * H : ℕ) * ((k : ℝ) * rate + β)) / (k : ℝ) =
        (endpoint / (k : ℝ) + (2 * H : ℕ) * rate) +
          ((2 * H : ℕ) : ℝ) * β / (k : ℝ) := by
      field_simp [hkr.ne']
      ring
    _ ≤ (Brough + roughEndpointRemainder d c K Ci k + (2 * H : ℕ) * rate) +
        ((2 * H : ℕ) : ℝ) * (Cβ * Real.log ((k : ℝ) + 2)) / (k : ℝ) :=
      _root_.add_le_add (_root_.add_le_add hendpoint le_rfl) hβ'
    _ = _ := by simp only [roughEndpointRemainder]; ring

/-- Normalize the selector's literal endpoint numerator to the entropy-defect
density. No sign restriction is imposed on that numerator. This implication
preserves the already selected point; it performs no second averaging.
Source: `08-scanner.tex`, lines 480–490. -/
theorem selected_density_le_of_normalized_budget
    {k n m D K : ℕ} {a C₁ width Q B Rbudget : ℝ}
    (hk : 0 < k) (hn : 0 < n) (hm : 0 < m) (hD : 0 < D) (hK : 0 < K)
    (ha : 0 < a) (hC : 0 < C₁) (hwidth : 0 < width)
    (hbudget : B / (k : ℝ) ≤ Rbudget)
    (hselection : Q ≤ B /
      (((k : ℝ) * a * ((1 / (2 * (C₁ + 1))) / ((n : ℝ) * D))) *
        ((n * m : ℕ) : ℝ) * width)) :
    Q / (K * n * D : ℝ) ≤
      (2 * (C₁ + 1) / (a * K * ((n * m : ℕ) : ℝ) * width)) * Rbudget := by
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hC1 : 0 < C₁ + 1 := by positivity
  have hcoeff : 0 ≤ 2 * (C₁ + 1) / (a * K * ((n * m : ℕ) : ℝ) * width) :=
    by positivity
  calc
    Q / (K * n * D : ℝ) ≤
        (B / (((k : ℝ) * a * ((1 / (2 * (C₁ + 1))) / ((n : ℝ) * D))) *
          ((n * m : ℕ) : ℝ) * width)) / (K * n * D : ℝ) :=
      div_le_div_of_nonneg_right hselection (by positivity)
    _ = (2 * (C₁ + 1) / (a * K * ((n * m : ℕ) : ℝ) * width)) *
        (B / (k : ℝ)) := by
      push_cast
      field_simp [hkr.ne', hnr.ne', hmr.ne', hDr.ne', hKr.ne',
        ha.ne', hC1.ne', hwidth.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hcoeff

/-- The rough endpoint bound gives the density bound at the same selected
charge point, with total weight equal to the per-band weight times the band count.
Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 457–490,
revision adc7f124. -/
theorem selected_density_of_rough_endpoint
    {k n m D K d : ℕ} {a W C₁ width Q endpoint Brough rate b : ℝ}
    (hk : 0 < k) (hn : 0 < n) (hm : 0 < m) (hD : 0 < D) (hK : 0 < K)
    (ha : 0 < a) (hC : 0 < C₁) (hwidth : 0 < width) (hW : a * (K : ℝ) = W)
    (c Ci Cb : ℝ)
    (hendpoint : endpoint / (k : ℝ) ≤ Brough + roughEndpointRemainder d c K Ci k)
    (hb : b ≤ Cb * Real.log ((k : ℝ) + 2))
    (hselection : Q ≤ (endpoint + (2 * n * m : ℕ) * ((k : ℝ) * rate + b)) /
      (((k : ℝ) * a * ((1 / (2 * (C₁ + 1))) / ((n : ℝ) * D))) *
        ((n * m : ℕ) : ℝ) * width)) :
    Q / (K * n * D : ℝ) ≤ (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * width)) *
      (Brough + (2 * n * m : ℕ) * rate +
        roughEndpointRemainder d c K (Ci + (2 * n * m : ℕ) * Cb) k) := by
  have hbudget := roughSelectionBudget_le_of_endpoint_budget (H := n * m)
    hk c Ci Cb endpoint Brough rate b hendpoint hb
  have hdensity := selected_density_le_of_normalized_budget hk hn hm hD hK ha hC hwidth
    hbudget (by simpa only [Nat.mul_assoc] using hselection)
  simpa only [hW, Nat.mul_assoc] using hdensity

end TNLean.PEPS.AreaLaw.Scan
