/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.CollarInformation
import TNLean.PEPS.AreaLaw.TwoFamilies

/-!
# The physical dimension in the collar information continuity cost

Only the target region contributes to the logarithmic dimension. Its actual
site cardinality controls that dimension with the fixed local factor log q.
No far-region cardinality or independent dimension certificate is used.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 936--941, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open Classical in
/-- The actual target cardinality supplies the logarithmic dimension needed
by the original-state continuity term. The finite local dimension is fixed
before the system size and region. -/
theorem log_exp_configuration_card_le_of_card
    {Λ : Finset (ℤ × ℤ)} {q n : ℕ} (hq : 1 ≤ q)
    (X : Finset (Site Λ)) {Cvol : ℝ}
    (hcard : (X.card : ℝ) ≤ Cvol * (n : ℝ) ^ 2) :
    Real.log (Real.exp 1 *
      Fintype.card (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) X)) ≤
        1 + (Cvol * Real.log q) * (n : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hdimpos : (0 : ℝ) <
      Fintype.card (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) X) := by
    simp only [FiniteProduct.Configuration, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, Nat.cast_pow]
    positivity
  rw [Real.log_mul (Real.exp_pos 1).ne' hdimpos.ne', Real.log_exp]
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hbound := _root_.add_le_add (le_refl (1 : ℝ))
    (mul_le_mul_of_nonneg_right hcard hlogq)
  simpa only [FiniteProduct.Configuration, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Nat.cast_pow, Real.log_pow, mul_right_comm] using hbound

end TNLean.PEPS.AreaLaw.Scan
