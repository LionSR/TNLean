/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Squarefree
import TNLean.MPS.Examples.WStateBlocking

/-!
# W-state bounds for divisors and squarefree lengths

The W-block compression preserves bond dimension and gives a periodic W representation at
every divisor of the original length. At a divisor having no factor between two and the bond
dimension, the existing general Wielandt estimate therefore bounds the whole divisor, rather
than just its prime factors.

For squarefree length `N`, the quotient `N / gcd N D!` is coprime to `D!`, so this gives
`N < gcd N D! * B(D) ≤ D! * B(D)`, where
`B(D) = 2 * max ((D² + 1)²) (3 * (D - 1) * ((D² + 1)² + 1))`.
These are project consequences of the blocking reduction in PGVWC07,
arXiv:quant-ph/0608197, lines 2090–2097, and the W-block isometry.

**Scope restriction (squarefree lengths and factorial bound):** these consequences do not
bound arbitrary lengths with repeated small prime factors. The factorial dependence is weaker
than the review's `D³ log D = Ω(N)` bound, which also needs the logarithmic Wielandt estimate.
The source-labelled claim remains open in `docs/paper-gaps/rmp_w_state_ti_bound.tex`.
-/

open scoped Matrix

namespace MPSTensor

/-- A divisor of a represented W length satisfies the fifth-degree bound if it has no factor
between two and the bond dimension. The shorter periodic representation is obtained from
`mpv_wBlockCompression_of_eq_wIndicator`, not assumed. -/
theorem divisor_lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor {D N : ℕ}
    (A : MPSTensor 2 D) (hN : 0 < N) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ)
    {m : ℕ} (hmN : m ∣ N) (hm : 2 ≤ m)
    (hdiv : ∀ a : ℕ, 2 ≤ a → a ≤ D → ¬a ∣ m) :
    m < 2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
  obtain ⟨k, rfl⟩ := hmN
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hroot : (Real.sqrt k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hk))
  exact lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor
    (rotatePhysical (wBlockEncoding k)ᴴ (blockTensor A k)) hm hdiv (mul_ne_zero hc hroot)
    (mpv_wBlockCompression_of_eq_wIndicator hk A hW)

/-- At squarefree length, the small prime factors contribute at most `gcd N D!` to the W-state
length bound. This is an arithmetic consequence of the divisor bound, with no canonical-form
or injectivity hypothesis on the tensor. -/
theorem lt_gcd_factorial_mul_of_mpv_eq_smul_wIndicator_of_squarefree {D N : ℕ}
    (A : MPSTensor 2 D) (hN : Squarefree N) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < N.gcd D.factorial *
      (2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1))) := by
  let k := N.gcd D.factorial
  let m := N / k
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN.ne_zero
  have hk : 0 < k := Nat.gcd_pos_of_pos_left _ hNpos
  have hkm : k * m = N := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hmN : m ∣ N := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hcop : m.Coprime D.factorial :=
    Nat.coprime_div_gcd_of_squarefree hN (Nat.factorial_ne_zero D)
  have hmB : m <
      2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
    by_cases hm : 2 ≤ m
    · apply divisor_lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor A hNpos hc hW hmN hm
      intro a ha haD ham
      have haf : a ∣ D.factorial := Nat.dvd_factorial (by omega) haD
      have := Nat.eq_one_of_dvd_coprimes hcop ham haf
      omega
    · have hm1 : m ≤ 1 := by omega
      have hmax := le_max_left ((D ^ 2 + 1) ^ 2)
        (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1))
      have hpos : 0 < (D ^ 2 + 1) ^ 2 := by positivity
      omega
  simpa only [hkm] using Nat.mul_lt_mul_of_pos_left hmB hk

/-- Every periodic W representation at squarefree length satisfies a factorial bound in its
bond dimension. The tensor may depend on the single represented length. -/
theorem lt_factorial_mul_of_mpv_eq_smul_wIndicator_of_squarefree {D N : ℕ}
    (A : MPSTensor 2 D) (hN : Squarefree N) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < D.factorial *
      (2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1))) := by
  exact (lt_gcd_factorial_mul_of_mpv_eq_smul_wIndicator_of_squarefree A hN hc hW).trans_le
    (Nat.mul_le_mul_right _ (Nat.gcd_le_right N (Nat.factorial_pos D)))

end MPSTensor
