/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.WStateCanonicalBound
import TNLean.MPS.CanonicalForm.PrimeLengthNormalBlocks

/-!
# W-state bounds at lengths without small divisors

The periodic decomposition in Pérez-García, Verstraete, Wolf, and Cirac
(arXiv:quant-ph/0608197, Theorem 5) makes a period-\(m\) block vanish at length \(N\)
whenever \(m\nmid N\). Nonzero cyclic sectors give \(m\le D\), so a length with no divisor
between \(2\) and \(D\) receives contributions only from primitive blocks. Applying the
canonical-block W-state argument and the general quantum Wielandt bound gives
\(N<2\max((D^2+1)^2,3(D-1)((D^2+1)^2+1))\).

This includes composite lengths whose prime factors exceed the bond dimension. The
prime-length theorem follows as a corollary, using the direct numerical bound when
\(N\le D\).

**Scope restriction (chain lengths and the general Wielandt index):** the cubic source
bound assumes Conjecture 2 of arXiv:quant-ph/0608197, and the review's bound
\(D^3\log D=\Omega(N)\) uses the Michałek–Shitov index. The general index used here yields
only a fifth-degree estimate, and lengths with a divisor between \(2\) and \(D\) require
an additional reduction. Documented in `docs/paper-gaps/rmp_w_state_ti_bound.tex`.

## Main results

* `MPSTensor.lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor` — the bound when no integer
  between two and the bond dimension divides the chain length.
* `MPSTensor.lt_of_mpv_eq_smul_wIndicator_of_prime` — the prime-length consequence.

## References

* arXiv:quant-ph/0608197, Theorem 5, Appendix "An open problem", and the W-state corollary;
  `Papers/quant-ph_0608197/MPSarchive.tex`, lines 849–858, 2090–2097, and 2182–2225.
* arXiv:2011.12127, Appendix A, "The W state";
  `Papers/2011.12127/TN-Review-main.tex`, line 2362.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

/-- Project result: the W-state bound when no integer between two and the bond dimension
divides the chain length.

The canonical reduction of arXiv:quant-ph/0608197, Appendix "An open problem", removes a
periodic block whenever its period does not divide the chain length (Theorem 5). The linear
period bound therefore suffices for this divisor hypothesis. The surviving primitive blocks
satisfy injectivity after \((D^2+1)^2\) sites by the general quantum Wielandt bound
(arXiv:0909.5347, Theorem 1). Grouping phase-equivalent blocks gives the hypotheses of the
canonical W-state bound. The remaining source restrictions are recorded in the module docstring. -/
theorem lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor {D : ℕ}
    (A : MPSTensor 2 D) {N : ℕ} (hN : 2 ≤ N)
    (hdiv : ∀ m : ℕ, 2 ≤ m → m ≤ D → ¬m ∣ N) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < 2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
  obtain ⟨r, dim, B, γ, hdim, _, hrD, hunital, hDual, hIrr,
      hC1, hDistinct, hγ, hdecomp⟩ := exists_normal_blocks_of_no_small_divisor A hN hdiv
  have hW' : ∀ σ : Cfg 2 N, ∑ j, γ j * mpv (B j) σ = c * wIndicator N σ := by
    intro σ
    rw [← hdecomp, hW]
  refine (lt_of_sum_mpv_eq_smul_wIndicator B hdim hunital hDual hIrr (by positivity)
    hC1 hDistinct γ hγ hc hW').trans_le ?_
  gcongr

/-- At prime chain length, every translation-invariant periodic representation of a nonzero
multiple of the W state satisfies the fifth-degree bond-dimension bound.

This is the prime-length reduction of arXiv:quant-ph/0608197, Appendix "An open problem",
with the general quantum Wielandt estimate in place of its Conjecture 2. For \(N>D\),
primality implies the hypothesis of `lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor`;
for \(N\le D\), the numerical bound is immediate. -/
theorem lt_of_mpv_eq_smul_wIndicator_of_prime {D : ℕ} (A : MPSTensor 2 D) {N : ℕ}
    (hN : N.Prime) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ) :
    N < 2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
  rcases le_or_gt N D with hND | hND
  · nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) D,
      le_max_left ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1))]
  · exact lt_of_mpv_eq_smul_wIndicator_of_no_small_divisor A hN.two_le
      (fun m hm2 hmD hdvd ↦ (hN.eq_one_or_self_of_dvd m hdvd).elim (by omega) (by omega)) hc hW

end MPSTensor
