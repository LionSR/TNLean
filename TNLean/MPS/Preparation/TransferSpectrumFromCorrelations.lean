/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DecayingCorrelations
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# A correlation decay rate bounds the nonunit transfer spectrum

Block injectivity already gives physical observables whose limiting
connected contraction is exactly `λ^n` for any transfer eigenvalue `λ ≠ 1`.
Thus a common exponential rate for all limiting block correlators bounds
every such eigenvalue by the same rate. Observable-dependent prefactors
cancel: if `|λ| > r`, the powers of `|λ| / r` are unbounded.

This is a conditional rate-transfer lemma. In the physical SPT converse,
ordinary finite-ring clustering must still be derived from the Hamiltonian
gap, passed to the limiting contractions, and transported to a
trace-preserving gauge. No such physical implication is claimed here.

## References

* arXiv:2307.01696, Supplemental Material, proof of Lemma 2: the existing
  physical-observable construction detecting a transfer eigenvalue.
* arXiv:1010.3732, Section II.F, lines 929–953 and Appendix C, lines
  2653–2717: the SPT separation argument for which a uniform transfer rate
  is required.
-/

open scoped Matrix

namespace MPSTensor

/-- A common positive geometric rate for all limiting block correlators
bounds every nonunit transfer spectral value, with no restriction on the
observable-dependent prefactors or initial separation thresholds. The physical
observables are supplied by
`exists_limitCorrelator_eq_pow` (arXiv:2307.01696, proof of Lemma 2).
This auxiliary implication assumes the correlator estimate explicitly; it
does not derive it from a Hamiltonian gap. -/
theorem norm_transfer_spectrum_le_of_limitCorrelator_bound
    {d D L : ℕ} {A : MPSTensor d D}
    (hL : Kraus.IsNBlkInjective A L) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : Matrix.trace ρ = 1)
    {r : ℝ} (hr : 0 < r)
    (hCorr : ∀ X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ‖limitCorrelator A ρ (by rw [hρ]; exact one_ne_zero) L X Y n‖ ≤ C * r ^ n)
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ (Kraus.transferMap A)) (hlamOne : lam ≠ 1) :
    ‖lam‖ ≤ r := by
  classical
  have hEigen := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlam
  obtain ⟨R, hR⟩ := hEigen.exists_hasEigenvector
  obtain ⟨X, Y, hXY⟩ := exists_limitCorrelator_eq_pow hL hA hρ hR.2
    hR.apply_eq_smul hlamOne
  obtain ⟨C, n₀, hC⟩ := hCorr X Y
  by_contra hle
  have hlt : r < ‖lam‖ := lt_of_not_ge hle
  have hratio : 1 < ‖lam‖ / r := (lt_div_iff₀ hr).mpr (by simpa using hlt)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
  have hbound := hC (n + n₀) (Nat.le_add_left n₀ n)
  rw [hXY, norm_pow] at hbound
  have hquot : (‖lam‖ / r) ^ (n + n₀) ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos hr (n + n₀))]
    exact hbound
  have hpow : (‖lam‖ / r) ^ n ≤ (‖lam‖ / r) ^ (n + n₀) :=
    pow_le_pow_right₀ hratio.le (Nat.le_add_right n n₀)
  exact (not_lt_of_ge hquot) (hn.trans_le hpow)

end MPSTensor
