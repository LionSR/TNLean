/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import TNLean.Algebra.TailPowerSumUniqueness

/-!
# Power sums of unit modulus

If a finite family of nonzero complex numbers `μ₁, …, μₙ` has power sums
`s_L = ∑ₖ μₖ^L` of modulus one at every positive exponent `L`, then the family has exactly one
member, and that member is a phase. Indeed `|s_L|² = ∑_{k,l} (μₖ μ̄ₗ)^L`, so the multiset
`{μₖ μ̄ₗ}` of `n²` nonzero numbers has the power sums of `{1}` at every positive exponent; by
uniqueness of power sums on a tail (`Multiset.eq_of_notMem_zero_of_forall_sum_map_pow_eq`) the
two multisets agree, and `n² = 1`.

This is the analytic step of arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 571–574,
where it is argued by comparing the exponents `N` and `2N` after bringing all `μₖ^N` close to
the positive real axis. The argument here replaces that approximation step by power-sum
uniqueness.

## Main results

* `Complex.exists_norm_eq_one_sum_pow_eq_pow`: the power sums are the powers of one phase.
-/

open scoped ComplexConjugate

namespace Complex

/-- Project result: **power sums of unit modulus come from one phase.** If `μ₁, …, μₙ` are
nonzero and `‖∑ₖ μₖ^L‖ = 1` for every positive `L`, then there is `λ` with `‖λ‖ = 1` and
`∑ₖ μₖ^L = λ^L` for every `L`; in particular `n = 1`. -/
theorem exists_norm_eq_one_sum_pow_eq_pow {n : ℕ} (μ : Fin n → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (h : ∀ L : ℕ, 0 < L → ‖(∑ k, μ k ^ L)‖ = 1) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ L : ℕ, ∑ k, μ k ^ L = lam ^ L := by
  classical
  set Λ : Multiset ℂ :=
    (Finset.univ : Finset (Fin n × Fin n)).val.map (fun p ↦ μ p.1 * conj (μ p.2)) with hΛ
  have hΛ0 : (0 : ℂ) ∉ Λ := by
    rw [hΛ, Multiset.mem_map]
    rintro ⟨p, -, hp⟩
    exact mul_ne_zero (hμ p.1) ((map_ne_zero _).2 (hμ p.2)) hp
  have hsum : ∀ L : ℕ, 1 ≤ L → (Λ.map (· ^ L)).sum = (({1} : Multiset ℂ).map (· ^ L)).sum := by
    intro L hL
    have hL' := h L hL
    rw [hΛ, Multiset.map_map]
    change ∑ p : Fin n × Fin n, (μ p.1 * conj (μ p.2)) ^ L = _
    simp only [Multiset.map_singleton, one_pow, Multiset.sum_singleton, mul_pow,
      ← map_pow, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, hL', one_pow, Complex.ofReal_one]
  have hEq := Multiset.eq_of_notMem_zero_of_forall_sum_map_pow_eq hΛ0 (by simp) ⟨1, hsum⟩
  have hcard := congrArg Multiset.card hEq
  simp only [hΛ, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Multiset.card_singleton] at hcard
  obtain rfl : n = 1 := Nat.eq_one_of_mul_eq_one_right hcard
  refine ⟨μ 0, ?_, fun L ↦ by rw [Fin.sum_univ_one]⟩
  simpa [Fin.sum_univ_one] using h 1 one_pos

end Complex
