/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic

/-!
# The scalar parity law for the blocked time-reversal sign

Blocking a time-reversal-invariant matrix product unitary produces one sign for
each blocking level. The blocking argument of arXiv:1703.09188 identifies the
sign at level `k` as `σ⁽¹⁾ζ^{k-1}`, where `ζ = σ⁽¹⁾σ⁽²⁾` is the ratio of the
signs at the first two levels (`paper_v2.tex` line 1687), and where the closing
identity `σ⁽ᵏ⁾ = σ⁽¹⁾ζ^{k-1}` is stated at `paper_v2.tex` line 1732.

This file isolates the scalar consequence of that identity for signs valued in
`{1, -1}`: the sign at level `k` is the first sign for odd `k` and the second
sign for even `k`. Only the sign algebra is treated here; the tensor-network
unwinding that produces the identity is not.

## Main results

- `TNLean.Algebra.blockedSign_eq_first_of_odd`: for odd blocking length the sign
  is the first sign.
- `TNLean.Algebra.blockedSign_eq_second_of_even`: for even blocking length the
  sign is the second sign.

## References

* [J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix product
  unitaries: structure, symmetries, and topological invariants*,
  arXiv:1703.09188, lines 1687 and 1732][Cirac2017MPU]
-/

namespace TNLean.Algebra

variable {σ₁ σ₂ : ℂ}

/-- The ratio of the first two blocking signs squares to one. This is the
elementary property of `ζ = σ⁽¹⁾σ⁽²⁾` from arXiv:1703.09188, `paper_v2.tex`
line 1687. -/
theorem sq_mul_eq_one_of_sign (h₁ : σ₁ = 1 ∨ σ₁ = -1) (h₂ : σ₂ = 1 ∨ σ₂ = -1) :
    (σ₁ * σ₂) ^ 2 = 1 := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> subst h₁ <;> subst h₂ <;> norm_num

/-- **Odd blocking length keeps the first sign.** For signs `σ₁, σ₂ ∈ {1, -1}`
and odd `k`, the blocked sign `σ₁(σ₁σ₂)^{k-1}` equals `σ₁`.

This is the odd case of `σ⁽ᵏ⁾ = σ⁽¹⁾ζ^{k-1}` from arXiv:1703.09188,
`paper_v2.tex` line 1732, with `ζ = σ⁽¹⁾σ⁽²⁾` from line 1687. -/
theorem blockedSign_eq_first_of_odd (h₁ : σ₁ = 1 ∨ σ₁ = -1) (h₂ : σ₂ = 1 ∨ σ₂ = -1)
    {k : ℕ} (hk : Odd k) : σ₁ * (σ₁ * σ₂) ^ (k - 1) = σ₁ := by
  obtain ⟨m, hm⟩ := hk
  have hk1 : k - 1 = 2 * m := by omega
  rw [hk1, pow_mul, sq_mul_eq_one_of_sign h₁ h₂, one_pow, mul_one]

/-- **Even blocking length gives the second sign.** For signs `σ₁, σ₂ ∈ {1, -1}`
and even positive `k`, the blocked sign `σ₁(σ₁σ₂)^{k-1}` equals `σ₂`.

This is the even case of `σ⁽ᵏ⁾ = σ⁽¹⁾ζ^{k-1}` from arXiv:1703.09188,
`paper_v2.tex` line 1732, with `ζ = σ⁽¹⁾σ⁽²⁾` from line 1687. -/
theorem blockedSign_eq_second_of_even (h₁ : σ₁ = 1 ∨ σ₁ = -1) (h₂ : σ₂ = 1 ∨ σ₂ = -1)
    {k : ℕ} (hk : 0 < k) (hke : Even k) : σ₁ * (σ₁ * σ₂) ^ (k - 1) = σ₂ := by
  obtain ⟨m, hm⟩ := hke
  have hk1 : k - 1 = 2 * (m - 1) + 1 := by omega
  rw [hk1, pow_succ, pow_mul, sq_mul_eq_one_of_sign h₁ h₂, one_pow, one_mul,
    ← mul_assoc]
  rcases h₁ with h₁ | h₁ <;> subst h₁ <;> norm_num

end TNLean.Algebra
