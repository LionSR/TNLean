/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.Primitivity.EasyDirections
import TNLean.Wielandt.Primitivity.Definitions

/-!
# Proposition 3, direction (b) to (a), and the index comparison

A normal tensor spreads every nonzero vector to the whole space at one fixed
length, and its primitivity index is at most its full-Kraus-rank index. Neither
statement needs a normalization of the tensor.

## Main results

* `MPSTensor.exists_vectorSpreadSpan_eq_top_of_isNormal`: Proposition 3,
  direction (b) to (a), of arXiv:0909.5347.
* `MPSTensor.qIndex_le_iIndex`: `q(E_A) ≤ i(A)` for a normal tensor.

## References

- Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Propositions 1 and 3.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-! ## (b)→(a): a full word span spreads every vector -/

/-- **Proposition 3, direction (b)⟹(a)**: if `S_N(A) = M_D(ℂ)` for a positive
`N`, then `H_N(A,φ) = ℂ^D` for every nonzero `φ`.

The hypothesis is clause (b) of the proposition, which is `Kraus.IsNormal A` by
definition; the conclusion is clause (a), written out.

Paper: "(b) ⟹ (a)" in Proposition 3, arXiv:0909.5347. -/
theorem exists_vectorSpreadSpan_eq_top_of_isNormal
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    ∃ q : ℕ, 0 < q ∧ ∀ φ : Fin D → ℂ, φ ≠ 0 → Kraus.vectorSpreadSpan A φ q = ⊤ := by
  obtain ⟨N, hNpos, hN⟩ := hA
  exact ⟨N, hNpos, fun φ hφ => Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top A hN φ hφ⟩

/-! ## Index bound: q(E_A) ≤ i(A) -/

/-- **q(E_A) ≤ i(A)**: the primitivity index is at most the full-Kraus-rank index,
provided the tensor is normal.

This is the normal case of "q(E_A) ≤ i(A)" (arXiv:0909.5347, Proposition 1);
the comparison for every channel is `qIndex_le_iIndex_of_tracePreserving`.

The proof uses `Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top`: since
`Kraus.wordSpan A (iIndex A) = ⊤`, we have `Kraus.vectorSpreadSpan A φ (iIndex A) = ⊤`
for all nonzero φ, so `qIndex A ≤ iIndex A`. -/
theorem qIndex_le_iIndex (A : MPSTensor d D)
    (hA : Kraus.IsNormal A) :
    qIndex A ≤ iIndex A := by
  -- iIndex A lies in the positive full-span set since hA makes it nonempty.
  have hne : {n : ℕ | 0 < n ∧ Kraus.wordSpan A n = ⊤}.Nonempty := by
    obtain ⟨N, hNpos, hN⟩ := hA
    exact ⟨N, hNpos, hN⟩
  have hi : Kraus.wordSpan A (iIndex A) = ⊤ := (Nat.sInf_mem hne).2
  -- iIndex A witnesses that the qIndex-defining set is nonempty
  have hq_mem : iIndex A ∈ {q : ℕ | 0 < q ∧ ∀ φ : Fin D → ℂ, φ ≠ 0 →
      Kraus.vectorSpreadSpan A φ q = ⊤} := by
    exact ⟨(Nat.sInf_mem hne).1,
      fun φ hφ => Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top A hi φ hφ⟩
  -- qIndex A = sInf of a set containing iIndex A, so qIndex A ≤ iIndex A
  exact Nat.sInf_le hq_mem

end MPSTensor
