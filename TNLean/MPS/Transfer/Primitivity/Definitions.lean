/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.WordSpan
import QICLean.Kraus.Transfer
import QICLean.Channel.Peripheral.Spectrum
import QICLean.Channel.Irreducible.Basic
import TNLean.MPS.Tensor

/-!
# Index definitions for the quantum Wielandt theorem

This file defines the Kraus rank and the two indices of Sanz, Pérez-García,
Wolf and Cirac, *A quantum version of Wielandt's inequality* (arXiv:0909.5347),
in the notation of the source: `S_n(A)`, `i(A)` and `q(E_A)`.

## Main definitions

* `krausRank A`: the dimension of `S₁(A) = Kraus.wordSpan A 1`, i.e.
  `dim(span{A₁,…,Aₐ})`.
* `iIndex A`: `sInf {n | 0 < n ∧ S_n(A) = M_D(ℂ)}`, the positive
  full-Kraus-rank index `i(A)`.
* `qIndex A`: `sInf {q | 0 < q ∧ ∀ φ ≠ 0, H_q(A,φ) = ℂ^D}`, the positive
  primitivity index `q(E_A)`.

## The notions of primitivity

The source introduces three properties of a channel `E_A` (arXiv:0909.5347,
`Papers/0909.5347/main.tex`, lines 403–430): (a) primitivity, a uniform length
`q` with `H_q(A,φ) = ℂ^D` for every nonzero `φ`; (b) eventually full Kraus
rank, a length `n` with `S_n(A) = M_D(ℂ)`; (c) strong irreducibility, a unique
eigenvalue of modulus one whose eigenvector is positive definite. None of the
three has a predicate of its own. Property (b) is `Kraus.IsNormal A` by
definition, the peripheral part of (c) is `IsPrimitive (Kraus.transferMap A)`,
and Proposition 3 of the source, which says the three are equivalent for a
trace-preserving family, is the single theorem `MPSTensor.primitivity_tfae` of
`Primitivity/Equivalence.lean`, with each clause written out.

## References

- [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347](https://arxiv.org/abs/0909.5347), Section II & Proposition 3
- Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-! ## Kraus rank -/

/-- **Kraus rank** of an MPS tensor: the dimension of `S₁(A)`, the span of
`{A₁, …, Aₐ}`.

Paper notation: this is `dim(S₁(A))`.
(arXiv:0909.5347, Section II) -/
noncomputable def krausRank (A : MPSTensor d D) : ℕ :=
  Module.finrank ℂ (Kraus.wordSpan A 1)

/-! ## Index definitions -/

/-- **Full-Kraus-rank index** `i(A)`: the smallest positive `i` such that
`S_i(A) = M_D(ℂ)`.

Paper: "i(A) := min{n : S_n(A) = M_D(ℂ)}."
(arXiv:0909.5347, after Proposition 3)

The paper takes its word lengths in `ℕ = {1, 2, …}`.  Accordingly this is
defined as `sInf {n | 0 < n ∧ Kraus.wordSpan A n = ⊤}`, the least length
witnessing `Kraus.IsNormal A`.  It returns 0 if no such `n` exists (as per
`Nat.sInf ∅ = 0`). -/
noncomputable def iIndex (A : MPSTensor d D) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ Kraus.wordSpan A n = ⊤}

/-- **Primitivity index** `q(E_A)`: the smallest positive `q` such that for all nonzero φ,
`H_q(A,φ) = ℂ^D`.

Paper: "q(E_A) := min{q : ∀ |φ⟩ ≠ 0, H_q(A,φ) = ℂ^D}."
(arXiv:0909.5347, Proposition 3)

The paper uses the same positive word-length convention as for `i(A)`.  Accordingly this
is `sInf {q | 0 < q ∧ ∀ φ ≠ 0, Kraus.vectorSpreadSpan A φ q = ⊤}`. It returns 0 if no such
`q` exists. -/
noncomputable def qIndex (A : MPSTensor d D) : ℕ :=
  sInf {q : ℕ | 0 < q ∧ ∀ φ : Fin D → ℂ, φ ≠ 0 →
    Kraus.vectorSpreadSpan A φ q = ⊤}

end MPSTensor
