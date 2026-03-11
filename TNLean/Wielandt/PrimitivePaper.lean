/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.WielandtBound

/-!
# Paper-facing definition layer for primitivity (arXiv:0909.5347)

This file provides **paper-faithful definitions** that mirror the notation and
terminology of Sanz–Pérez-García–Wolf–Cirac, *A quantum version of Wielandt's
inequality* (arXiv:0909.5347) and Wolf's lecture notes (Chapter 6).

All definitions here are thin wrappers around existing codebase constructs.
They are intended as the public API surface for stating Proposition 3 and the
Wielandt bound in paper notation, without changing the internal proof machinery.

## Main definitions

* `krausRank A`: the dimension of `S₁(A) = wordSpan A 1`, i.e.
  `dim(span{A₁,…,Aₐ})`.
* `HasEventuallyFullKrausRank A`: `∃ i, S_i(A) = M_D(ℂ)`, i.e. `IsNormal A`.
* `IsPrimitivePaper A`: paper-faithful primitivity — there exists `q` such that
  for every nonzero φ, `H_q(A,φ) = ℂ^D`. This is Proposition 3(a) of the paper.
* `iIndex A`: `sInf {n | S_n(A) = M_D(ℂ)}` — the full-Kraus-rank index `i(A)`.
* `qIndex A`: `sInf {q | ∀ φ ≠ 0, H_q(A,φ) = ℂ^D}` — the primitivity index `q(E_A)`.

## Relationship to existing definitions

* `HasEventuallyFullKrausRank A ↔ IsNormal A` — proved as
  `hasEventuallyFullKrausRank_iff_isNormal`.
* `IsPrimitivePaper A` is **stronger** than the current `IsPrimitive A`
  (which only asks for a spectral gap with PSD fixed point). The easy direction
  `HasEventuallyFullKrausRank → IsPrimitivePaper` is proved in `PrimitiveEquiv.lean`.
  The converse (and full equivalence with `IsPrimitive`) requires additional
  spectral infrastructure and is deferred.

## Design notes

These are **paper-facing wrappers only**. The internal proof chain still flows
through `IsNormal`, `IsPrimitiveMPS`, etc. The harder equivalence directions
of Proposition 3 are deferred to future files.

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
  Module.finrank ℂ (wordSpan A 1)

/-! ## Eventually full Kraus rank -/

/-- **Eventually full Kraus rank**: there exists an index `i` such that `S_i(A)` spans
the full matrix algebra `M_D(ℂ)`.

Paper: "We say that the set `{A₁,…,Aₐ}` has eventually full Kraus rank if
there exists `i` such that `S_i(A) = M_D(ℂ)`."
(arXiv:0909.5347, Definition after equation (1))

This is equivalent to `IsNormal A` (see `hasEventuallyFullKrausRank_iff_isNormal`). -/
def HasEventuallyFullKrausRank (A : MPSTensor d D) : Prop :=
  ∃ i : ℕ, wordSpan A i = ⊤

/-- `HasEventuallyFullKrausRank` is equivalent to `IsNormal`. -/
theorem hasEventuallyFullKrausRank_iff_isNormal (A : MPSTensor d D) :
    HasEventuallyFullKrausRank A ↔ IsNormal A := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (wordSpan_eq_top_iff_isNBlkInjective A i).mp hi⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, (wordSpan_eq_top_iff_isNBlkInjective A N).mpr hN⟩

/-! ## Paper-faithful primitivity -/

/-- **Paper-faithful primitivity** (Proposition 3(a) of arXiv:0909.5347):
an MPS tensor `A` is primitive (in the paper's sense) if there exists `q` such
that for every nonzero vector `φ`, `H_q(A,φ) = ℂ^D`, i.e. length-`q` word
products applied to `φ` span all of `ℂ^D`.

Paper: "E_A is primitive ⟺ for all |φ⟩ ≠ 0, ∃ q s.t. H_q(A,φ) = ℂ^D."
The uniform `q` (independent of `φ`) is part of the paper's definition.

Note: the paper's Proposition 3 states several equivalent conditions.
The full equivalence is deferred. In particular, the relationship between
`IsPrimitivePaper` and the spectral-gap definition `IsPrimitive` used
internally in this library is established only partially so far
(see `PrimitiveEquiv.lean`). -/
def IsPrimitivePaper (A : MPSTensor d D) : Prop :=
  ∃ q : ℕ, ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan A φ q = ⊤

/-! ## Index definitions -/

/-- **Full-Kraus-rank index** `i(A)`: the smallest `i` such that `S_i(A) = M_D(ℂ)`.

Paper: "i(A) := min{n : S_n(A) = M_D(ℂ)}."
(arXiv:0909.5347, after Proposition 3)

Defined as `sInf {n | wordSpan A n = ⊤}`. Returns 0 if no such `n` exists
(as per `Nat.sInf ∅ = 0`). -/
noncomputable def iIndex (A : MPSTensor d D) : ℕ :=
  sInf {n : ℕ | wordSpan A n = ⊤}

/-- **Primitivity index** `q(E_A)`: the smallest `q` such that for all nonzero φ,
`H_q(A,φ) = ℂ^D`.

Paper: "q(E_A) := min{q : ∀ |φ⟩ ≠ 0, H_q(A,φ) = ℂ^D}."
(arXiv:0909.5347, Proposition 3)

Defined as `sInf {q | ∀ φ ≠ 0, vectorSpreadSpan A φ q = ⊤}`. Returns 0
if no such `q` exists. -/
noncomputable def qIndex (A : MPSTensor d D) : ℕ :=
  sInf {q : ℕ | ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan A φ q = ⊤}

end MPSTensor
