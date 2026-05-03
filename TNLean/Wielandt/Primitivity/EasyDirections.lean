/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.Primitivity.PaperDefinitions
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan

/-!
# Primitive equivalences — easy directions (Proposition 3)

This file proves the **easy first directions** of Proposition 3 from
arXiv:0909.5347, which establishes equivalences between primitivity,
eventually full Kraus rank, and strong irreducibility.

## What is proved here

* `vectorSpreadSpan_eq_top_of_wordSpan_eq_top`:
  If `wordSpan A N = ⊤` (the exact word span at level N is full) and `φ ≠ 0`,
  then `vectorSpreadSpan A φ N = ⊤` (exact vector spread at level N is full).
  This is the (b)→(a) direction of Proposition 3.

* `isPrimitivePaper_of_hasEventuallyFullKrausRank`:
  Eventually full Kraus rank implies paper-primitivity.
  This is direction (b)→(a) of Proposition 3 at the predicate level.

* `qIndex_le_iIndex`:
  The primitivity index `q(E_A)` is at most the full-Kraus-rank index `i(A)`,
  provided the tensor has eventually full Kraus rank.

## The full equivalence

All three directions of Proposition 3 are now proved:

* **(b)→(a)**: Proved here (`isPrimitivePaper_of_hasEventuallyFullKrausRank`).
* **(a)→(c)**: Proved in `Primitivity/ImpliesStronglyIrreducible.lean`
  (`isStronglyIrreduciblePaper_of_isPrimitivePaper`).
* **(c)→(b)**: Proved in `Primitivity/StronglyIrreducibleToFullRank.lean`
  (`hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper`).

The full circular equivalence and `Iff` statements are assembled in `Primitivity/Equivalence.lean`.

## References

- [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347](https://arxiv.org/abs/0909.5347), Proposition 3
- Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.4
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-! ## (b)→(a): Full word span implies full vector spread -/

/-- If `wordSpan A N = ⊤` and `φ ≠ 0`, then `vectorSpreadSpan A φ N = ⊤`.

**Proof sketch**: The map `f : M ↦ M *ᵥ φ` sends `wordSpan A N` onto
`vectorSpreadSpan A φ N` (by `map_wordSpan_eq_vectorSpreadSpan`). If
`wordSpan A N = ⊤`, then the image is `range f`. Since `φ ≠ 0`, the map
`f` is surjective: for any target vector `v`, we can build `M` with
`M *ᵥ φ = v` using `Matrix.single` basis elements.

Paper: This is implicit in Proposition 3's direction (b)⟹(a).
"If S_N(A) = M_D(ℂ), then for any |φ⟩ ≠ 0, S_N(A)|φ⟩ = M_D(ℂ)|φ⟩ = ℂ^D."
(arXiv:0909.5347, Proposition 3) -/
theorem vectorSpreadSpan_eq_top_of_wordSpan_eq_top
    (A : MPSTensor d D) {N : ℕ}
    (htop : wordSpan A N = ⊤)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0) :
    vectorSpreadSpan A φ N = ⊤ := by
  -- The image of wordSpan A N under (· *ᵥ φ) is vectorSpreadSpan A φ N
  rw [← map_wordSpan_eq_vectorSpreadSpan A φ N, htop, Submodule.map_top]
  -- It suffices to show that (· *ᵥ φ) is surjective
  rw [LinearMap.range_eq_top]
  intro v
  -- Since φ ≠ 0, there exists k with φ k ≠ 0
  obtain ⟨k, hk⟩ : ∃ k : Fin D, φ k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hφ (funext fun i => hall i)
  -- Construct M with M *ᵥ φ = v
  refine ⟨∑ j, Matrix.single j k (v j * (φ k)⁻¹), ?_⟩
  change (∑ j, Matrix.single j k (v j * (φ k)⁻¹)) *ᵥ φ = v
  simp only [Matrix.sum_mulVec, Matrix.single_mulVec]
  ext j
  simp only [Finset.sum_apply, Function.update_apply, Pi.zero_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  field_simp

/-! ## (b)→(a): Eventually full Kraus rank implies paper-primitivity -/

/-- **Proposition 3, direction (b)⟹(a)**:
If `A` has eventually full Kraus rank, then `A` is primitive in the paper's sense.

This is the easy direction: if some `wordSpan A N = ⊤`, then taking `q = N`,
we have `vectorSpreadSpan A φ N = ⊤` for every nonzero `φ` by
`vectorSpreadSpan_eq_top_of_wordSpan_eq_top`.

Paper: "(b) ⟹ (a)" in Proposition 3, arXiv:0909.5347. -/
theorem isPrimitivePaper_of_hasEventuallyFullKrausRank
    (A : MPSTensor d D) (hA : HasEventuallyFullKrausRank A) :
    IsPrimitivePaper A := by
  obtain ⟨N, hN⟩ := hA
  exact ⟨N, fun φ hφ => vectorSpreadSpan_eq_top_of_wordSpan_eq_top A hN φ hφ⟩

/-- **Proposition 3, direction (b)⟹(a)**, stated with `IsNormal`:
If `A` is normal, then `A` is primitive in the paper's sense.

This is the restatement of `isPrimitivePaper_of_hasEventuallyFullKrausRank`
using the library's `IsNormal` predicate instead of
`HasEventuallyFullKrausRank`. -/
theorem isPrimitivePaper_of_isNormal
    (A : MPSTensor d D) (hA : IsNormal A) :
    IsPrimitivePaper A :=
  isPrimitivePaper_of_hasEventuallyFullKrausRank A
    ((hasEventuallyFullKrausRank_iff_isNormal A).mpr hA)

/-! ## Index bound: q(E_A) ≤ i(A) -/

/-- **q(E_A) ≤ i(A)**: the primitivity index is at most the full-Kraus-rank index,
provided the tensor has eventually full Kraus rank.

Paper: "q(E_A) ≤ i(A)" (arXiv:0909.5347, equation (2)).

The proof uses `vectorSpreadSpan_eq_top_of_wordSpan_eq_top`: since
`wordSpan A (iIndex A) = ⊤`, we have `vectorSpreadSpan A φ (iIndex A) = ⊤`
for all nonzero φ, so `qIndex A ≤ iIndex A`. -/
theorem qIndex_le_iIndex (A : MPSTensor d D)
    (hA : HasEventuallyFullKrausRank A) :
    qIndex A ≤ iIndex A := by
  -- iIndex A ∈ {n | wordSpan A n = ⊤} since hA gives the set is nonempty
  have hne : {n : ℕ | wordSpan A n = ⊤}.Nonempty := hA
  have hi : wordSpan A (iIndex A) = ⊤ := Nat.sInf_mem hne
  -- iIndex A witnesses that the qIndex-defining set is nonempty
  have hq_mem : iIndex A ∈ {q : ℕ | ∀ φ : Fin D → ℂ, φ ≠ 0 →
      vectorSpreadSpan A φ q = ⊤} := by
    intro φ hφ
    exact vectorSpreadSpan_eq_top_of_wordSpan_eq_top A hi φ hφ
  -- qIndex A = sInf of a set containing iIndex A, so qIndex A ≤ iIndex A
  exact Nat.sInf_le hq_mem

end MPSTensor
