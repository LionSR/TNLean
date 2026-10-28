/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Cover
import Mathlib.Order.Fin.Basic
import Mathlib.Order.ModularLattice

/-!
# The matching of two covering chains in a modular lattice

Let `α` be a modular lattice. A step `P ⋖ Q` is a covering pair: nothing lies strictly between `P`
and `Q`. For the lattice of invariant subspaces of a tensor, a step is exactly an invariant subspace
`P ⊂ Q` with `Q / P` irreducible.

This file proves the explicit Jordan–Hölder matching of two flags of invariant subspaces (blueprint
`sec:asym_uniqueness`). For two steps `P ⋖ Q` and `P' ⋖ Q'` with `P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')`, the
step lemma (blueprint `lem:asym_uniq_step`, *One step against another*) gives, with `U = Q ⊓ Q'`,
* (a) `P ⊔ U = Q` and `Q ⊓ P' ≤ P`;
* (b) `P' ⊔ U = Q'` and `Q' ⊓ P ≤ P'`;
* (c) `P ⊓ Q' = Q ⊓ P'`, and the same strict inequality with the two steps exchanged.

For two chains `⊥ = M 0 ⋖ M 1 ⋖ ⋯ ⋖ M r = ⊤` and `⊥ = M' 0 ⋖ ⋯ ⋖ M' r' = ⊤`, the matching (blueprint
`prop:asym_uniq_matching`, *The matching*) assigns to the step `k` of the first chain the least
index `k'` with `M (k + 1) ⊓ M' (k' + 1) ≰ M k`. This is the only index at which the chain
`M k ⊔ (M (k + 1) ⊓ M' j)` increases; the same rule with the chains exchanged is its inverse, so
`r = r'`, and the matched steps satisfy the identities of the step lemma.

Mathlib's `CompositionSeries.jordan_holder` is not used: it produces an equivalence of composition
series, which records only that the factors agree up to a permutation, whereas the comparison of
reductions needs the specific matching rule above together with the four lattice identities that
identify both matched factors with `U / K`, where `K = P ⊓ Q' = Q ⊓ P'`. The isomorphisms
`U / K ≃ Q / P` and `U / K ≃ Q' / P'` of the step lemma are not lattice statements and are not
formalized here.

## References

Blueprint chapter *The Multi-Block Asymmetric Fundamental Theorem* (`ch:asymmetric_ft`), section
*Uniqueness of multi-block compressions*: `lem:asym_uniq_step`, *One step against another*, and
`prop:asym_uniq_matching`, *The matching*.
-/

namespace CoveringMatching

variable {α : Type*} [Lattice α]

section Step

/-- If `x` and `y` lie between the two ends of a covering pair `P ⋖ Q` and `x < y`, then `x = P`
and `y = Q`. -/
theorem eq_and_eq_of_lt {P Q x y : α} (hPQ : P ⋖ Q) (hPx : P ≤ x) (hxy : x < y) (hyQ : y ≤ Q) :
    x = P ∧ y = Q := by
  have hx : x = P := (hPQ.eq_or_eq hPx (hxy.le.trans hyQ)).resolve_right
    fun h ↦ (h ▸ hxy).not_ge hyQ
  refine ⟨hx, (hPQ.eq_or_eq (hPx.trans hxy.le) hyQ).resolve_left fun h ↦ ?_⟩
  exact hxy.ne (hx.trans h.symm)

/-- The first two conclusions of the step lemma (blueprint `lem:asym_uniq_step`, *One step against
another*): if `P ⋖ Q` and `P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')`, then `P ⊔ (Q ⊓ Q') = Q` and `Q ⊓ P' ≤ P`.
Both sides of the inequality lie between `P` and `Q`, so the smaller is `P` and the larger is `Q`.
The covering hypothesis on `P' ⋖ Q'` and the modular law are not needed for this part. -/
theorem step_sup_eq_of_lt {P Q P' Q' : α} (hPQ : P ⋖ Q)
    (h : P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')) : P ⊔ (Q ⊓ Q') = Q ∧ Q ⊓ P' ≤ P := by
  obtain ⟨hlow, hhigh⟩ := eq_and_eq_of_lt hPQ le_sup_left h (sup_le hPQ.le inf_le_left)
  exact ⟨hhigh, sup_eq_left.mp hlow⟩

variable [IsModularLattice α]

/-- The third and fourth conclusions of the step lemma (blueprint `lem:asym_uniq_step`, *One step
against another*): if `P ⋖ Q`, `P' ⋖ Q'` and `P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')`, then
`P' ⊔ (Q ⊓ Q') = Q'` and `Q' ⊓ P ≤ P'`. In each of the two excluded cases, `Q ⊓ Q' ≤ P` follows,
using `step_sup_eq_of_lt` and, in the second case, the modular law `(P ⊔ P') ⊓ Q = P ⊔ (P' ⊓ Q)` for
`P ≤ Q`; this contradicts `P ⊔ (Q ⊓ Q') = Q`. -/
theorem step_sup_eq_of_lt' {P Q P' Q' : α} (hPQ : P ⋖ Q) (hPQ' : P' ⋖ Q')
    (h : P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')) : P' ⊔ (Q ⊓ Q') = Q' ∧ Q' ⊓ P ≤ P' := by
  obtain ⟨hsup, hinf⟩ := step_sup_eq_of_lt hPQ h
  -- From `Q ⊓ Q' ≤ P` the identity `P ⊔ (Q ⊓ Q') = Q` would give `P = Q`.
  have hU : ¬ Q ⊓ Q' ≤ P := fun hle ↦ hPQ.ne (by rwa [sup_eq_left.mpr hle] at hsup)
  refine ⟨(hPQ'.eq_or_eq le_sup_left (sup_le hPQ'.le inf_le_right)).resolve_left fun hU' ↦ ?_,
    sup_eq_left.mp <|
      (hPQ'.eq_or_eq le_sup_left (sup_le hPQ'.le inf_le_left)).resolve_right fun hQ' ↦ ?_⟩
  · -- First case: `Q ⊓ Q' ≤ P'`, hence `Q ⊓ Q' ≤ Q ⊓ P' ≤ P`.
    exact hU ((le_inf inf_le_left (sup_eq_left.mp hU')).trans hinf)
  · -- Second case: `Q' ≤ P' ⊔ P`, hence `Q ⊓ Q' ≤ (P ⊔ P') ⊓ Q = P ⊔ (P' ⊓ Q) = P`.
    refine hU ?_
    have hQ'le : Q' ≤ P ⊔ P' :=
      hQ'.symm.le.trans (sup_le le_sup_right (inf_le_right.trans le_sup_left))
    calc Q ⊓ Q' ≤ (P ⊔ P') ⊓ Q := le_inf (inf_le_right.trans hQ'le) inf_le_left
      _ = P ⊔ (P' ⊓ Q) := sup_inf_assoc_of_le P' hPQ.le
      _ ≤ P := sup_le le_rfl ((inf_comm P' Q).le.trans hinf)

/-- The fifth conclusion of the step lemma (blueprint `lem:asym_uniq_step`, *One step against
another*): if `P ⋖ Q`, `P' ⋖ Q'` and `P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')`, then `P ⊓ Q' = Q ⊓ P'`. -/
theorem step_inf_eq_of_lt {P Q P' Q' : α} (hPQ : P ⋖ Q) (hPQ' : P' ⋖ Q')
    (h : P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')) : P ⊓ Q' = Q ⊓ P' := by
  have ha := (step_sup_eq_of_lt hPQ h).2
  have hb := (step_sup_eq_of_lt' hPQ hPQ' h).2
  refine le_antisymm (le_inf (inf_le_left.trans hPQ.le) ?_)
    (le_inf ha (inf_le_right.trans hPQ'.le))
  exact (inf_comm P Q').le.trans hb

/-- The last conclusion of the step lemma (blueprint `lem:asym_uniq_step`, *One step against
another*): if `P ⋖ Q`, `P' ⋖ Q'` and `P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')`, then the same inequality holds
with the two steps exchanged. By `step_sup_eq_of_lt'` it reads `P' < Q'`. -/
theorem step_lt_symm {P Q P' Q' : α} (hPQ : P ⋖ Q) (hPQ' : P' ⋖ Q')
    (h : P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q')) : P' ⊔ (Q' ⊓ P) < P' ⊔ (Q' ⊓ Q) := by
  obtain ⟨hsup, hinf⟩ := step_sup_eq_of_lt' hPQ hPQ' h
  rw [sup_eq_left.mpr hinf, inf_comm Q' Q, hsup]
  exact hPQ'.lt

end Step

/-- A chain `⊥ = M 0 ⋖ M 1 ⋖ ⋯ ⋖ M r = ⊤` of covering pairs. For the lattice of invariant subspaces
of a tensor this is an invariant flag whose steps are irreducible, as in the matching (blueprint
`prop:asym_uniq_matching`, *The matching*). -/
structure CoveringChain (α : Type*) [Lattice α] [OrderBot α] [OrderTop α] (r : ℕ) where
  /-- The members of the chain. -/
  toFun : Fin (r + 1) → α
  toFun_zero : toFun 0 = ⊥
  toFun_last : toFun (Fin.last r) = ⊤
  covBy : ∀ k : Fin r, toFun k.castSucc ⋖ toFun k.succ

namespace CoveringChain

variable [OrderBot α] [OrderTop α] {r r' : ℕ}

/-- The members of a covering chain increase. -/
theorem monotone (c : CoveringChain α r) : Monotone c.toFun :=
  Fin.monotone_iff_le_succ.mpr fun k ↦ (c.covBy k).le

/-- Some step `k'` of `c'` has `c.toFun (k + 1) ⊓ c'.toFun (k' + 1) ≰ c.toFun k`, namely the last
step, because `c'.toFun r' = ⊤`. -/
theorem exists_not_inf_le (c : CoveringChain α r) (c' : CoveringChain α r') (k : Fin r) :
    ∃ k' : Fin r', ¬ c.toFun k.succ ⊓ c'.toFun k'.succ ≤ c.toFun k.castSucc := by
  have hr' : 0 < r' := by
    rcases Nat.eq_zero_or_pos r' with h | h
    · subst h
      have h0 : c'.toFun (Fin.last 0) = c'.toFun 0 := rfl
      rw [c'.toFun_last, c'.toFun_zero] at h0
      exact absurd ((le_top.trans h0.le).trans bot_le)
        (c.covBy k).lt.not_ge
    · exact h
  refine ⟨⟨r' - 1, by omega⟩, ?_⟩
  have hlast : (⟨r' - 1, by omega⟩ : Fin r').succ = Fin.last r' := by
    ext; simp; omega
  rw [hlast, c'.toFun_last, inf_top_eq]
  exact (c.covBy k).lt.not_ge

open scoped Classical in
/-- The step of `c'` matched with the step `k` of `c` (blueprint `prop:asym_uniq_matching`, *The
matching*), namely the least `k'` with `c.toFun (k + 1) ⊓ c'.toFun (k' + 1) ≰ c.toFun k`. -/
noncomputable def jump (c : CoveringChain α r) (c' : CoveringChain α r') (k : Fin r) : Fin r' :=
  (Finset.univ.filter fun k' : Fin r' ↦
      ¬ c.toFun k.succ ⊓ c'.toFun k'.succ ≤ c.toFun k.castSucc).min'
    (by
      obtain ⟨k', hk'⟩ := exists_not_inf_le c c' k
      exact ⟨k', by simpa using hk'⟩)

/-- The matched step satisfies its defining condition. -/
theorem not_inf_jump_succ_le (c : CoveringChain α r) (c' : CoveringChain α r') (k : Fin r) :
    ¬ c.toFun k.succ ⊓ c'.toFun (jump c c' k).succ ≤ c.toFun k.castSucc := by
  classical
  have := Finset.min'_mem
    (Finset.univ.filter fun k' : Fin r' ↦ ¬ c.toFun k.succ ⊓ c'.toFun k'.succ ≤ c.toFun k.castSucc)
    (by
      obtain ⟨k', hk'⟩ := exists_not_inf_le c c' k
      exact ⟨k', by simpa using hk'⟩)
  simpa [jump] using this

/-- The matched step is the least step satisfying its defining condition. -/
theorem jump_le_of_not_inf_le (c : CoveringChain α r) (c' : CoveringChain α r') (k : Fin r)
    {j : Fin r'} (hj : ¬ c.toFun k.succ ⊓ c'.toFun j.succ ≤ c.toFun k.castSucc) :
    jump c c' k ≤ j := by
  classical
  exact Finset.min'_le _ _ (by simpa using hj)

/-- Below the matched step the defining condition fails: `c.toFun (k + 1) ⊓ c'.toFun k' ≤ c.toFun k`
for `k' = jump c c' k`. -/
theorem inf_jump_castSucc_le (c : CoveringChain α r) (c' : CoveringChain α r') (k : Fin r) :
    c.toFun k.succ ⊓ c'.toFun (jump c c' k).castSucc ≤ c.toFun k.castSucc := by
  set k' := jump c c' k with hk'
  rcases Nat.eq_zero_or_pos k'.val with h0 | hpos
  · have : k'.castSucc = 0 := Fin.ext (by simpa using h0)
    rw [this, c'.toFun_zero, inf_bot_eq]
    exact bot_le
  · by_contra hne
    set j : Fin r' := ⟨k'.val - 1, by omega⟩
    have hj : j.succ = k'.castSucc := by ext; simp [j]; omega
    have hle := jump_le_of_not_inf_le c c' k (j := j) (by rwa [hj])
    rw [← hk'] at hle
    have : k'.val ≤ k'.val - 1 := hle
    omega

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*): the chain
`c.toFun k ⊔ (c.toFun (k + 1) ⊓ c'.toFun j)` increases strictly at the matched step
`j = jump c c' k`. -/
theorem jump_spec (c : CoveringChain α r) (c' : CoveringChain α r') (k : Fin r) :
    c.toFun k.castSucc ⊔ (c.toFun k.succ ⊓ c'.toFun (jump c c' k).castSucc) <
      c.toFun k.castSucc ⊔ (c.toFun k.succ ⊓ c'.toFun (jump c c' k).succ) := by
  rw [sup_eq_left.mpr (inf_jump_castSucc_le c c' k)]
  exact lt_of_le_not_ge le_sup_left fun h ↦ not_inf_jump_succ_le c c' k (le_sup_right.trans h)

/-- The matched step is the only step `j` of `c'` at which the chain
`c.toFun k ⊔ (c.toFun (k + 1) ⊓ c'.toFun j)` increases strictly (blueprint
`prop:asym_uniq_matching`, *The matching*). -/
theorem jump_unique [IsModularLattice α] (c : CoveringChain α r) (c' : CoveringChain α r')
    (k : Fin r) {j : Fin r'}
    (hj : c.toFun k.castSucc ⊔ (c.toFun k.succ ⊓ c'.toFun j.castSucc) <
      c.toFun k.castSucc ⊔ (c.toFun k.succ ⊓ c'.toFun j.succ)) : j = jump c c' k := by
  obtain ⟨hsup, hinf⟩ := step_sup_eq_of_lt (c.covBy k) hj
  have hnot : ¬ c.toFun k.succ ⊓ c'.toFun j.succ ≤ c.toFun k.castSucc := fun hle ↦
    (c.covBy k).ne (by rwa [sup_eq_left.mpr hle] at hsup)
  refine le_antisymm ?_ (jump_le_of_not_inf_le c c' k hnot)
  by_contra hlt
  rw [not_le] at hlt
  refine not_inf_jump_succ_le c c' k ((inf_le_inf_left _ (c'.monotone ?_)).trans hinf)
  rw [Fin.le_def]
  simp only [Fin.val_succ, Fin.val_castSucc]
  exact hlt

/-- The matching rule (blueprint `prop:asym_uniq_matching`, *The matching*) applied with the two
chains exchanged sends the matched step back to `k`. This is the last conclusion of the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*) together with the uniqueness of the
matched step. -/
theorem jump_jump [IsModularLattice α] (c : CoveringChain α r) (c' : CoveringChain α r')
    (k : Fin r) : jump c' c (jump c c' k) = k :=
  (jump_unique c' c _ (step_lt_symm (c.covBy k) (c'.covBy _) (jump_spec c c' k))).symm

/-- The matching of the steps of two covering chains (blueprint `prop:asym_uniq_matching`, *The
matching*), with inverse the matching with the chains exchanged. -/
noncomputable def jumpEquiv [IsModularLattice α] (c : CoveringChain α r)
    (c' : CoveringChain α r') : Fin r ≃ Fin r' where
  toFun := jump c c'
  invFun := jump c' c
  left_inv := jump_jump c c'
  right_inv := jump_jump c' c

/-- The matching is a bijection (blueprint `prop:asym_uniq_matching`, *The matching*). -/
theorem jump_bijective [IsModularLattice α] (c : CoveringChain α r) (c' : CoveringChain α r') :
    Function.Bijective (jump c c') :=
  (jumpEquiv c c').bijective

/-- Two covering chains have the same length (blueprint `prop:asym_uniq_matching`, *The matching*).
-/
theorem length_eq [IsModularLattice α] (c : CoveringChain α r) (c' : CoveringChain α r') :
    r = r' :=
  Fin.equiv_iff_eq.mp ⟨jumpEquiv c c'⟩

/-- The matching (blueprint `prop:asym_uniq_matching`, *The matching*) with the step lemma
(blueprint `lem:asym_uniq_step`, *One step against another*): for the matched steps
`P = c.toFun k ⋖ Q = c.toFun (k + 1)` and `P' = c'.toFun k' ⋖ Q' = c'.toFun (k' + 1)`, with
`U = Q ⊓ Q'` and `K = P ⊓ Q'`, one has `P ⊔ U = Q`, `P' ⊔ U = Q'`, `U ⊓ P = K`, `U ⊓ P' = K` and
`K = Q ⊓ P'`. -/
theorem jump_sup_eq [IsModularLattice α] (c : CoveringChain α r) (c' : CoveringChain α r')
    (k : Fin r) :
    c.toFun k.castSucc ⊔ (c.toFun k.succ ⊓ c'.toFun (jump c c' k).succ) = c.toFun k.succ ∧
      c'.toFun (jump c c' k).castSucc ⊔ (c.toFun k.succ ⊓ c'.toFun (jump c c' k).succ) =
        c'.toFun (jump c c' k).succ ∧
      c.toFun k.succ ⊓ c'.toFun (jump c c' k).succ ⊓ c.toFun k.castSucc =
        c.toFun k.castSucc ⊓ c'.toFun (jump c c' k).succ ∧
      c.toFun k.succ ⊓ c'.toFun (jump c c' k).succ ⊓ c'.toFun (jump c c' k).castSucc =
        c.toFun k.castSucc ⊓ c'.toFun (jump c c' k).succ ∧
      c.toFun k.castSucc ⊓ c'.toFun (jump c c' k).succ =
        c.toFun k.succ ⊓ c'.toFun (jump c c' k).castSucc := by
  set P := c.toFun k.castSucc
  set Q := c.toFun k.succ
  set P' := c'.toFun (jump c c' k).castSucc
  set Q' := c'.toFun (jump c c' k).succ
  have hPQ : P ⋖ Q := c.covBy k
  have hPQ' : P' ⋖ Q' := c'.covBy _
  have h : P ⊔ (Q ⊓ P') < P ⊔ (Q ⊓ Q') := jump_spec c c' k
  have hK := step_inf_eq_of_lt hPQ hPQ' h
  refine ⟨(step_sup_eq_of_lt hPQ h).1, (step_sup_eq_of_lt' hPQ hPQ' h).1, ?_, ?_, hK⟩
  · rw [inf_right_comm, inf_eq_right.mpr hPQ.le, inf_comm]
  · rw [inf_assoc, inf_eq_right.mpr hPQ'.le, ← hK]

end CoveringChain

end CoveringMatching
