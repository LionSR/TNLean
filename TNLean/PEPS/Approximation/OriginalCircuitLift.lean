/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SiteRegisters
import TNLean.PEPS.Approximation.WordAppendTail
import TNLean.PEPS.Approximation.WordOriginalCircuit

/-!
# Original circuits beside spectator registers

An original circuit acting on some registers also acts on a larger memory in which these
registers sit between untouched spectator registers: frame it by the spectators in front
(`OriginalCircuit.frameList`) and place it before the spectators behind
(`OriginalCircuit.appendTail`, which moves the spectators to the front by exchanges of tensor
factors and back). The operator is the original operator tensored with the spectator identities,
and the nonprivate gates, their participants and their expansions are unchanged: the inserted
exchanges contain no gate.

In the protocol of Proposition 7.1 the memory holds several sheets, and a bounded change acts on
the registers of one or two of them; the other sheets are spectators (`06-geometry.tex`,
lines 658–667).

## Main definitions

* `PairEffect.OriginalCircuit.castLayouts`, `PairEffect.OriginalCircuit.frameList`,
  `PairEffect.OriginalCircuit.appendTail`.

## Main results

* `PairEffect.OriginalCircuit.eval_frameList_appendIso_symm`,
  `PairEffect.OriginalCircuit.eval_appendTail_appendIso_symm` : the operators beside
  spectators.
* `nonprivateCount_*`, `participants_*_subset`, `isExpansionBounded_*`, `isMonomialBounded_*` :
  the gate data are unchanged.

## References

* Polynomial-PEPS manuscript (September 24, 2026), original circuits, `04-compression.tex`,
  lines 21–43 and 199–208; the sheets of Proposition 7.1, `06-geometry.tex`, lines 658–667.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

namespace Word

/-- A reordering word contains no nonprivate gate. -/
theorem nonprivateCount_toOriginalCircuit_of_isReordering {a b : Layout P} {w : Word a b}
    (hw : w.IsReordering) : (w.toOriginalCircuit hw.isAllowed).nonprivateCount = 0 := by
  rw [nonprivateCount_toOriginalCircuit, hw.sourceCount_eq]

/-- A word without pair sources gives original circuits with arbitrary expansion bounds. -/
theorem isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero {a b : Layout P}
    (w : Word a b) (hw : w.IsAllowed) (h0 : w.sourceCount = 0) (r : ℕ) (s : ℝ) :
    (w.toOriginalCircuit hw).IsExpansionBounded r s := by
  induction w with
  | id => trivial
  | comp w w' ih ih' =>
      simp only [sourceCount, Nat.add_eq_zero_iff] at h0
      exact ⟨ih hw.1 h0.1, ih' hw.2 h0.2⟩
  | localMap => trivial
  | source => exact absurd h0 one_ne_zero
  | swap => trivial
  | frame r w ih => exact ih hw h0

/-- A word without pair sources gives original circuits with arbitrary monomial bounds. -/
theorem isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero {a b : Layout P}
    (w : Word a b) (hw : w.IsAllowed) (h0 : w.sourceCount = 0) (K : ℕ) :
    (w.toOriginalCircuit hw).IsMonomialBounded K := by
  induction w with
  | id => trivial
  | comp w w' ih ih' =>
      simp only [sourceCount, Nat.add_eq_zero_iff] at h0
      exact ⟨ih hw.1 h0.1, ih' hw.2 h0.2⟩
  | localMap => trivial
  | source => exact absurd h0 one_ne_zero
  | swap => trivial
  | frame r w ih => exact ih hw h0

theorem isReordering_castLayouts {ℓ ℓ' a b : Layout P} {w : Word ℓ ℓ'} (hw : w.IsReordering)
    (h : ℓ = a) (h' : ℓ' = b) : (w.castLayouts h h').IsReordering := by
  cases h
  cases h'
  exact hw

theorem isReordering_exchangeTwo (a b : Layout P) : (exchangeTwo a b).IsReordering :=
  isReordering_castLayouts (isReordering_exchangeBlocks a b []) _ _

end Word

namespace OriginalCircuit

/-! ### Identifying equal layouts -/

/-- Identify equal input and output layouts without adding an operation. -/
def castLayouts {a b a' b' : Layout P} (c : OriginalCircuit a b) (ha : a = a') (hb : b = b') :
    OriginalCircuit a' b' :=
  ha ▸ hb ▸ c

/-- Every layout-dependent circuit proposition is preserved by identifying
its input and output layouts with equal layouts. This is the elimination
principle for `castLayouts`.

Source: polynomial-PEPS manuscript, original circuits, `04-compression.tex`,
lines 21–43 and 199–208. -/
theorem castLayouts_rec {a b a' b' : Layout P}
    (c : OriginalCircuit a b) (ha : a = a') (hb : b = b')
    {motive : {x y : Layout P} → OriginalCircuit x y → Prop}
    (h : motive c) : motive (c.castLayouts ha hb) :=
  match ha, hb with
  | rfl, rfl => h

theorem eval_castLayouts {a b a' b' : Layout P} (c : OriginalCircuit a b) (ha : a = a')
    (hb : b = b') :
    (c.castLayouts ha hb).eval =
      isoL (Layout.memCongr hb) ∘L c.eval ∘L isoL (Layout.memCongr ha).symm := by
  cases ha
  cases hb
  rfl

@[simp] theorem nonprivateCount_castLayouts {a b a' b' : Layout P} (c : OriginalCircuit a b)
    (ha : a = a') (hb : b = b') : (c.castLayouts ha hb).nonprivateCount = c.nonprivateCount :=
  castLayouts_rec c ha hb (motive := fun w ↦ w.nonprivateCount = c.nonprivateCount) rfl

theorem participants_castLayouts_subset {S : Set P} {a b a' b' : Layout P}
    (c : OriginalCircuit a b) (ha : a = a') (hb : b = b')
    (hc : ∀ g, (↑(c.participants g) : Set P) ⊆ S) (g : (c.castLayouts ha hb).nonprivateLocations) :
    (↑((c.castLayouts ha hb).participants g) : Set P) ⊆ S :=
  (castLayouts_rec c ha hb
    (motive := fun w ↦ ∀ g, (↑(w.participants g) : Set P) ⊆ S) hc) g

theorem isExpansionBounded_castLayouts {a b a' b' : Layout P} (c : OriginalCircuit a b)
    (ha : a = a') (hb : b = b') {r : ℕ} {s : ℝ} (hc : c.IsExpansionBounded r s) :
    (c.castLayouts ha hb).IsExpansionBounded r s :=
  castLayouts_rec c ha hb (motive := fun w ↦ w.IsExpansionBounded r s) hc

theorem isMonomialBounded_castLayouts {a b a' b' : Layout P} (c : OriginalCircuit a b)
    (ha : a = a') (hb : b = b') {K : ℕ} (hc : c.IsMonomialBounded K) :
    (c.castLayouts ha hb).IsMonomialBounded K :=
  castLayouts_rec c ha hb (motive := fun w ↦ w.IsMonomialBounded K) hc

/-! ### Spectators in front -/

/-- A circuit framed by a list of untouched registers in front. -/
def frameList {a b : Layout P} : (rs : Layout P) → OriginalCircuit a b →
    OriginalCircuit (rs ++ a) (rs ++ b)
  | [], c => c
  | r :: rs, c => .frame r (frameList rs c)

/-- Framing by a list acts on the second factor of the concatenated memory. -/
theorem eval_frameList_appendIso_symm {a b : Layout P} (c : OriginalCircuit a b) :
    (rs : Layout P) → (x : Mem rs) → (y : Mem a) →
      (frameList rs c).eval ((appendIso rs a).symm (x ⊗ₜ y)) =
        (appendIso rs b).symm (x ⊗ₜ c.eval y)
  | [], x, y => map_smul c.eval x y
  | r :: rs, x, y => by
      induction x using TensorProduct.inductionOn with
      | tmul u v => exact congrArg (fun z ↦ u ⊗ₜ z) (eval_frameList_appendIso_symm c rs v y)
      | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]

@[simp] theorem nonprivateCount_frameList {a b : Layout P} (c : OriginalCircuit a b) :
    (rs : Layout P) → (frameList rs c).nonprivateCount = c.nonprivateCount
  | [] => rfl
  | _ :: rs => nonprivateCount_frameList c rs

theorem participants_frameList_subset {S : Set P} {a b : Layout P} (c : OriginalCircuit a b)
    (hc : ∀ g, (↑(c.participants g) : Set P) ⊆ S) :
    (rs : Layout P) → (g : (frameList rs c).nonprivateLocations) →
      (↑((frameList rs c).participants g) : Set P) ⊆ S
  | [], g => hc g
  | _ :: rs, g => participants_frameList_subset c hc rs g

theorem isExpansionBounded_frameList {a b : Layout P} (c : OriginalCircuit a b) {r : ℕ} {s : ℝ}
    (hc : c.IsExpansionBounded r s) :
    (rs : Layout P) → (frameList rs c).IsExpansionBounded r s
  | [] => hc
  | _ :: rs => isExpansionBounded_frameList c hc rs

theorem isMonomialBounded_frameList {a b : Layout P} (c : OriginalCircuit a b) {K : ℕ}
    (hc : c.IsMonomialBounded K) : (rs : Layout P) → (frameList rs c).IsMonomialBounded K
  | [] => hc
  | _ :: rs => isMonomialBounded_frameList c hc rs

/-! ### Spectators behind -/

/-- A circuit placed before untouched registers: exchange the spectators to the front, apply
the framed circuit, and exchange them back. -/
def appendTail {a b : Layout P} (c : OriginalCircuit a b) (t : Layout P) :
    OriginalCircuit (a ++ t) (b ++ t) :=
  .comp ((Word.exchangeTwo a t).toOriginalCircuit (Word.isReordering_exchangeTwo a t).isAllowed)
    (.comp (frameList t c)
      ((Word.exchangeTwo t b).toOriginalCircuit (Word.isReordering_exchangeTwo t b).isAllowed))

/-- A circuit before spectators acts on the first factor of the concatenated memory. -/
theorem eval_appendTail_appendIso_symm {a b : Layout P} (c : OriginalCircuit a b)
    (t : Layout P) (x : Mem a) (y : Mem t) :
    (c.appendTail t).eval ((appendIso a t).symm (x ⊗ₜ y)) =
      (appendIso b t).symm (c.eval x ⊗ₜ y) := by
  simp only [appendTail, eval, comp_apply, Word.eval_toOriginalCircuit, Word.eval_exchangeTwo,
    eval_frameList_appendIso_symm]

@[simp] theorem nonprivateCount_appendTail {a b : Layout P} (c : OriginalCircuit a b)
    (t : Layout P) : (c.appendTail t).nonprivateCount = c.nonprivateCount := by
  simp only [appendTail, nonprivateCount, nonprivateCount_frameList,
    Word.nonprivateCount_toOriginalCircuit_of_isReordering (Word.isReordering_exchangeTwo _ _),
    zero_add, add_zero]

theorem participants_appendTail_subset {S : Set P} {a b : Layout P} (c : OriginalCircuit a b)
    (t : Layout P) (hc : ∀ g, (↑(c.participants g) : Set P) ⊆ S)
    (g : (c.appendTail t).nonprivateLocations) :
    (↑((c.appendTail t).participants g) : Set P) ⊆ S := by
  rcases g with g | g | g
  · exact Word.participants_toOriginalCircuit_subset _ _
      ((Word.isReordering_exchangeTwo a t).usesOnly S) g
  · exact participants_frameList_subset c hc t g
  · exact Word.participants_toOriginalCircuit_subset _ _
      ((Word.isReordering_exchangeTwo t b).usesOnly S) g

theorem isExpansionBounded_appendTail {a b : Layout P} (c : OriginalCircuit a b) (t : Layout P)
    {r : ℕ} {s : ℝ} (hc : c.IsExpansionBounded r s) : (c.appendTail t).IsExpansionBounded r s :=
  ⟨Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      (Word.isReordering_exchangeTwo a t).sourceCount_eq r s,
    isExpansionBounded_frameList c hc t,
    Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      (Word.isReordering_exchangeTwo t b).sourceCount_eq r s⟩

theorem isMonomialBounded_appendTail {a b : Layout P} (c : OriginalCircuit a b) (t : Layout P)
    {K : ℕ} (hc : c.IsMonomialBounded K) : (c.appendTail t).IsMonomialBounded K :=
  ⟨Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      (Word.isReordering_exchangeTwo a t).sourceCount_eq K,
    isMonomialBounded_frameList c hc t,
    Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      (Word.isReordering_exchangeTwo t b).sourceCount_eq K⟩

end OriginalCircuit

end TNLean.PEPS.PairEffect
