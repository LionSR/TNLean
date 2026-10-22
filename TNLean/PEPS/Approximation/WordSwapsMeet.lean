/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameBoundedChanges

/-!
# Exchanges of tensor factors that move a selected register

A monomial that uses only selected parties may still exchange two registers of unselected
parties, which acts nontrivially on their memory. The condition `Word.SwapsMeet f`,
`PartyChain.SwapsMeet f` asks that every exchange of tensor factors move a register of a party
selected by `f`. This file defines it and checks it for the reordering words that place a
monomial on the registers of an encoded frame: moving registers to the front past others
(`Word.moveHead`, `Word.exchangeBlocks`), partitioning the raw registers of a list of sites
(`partWord`, `unpartWord`), renaming owners (`relabelSites`), and grouping the raw registers of
two regions at their owners (`Sheet.groupWord`, `Sheet.ungroupWord`). Every
exchange in these words moves a register of a party whose registers are being moved, so the
condition holds as soon as the selection contains the owners of the moved registers.

## Main definitions

* `PartyCircuit.Word.SwapsMeet`, `PartyCircuit.PartyChain.SwapsMeet`,
  `PartyCircuit.PartyChain.SwapsMeetSet`.

## Main results

* `PartyCircuit.Word.SwapsMeet.mono`: enlarging the selection keeps the condition.
* `EncodedFrame.swapsMeet_groupWord`, `EncodedFrame.swapsMeet_ungroupWord`,
  `EncodedFrame.swapsMeet_relabelRest`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
  lines 21–43; the gates of Proposition 7.1, `06-geometry.tex`, lines 574–583.
-/

noncomputable section

namespace TNLean
open TNLean.Lattice.PartyCircuit

variable {P : Type}

namespace Lattice.PartyCircuit.Word

/-- Every exchange of tensor factors in the word moves a register of a selected party. -/
def SwapsMeet (f : P → Bool) : {ℓ ℓ' : Layout P} → Word ℓ ℓ' → Prop
  | _, _, id _ => True
  | _, _, comp w w' => w.SwapsMeet f ∧ w'.SwapsMeet f
  | _, _, localMap .. => True
  | _, _, source .. => True
  | _, _, swap r r' _ => f r.owner = true ∨ f r'.owner = true
  | _, _, frame _ w => w.SwapsMeet f

/-- Enlarging the selection keeps the condition. -/
theorem SwapsMeet.mono {f g : P → Bool} (hfg : ∀ p, f p = true → g p = true)
    {ℓ ℓ' : Layout P} {w : Word ℓ ℓ'} (hw : w.SwapsMeet f) : w.SwapsMeet g := by
  induction w with
  | id => trivial
  | comp _ _ ih ih' => exact ⟨ih hw.1, ih' hw.2⟩
  | localMap => trivial
  | source => trivial
  | swap => exact hw.imp (hfg _) (hfg _)
  | frame _ _ ih => exact ih hw

theorem swapsMeet_frameList (f : P → Bool) {ℓ ℓ' : Layout P} {w : Word ℓ ℓ'}
    (hw : w.SwapsMeet f) : (ℓ₀ : Layout P) → (frameList ℓ₀ w).SwapsMeet f
  | [] => hw
  | _ :: ℓ₀ => swapsMeet_frameList f hw ℓ₀

/-- Moving a register past selected registers meets the selection at every exchange. -/
theorem swapsMeet_moveHead (f : P → Bool) (r : Reg P) :
    (ℓ₀ tail : Layout P) → (∀ t ∈ ℓ₀, f t.owner = true) → (moveHead r ℓ₀ tail).SwapsMeet f
  | [], _, _ => trivial
  | t :: ℓ₀, tail, h =>
      ⟨swapsMeet_moveHead f r ℓ₀ tail fun t' ht' => h t' (List.mem_cons_of_mem _ ht'),
        Or.inl (h t List.mem_cons_self)⟩

/-- Moving a selected register meets the selection at every exchange. -/
theorem swapsMeet_moveHead_of_owner (f : P → Bool) {r : Reg P} (hr : f r.owner = true) :
    (ℓ₀ tail : Layout P) → (moveHead r ℓ₀ tail).SwapsMeet f
  | [], _ => trivial
  | _ :: ℓ₀, tail => ⟨swapsMeet_moveHead_of_owner f hr ℓ₀ tail, Or.inr hr⟩

/-- Exchanging two lists of registers, the first of them selected. -/
theorem swapsMeet_exchangeBlocks_of_left (f : P → Bool) {a : Layout P}
    (ha : ∀ t ∈ a, f t.owner = true) : (b tail : Layout P) → (exchangeBlocks a b tail).SwapsMeet f
  | [], _ => trivial
  | r :: b, tail =>
      ⟨swapsMeet_moveHead f r a _ ha, swapsMeet_exchangeBlocks_of_left f ha b tail⟩

/-- Exchanging two lists of registers, the second of them selected. -/
theorem swapsMeet_exchangeBlocks_of_right (f : P → Bool) (a : Layout P) :
    (b tail : Layout P) → (∀ t ∈ b, f t.owner = true) → (exchangeBlocks a b tail).SwapsMeet f
  | [], _, _ => trivial
  | r :: b, tail, hb =>
      ⟨swapsMeet_moveHead_of_owner f (hb r List.mem_cons_self) a _,
        swapsMeet_exchangeBlocks_of_right f a b tail fun t ht => hb t (List.mem_cons_of_mem _ ht)⟩

theorem swapsMeet_appendNil (f : P → Bool) : (ℓ : Layout P) → (appendNil ℓ).SwapsMeet f
  | [] => trivial
  | _ :: ℓ => swapsMeet_appendNil f ℓ

theorem swapsMeet_dropNil (f : P → Bool) : (ℓ : Layout P) → (dropNil ℓ).SwapsMeet f
  | [] => trivial
  | _ :: ℓ => swapsMeet_dropNil f ℓ

end Lattice.PartyCircuit.Word

namespace Lattice.PartyCircuit.PartyChain

/-- Every exchange of tensor factors in the monomial moves a register of a selected party. -/
def SwapsMeet (f : P → Bool) : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Prop
  | _, _, final w => w.SwapsMeet f
  | _, _, effect _ _ _ _ w _ rest => w.SwapsMeet f ∧ rest.SwapsMeet f

/-- Every exchange of tensor factors in the monomial moves a register of a party of `S`, read
for every Boolean selection containing `S`. -/
def SwapsMeetSet (S : Set P) {ℓX ℓY : Layout P} (M : PartyChain ℓX ℓY) : Prop :=
  ∀ f : P → Bool, (∀ p ∈ S, f p = true) → M.SwapsMeet f

theorem swapsMeet_precomp (f : P → Bool) {ℓ₀ ℓX ℓY : Layout P} {w : Word ℓ₀ ℓX}
    (hw : w.SwapsMeet f) : {M : PartyChain ℓX ℓY} → M.SwapsMeet f → (M.precomp w).SwapsMeet f
  | final _, hM => ⟨hw, hM⟩
  | effect .., hM => ⟨⟨hw, hM.1⟩, hM.2⟩

theorem swapsMeet_postcomp (f : P → Bool) {ℓX ℓY ℓZ : Layout P} {w : Word ℓY ℓZ}
    (hw : w.SwapsMeet f) : {M : PartyChain ℓX ℓY} → M.SwapsMeet f → (M.postcomp w).SwapsMeet f
  | final _, hM => ⟨hM, hw⟩
  | effect _ _ _ _ _ _ rest, hM => ⟨hM.1, swapsMeet_postcomp f hw (M := rest) hM.2⟩

end Lattice.PartyCircuit.PartyChain

end TNLean

namespace TNLean.PEPS.EncodedFrame
open TNLean.Lattice.Sheet

open TNLean.Lattice.PartyCircuit

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### Words on the raw registers of a list of sites -/

section Sites

variable (f : Party → Bool) (own : ι → Party)

theorem swapsMeet_relabelHead {p p' : Party} (h : p = p') (X : HSpace) (ℓ : Layout Party) :
    (relabelHead h X ℓ).SwapsMeet f := by
  subst h
  trivial

theorem swapsMeet_relabelSitesApp (own' : ι → Party) (tail : Layout Party) :
    (S : List ι) → (h : ∀ x ∈ S, own x = own' x) →
      (relabelSitesApp (q := q) own own' tail S h).SwapsMeet f
  | [], _ => trivial
  | _ :: S, _ => ⟨swapsMeet_relabelSitesApp own' tail S _, swapsMeet_relabelHead f _ _ _⟩

theorem swapsMeet_relabelSites (own' : ι → Party) (S : List ι) (h : ∀ x ∈ S, own x = own' x) :
    (relabelSites (q := q) own own' S h).SwapsMeet f :=
  ⟨Word.swapsMeet_appendNil f _, swapsMeet_relabelSitesApp f own own' [] S h,
    Word.swapsMeet_dropNil f _⟩

theorem swapsMeet_partStepApp (x : ι) (a b : List ι) (tail : Layout Party)
    (ha : ∀ y ∈ a, f (own y) = true) :
    (c : Bool) → (partStepApp (q := q) own x a b tail c).SwapsMeet f
  | true => trivial
  | false => Word.swapsMeet_exchangeBlocks_of_right f _ _ _ fun r hr => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
      exact ha y hy

theorem swapsMeet_unpartStepApp (x : ι) (a b : List ι) (tail : Layout Party)
    (ha : ∀ y ∈ a, f (own y) = true) :
    (c : Bool) → (unpartStepApp (q := q) own x a b tail c).SwapsMeet f
  | true => trivial
  | false => Word.swapsMeet_moveHead f _ _ _ fun r hr => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
      exact ha y hy

variable {p : ι → Bool} (hp : ∀ x, p x = true → f (own x) = true)
include hp

theorem swapsMeet_partWordApp (tail : Layout Party) :
    (S : List ι) → (partWordApp (q := q) own p tail S).SwapsMeet f
  | [] => trivial
  | x :: S => ⟨swapsMeet_partWordApp tail S, swapsMeet_partStepApp f own x _ _ tail
      (fun y hy => hp y ((mem_partSites_fst p S y).mp hy).2) (p x)⟩

theorem swapsMeet_unpartWordApp (tail : Layout Party) :
    (S : List ι) → (unpartWordApp (q := q) own p tail S).SwapsMeet f
  | [] => trivial
  | x :: S => ⟨swapsMeet_unpartStepApp f own x _ _ tail
      (fun y hy => hp y ((mem_partSites_fst p S y).mp hy).2) (p x),
      swapsMeet_unpartWordApp tail S⟩

theorem swapsMeet_partWord (S : List ι) : (partWord (q := q) own p S).SwapsMeet f :=
  ⟨Word.swapsMeet_appendNil f _, swapsMeet_partWordApp f own hp [] S,
    Word.swapsMeet_frameList f (Word.swapsMeet_dropNil f _) _⟩

theorem swapsMeet_unpartWord (S : List ι) : (unpartWord (q := q) own p S).SwapsMeet f :=
  ⟨Word.swapsMeet_frameList f (Word.swapsMeet_appendNil f _) _,
    swapsMeet_unpartWordApp f own hp [] S, Word.swapsMeet_dropNil f _⟩

end Sites

/-! ### Grouping the raw registers of two regions -/

section Group

variable [Fintype ι] [DecidableEq ι] {S : List ι} {T E : Finset ι} (f : Party → Bool)

omit [Fintype ι] in
private theorem owner_listT_selected {own : ι → Party} {pA : Party} (hA : ∀ x ∈ T, own x = pA)
    (hf : f pA = true) : ∀ r ∈ siteRegs q own (listT S T), f r.owner = true := by
  intro r hr
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
  rw [hA y (by simpa using ((mem_partSites_fst _ S y).mp hy).2)]
  exact hf

private theorem owner_listU_selected {own : ι → Party} {pB : Party}
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) (hf : f pB = true) :
    ∀ r ∈ siteRegs q own (listU S T E), f r.owner = true := by
  intro r hr
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
  rw [hB y (by simpa using ((mem_partSites_fst _ _ y).mp hy).2)]
  exact hf

/-- Grouping two regions moves, at every exchange of tensor factors, a register of one of the two
owners `p_A`, `p_B`. -/
theorem swapsMeet_groupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) (hfA : f pA = true) (hfB : f pB = true) :
    (groupWord (q := q) own hS hall ℓ₀ hA hB).SwapsMeet f :=
  ⟨Word.swapsMeet_frameList f (swapsMeet_partWord f own (fun x hx => by
      rw [hA x (by simpa using hx)]; exact hfA) S) _,
    Word.swapsMeet_frameList f (Word.swapsMeet_frameList f (swapsMeet_partWord f own
      (fun x hx => by rw [hB x (by simpa using hx)]; exact hfB) _) _) _,
    Word.swapsMeet_exchangeBlocks_of_right f _ _ _ (owner_listT_selected f hA hfA), trivial,
    Word.swapsMeet_exchangeBlocks_of_right f _ _ _ (owner_listU_selected f hB hfB), trivial⟩

/-- Ungrouping two regions moves, at every exchange of tensor factors, a register of one of the
two owners `p_A`, `p_B`. -/
theorem swapsMeet_ungroupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) (hfA : f pA = true) (hfB : f pB = true) :
    (ungroupWord (q := q) own hS hall ℓ₀ hA hB).SwapsMeet f :=
  ⟨trivial, Word.swapsMeet_exchangeBlocks_of_left f (owner_listU_selected f hB hfB) _ _, trivial,
    Word.swapsMeet_exchangeBlocks_of_left f (owner_listT_selected f hA hfA) _ _,
    Word.swapsMeet_frameList f (Word.swapsMeet_frameList f (swapsMeet_unpartWord f own
      (fun x hx => by rw [hB x (by simpa using hx)]; exact hfB) _) _) _,
    Word.swapsMeet_frameList f (swapsMeet_unpartWord f own (fun x hx => by
      rw [hA x (by simpa using hx)]; exact hfA) S) _⟩

/-- Renaming the owners of the untouched raw registers exchanges no tensor factors. -/
theorem swapsMeet_relabelRest (own own' : ι → Party) (hall : ∀ x, x ∈ S) (h : Disjoint T E)
    (hE : ∀ x ∈ E, own x = own' x) (ℓ₀ : Layout Party) (rA rB : Reg Party) :
    (relabelRest (q := q) own own' hall h hE ℓ₀ rA rB).SwapsMeet f :=
  Word.swapsMeet_frameList f (swapsMeet_relabelSites f own own' _ _) ℓ₀

end Group

end TNLean.PEPS.EncodedFrame
