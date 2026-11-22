/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TensorProduct.TensorProductRegrouping
import TNLean.Lattice.PartyCircuit.PairEffectElimination

/-!
# Circuits between layouts, for an arbitrary family of gates

A *layout* is a list of registers, each with an owner party and a Hilbert space; its memory
is the tensor product of the registers.  A *circuit* from a layout to a layout is a
composition of local maps on the registers of one party, gates of a prescribed family,
exchanges of adjacent tensor factors, and operations framed by untouched registers.  The
party calculus uses four families of gates: pair sources (`Word`), nonprivate gates with their
side conditions (`OriginalCircuit`), nonprivate gates (`EffectCircuit`) and source-prepared
gates (`SourceCircuit`).  Each of the four is `Circuit κ G` for its own `κ` and `G`.

## Design

* The gate family is `G : Layout P → Layout P → Type 1`, indexed by the input and the output
  layout.  The index carries the shape of each gate: a pair source goes from `ℓ` to two fresh
  registers in front of `ℓ`, the other three families replace `mapOwner owner a ++ tail` by
  `mapOwner owner b ++ tail`.  The syntax has one constructor `gate` for all of them.
* The operator of a gate, the condition under which it is a contraction, and its
  participating parties are the fields of the class `GateFamily G`.
* The local maps of a circuit satisfy a condition `κ : LocalCondition P` recorded in the
  syntax.  It is `LocalCondition.any` for `Word`, `EffectCircuit` and `SourceCircuit`, whose
  contraction hypothesis is the predicate `Circuit.IsAllowed`, and `LocalCondition.contraction`
  for `OriginalCircuit`, whose theorems quantify over all circuits with no side hypothesis.
  The condition is the last argument of `localMap` and is filled by `trivial` when it is
  `LocalCondition.any`.
* Registers have types in `Type`, so layouts and circuits live in `Type 1`.
* Each of the four types keeps its constructor names as match patterns (`Word.source`,
  `OriginalCircuit.privateMap`, `OriginalCircuit.nonprivateGate`, ...), typed `frameList` and
  `castLayouts`, and an induction eliminator whose cases are its own constructors, so that its
  consumers pattern-match and induct as on a separate inductive type.  These constructor
  names, `frameList` and `castLayouts` are the specializations of the shared ones to the type's
  local condition and gate family, written with those two arguments named; every fact about
  them is a fact about `Circuit`, obtained by unfolding.

## Main definitions

* `PartyCircuit.Reg`, `PartyCircuit.Layout`, `PartyCircuit.Mem` : registers with owners,
  layouts and their memory spaces.
* `PartyCircuit.GateFamily`, `PartyCircuit.LocalCondition`, `PartyCircuit.Circuit` : the
  syntax.
* `PartyCircuit.Circuit.eval`, `PartyCircuit.Circuit.IsAllowed` : the operator of a circuit and
  the contraction condition.
* `PartyCircuit.Circuit.frameList`, `PartyCircuit.Circuit.castLayouts` : spectators in front
  and identification of equal layouts.
* `PartyCircuit.Circuit.gateCount`, `PartyCircuit.Circuit.gateLocations`,
  `PartyCircuit.Circuit.participants` : the gate occurrences and their participating parties.

## Main results

* `PartyCircuit.Circuit.norm_eval_le_one` : an allowed circuit is a contraction.
* `PartyCircuit.Circuit.eval_frameList_appendIso_symm` : framing acts on the second factor.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1, `04-compression.tex`, lines 21–36.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.Lattice.PartyCircuit

open EuclideanSpace CyclicInsertion ContinuousLinearMap

/-! ### Registers, layouts and memory spaces -/

/-- A register: an owner party and a Hilbert space.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 23–25: a party is
a label for a collection of registers, and the memory is the tensor product of the parties'
spaces. -/
structure Reg (P : Type) : Type 1 where
  /-- The party owning the register. -/
  owner : P
  /-- The Hilbert space of the register. -/
  space : HSpace

/-- A layout: a list of registers.  The order only fixes the order of the tensor factors. -/
abbrev Layout (P : Type) : Type 1 := List (Reg P)

variable {P : Type}

/-- The memory space of a layout: the tensor product of its registers. -/
@[reducible] def Mem : Layout P → HSpace
  | [] => HSpace.of ℂ
  | r :: ℓ => HSpace.of (r.space ⊗[ℂ] Mem ℓ)

/-- The Euclidean space `ℂ^α` as a register space. -/
abbrev euc (α : Type) [Fintype α] : HSpace := HSpace.of (EuclideanSpace ℂ α)

/-- The memory of a concatenation is the tensor product of the memories. -/
def appendIso : (ℓ₁ ℓ : Layout P) → Mem (ℓ₁ ++ ℓ) ≃ₗᵢ[ℂ] Mem ℓ₁ ⊗[ℂ] Mem ℓ
  | [], ℓ => (TensorProduct.lidIsometry ℂ (Mem ℓ)).symm
  | r :: ℓ₁, ℓ => ((appendIso ℓ₁ ℓ).lTensor r.space).trans
      (TensorProduct.assocIsometry ℂ r.space (Mem ℓ₁) (Mem ℓ)).symm

/-! ### Gate families and circuits -/

/-- A condition on local maps that is recorded in the syntax of circuits. -/
abbrev LocalCondition (P : Type) : Type 1 :=
  ∀ ⦃a b : Layout P⦄, (Mem a →L[ℂ] Mem b) → Prop

namespace LocalCondition

/-- No condition: every local map is admitted. -/
abbrev any : LocalCondition P := fun _ _ _ => True

/-- The local maps are contractions. -/
abbrev contraction : LocalCondition P := fun _ _ U => ‖U‖ ≤ 1

end LocalCondition

/-- A family of gates between layouts: the operator of a gate, the condition under which the
gate is allowed, which makes it a contraction, and the parties taking part in it.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 25–35. -/
class GateFamily (G : Layout P → Layout P → Type 1) where
  /-- The operator of a gate. -/
  eval : {a b : Layout P} → G a b → (Mem a →L[ℂ] Mem b)
  /-- The condition under which a gate is allowed. -/
  IsAllowed : {a b : Layout P} → G a b → Prop
  /-- An allowed gate is a contraction. -/
  norm_eval_le_one : ∀ {a b : Layout P} (g : G a b), IsAllowed g → ‖eval g‖ ≤ 1
  /-- The parties taking part in a gate. -/
  participants : {a b : Layout P} → G a b → Finset P

/-- A circuit from the layout `ℓ` to the layout `ℓ'`, with gates of the family `G` and local
maps satisfying `κ`.

* `id`, `comp` : the empty circuit and composition.
* `localMap p h₁ h₂ U ℓ` : a local map `U` from registers `ℓ₁` of the party `p` to registers
  `ℓ₂` of `p`, next to the untouched registers `ℓ`.
* `gate g` : a gate of the family.
* `swap r r' ℓ` : exchange of two adjacent tensor factors.
* `frame r w` : the circuit `w` next to the untouched register `r`.

`swap` and `frame` only reorder or skip tensor factors; the memory is the tensor product of
the parties' spaces, in which the order of factors carries no information.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–36. -/
inductive Circuit (κ : LocalCondition P) (G : Layout P → Layout P → Type 1) :
    Layout P → Layout P → Type 1
  | id (ℓ : Layout P) : Circuit κ G ℓ ℓ
  | comp {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : Circuit κ G ℓ₁ ℓ₂) (w' : Circuit κ G ℓ₂ ℓ₃) :
      Circuit κ G ℓ₁ ℓ₃
  | localMap (p : P) {ℓ₁ ℓ₂ : Layout P} (h₁ : ∀ r ∈ ℓ₁, r.owner = p)
      (h₂ : ∀ r ∈ ℓ₂, r.owner = p) (U : Mem ℓ₁ →L[ℂ] Mem ℓ₂) (ℓ : Layout P)
      (hU : κ U := by trivial) : Circuit κ G (ℓ₁ ++ ℓ) (ℓ₂ ++ ℓ)
  | gate {ℓ ℓ' : Layout P} (g : G ℓ ℓ') : Circuit κ G ℓ ℓ'
  | swap (r r' : Reg P) (ℓ : Layout P) : Circuit κ G (r :: r' :: ℓ) (r' :: r :: ℓ)
  | frame (r : Reg P) {ℓ ℓ' : Layout P} (w : Circuit κ G ℓ ℓ') : Circuit κ G (r :: ℓ) (r :: ℓ')

namespace Circuit

variable {κ : LocalCondition P} {G : Layout P → Layout P → Type 1}

section Eval

variable [GateFamily G]

/-- The operator of a circuit. -/
def eval : {ℓ ℓ' : Layout P} → Circuit κ G ℓ ℓ' → (Mem ℓ →L[ℂ] Mem ℓ')
  | _, _, id _ => ContinuousLinearMap.id ℂ _
  | _, _, comp w w' => w'.eval ∘L w.eval
  | _, _, @localMap _ _ _ _ ℓ₁ ℓ₂ _ _ U ℓ _ =>
      isoL (appendIso ℓ₂ ℓ).symm ∘L U.rTensor (Mem ℓ) ∘L isoL (appendIso ℓ₁ ℓ)
  | _, _, gate g => GateFamily.eval g
  | _, _, swap r r' ℓ => leftCommL r.space r'.space (Mem ℓ)
  | _, _, frame r w => w.eval.lTensor r.space

/-- A circuit is allowed when its local maps are contractions and its gates are allowed.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35. -/
def IsAllowed : {ℓ ℓ' : Layout P} → Circuit κ G ℓ ℓ' → Prop
  | _, _, id _ => True
  | _, _, comp w w' => w.IsAllowed ∧ w'.IsAllowed
  | _, _, localMap _ _ _ U _ _ => ‖U‖ ≤ 1
  | _, _, gate g => GateFamily.IsAllowed g
  | _, _, swap .. => True
  | _, _, frame _ w => w.IsAllowed

/-- An allowed circuit is a contraction.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 215–217. -/
theorem norm_eval_le_one : {ℓ ℓ' : Layout P} → (w : Circuit κ G ℓ ℓ') → w.IsAllowed →
    ‖w.eval‖ ≤ 1
  | _, _, id _, _ => ContinuousLinearMap.norm_id_le
  | _, _, comp w w', h => norm_comp_le_one (norm_eval_le_one w' h.2) (norm_eval_le_one w h.1)
  | _, _, localMap _ _ _ _ _ _, h =>
      norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_comp_le_one ((norm_rTensor_le _ _).trans h)
          (LinearIsometry.norm_toContinuousLinearMap_le _))
  | _, _, gate g, h => GateFamily.norm_eval_le_one g h
  | _, _, swap .., _ => norm_leftCommL_le
  | _, _, frame _ w, h => (norm_lTensor_le _ _).trans (norm_eval_le_one w h)

@[simp] theorem eval_id (ℓ : Layout P) :
    (id ℓ : Circuit κ G ℓ ℓ).eval = ContinuousLinearMap.id ℂ _ :=
  rfl

@[simp] theorem eval_comp {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : Circuit κ G ℓ₁ ℓ₂)
    (w' : Circuit κ G ℓ₂ ℓ₃) : (comp w w').eval = w'.eval ∘L w.eval :=
  rfl

theorem eval_localMap (p : P) {ℓ₁ ℓ₂ : Layout P} (h₁ : ∀ r ∈ ℓ₁, r.owner = p)
    (h₂ : ∀ r ∈ ℓ₂, r.owner = p) (U : Mem ℓ₁ →L[ℂ] Mem ℓ₂) (ℓ : Layout P) (hU : κ U) :
    (localMap p h₁ h₂ U ℓ hU : Circuit κ G _ _).eval =
      isoL (appendIso ℓ₂ ℓ).symm ∘L U.rTensor (Mem ℓ) ∘L isoL (appendIso ℓ₁ ℓ) :=
  rfl

theorem eval_gate {ℓ ℓ' : Layout P} (g : G ℓ ℓ') :
    (gate g : Circuit κ G ℓ ℓ').eval = GateFamily.eval g :=
  rfl

theorem eval_swap (r r' : Reg P) (ℓ : Layout P) :
    (swap r r' ℓ : Circuit κ G _ _).eval = leftCommL r.space r'.space (Mem ℓ) :=
  rfl

theorem eval_frame (r : Reg P) {ℓ ℓ' : Layout P} (w : Circuit κ G ℓ ℓ') :
    (frame r w).eval = w.eval.lTensor r.space :=
  rfl

/-- The local maps of a circuit with contractive local maps and allowed gates are allowed. -/
theorem isAllowed_of_contraction : {ℓ ℓ' : Layout P} →
    (w : Circuit LocalCondition.contraction G ℓ ℓ') →
    (∀ {a b : Layout P} (g : G a b), GateFamily.IsAllowed g) → w.IsAllowed
  | _, _, id _, _ => trivial
  | _, _, comp w w', h => ⟨isAllowed_of_contraction w h, isAllowed_of_contraction w' h⟩
  | _, _, localMap _ _ _ _ _ hU, _ => hU
  | _, _, gate g, h => h g
  | _, _, swap .., _ => trivial
  | _, _, frame _ w, h => isAllowed_of_contraction w h

end Eval

/-! ### Spectators in front -/

/-- A circuit framed by a list of untouched registers. -/
def frameList {ℓ ℓ' : Layout P} : (ℓ₀ : Layout P) → Circuit κ G ℓ ℓ' →
    Circuit κ G (ℓ₀ ++ ℓ) (ℓ₀ ++ ℓ')
  | [], w => w
  | r :: ℓ₀, w => frame r (frameList ℓ₀ w)

theorem isAllowed_frameList [GateFamily G] {ℓ ℓ' : Layout P} (w : Circuit κ G ℓ ℓ')
    (hw : w.IsAllowed) : (ℓ₀ : Layout P) → (frameList ℓ₀ w).IsAllowed
  | [] => hw
  | _ :: ℓ₀ => isAllowed_frameList w hw ℓ₀

/-- Framing by a list acts on the second factor of the concatenated memory. -/
theorem eval_frameList_appendIso_symm [GateFamily G] {a b : Layout P} (c : Circuit κ G a b) :
    (rs : Layout P) → (x : Mem rs) → (y : Mem a) →
      (frameList rs c).eval ((appendIso rs a).symm (x ⊗ₜ y)) =
        (appendIso rs b).symm (x ⊗ₜ c.eval y)
  | [], x, y => map_smul c.eval x y
  | r :: rs, x, y => by
      induction x using TensorProduct.inductionOn with
      | tmul u v => exact congrArg (fun z ↦ u ⊗ₜ z) (eval_frameList_appendIso_symm c rs v y)
      | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]

/-! ### Identifying equal layouts -/

/-- Identify equal input and output layouts without adding an operation. -/
def castLayouts {ℓ ℓ' a b : Layout P} (w : Circuit κ G ℓ ℓ') (h : ℓ = a) (h' : ℓ' = b) :
    Circuit κ G a b :=
  h ▸ h' ▸ w

@[simp] theorem isAllowed_castLayouts [GateFamily G] {ℓ ℓ' a b : Layout P}
    (w : Circuit κ G ℓ ℓ') (h : ℓ = a) (h' : ℓ' = b) :
    (w.castLayouts h h').IsAllowed ↔ w.IsAllowed := by
  cases h
  cases h'
  rfl

theorem eval_castLayouts_heq [GateFamily G] {ℓ ℓ' a b : Layout P} (w : Circuit κ G ℓ ℓ')
    (h : ℓ = a) (h' : ℓ' = b) : HEq (w.castLayouts h h').eval w.eval := by
  cases h
  cases h'
  rfl

/-! ### Gate occurrences and their participants -/

/-- The number of gate occurrences, excluding local maps and changes of tensor order.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 199–202. -/
def gateCount : {ℓ ℓ' : Layout P} → Circuit κ G ℓ ℓ' → ℕ
  | _, _, id _ => 0
  | _, _, comp w w' => w.gateCount + w'.gateCount
  | _, _, localMap .. => 0
  | _, _, gate _ => 1
  | _, _, swap .. => 0
  | _, _, frame _ w => w.gateCount

@[simp] theorem gateCount_frameList {ℓ ℓ' : Layout P} (w : Circuit κ G ℓ ℓ') :
    (ℓ₀ : Layout P) → (frameList ℓ₀ w).gateCount = w.gateCount
  | [] => rfl
  | _ :: ℓ₀ => gateCount_frameList w ℓ₀

@[simp] theorem gateCount_castLayouts {ℓ ℓ' a b : Layout P} (w : Circuit κ G ℓ ℓ')
    (h : ℓ = a) (h' : ℓ' = b) : (w.castLayouts h h').gateCount = w.gateCount := by
  cases h
  cases h'
  rfl

/-- The gate occurrences of a circuit, kept distinct even when their operators coincide.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 199–229. -/
def gateLocations : {ℓ ℓ' : Layout P} → Circuit κ G ℓ ℓ' → Type
  | _, _, id _ => Empty
  | _, _, comp w w' => gateLocations w ⊕ gateLocations w'
  | _, _, localMap .. => Empty
  | _, _, gate _ => Unit
  | _, _, swap .. => Empty
  | _, _, frame _ w => gateLocations w

/-- A circuit has finitely many gate occurrences, even when the type of parties is
infinite. -/
instance gateLocationsFintype : {ℓ ℓ' : Layout P} → (w : Circuit κ G ℓ ℓ') →
    Fintype (gateLocations w)
  | _, _, id _ => inferInstanceAs (Fintype Empty)
  | _, _, comp w w' => by
      letI := gateLocationsFintype w
      letI := gateLocationsFintype w'
      exact inferInstanceAs (Fintype (gateLocations w ⊕ gateLocations w'))
  | _, _, localMap .. => inferInstanceAs (Fintype Empty)
  | _, _, gate _ => inferInstanceAs (Fintype Unit)
  | _, _, swap .. => inferInstanceAs (Fintype Empty)
  | _, _, frame _ w => gateLocationsFintype w

/-- The number of gate occurrences is the cardinality of the type of occurrences. -/
theorem card_gateLocations : {ℓ ℓ' : Layout P} → (w : Circuit κ G ℓ ℓ') →
    Fintype.card (gateLocations w) = w.gateCount
  | _, _, id _ => rfl
  | _, _, comp w w' => by
      exact (Fintype.card_sum (α := gateLocations w) (β := gateLocations w')).trans
        (congrArg₂ _ (card_gateLocations w) (card_gateLocations w'))
  | _, _, localMap .. => rfl
  | _, _, gate _ => rfl
  | _, _, swap .. => rfl
  | _, _, frame _ w => card_gateLocations w

/-- The parties taking part in a gate occurrence.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 25–27 and 229. -/
def participants [GateFamily G] : {ℓ ℓ' : Layout P} → (w : Circuit κ G ℓ ℓ') →
    gateLocations w → Finset P
  | _, _, id _ => Empty.elim
  | _, _, comp w w' => Sum.elim (participants w) (participants w')
  | _, _, localMap .. => Empty.elim
  | _, _, gate g => fun _ => GateFamily.participants g
  | _, _, swap .. => Empty.elim
  | _, _, frame _ w => participants w

end Circuit

/- The operations and lemmas shared by all gate families are used unqualified throughout the
party calculus. -/
export Circuit (eval IsAllowed frameList castLayouts norm_eval_le_one eval_comp eval_frame
  isAllowed_frameList isAllowed_castLayouts eval_castLayouts_heq eval_frameList_appendIso_symm
  gateCount gateLocations participants)

end TNLean.Lattice.PartyCircuit
