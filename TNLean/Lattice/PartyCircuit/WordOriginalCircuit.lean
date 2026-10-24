/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.EffectReplacementExpansion
import TNLean.Lattice.PartyCircuit.FrontRegisters
import TNLean.Lattice.PartyCircuit.WordOwnerMap

/-!
# Allowed monomials as original circuits

An allowed monomial of Theorem 5.2 is a composition of local contractions, normalized pair
sources and normalized pair effects. Read operation by operation, it is an original circuit in
the sense of `TNLean.Lattice.PartyCircuit.OriginalCircuit`: every local contraction is a private
map of its party, every pair source and every pair effect is a nonprivate gate whose two
participants are the endpoint parties, and the exchanges of tensor factors are kept.

This is how the bounded changes of §6 of the polynomial-PEPS manuscript, which are given as
monomials on the registers of encoded frames, enter the protocol of Proposition 7.1: each
change is a fixed number of nonprivate gates, all participants of which are parties named by
the change (`06-geometry.tex`, lines 574–583).

## Main definitions

* `PartyCircuit.pairOwner` : the two endpoint parties of a pair source or effect.
* `PartyCircuit.Word.toOriginalCircuit` : a source-only word as an original circuit.
* `PartyCircuit.PartyChain.toOriginalCircuit` : an allowed monomial as an original circuit.

## Main results

* `PartyCircuit.Word.eval_toOriginalCircuit`, `PartyCircuit.PartyChain.eval_toOriginalCircuit` :
  the original circuit has the operator of the monomial.
* `PartyCircuit.Word.nonprivateCount_toOriginalCircuit`,
  `PartyCircuit.PartyChain.nonprivateCount_toOriginalCircuit` : one nonprivate gate per pair
  source and per pair effect.
* `PartyCircuit.Word.participants_toOriginalCircuit_subset`,
  `PartyCircuit.PartyChain.participants_toOriginalCircuit_subset` : the participants are parties
  used by the monomial.
* `PartyCircuit.Word.isExpansionBounded_toOriginalCircuit`,
  `PartyCircuit.PartyChain.isExpansionBounded_toOriginalCircuit` : each gate is a single monomial
  with coefficient one and at most one pair effect.

## References

* Polynomial-PEPS manuscript (September 24, 2026), allowed monomials and original circuits,
  `04-compression.tex`, lines 21–43 and 199–208; the gate count of Proposition 7.1,
  `06-geometry.tex`, lines 574–583.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.Lattice.PartyCircuit

variable {P : Type}

/-! ### Two-party gates -/

/-- The two endpoint parties `p ≠ q` of a pair source or a pair effect, indexed by `Bool`:
`false ↦ p` and `true ↦ q`. -/
def pairOwner {p q : P} (hpq : p ≠ q) : Bool ↪ P where
  toFun b := cond b q p
  inj' := by
    intro a b h
    cases a <;> cases b <;> first | rfl | exact absurd h hpq | exact absurd h.symm hpq

theorem card_bool_ne_one : Fintype.card Bool ≠ 1 := by decide

theorem coe_univ_map_pairOwner_subset {p q : P} (hpq : p ≠ q) {S : Set P} (hp : p ∈ S)
    (hq : q ∈ S) : (↑(Finset.univ.map (pairOwner hpq)) : Set P) ⊆ S := by
  intro x hx
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hx
  cases b
  · exact hp
  · exact hq

/-- A gate expansion consisting of one monomial with coefficient one. -/
abbrev singleGate {C : Type} {a b : Layout C} (M : PartyChain a b) : PartyGate a b :=
  [(1, M)]

theorem gate_toGate_singleGate {C : Type} {a b : Layout C} (M : PartyChain a b) :
    gate (toGate (singleGate M)) = M.toEffectChain.eval := by
  simp [gate]

/-- The single pair source of a two-party gate, on the empty spectator layout. -/
abbrev sourceMonomial (U V : HSpace) (η : U ⊗[ℂ] V) :
    PartyChain ([] : Layout Bool) [⟨false, U⟩, ⟨true, V⟩] :=
  .final (.source Bool.false_ne_true U V η [])

/-- The single pair effect of a two-party gate, on the empty spectator layout. -/
abbrev effectMonomial (α β : Type) [Fintype α] [Fintype β] (η : EuclideanSpace ℂ (α × β)) :
    PartyChain ([⟨false, euc α⟩, ⟨true, euc β⟩] : Layout Bool) [] :=
  .effect Bool.false_ne_true α β [] (.id _) η (.final (.id []))

theorem norm_gate_sourceMonomial_le (U V : HSpace) {η : U ⊗[ℂ] V} (hη : ‖η‖ = 1) :
    ‖gate (toGate (singleGate (sourceMonomial U V η)))‖ ≤ 1 := by
  rw [gate_toGate_singleGate]
  exact Word.norm_eval_le_one (.source Bool.false_ne_true U V η []) hη

theorem norm_gate_effectMonomial_le (α β : Type) [Fintype α] [Fintype β]
    {η : EuclideanSpace ℂ (α × β)} (hη : ‖η‖ = 1) :
    ‖gate (toGate (singleGate (effectMonomial α β η)))‖ ≤ 1 := by
  rw [gate_toGate_singleGate]
  have h := PartyChain.isAllowed_toEffectChain (effectMonomial α β η) ⟨trivial, hη, trivial⟩
  exact EffectChain.norm_eval_le_one _ h

/-- A normalized pair source on the parties `p ≠ q`, as a two-party nonprivate gate.
Polynomial-PEPS manuscript, `04-compression.tex`, lines 25–35. -/
def sourceCircuit {p q : P} (hpq : p ≠ q) (U V : HSpace) (η : U ⊗[ℂ] V) (hη : ‖η‖ = 1)
    (ℓ : Layout P) : OriginalCircuit ℓ (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ) :=
  .nonprivateGate (pairOwner hpq) card_bool_ne_one (singleGate (sourceMonomial U V η))
    (fun m hm => by rw [List.mem_singleton.mp hm]; exact hη)
    (norm_gate_sourceMonomial_le U V hη) ℓ

/-- A normalized pair effect on the parties `p ≠ q`, as a two-party nonprivate gate.
Polynomial-PEPS manuscript, `04-compression.tex`, lines 25–35. -/
def effectCircuit {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [Fintype β]
    (η : EuclideanSpace ℂ (α × β)) (hη : ‖η‖ = 1) (ℓ : Layout P) :
    OriginalCircuit (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ) ℓ :=
  .nonprivateGate (pairOwner hpq) card_bool_ne_one (singleGate (effectMonomial α β η))
    (fun m hm => by rw [List.mem_singleton.mp hm]; exact ⟨trivial, hη, trivial⟩)
    (norm_gate_effectMonomial_le α β hη) ℓ

private theorem appendIso_pair_symm_assocL {p q : P} (U V : HSpace) (ℓ : Layout P)
    (η : U ⊗[ℂ] V) (x : Mem ℓ) :
    (appendIso [⟨p, U⟩, ⟨q, V⟩] ℓ).symm (assocL U V ℂ (η ⊗ₜ (1 : ℂ)) ⊗ₜ x) =
      (assocL U V (Mem ℓ) (η ⊗ₜ x) : Mem (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ)) := by
  induction η using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [assocL_tmul]
      rw [LinearIsometryEquiv.symm_apply_eq]
      exact (appendIso_two_tmul ⟨p, U⟩ ⟨q, V⟩ ℓ u v x).symm
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]

theorem eval_sourceCircuit {p q : P} (hpq : p ≠ q) (U V : HSpace) (η : U ⊗[ℂ] V)
    (hη : ‖η‖ = 1) (ℓ : Layout P) :
    (sourceCircuit hpq U V η hη ℓ).eval = (Word.source hpq U V η ℓ).eval := by
  classical
  have hm := Word.eval_mapOwner_comp (pairOwner hpq) (Word.source Bool.false_ne_true U V η [])
  have hw : (Word.source Bool.false_ne_true U V η []).mapOwner (pairOwner hpq) =
      Word.source hpq U V η [] := by
    simp only [Word.mapOwner]
    split
    · next h => exact absurd h hpq
    · rfl
  rw [hw] at hm
  ext x
  simp only [sourceCircuit, OriginalCircuit.eval, comp_apply, isoL_apply]
  rw [gate_toGate_singleGate]
  have hx : appendIso (Layout.mapOwner (pairOwner hpq) []) ℓ x =
      (show Mem (Layout.mapOwner (pairOwner hpq) ([] : Layout Bool)) from (1 : ℂ)) ⊗ₜ x := rfl
  rw [hx, rTensor_tmul]
  have h1 := DFunLike.congr_fun hm (show Mem ([] : Layout Bool) from (1 : ℂ))
  simp only [comp_apply, isoL_apply] at h1
  simp only [comp_apply, isoL_apply]
  erw [← h1]
  exact appendIso_pair_symm_assocL U V ℓ η x

/-- A nonprivate gate acts on its participants' registers next to untouched spectators. -/
theorem OriginalCircuit.eval_nonprivateGate_appendIso_symm
    {C : Type} [Fintype C] (owner : C ↪ P) (hC : Fintype.card C ≠ 1) {a b : Layout C}
    (L : PartyGate a b) (hL : ∀ q ∈ L, q.2.IsAllowed) (hG : ‖gate (toGate L)‖ ≤ 1)
    (tail : Layout P) (u : Mem (Layout.mapOwner owner a)) (t : Mem tail) :
    (OriginalCircuit.nonprivateGate owner hC L hL hG tail).eval
        ((appendIso (Layout.mapOwner owner a) tail).symm (u ⊗ₜ t)) =
      (appendIso (Layout.mapOwner owner b) tail).symm
        (Layout.mapOwnerIso owner b (gate (toGate L) ((Layout.mapOwnerIso owner a).symm u)) ⊗ₜ
          t) := by
  simp only [OriginalCircuit.eval, comp_apply, isoL_apply, LinearIsometryEquiv.apply_symm_apply,
    rTensor_tmul]

theorem eval_effectCircuit {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [Fintype β]
    (η : EuclideanSpace ℂ (α × β)) (hη : ‖η‖ = 1) (ℓ : Layout P) :
    (effectCircuit hpq α β η hη ℓ).eval =
      effectMap η (Mem ℓ) ∘L isoL (pairHeadIso (p := p) (q := q) ℓ) := by
  apply clm_ext_tmul₃
  intro x y s
  have hx : (x ⊗ₜ (y ⊗ₜ s) : Mem (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ)) =
      (appendIso [⟨p, euc α⟩, ⟨q, euc β⟩] ℓ).symm ((x ⊗ₜ (y ⊗ₜ (1 : ℂ))) ⊗ₜ s) := by
    rw [LinearIsometryEquiv.eq_symm_apply]
    exact appendIso_two_tmul _ _ ℓ x y s
  rw [hx]
  refine (OriginalCircuit.eval_nonprivateGate_appendIso_symm _ _ _ _ _ ℓ _ s).trans ?_
  rw [gate_toGate_singleGate]
  rw [comp_apply, isoL_apply, ← hx, pairHeadIso_tmul, effectMap_tmul]
  change (appendIso [] ℓ).symm
    (effectMap η ℂ (pairHeadIso [] (x ⊗ₜ (y ⊗ₜ (1 : ℂ)))) ⊗ₜ s) = _
  rw [pairHeadIso_tmul, effectMap_tmul, appendIso_nil_symm_tmul, smul_eq_mul, mul_one]

/-! ### Source-only words -/

namespace Word

/-- A source-only word as an original circuit: a local contraction is a private map of its
party, and a normalized pair source is a two-party nonprivate gate. Exchanges of tensor factors
are kept. Polynomial-PEPS manuscript, `04-compression.tex`, lines 21–43. -/
def toOriginalCircuit : {a b : Layout P} → (w : Word a b) → w.IsAllowed → OriginalCircuit a b
  | _, _, id a, _ => .id a
  | _, _, comp w w', h => .comp (toOriginalCircuit w h.1) (toOriginalCircuit w' h.2)
  | _, _, localMap p h₁ h₂ U ℓ, h => .privateMap p h₁ h₂ U h ℓ
  | _, _, source hpq U V η ℓ, h => sourceCircuit hpq U V η h ℓ
  | _, _, swap r r' ℓ, _ => .swap r r' ℓ
  | _, _, frame r w, h => .frame r (toOriginalCircuit w h)

/-- The original circuit of a word has the operator of the word. -/
theorem eval_toOriginalCircuit {a b : Layout P} (w : Word a b) (hw : w.IsAllowed) :
    (w.toOriginalCircuit hw).eval = w.eval := by
  induction w with
  | id => rfl
  | comp w w' ih ih' =>
      simp only [toOriginalCircuit, OriginalCircuit.eval, eval_comp, ih, ih']
  | localMap => rfl
  | source hpq U V η ℓ => exact eval_sourceCircuit hpq U V η hw ℓ
  | swap => rfl
  | frame r w ih =>
      simp only [toOriginalCircuit, OriginalCircuit.eval, eval_frame]
      rw [ih hw]

/-- One nonprivate gate for each pair source of the word. -/
theorem nonprivateCount_toOriginalCircuit {a b : Layout P} (w : Word a b)
    (hw : w.IsAllowed) : (w.toOriginalCircuit hw).nonprivateCount = w.sourceCount := by
  induction w with
  | id => rfl
  | comp w w' ih ih' =>
      simp only [toOriginalCircuit, OriginalCircuit.nonprivateCount, sourceCount, ih, ih']
  | localMap => rfl
  | source => rfl
  | swap => rfl
  | frame r w ih => exact ih hw

/-- Every participant of a nonprivate gate of the circuit is a party used by the word. -/
theorem participants_toOriginalCircuit_subset {S : Set P} {a b : Layout P} (w : Word a b)
    (hw : w.IsAllowed) (hS : w.UsesOnly S) (g : (w.toOriginalCircuit hw).nonprivateLocations) :
    (↑((w.toOriginalCircuit hw).participants g) : Set P) ⊆ S := by
  induction w with
  | id => exact nomatch g
  | comp w w' ih ih' =>
      cases g with
      | inl g => exact ih hw.1 hS.1 g
      | inr g => exact ih' hw.2 hS.2 g
  | localMap => exact nomatch g
  | source hpq U V η ℓ => exact coe_univ_map_pairOwner_subset hpq hS.1 hS.2
  | swap => exact nomatch g
  | frame r w ih => exact ih hw hS g

/-- Each nonprivate gate of the circuit is a single monomial with coefficient one and no pair
effect. -/
theorem isExpansionBounded_toOriginalCircuit {a b : Layout P} (w : Word a b)
    (hw : w.IsAllowed) (r : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    (w.toOriginalCircuit hw).IsExpansionBounded r s := by
  induction w with
  | id => trivial
  | comp w w' ih ih' => exact ⟨ih hw.1, ih' hw.2⟩
  | localMap => trivial
  | source =>
      refine ⟨fun m hm => ?_, by simpa using hs⟩
      rw [List.mem_singleton] at hm
      subst hm
      exact Nat.zero_le r
  | swap => trivial
  | frame r w ih => exact ih hw

/-- Each nonprivate gate of the circuit has one monomial. -/
theorem isMonomialBounded_toOriginalCircuit {a b : Layout P} (w : Word a b)
    (hw : w.IsAllowed) {K : ℕ} (hK : 1 ≤ K) : (w.toOriginalCircuit hw).IsMonomialBounded K := by
  induction w with
  | id => trivial
  | comp w w' ih ih' => exact ⟨ih hw.1, ih' hw.2⟩
  | localMap => trivial
  | source => exact hK
  | swap => trivial
  | frame r w ih => exact ih hw

end Word

/-! ### Allowed monomials -/

namespace PartyChain

/-- An allowed monomial as an original circuit: its source-only words as in
`Word.toOriginalCircuit`, and each normalized pair effect as a two-party nonprivate gate.
Polynomial-PEPS manuscript, `04-compression.tex`, lines 21–43. -/
def toOriginalCircuit : {a b : Layout P} → (M : PartyChain a b) → M.IsAllowed →
    OriginalCircuit a b
  | _, _, final w, h => w.toOriginalCircuit h
  | _, _, effect hpq α β ℓS w η rest, h =>
      .comp (w.toOriginalCircuit h.1)
        (.comp (effectCircuit hpq α β η h.2.1 ℓS) (toOriginalCircuit rest h.2.2))

/-- The original circuit of a monomial has the operator of the monomial. -/
theorem eval_toOriginalCircuit {a b : Layout P} (M : PartyChain a b) (hM : M.IsAllowed) :
    (M.toOriginalCircuit hM).eval = M.toEffectChain.eval := by
  induction M with
  | final w => exact w.eval_toOriginalCircuit hM
  | effect hpq α β ℓS w η rest ih =>
      simp only [toOriginalCircuit, OriginalCircuit.eval, Word.eval_toOriginalCircuit,
        eval_effectCircuit, ih, EffectChain.eval]
      rfl

/-- One nonprivate gate for each pair source and each pair effect of the monomial. -/
theorem nonprivateCount_toOriginalCircuit {a b : Layout P} (M : PartyChain a b)
    (hM : M.IsAllowed) :
    (M.toOriginalCircuit hM).nonprivateCount = M.sourceCount + M.toEffectChain.effectCount := by
  induction M with
  | final w => exact w.nonprivateCount_toOriginalCircuit hM
  | effect hpq α β ℓS w η rest ih =>
      simp only [toOriginalCircuit, OriginalCircuit.nonprivateCount,
        Word.nonprivateCount_toOriginalCircuit, ih, sourceCount, EffectChain.effectCount]
      change w.sourceCount + (1 + _) = _
      omega

/-- Every participant of a nonprivate gate of the circuit is a party used by the monomial. -/
theorem participants_toOriginalCircuit_subset {S : Set P} {a b : Layout P}
    (M : PartyChain a b) (hM : M.IsAllowed) (hS : M.UsesOnly S)
    (g : (M.toOriginalCircuit hM).nonprivateLocations) :
    (↑((M.toOriginalCircuit hM).participants g) : Set P) ⊆ S := by
  induction M with
  | final w => exact w.participants_toOriginalCircuit_subset hM hS g
  | effect hpq α β ℓS w η rest ih =>
      rcases g with g | g | g
      · exact w.participants_toOriginalCircuit_subset hM.1 hS.2.2.1 g
      · exact coe_univ_map_pairOwner_subset hpq hS.1 hS.2.1
      · exact ih hM.2.2 hS.2.2.2 g

/-- Each nonprivate gate of the circuit is a single monomial with coefficient one and at most
one pair effect. -/
theorem isExpansionBounded_toOriginalCircuit {a b : Layout P} (M : PartyChain a b)
    (hM : M.IsAllowed) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 1 ≤ s) :
    (M.toOriginalCircuit hM).IsExpansionBounded r s := by
  induction M with
  | final w => exact w.isExpansionBounded_toOriginalCircuit hM r hs
  | effect hpq α β ℓS w η rest ih =>
      refine ⟨w.isExpansionBounded_toOriginalCircuit hM.1 r hs,
        ⟨fun m hm => ?_, by simpa using hs⟩, ih hM.2.2⟩
      rw [List.mem_singleton] at hm
      subst hm
      exact hr

/-- Each nonprivate gate of the circuit has one monomial. -/
theorem isMonomialBounded_toOriginalCircuit {a b : Layout P} (M : PartyChain a b)
    (hM : M.IsAllowed) {K : ℕ} (hK : 1 ≤ K) : (M.toOriginalCircuit hM).IsMonomialBounded K := by
  induction M with
  | final w => exact w.isMonomialBounded_toOriginalCircuit hM hK
  | effect hpq α β ℓS w η rest ih =>
      exact ⟨w.isMonomialBounded_toOriginalCircuit hM.1 hK, hK, ih hM.2.2⟩

end PartyChain

end TNLean.Lattice.PartyCircuit
