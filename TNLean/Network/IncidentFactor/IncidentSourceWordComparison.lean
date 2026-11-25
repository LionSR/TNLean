/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.ExteriorScalar
import TNLean.Network.IncidentFactor.IncidentSourceWord

/-!
# The prepared source operation reads only the incident labels

At an original party, the local part of a branch of the expansion along all parties is built
from the gates of the circuit one after the other. A gate whose cell does not contain the party
acts there as the identification of equal bases, whatever its label; a gate whose cell contains
the party is the same branch word for two branches with the same label there; and the fresh
factors of the later sources do not depend on the labels, only on the bases of the slots. Hence
the operation at the party of the residual of a branch, and of the prepared source word, is the
same for two branches with the same labels at the incident gates. In particular it is the
operation `incidentSourceOp` constructed from the incident labels.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139, 246–267, 351–434
and 565–588.
-/

noncomputable section

open Matrix ManyBody

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-- Matrices of casts from a common basis are heterogeneously equal. -/
private theorem heq_toMatrix_cast_left {T U U' : Type} [DecidableEq U] [DecidableEq U']
    (h : T = U) (h' : T = U') :
    HEq ((Equiv.cast h).toPEquiv.toMatrix : Matrix T U ℂ)
      ((Equiv.cast h').toPEquiv.toMatrix : Matrix T U' ℂ) := by
  subst h h'
  rename_i i₁ i₂
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  rfl

/-- Matrices of casts into a common basis are heterogeneously equal. -/
private theorem heq_toMatrix_cast_right {T U U' : Type} [DecidableEq T]
    (h : U = T) (h' : U' = T) :
    HEq ((Equiv.cast h).toPEquiv.toMatrix : Matrix U T ℂ)
      ((Equiv.cast h').toPEquiv.toMatrix : Matrix U' T ℂ) := by
  subst h h'
  rfl

/-- Products of heterogeneously equal factors are heterogeneously equal. -/
private theorem heq_mul {l m n l' m' n' : Type} [Fintype m] [Fintype m'] (hl : l = l')
    (hm : m = m') (hn : n = n') {A : Matrix l m ℂ} {A' : Matrix l' m' ℂ} {B : Matrix m n ℂ}
    {B' : Matrix m' n' ℂ} (hA : HEq A A') (hB : HEq B B') : HEq (A * B) (A' * B') := by
  subst hl hm hn
  rename_i i₁ i₂
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  obtain rfl := eq_of_heq hA
  obtain rfl := eq_of_heq hB
  rfl

/-- Reading the columns through casts keeps heterogeneous equality. -/
private theorem heq_submatrix_cast {l m n m' n' : Type} (hm : m = m') (hn : n = n')
    {A : Matrix l m ℂ} {A' : Matrix l m' ℂ} (e : n = m) (e' : n' = m') (hA : HEq A A') :
    HEq (A.submatrix id (Equiv.cast e)) (A'.submatrix id (Equiv.cast e')) := by
  subst hm hn
  obtain rfl := eq_of_heq hA
  rfl

/-- Running heterogeneously equal operations beside the same fresh pair gives heterogeneously
equal operations. -/
private theorem addPairMatrix_heq {a b : P} (hab : a ≠ b) (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {Y₁ Y₂ Y₁' Y₂' : P → Type} (hY : Y₁ = Y₂)
    (hY' : Y₁' = Y₂') (C₁ : ∀ s, Matrix (Y₁' s) (Y₁ s) ℂ) (C₂ : ∀ s, Matrix (Y₂' s) (Y₂ s) ℂ)
    (p : P) (h : HEq (C₁ p) (C₂ p)) :
    HEq (addPairMatrix hab α β C₁ p) (addPairMatrix hab α β C₂ p) := by
  subst hY hY'
  unfold addPairMatrix
  rw [eq_of_heq h]

namespace SourceInventory

/-- Running party operations beside the fresh factors of two slot inventories that differ only
in their vectors gives heterogeneously equal operations at a party where the operations are
heterogeneously equal. -/
private theorem liftOps_ofSlots_heq : (R : SourceInventory P) → (B : SlotBases R.length) →
    (η η' : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) →
    {X₁ X₂ X₁' X₂' : P → Type} → (hX : X₁ = X₂) → (hX' : X₁' = X₂') →
    (A₁ : ∀ s, Matrix (X₁' s) (X₁ s) ℂ) → (A₂ : ∀ s, Matrix (X₂' s) (X₂ s) ℂ) → (p : P) →
    HEq (A₁ p) (A₂ p) → HEq ((ofSlots R B η).liftOps A₁ p) ((ofSlots R B η').liftOps A₂ p)
  | [], _, _, _, _, _, _, _, hX, hX', A₁, A₂, p, h => by
    subst hX hX'
    exact h
  | r :: R, B, η, η', _, _, _, _, hX, hX', A₁, A₂, p, h => by
    rw [ofSlots_cons, ofSlots_cons]
    have ih := liftOps_ofSlots_heq R B.tail (fun i ↦ η i.succ) (fun i ↦ η' i.succ) hX hX'
      A₁ A₂ p h
    subst hX hX'
    exact addPairMatrix_heq r.distinct (B.left 0) (B.right 0)
      ((system_ofSlots R B.tail _ _).trans (system_ofSlots R B.tail _ _).symm)
      ((system_ofSlots R B.tail _ _).trans (system_ofSlots R B.tail _ _).symm) _ _ p ih

/-- Equal inventories run the same operations. -/
private theorem liftOps_heq_of_eq {X X' : P → Type} {S S' : SourceInventory P} (h : S = S')
    (A : ∀ s, Matrix (X' s) (X s) ℂ) (p : P) : HEq (S.liftOps A p) (S'.liftOps A p) := by
  subst h
  rfl

end SourceInventory

namespace SourceCircuit

variable [Fintype P]

/-- Two branches of the expansion along all parties have the same system of sources. -/
private theorem system_sources_partialWord_all {X Y : P → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] (w : SourceCircuit X Y) (ξ ξ' : Choices (fun _ ↦ true) w)
    (Z : Option {_p : P // true = true} → Type) :
    (partialWord (fun _ ↦ true) w ξ).sources.system Z =
      (partialWord (fun _ ↦ true) w ξ').sources.system Z := by
  rw [← ofSlots_partialSlotVector, ← ofSlots_partialSlotVector, SourceInventory.system_ofSlots,
    SourceInventory.system_ofSlots]

/-- The local part at an original party of a branch of the expansion along all parties reads
only the labels of the gates in which the party participates. -/
private theorem localPartOp_partialWord_all_heq : {X Y : P → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (w : SourceCircuit X Y) → (p : P) →
    (ξ ξ' : Choices (fun _ ↦ true) w) →
    (∀ g hg, p ∈ w.participants g →
      choiceAt (fun _ ↦ true) w ξ g hg = choiceAt (fun _ ↦ true) w ξ' g hg) →
    HEq ((partialWord (fun _ ↦ true) w ξ).localPartOp (some ⟨p, rfl⟩))
      ((partialWord (fun _ ↦ true) w ξ').localPartOp (some ⟨p, rfl⟩))
  | _, _, _, _, PartyCircuit.done _, _, _, _, _ => HEq.rfl
  | _, _, _, _, PartyCircuit.gate D hY g, p, ξ, ξ', h => by
    by_cases ht : PreparedGate.IsTouched (fun _ ↦ true) D
    · by_cases hp : p ∈ D
      · obtain rfl : ξ = ξ' := (cast_inj _).mp (h () ht hp)
        rfl
      · obtain ⟨e, he⟩ := localPartOp_partialWord_all_gate_of_notMem D hY g p hp ξ
        obtain ⟨e', he'⟩ := localPartOp_partialWord_all_gate_of_notMem D hY g p hp ξ'
        rw [he, he']
        exact heq_toMatrix_cast_left e e'
    · have : Subsingleton (Choices (fun _ ↦ true)
          (PartyCircuit.gate D hY g : SourceCircuit _ _)) := by
        dsimp only [Choices]
        rw [ite_eq_right ht]
        infer_instance
      obtain rfl : ξ = ξ' := Subsingleton.elim _ _
      rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _, _ => HEq.rfl
  | _, _, _, _, PartyCircuit.localOps _, _, _, _, _ => HEq.rfl
  | X, _, _, _, @PartyCircuit.comp _ _ _ M _ _ _ c c', p, ξ, ξ', h => by
    have ih := localPartOp_partialWord_all_heq c p ξ.1 ξ'.1 fun g hg ↦ h (Sum.inl g) hg
    have ih' := localPartOp_partialWord_all_heq c' p ξ.2 ξ'.2 fun g hg ↦ h (Sum.inr g) hg
    have hs := system_sources_partialWord_all c ξ.1 ξ'.1
    have hs' := system_sources_partialWord_all c' ξ.2 ξ'.2
    let q : Option {_p : P // true = true} := some ⟨p, rfl⟩
    have hlift : HEq ((partialWord (fun _ ↦ true) c' ξ.2).sources.liftOps
        (partialWord (fun _ ↦ true) c ξ.1).localPartOp q)
        ((partialWord (fun _ ↦ true) c' ξ'.2).sources.liftOps
          (partialWord (fun _ ↦ true) c ξ'.1).localPartOp q) :=
      (SourceInventory.liftOps_heq_of_eq (ofSlots_partialSlotVector _ c' ξ.2).symm _ q).trans
        ((SourceInventory.liftOps_ofSlots_heq _ _ _ _ (hs _) rfl _ _ q ih).trans
          (SourceInventory.liftOps_heq_of_eq (ofSlots_partialSlotVector _ c' ξ'.2) _ q))
    refine heq_submatrix_cast ?_ ?_ _ _ (heq_mul rfl (congrFun (hs' _) q) ?_ ih' hlift)
    · rw [hs', hs]
    · change SourceInventory.system (_ ++ _) _ q = SourceInventory.system (_ ++ _) _ q
      rw [SourceInventory.system_append, SourceInventory.system_append, hs', hs]
    · rw [hs', hs]

/-- **The residual at an original party reads only the labels of its incident gates.** -/
theorem partyOp_partialResidual_all_eq_of_incident {X Y : P → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (w : SourceCircuit X Y) (p : P) (ξ ξ' : Choices (fun _ ↦ true) w)
    (h : ∀ g hg, p ∈ w.participants g →
      choiceAt (fun _ ↦ true) w ξ g hg = choiceAt (fun _ ↦ true) w ξ' g hg) :
    PartyCircuit.partyOp (partialResidual (fun _ ↦ true) w ξ) (some ⟨p, rfl⟩) =
      PartyCircuit.partyOp (partialResidual (fun _ ↦ true) w ξ') (some ⟨p, rfl⟩) := by
  let q : Option {_p : P // true = true} := some ⟨p, rfl⟩
  have hs := system_sources_partialWord_all w ξ ξ' (blockSystem (affectedOwner fun _ ↦ true) X)
  refine eq_of_heq (heq_mul rfl (congrFun hs q) rfl
    (localPartOp_partialWord_all_heq w p ξ ξ' h) (heq_toMatrix_cast_right _ _))

/-- **The prepared source word at an original party reads only the labels of its incident
gates.** -/
theorem partyOp_partialSourceWord_eq_of_incident {X Y : P → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (w : SourceCircuit X Y) (φ : ∀ s, EuclideanSpace ℂ (X s)) (p : P)
    (ξ ξ' : Choices (fun _ ↦ true) w)
    (h : ∀ g hg, p ∈ w.participants g →
      choiceAt (fun _ ↦ true) w ξ g hg = choiceAt (fun _ ↦ true) w ξ' g hg) :
    PartyCircuit.partyOp (partialSourceWord w φ ξ) (some ⟨p, rfl⟩) =
      PartyCircuit.partyOp (partialSourceWord w φ ξ') (some ⟨p, rfl⟩) := by
  rw [partialSourceWord, partialSourceWord, PartyCircuit.partyOp_comp,
    PartyCircuit.partyOp_comp, partyOp_partialResidual_all_eq_of_incident w p ξ ξ' h]

/-- At an original party, the prepared source word of a branch is the operation constructed
from the labels of the branch at the incident gates. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267, 351–434 and 565–588. -/
theorem partyOp_partialSourceWord_eq_incidentSourceOp {X Y : P → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (w : SourceCircuit X Y) (φ : ∀ s, EuclideanSpace ℂ (X s)) (p : P)
    (ξ : Choices (fun _ ↦ true) w) :
    PartyCircuit.partyOp (partialSourceWord w φ ξ) (some ⟨p, rfl⟩) =
      incidentSourceOp w φ p (originalGateLabelsAtOfAllChoices w p ξ) := by
  have hf : Function.FactorsThrough
      (fun ξ ↦ PartyCircuit.partyOp (partialSourceWord w φ ξ) (some ⟨p, rfl⟩))
      (originalGateLabelsAtOfAllChoices w p) := fun ξ ξ' hξ ↦
    partyOp_partialSourceWord_eq_of_incident w φ p ξ ξ' fun g _ hp ↦
      congrFun hξ ⟨⟨⟨g, ⟨p, hp⟩⟩, Finset.mem_univ _⟩, hp⟩
  exact (hf.extend_apply 0 ξ).symm

end SourceCircuit

end QuantumCircuit.Party
