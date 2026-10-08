/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PreparedSourceGate
import TNLean.PEPS.Approximation.WordAppendTail
import TNLean.PEPS.Approximation.AffectedOwners

/-!
# Chronological compositions of source-prepared gates

Each nonprivate gate has its own participating party type and its own common
source positions. Gates act in their prescribed order with arbitrary spectator
registers. A partial expansion chooses labels only at gates meeting the affected
parties; every other gate retains its complete aggregate contraction.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 21–36, 133–151, 233–267 and 351–417.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- A chronological composition with source-prepared nonprivate gates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–36,
133–151 and 233–267. -/
inductive SourceCircuit : Layout P → Layout P → Type 1
  | id (a : Layout P) : SourceCircuit a a
  | comp {a b d : Layout P} (w : SourceCircuit a b) (v : SourceCircuit b d) :
      SourceCircuit a d
  | localMap (p : P) {a b : Layout P}
      (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
      (A : Mem a →L[ℂ] Mem b) (tail : Layout P) :
      SourceCircuit (a ++ tail) (b ++ tail)
  | gate {C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P)
      {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P) :
      SourceCircuit (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail)
  | swap (r s : Reg P) (tail : Layout P) : SourceCircuit (r :: s :: tail) (s :: r :: tail)
  | frame (r : Reg P) {a b : Layout P} (w : SourceCircuit a b) :
      SourceCircuit (r :: a) (r :: b)

namespace SourceCircuit

/-- The complete memory operator in chronological order, with each gate's
aggregate contraction and every spectator identity retained.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–36 and 233–267. -/
def eval : {a b : Layout P} → SourceCircuit a b → Mem a →L[ℂ] Mem b
  | _, _, .id _ => .id ℂ _
  | _, _, .comp w v => v.eval ∘L w.eval
  | _, _, .localMap p ha hb A tail => (Word.localMap p ha hb A tail).eval
  | _, _, @SourceCircuit.gate _ C _ι _ _ owner a b _c G tail =>
      isoL (appendIso (Layout.mapOwner owner b) tail).symm ∘L
        (G.evalAtOwners owner).rTensor (Mem tail) ∘L
          isoL (appendIso (Layout.mapOwner owner a) tail)
  | _, _, .swap r s tail => (Word.swap r s tail).eval
  | _, _, .frame r w => w.eval.lTensor r.space

/-- Every private operation is a contraction. The prepared nonprivate gates
already carry their aggregate contraction bounds.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 133–151. -/
def IsAllowed : {a b : Layout P} → SourceCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsAllowed ∧ v.IsAllowed
  | _, _, .localMap _ _ _ A _ => ‖A‖ ≤ 1
  | _, _, @SourceCircuit.gate _ _ _ _ _ _ _ _ _ _ _ => True
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsAllowed

/-- A chronological composition of allowed operations is a contraction.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 133–151 and 215–226. -/
theorem norm_eval_le_one {a b : Layout P} (w : SourceCircuit a b)
    (hw : w.IsAllowed) : ‖w.eval‖ ≤ 1 := by
  induction w with
  | id => exact norm_id_le
  | comp w v ihw ihv => exact norm_comp_le_one (ihv hw.2) (ihw hw.1)
  | localMap p ha hb A tail =>
      exact Word.norm_eval_le_one (.localMap p ha hb A tail) (show ‖A‖ ≤ 1 from hw)
  | @gate C ι _ _ owner a b c G tail =>
      exact norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_comp_le_one ((norm_rTensor_le (Mem tail) _).trans (G.norm_evalAtOwners_le_one owner))
          (LinearIsometry.norm_toContinuousLinearMap_le _))
  | swap r s tail => exact Word.norm_eval_le_one (.swap r s tail) trivial
  | frame r w ih => exact (norm_lTensor_le r.space _).trans (ih hw)

/-- Monomial choices occur exactly at gates touching the affected parties.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
def Choices (A : P → Bool) : {a b : Layout P} → SourceCircuit a b → Type
  | _, _, .id _ => Unit
  | _, _, .comp w v => Choices A w × Choices A v
  | _, _, .localMap .. => Unit
  | _, _, @SourceCircuit.gate _ C ι _ _ owner _ _ _ _ _ => by
      classical
      exact if ∃ p : C, A (owner p) = true then ι else Unit
  | _, _, .swap .. => Unit
  | _, _, .frame _ w => Choices A w

/-- A partial expansion has finitely many monomial choices.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
instance choicesFintype (A : P → Bool) : {a b : Layout P} →
    (w : SourceCircuit a b) → Fintype (Choices A w)
  | _, _, .id _ => inferInstanceAs (Fintype Unit)
  | _, _, .comp w v => by
      letI := choicesFintype A w
      letI := choicesFintype A v
      exact inferInstanceAs (Fintype (Choices A w × Choices A v))
  | _, _, .localMap .. => inferInstanceAs (Fintype Unit)
  | _, _, @SourceCircuit.gate _ C ι _ _ owner _ _ _ _ _ => by
      classical
      dsimp only [Choices]
      split <;> infer_instance
  | _, _, .swap .. => inferInstanceAs (Fintype Unit)
  | _, _, .frame _ w => choicesFintype A w

private theorem exterior_layout {C : Type} (A : P → Bool) (owner : C → P)
    (h : ¬ ∃ p, A (owner p) = true) (a : Layout C) :
    ∀ r ∈ Layout.mapOwner owner a, affectedOwner A r.owner = none := by
  rintro r hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
  exact (affectedOwner_eq_none A _).mpr (Bool.eq_false_iff.mpr (fun hp ↦ h ⟨s.owner, hp⟩))

/-- The actual branch of the partial expansion; untouched exterior gates are
retained as whole local operations. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–417. -/
def partialWord (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    Choices A w → Word (Layout.mapOwner (affectedOwner A) a)
      (Layout.mapOwner (affectedOwner A) b)
  | _, _, .id a, _ => .id _
  | _, _, .comp w v, ξ => .comp (partialWord A w ξ.1) (partialWord A v ξ.2)
  | _, _, .localMap p ha hb T tail, _ =>
      (Word.localMap p ha hb T tail).mapOwner (affectedOwner A)
  | _, _, @SourceCircuit.gate _ C ι _ _ owner a b c G tail, ξ => by
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · have i : ι := by simpa only [Choices, ite_eq_left h] using ξ
        exact (((G.branchWord i).mapOwner owner).appendTail tail).mapOwner (affectedOwner A)
      · exact Word.groupedBlockMap (affectedOwner A) none
          (Layout.mapOwner owner a) (Layout.mapOwner owner b)
          (exterior_layout A owner h a) (exterior_layout A owner h b)
          (G.evalAtOwners owner) tail
  | _, _, .swap r t tail, _ => (Word.swap r t tail).mapOwner (affectedOwner A)
  | _, _, .frame r w, ξ => .frame ⟨affectedOwner A r.owner, r.space⟩ (partialWord A w ξ)

/-- Scalar weights are charged only at gates whose labels are actually expanded.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
def coefficient (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) → Choices A w → ℂ
  | _, _, .id _, _ => 1
  | _, _, .comp w v, ξ => coefficient A w ξ.1 * coefficient A v ξ.2
  | _, _, .localMap .., _ => 1
  | _, _, @SourceCircuit.gate _ C ι _ _ owner _ _ c _ _, ξ => by
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · have i : ι := by simpa only [Choices, ite_eq_left h] using ξ
        exact c i
      · exact 1
  | _, _, .swap .., _ => 1
  | _, _, .frame _ w, ξ => coefficient A w ξ

end SourceCircuit
end TNLean.PEPS.PairEffect
