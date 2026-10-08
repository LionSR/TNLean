/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FullResidualLocality
import TNLean.PEPS.Approximation.SourcePreparationCoordinates

/-! # Actual complete branches and pair-source vectors

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 342–381.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The actual word for a complete choice of chronological monomials.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 342–355. -/
def fullBranchWord : {a b : Layout P} → (w : SourceCircuit a b) →
    FullLabels w → Word a b
  | _, _, .id a, _ => .id a
  | _, _, .comp w v, ξ => .comp (fullBranchWord w (fun g => ξ (.inl g)))
      (fullBranchWord v (fun g => ξ (.inr g)))
  | _, _, .localMap p ha hb A tail, _ => .localMap p ha hb A tail
  | _, _, @SourceCircuit.gate _ _ _ _ _ owner _ _ _ G tail, ξ =>
      ((G.branchWord (ξ ())).mapOwner owner).appendTail tail
  | _, _, .swap r s tail, _ => .swap r s tail
  | _, _, .frame r w, ξ => .frame r (fullBranchWord w ξ)

/-- The product of the actual pair-source vectors, in the fixed chronological
source-register order. Source: polynomial-PEPS 04-compression.tex, lines 233–251
and 342–355. -/
def fullSourceVector : {a b : Layout P} → (w : SourceCircuit a b) →
    FullLabels w → Mem w.fixedSourceLayout
  | _, _, .id _, _ => (1 : ℂ)
  | _, _, .comp w v, ξ => (appendIso v.fixedSourceLayout w.fixedSourceLayout).symm
      (fullSourceVector v (fun g => ξ (.inr g)) ⊗ₜ[ℂ]
        fullSourceVector w (fun g => ξ (.inl g)))
  | _, _, .localMap .., _ => (1 : ℂ)
  | _, _, @SourceCircuit.gate _ _ _ _ _ owner _ _ _ G _, ξ =>
      Layout.mapOwnerIso owner _ (SourceInventory.slotVector G.slots
        (fun i => euc (Fin (G.leftDim i))) (fun i => euc (Fin (G.rightDim i)))
        (G.vector (ξ ())))
  | _, _, .swap .., _ => (1 : ℂ)
  | _, _, .frame _ w, ξ => fullSourceVector w ξ

private theorem memCongr_heq {a b : Layout P} (h : a = b) (x : Mem a) :
    HEq (Layout.memCongr h x) x := by
  cases h
  rfl

private theorem append_tmul_heq {a b a' b' : Layout P} (ha : a = a') (hb : b = b')
    {x : Mem a} {x' : Mem a'} {y : Mem b} {y' : Mem b'}
    (hx : HEq x x') (hy : HEq y y') :
    HEq ((appendIso a b).symm (x ⊗ₜ[ℂ] y))
      ((appendIso a' b').symm (x' ⊗ₜ[ℂ] y')) := by
  cases ha
  cases hb
  cases hx
  cases hy
  rfl


/-- The actual mapped gate residual, after insertion of its recorded source
vector, is the actual prepared branch, with arbitrary spectator registers.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 342–355. -/
theorem fullRemainingWord_gate_prepare_tmul {C ι : Type} [Fintype C] [Fintype ι]
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (ξ : ι)
    (x : Mem a) (y : Mem tail) :
    let w := SourceCircuit.gate owner G tail
    (w.fullRemainingWord (fun _ => ξ)).eval
      ((appendIso w.fixedSourceLayout (Layout.mapOwner owner a ++ tail)).symm
        (w.fullSourceVector (fun _ => ξ) ⊗ₜ[ℂ]
          (appendIso (Layout.mapOwner owner a) tail).symm
            (Layout.mapOwnerIso owner a x ⊗ₜ[ℂ] y))) =
    (w.fullBranchWord (fun _ => ξ)).eval
      ((appendIso (Layout.mapOwner owner a) tail).symm
        (Layout.mapOwnerIso owner a x ⊗ₜ[ℂ] y)) := by
  let S := SourceInventory.slotLayout G.slots
    (fun i => euc (Fin (G.leftDim i))) (fun i => euc (Fin (G.rightDim i)))
  let η : Mem S := SourceInventory.slotVector G.slots
    (fun i => euc (Fin (G.leftDim i))) (fun i => euc (Fin (G.rightDim i))) (G.vector ξ)
  have hm : HEq
      ((appendIso (Layout.mapOwner owner S) (Layout.mapOwner owner a)).symm
        (Layout.mapOwnerIso owner S η ⊗ₜ[ℂ] Layout.mapOwnerIso owner a x))
      (Layout.mapOwnerIso owner (S ++ a) ((appendIso S a).symm (η ⊗ₜ[ℂ] x))) :=
    (heq_of_eq (Layout.mapOwnerIso_append_tmul owner S a η x).symm).trans
      (memCongr_heq _ _)
  have hn := append_tmul_heq (Layout.mapOwner_append owner S a).symm
    (rfl : tail = tail) hm (HEq.rfl : HEq y y)
  have hin := (appendIso_assoc_symm_heq (Layout.mapOwner owner S)
    (Layout.mapOwner owner a) tail (Layout.mapOwnerIso owner S η)
    (Layout.mapOwnerIso owner a x) y).trans hn
  have heR := DFunLike.congr_fun
    (Word.eval_appendTail ((G.remaining ξ).mapOwner owner) tail)
    (Layout.mapOwnerIso owner (S ++ a) ((appendIso S a).symm (η ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ] y)
  have heB := DFunLike.congr_fun
    (Word.eval_appendTail ((G.branchWord ξ).mapOwner owner) tail)
    (Layout.mapOwnerIso owner a x ⊗ₜ[ℂ] y)
  have heG : (G.remaining ξ).eval ((appendIso S a).symm (η ⊗ₜ[ℂ] x)) =
      (G.branchWord ξ).eval x := by
    simp only [PreparedSourceGate.branchWord, Word.eval_comp, comp_apply,
      SourceInventory.eval_prepareSlots_eq_appendIso_symm]
    rfl
  calc
    _ = (((G.remaining ξ).mapOwner owner).appendTail tail).eval
        ((appendIso (Layout.mapOwner owner (S ++ a)) tail).symm
          (Layout.mapOwnerIso owner (S ++ a) ((appendIso S a).symm (η ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ] y)) :=
      Word.eval_castInput_of_heq _ _ hin
    _ = (appendIso (Layout.mapOwner owner b) tail).symm
        (Layout.mapOwnerIso owner b ((G.remaining ξ).eval
          ((appendIso S a).symm (η ⊗ₜ[ℂ] x))) ⊗ₜ[ℂ] y) :=
      heR.trans (congrArg (fun z =>
        (appendIso (Layout.mapOwner owner b) tail).symm (z ⊗ₜ[ℂ] y))
        (Word.eval_mapOwner owner (G.remaining ξ) _))
    _ = (appendIso (Layout.mapOwner owner b) tail).symm
        (Layout.mapOwnerIso owner b ((G.branchWord ξ).eval x) ⊗ₜ[ℂ] y) :=
      congrArg (fun z => (appendIso (Layout.mapOwner owner b) tail).symm
        (Layout.mapOwnerIso owner b z ⊗ₜ[ℂ] y)) heG
    _ = _ := (heB.trans (congrArg (fun z =>
      (appendIso (Layout.mapOwner owner b) tail).symm (z ⊗ₜ[ℂ] y))
      (Word.eval_mapOwner owner (G.branchWord ξ) x))).symm
end TNLean.PEPS.PairEffect.SourceCircuit
