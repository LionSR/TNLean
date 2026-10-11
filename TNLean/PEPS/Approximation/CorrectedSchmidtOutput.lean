/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceInputSchmidtFrames
import TNLean.PEPS.Approximation.CorrectedSchmidtInput
import TNLean.PEPS.Approximation.LocalSchmidtOutput

/-!
# The actual partial output in corrected-source Schmidt coordinates

Only corrected source vectors are replaced by endpoint columns. Exact crossing
sources and the fixed sources retain their original vectors. The resulting
output is evaluated by the actual two local words on constructed input frames.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped TensorProduct Matrix
namespace TNLean.PEPS.PairEffect.SourceCircuit
open SourceInventory TNLean.PEPS.Approximation
variable {P : Type} {a b : Layout P}
variable (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (E : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (F : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

open Classical in
/-- The actual partial output on a genuinely prepared input has a Schmidt
expansion through two allowed local words. The frames are constructed from the
original corrected endpoint columns and the exact crossing-source vector. -/
theorem exists_correctedSchmidtOutput (hw : w.IsAllowed)
    (hE : ∀ e ξ, (E e ξ)ᴴ * E e ξ = 1) (hF : ∀ e ξ, (F e ξ)ᴴ * F e ξ = 1)
    (p₀ : Word [] a) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (ξ : Choices (correctedMask w S) w) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let C := freeSlotLayout R U V (correctedSlotMask w S)
    let T := freeSlotLayout R U V (crossingSlotMask w S)
    let out := Layout.mapOwner (affectedOwner A) b
    let side := fun p : Option {p // A p = true} ↦ p.isSome
    let e := partialSchmidtCoordinateEquiv A w S (correctedMask_meets w S)
    Word.HasSchmidtOutput (Layout.mapOwner side (C ++ T)) (Layout.mapOwner side out)
      (fun i : CorrectedSchmidtCoordinates w S ↦
        Layout.partitionIso (fun p : Bool ↦ p) (Layout.mapOwner side out)
          (Layout.mapOwnerIso side out
            (Layout.mapOwnerIso (affectedOwner A) b
              (partialSchmidtOutput A w S E F ξ (e.symm i) (p₀.eval 1))))) := by
  intro A R U V C T out side e
  obtain ⟨u, hu, hus, hinput⟩ := exists_correctedSchmidtInput_identity w S E F p₀
  let v : Word (C ++ T) out := correctedPreparedWord w S p₀ u ξ
  have hv : Word.HasTensorPartition side v :=
    hasTensorPartition_prepared_reordered_partial w hw S p₀ hp₀ hp₀s u hu hus ξ
  let I := CorrectedSchmidtCoordinates w S
  let frame : EuclideanSpace ℂ I →ₗᵢ[ℂ] Mem (Layout.mapOwner side C) :=
    correctedSourceFrame w S E F hE hF ξ
  let η : I → ∀ j : Fin R.length, U j ⊗[ℂ] V j :=
    fun i ↦ partialSchmidtSourceVectors A w S E F ξ (e.symm i)
  let x : I → Mem C := fun i ↦ freeSourceVector R U V (correctedSlotMask w S) (η i)
  let y : Mem T := freeSourceVector R U V (crossingSlotMask w S) (partialSlotVector A w ξ)
  have hx : ∀ i : I,
      frame (EuclideanSpace.basisFun I ℂ i) = Layout.mapOwnerIso side C (x i) := by
    intro i
    have h := correctedSourceFrame_basis w S E F hE hF ξ (e.symm i)
    change frame (EuclideanSpace.basisFun I ℂ (e (e.symm i))) =
      Layout.mapOwnerIso side C (x i) at h
    simpa only [Equiv.apply_symm_apply] using h
  have hf : HasSchmidtInputFrames (Layout.mapOwner side C) (Layout.mapOwner side T) frame
      (Layout.partitionIso (fun p : Bool ↦ p) (Layout.mapOwner side T)
        (Layout.mapOwnerIso side T y)) := exists_correctedInputFrames w S E F hE hF ξ
  have ho := Word.hasSchmidtOutput_of_hasTensorPartition side C T out v hv frame x y hx hf
  have hfun := funext (fun i : I ↦ congrArg
    (fun z : Mem out ↦ Layout.partitionIso (fun p : Bool ↦ p) (Layout.mapOwner side out)
      (Layout.mapOwnerIso side out z)) (hinput ξ i))
  exact (congrArg (Word.HasSchmidtOutput (Layout.mapOwner side (C ++ T))
    (Layout.mapOwner side out)) hfun).mpr ho

end TNLean.PEPS.PairEffect.SourceCircuit
