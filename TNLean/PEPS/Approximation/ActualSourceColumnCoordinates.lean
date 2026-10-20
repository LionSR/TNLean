/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePrivatePreparation
import TNLean.PEPS.Approximation.ActualSourceInputBasis
import TNLean.Lattice.PartyCircuit.UnitMemoryCoordinates

/-!
# Coordinates of actual source-to-output columns

The basis vector on the input to the private preparation is the corresponding
source-slot basis vector tensored with scalar one. Consequently the literal
chronological column matrix is the matrix of the actual source-free word.
This identification permits a subsequent change to party source coordinates.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 137–139, 246–267, 409–434 and 565–588.
-/

noncomputable section
open scoped TensorProduct Matrix
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- The literal source-to-output matrix of an actual all-party chronological
choice after preparing the recorded product input.
Source: polynomial-PEPS, `04-compression.tex`, lines 137–139 and 409–434. -/
def partialSourceGlobalMatrix {a b : Layout P} (w : SourceCircuit a b)
    (ψ : ProductInput a) (ξ : Choices (fun _ => true) w)
    {m : Type} [Fintype m]
    (bOut : OrthonormalBasis m ℂ
      (Mem (Layout.mapOwner (affectedOwner (fun _ => true)) b))) :
    Matrix m (∀ i : Fin (partialSlots (fun _ => true) w).length,
      Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1 ×
        Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2) ℂ :=
  let R := partialSlots (fun _ => true) w
  let U := fun i : Fin R.length =>
    euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1)
  let V := fun i : Fin R.length =>
    euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2)
  let bU := fun i : Fin R.length =>
    EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1) ℂ
  let bV := fun i : Fin R.length =>
    EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2) ℂ
  fun row x => bOut.repr ((w.partialSourceWord ψ ξ).eval
    ((appendIso w.allResidualSourceLayout []).symm
      (SourceInventory.slotBasis R U V bU bV x ⊗ₜ[ℂ] (1 : ℂ)))) row

/-- The actual input-basis vector is the literal source vector with its
terminal scalar unit. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–267 and 409–434. -/
theorem actualSourceInputBasis_apply (w : SourceCircuit a b) (x : w.allSourceLabels) :
    w.actualSourceInputBasis x =
      (appendIso w.allResidualSourceLayout []).symm
        (w.allSourceBasis x ⊗ₜ[ℂ] (1 : ℂ)) := by
  rw [actualSourceInputBasis, OrthonormalBasis.map_apply, Layout.memCongr_symm,
    ← Layout.appendIso_symm_tmul_one_eq_memCongr_symm]
  exact List.append_nil _

/-- The literal columns are the coordinates of the actual chronological word
on its actual source input. No basis identity is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
409–434 and 565–588. -/
theorem partialSourceGlobalMatrix_eq_toMatrix (w : SourceCircuit a b)
    (ψ : ProductInput a) (ξ : Choices (fun _ => true) w)
    {m : Type} [Fintype m]
    (bOut : OrthonormalBasis m ℂ
      (Mem (Layout.mapOwner (affectedOwner (fun _ => true)) b))) :
    w.partialSourceGlobalMatrix ψ ξ bOut =
      LinearMap.toMatrix w.actualSourceInputBasis.toBasis bOut.toBasis
        (w.partialSourceWord ψ ξ).eval.toLinearMap := by
  classical
  ext r x
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, actualSourceInputBasis_apply]
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
