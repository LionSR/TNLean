/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DistributedConstruction
import TNLean.Lattice.Compression.SelectedPhysicalPrivateTrace

/-! # The original physical density in the actual grouped coordinates

The original circuit output may be expressed in the actual grouped
physical/private basis. Removing the exterior singleton coordinate and
tracing the private coordinates gives the construction's original physical
density. The output is not divided by its norm.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–153 and 574–579.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect.DistributedConstruction
variable {P : Type} [Fintype P] [DecidableEq P]
variable {E : Option {_p : P // true = true} → Type} [∀ q, Fintype (E q)]

/-- The partial trace of the original output in the actual grouped coordinates
is the original physical density, with its original local physical dimensions.
No normalization of the output is performed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–153 and 574–579. -/
theorem physicalDensity_eq_grouped_partialTrace
    (C : DistributedConstruction P)
    (bGarbage : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) C.privateOutput)))) :
    let qs := selectedPartyOrder C.physicalOrder
    let B := partyGroupedBasis
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout C.physicalDimension C.physicalOrder ++ C.privateOutput))
      (selectedPhysicalPrivateBasis C.physicalDimension C.physicalOrder
        C.physicalOrder_nodup C.mem_physicalOrder C.privateOutput bGarbage) qs
      (selectedPartyOrder_nodup C.physicalOrder C.physicalOrder_nodup)
      (mem_selectedPartyOrder C.physicalOrder C.mem_physicalOrder)
    let e := (Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true})
      (selectedFamilyPhysicalIndex C.physicalDimension) E).trans
        (Equiv.prodCongr (selectedFamilyPhysicalConfigEquiv C.physicalDimension)
          (Equiv.refl ((q : Option {_p : P // true = true}) → E q)))
    let v := B.repr (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true))
      (familyPhysicalLayout C.physicalDimension C.physicalOrder ++ C.privateOutput)
      (C.circuit.eval C.input.vector))
    Matrix.partialTraceRight
        ((Matrix.euclideanOuterProduct v v).submatrix e.symm e.symm) =
      C.physicalDensity := by
  classical
  let := Layout.finiteDimensional_mem_of_registers C.privateOutput C.finite_privateOutput
  have h := selectedPhysicalPrivateBasis_partialTrace_mixed
    C.physicalDimension C.physicalOrder C.physicalOrder_nodup C.mem_physicalOrder
    C.privateOutput bGarbage (stdOrthonormalBasis ℂ (Mem C.privateOutput).carrier)
    (C.circuit.eval C.input.vector) (C.circuit.eval C.input.vector)
  let coords := ((familyLabelledPhysicalBasis C.physicalDimension C.physicalOrder
    C.physicalOrder_nodup C.mem_physicalOrder).tensorProduct
      (stdOrthonormalBasis ℂ (Mem C.privateOutput).carrier)).repr
        (appendIso (familyPhysicalLayout C.physicalDimension C.physicalOrder) C.privateOutput
          (C.circuit.eval C.input.vector))
  have hDensity : C.physicalDensity =
      Matrix.partialTraceRight (Matrix.euclideanOuterProduct coords coords) := rfl
  rw [hDensity]
  simpa only [Matrix.euclideanOuterProduct, Pi.star_def, starRingEnd_apply] using h

end TNLean.PEPS.PairEffect.DistributedConstruction
