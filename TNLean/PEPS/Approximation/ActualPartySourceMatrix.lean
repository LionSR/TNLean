/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceColumnCoordinates
import TNLean.PEPS.Approximation.WordPartyMixedMatrix
import TNLean.PEPS.Approximation.BasisMatrixOperator
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Actual source columns in party coordinates

The original source-slot basis is expanded in the chosen party input basis
through the matrix of the identity map. The literal chronological columns are
the product of the actual party-restriction matrices followed by this change
of basis. Every owner, including the exterior owner, remains in the product.
The same chosen bases and party order may be used for independent ket and bra
choices.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} [Fintype P] [DecidableEq P] {a b : Layout P}
variable {I O : Option {_p : P // true = true} → Type}
variable [∀ q, Fintype (I q)] [∀ q, Fintype (O q)]

/-- The matrix of the identity from literal source-slot coordinates to the
chosen party input coordinates. It is fixed independently of any branch choice.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 253–267, 409–434 and 565–588. -/
def actualPartySourceBasisChange (w : SourceCircuit a b)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (ps : List (Option {_p : P // true = true})) (hn : ps.Nodup)
    (hc : ∀ q, q ∈ ps) : Matrix ((q : Option {_p : P // true = true}) → I q)
      w.allSourceLabels ℂ :=
  LinearMap.toMatrix w.actualSourceInputBasis.toBasis
    (partyGroupedBasis (w.allResidualSourceLayout ++ []) B ps hn hc).toBasis
    LinearMap.id

/-- The matrix of an actual singleton restriction after preparing the original
private product input. All owners, including the exterior owner, are included.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–139, 409–434 and 565–588. -/
def partialSourcePartyMatrix (w : SourceCircuit a b) (ψ : ProductInput a)
    (ξ : Choices (fun _ : P ↦ true) w)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (C : ∀ q, OrthonormalBasis (O q) ℂ
      (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b))))
    (q : Option {_p : P // true = true}) : Matrix (O q) (I q) ℂ :=
  Matrix.of (fun row col ↦ (C q).repr
    (((w.partialSourceWord ψ ξ).restrict (partySelector q)
      (sources_partialSourceWord w ψ ξ)).eval (B q col)) row)

/-- Literal source columns are the product of the actual party matrices followed
by the constructed change from source-slot coordinates to party coordinates.
This is a coordinate consequence of the actual source-free word factorization.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–139, 409–434 and 565–588. -/
theorem partialSourceGlobalMatrix_eq_partyProduct_mul_basisChange
    (w : SourceCircuit a b) (ψ : ProductInput a)
    (ξ : Choices (fun _ : P ↦ true) w)
    (B : ∀ q, OrthonormalBasis (I q) ℂ
      (Mem (Layout.atParty q (w.allResidualSourceLayout ++ []))))
    (C : ∀ q, OrthonormalBasis (O q) ℂ
      (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b))))
    (ps : List (Option {_p : P // true = true})) (hn : ps.Nodup)
    (hc : ∀ q, q ∈ ps) :
    w.partialSourceGlobalMatrix ψ ξ
        (partyGroupedBasis (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)
          C ps hn hc) =
      dependentPhysicalProductFamilyMatrix (w.partialSourcePartyMatrix ψ ξ B C) *
        w.actualPartySourceBasisChange B ps hn hc := by
  classical
  let bIn := partyGroupedBasis (w.allResidualSourceLayout ++ []) B ps hn hc
  let bOut := partyGroupedBasis
    (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b) C ps hn hc
  have hparty := Word.partyGroupedBasis_matrix_eval (w.partialSourceWord ψ ξ)
    (sources_partialSourceWord w ψ ξ) B C ps hn hc
  have hmatrix : Matrix.of (fun row col ↦
      bOut.repr ((w.partialSourceWord ψ ξ).eval (bIn col)) row) =
      dependentPhysicalProductFamilyMatrix (fun q ↦
        w.partialSourcePartyMatrix ψ ξ B C q) := by
    simpa only [bIn, bOut, partialSourcePartyMatrix] using hparty
  have hm : LinearMap.toMatrix bIn.toBasis bOut.toBasis
      (w.partialSourceWord ψ ξ).eval.toLinearMap =
      dependentPhysicalProductFamilyMatrix (w.partialSourcePartyMatrix ψ ξ B C) := by
    simpa only [matrix_repr_eval_eq_toMatrix] using hmatrix
  have hchange := linearMap_toMatrix_mul_basis_toMatrix
    w.actualSourceInputBasis.toBasis bIn.toBasis bOut.toBasis
    (w.partialSourceWord ψ ξ).eval.toLinearMap
  have hid := LinearMap.toMatrix_id_eq_basis_toMatrix
    w.actualSourceInputBasis.toBasis bIn.toBasis
  exact (partialSourceGlobalMatrix_eq_toMatrix w ψ ξ bOut).trans
    (hchange.symm.trans
      ((congrArg (fun M ↦ M * bIn.toBasis.toMatrix w.actualSourceInputBasis.toBasis) hm).trans
        (congrArg (fun R ↦ dependentPhysicalProductFamilyMatrix
          (w.partialSourcePartyMatrix ψ ξ B C) * R) hid.symm)))

end TNLean.PEPS.PairEffect.SourceCircuit
