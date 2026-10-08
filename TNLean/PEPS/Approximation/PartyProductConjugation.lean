/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyProductPartialTrace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # Local conjugation and private traces of party products

Two families of local maps act on a product source matrix. Conjugation and the
final private trace are computed within each party, including for arbitrary
source matrices and distinct ket and bra maps.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect
variable {P : Type} [Fintype P]
variable {I O : P → Type}

/-- Taking the adjoint of a party product takes the adjoint of each local map.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588. -/
theorem partyProductMatrix_conjTranspose
    (B : (p : P) → Matrix (O p) (I p) ℂ) :
    (dependentPhysicalProductFamilyMatrix B)ᴴ =
      dependentPhysicalProductFamilyMatrix (fun p => (B p)ᴴ) := by
  ext x y
  simp only [dependentPhysicalProductFamilyMatrix, Matrix.conjTranspose_apply, star_prod]
/-- Two party-local maps conjugate a product source matrix separately at each
party. The maps and source matrices may be arbitrary.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588. -/
theorem partyProductMatrix_conjugate [DecidableEq P] [∀ p, Fintype (I p)]
    (A B : (p : P) → Matrix (O p) (I p) ℂ)
    (X : (p : P) → Matrix (I p) (I p) ℂ) :
    dependentPhysicalProductFamilyMatrix A * dependentPhysicalProductFamilyMatrix X *
      (dependentPhysicalProductFamilyMatrix B)ᴴ =
        dependentPhysicalProductFamilyMatrix (fun p => A p * X p * (B p)ᴴ) := by
  classical
  rw [partyProductMatrix_conjTranspose, dependentPhysicalProductFamilyMatrix_mul,
    dependentPhysicalProductFamilyMatrix_mul]
open Classical in
/-- After two local maps act on a product source matrix, tracing all private
coordinates is exactly the product of the corresponding local physical matrices.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588. -/
theorem partialTraceRight_partyProduct_conjugate
    {Phys Priv : P → Type} [∀ p, Fintype (I p)] [∀ p, Fintype (Priv p)]
    (A B : (p : P) → Matrix (Phys p × Priv p) (I p) ℂ)
    (X : (p : P) → Matrix (I p) (I p) ℂ) :
    Matrix.partialTraceRight
      (fun (xi yj : ((p : P) → Phys p) × ((p : P) → Priv p)) =>
        (dependentPhysicalProductFamilyMatrix A * dependentPhysicalProductFamilyMatrix X *
          (dependentPhysicalProductFamilyMatrix B)ᴴ)
            (fun p => (xi.1 p, xi.2 p)) (fun p => (yj.1 p, yj.2 p))) =
      dependentPhysicalProductFamilyMatrix
        (fun p => Matrix.partialTraceRight (A p * X p * (B p)ᴴ)) := by
  simpa only [partyProductMatrix_conjugate, dependentPhysicalProductFamilyMatrix] using
    partialTraceRight_partyProductMatrix (fun p => A p * X p * (B p)ᴴ)
end TNLean.PEPS.PairEffect
