/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePrivatePreparation
import TNLean.PEPS.Approximation.SourcePhysicalDensity

/-! # Local source-to-output matrices

These are matrix coordinates of the actual local maps after preparing the
original private input. Their mixed output matrices trace the final private
coordinates; arbitrary source operators need not produce positive matrices.
Source: polynomial-PEPS, `04-compression.tex`, lines 137–139, 279–355,
351–381 and 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-actualsourcelocalmatrices-01
TNLean.PEPS.PairEffect.SourceCircuit.partialSourceLocalMatrix
Provenance-ID: 8769-chronological-network-actualsourcelocalmatrices-02
TNLean.PEPS.PairEffect.SourceCircuit.partialSourceLocalMatrix_eq_actual_restriction
Provenance-ID: 8769-chronological-network-actualsourcelocalmatrices-03
TNLean.PEPS.PairEffect.SourceCircuit.partialSourceLocalPhysicalMatrix
-/


noncomputable section
open scoped Matrix
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Matrix coefficients of the actual local source-to-output map after the
recorded private product input is prepared. The bases give explicit coordinates
of the actual source and output memories.
Source: polynomial-PEPS 04-compression.tex, lines 137–139, 351–381 and 565–588. -/
def partialSourceLocalMatrix {a b : Layout P} (w : SourceCircuit a b) (ψ : ProductInput a)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (η : Choices (fun p => f (affectedOwner (fun _ => true) p)) w)
    {I O : Type} [Fintype I] [Fintype O]
    (bIn : OrthonormalBasis I ℂ (Mem (Layout.restrict f (w.allResidualSourceLayout ++ []))))
    (bOut : OrthonormalBasis O ℂ
      (Mem (Layout.restrict f (Layout.mapOwner (affectedOwner (fun _ => true)) b)))) :
    Matrix O I ℂ :=
  fun row col => bOut.repr (w.partialSourceLocalMap ψ f η (bIn col)) row

set_option maxHeartbeats 800000 in
-- Matrix coordinates retain the actual dependent source-layout transports.
/-- The constructed local matrix is the matrix of the singleton restriction
of the actual complete chronological branch, at its actual incident choices.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 565–588. -/
theorem partialSourceLocalMatrix_eq_actual_restriction {a b : Layout P}
    (w : SourceCircuit a b) (ψ : ProductInput a)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (ξ : Choices (fun _ => true) w) {I O : Type} [Fintype I] [Fintype O]
    (bIn : OrthonormalBasis I ℂ (Mem (Layout.restrict f (w.allResidualSourceLayout ++ []))))
    (bOut : OrthonormalBasis O ℂ
      (Mem (Layout.restrict f (Layout.mapOwner (affectedOwner (fun _ => true)) b)))) :
    w.partialSourceLocalMatrix ψ f
        (projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ξ) bIn bOut =
      fun row col => bOut.repr
        (((w.partialSourceWord ψ ξ).restrict f (sources_partialSourceWord w ψ ξ)).eval
          (bIn col)) row := by
  exact congrArg (fun A => fun row col => bOut.repr (A (bIn col)) row)
    (restrict_partialSourceWord_eq_partialSourceLocalMap w ψ f ξ).symm

/-- The local physical matrix obtained from two actual incident branch choices
and a source operator, tracing the actual final private coordinate. Arbitrary
source operators may give arbitrary matrices; positivity is not asserted here.
Source: polynomial-PEPS 04-compression.tex, lines 279–355 and 565–588. -/
def partialSourceLocalPhysicalMatrix {a b : Layout P} (w : SourceCircuit a b)
    (ψ : ProductInput a)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (η ζ : Choices (fun p => f (affectedOwner (fun _ => true) p)) w)
    {I Phys Priv : Type} [Fintype I] [Fintype Phys] [Fintype Priv]
    (bIn : OrthonormalBasis I ℂ (Mem (Layout.restrict f (w.allResidualSourceLayout ++ []))))
    (bOut : OrthonormalBasis (Phys × Priv) ℂ
      (Mem (Layout.restrict f (Layout.mapOwner (affectedOwner (fun _ => true)) b))))
    (X : Matrix I I ℂ) : Matrix Phys Phys ℂ :=
  Matrix.partialTraceRight
    (w.partialSourceLocalMatrix ψ f η bIn bOut * X *
      (w.partialSourceLocalMatrix ψ f ζ bIn bOut)ᴴ)

end TNLean.PEPS.PairEffect.SourceCircuit
