/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointMatrixWord

/-! # Actual endpoint coordinates and their sample average

The literal endpoint operator is expressed in the recorded source-slot bases.
The sample assignments are shared between the two endpoints of each slot.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- The party restriction of the literal endpoint matrix word depends only
on the matrices at that party's incident endpoints. No complementary operator
is cancelled in this identity.
Source: polynomial-PEPS 04-compression.tex, lines 565–588. -/
theorem restrict_endpointMatrixWord_eval_eq_of_agree (f : P → Bool)
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {I J : Fin R.length → Type} [∀ i, Fintype (I i)] [∀ i, Fintype (J i)]
    (bU : ∀ i, OrthonormalBasis (I i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (J i) ℂ (V i))
    (A A' : ∀ i, Matrix (I i) (I i) ℂ)
    (B B' : ∀ i, Matrix (J i) (J i) ℂ)
    (hA : ∀ i, f (R.get i).left = true → A i = A' i)
    (hB : ∀ i, f (R.get i).right = true → B i = B' i) :
    ((endpointMatrixWord R U V bU bV A B).restrict f
      (sources_endpointWord ..)).eval =
    ((endpointMatrixWord R U V bU bV A' B').restrict f
      (sources_endpointWord ..)).eval := by
  apply restrict_endpointWord_eval_eq_of_agree
  · intro i hi
    exact congrArg (basisMatrixOperator (bU i)) (hA i hi)
  · intro i hi
    exact congrArg (basisMatrixOperator (bV i)) (hB i hi)

end TNLean.PEPS.PairEffect.SourceInventory
