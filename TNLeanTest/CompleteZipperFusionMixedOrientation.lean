/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionMixedOrientation
import TNLean.MPS.MPDO.CompleteZipperFusionMixedEntries

/-! # Actual fourfold mixed-orientation comparison regressions -/

set_option linter.hashCommand false

open MPOTensor
open scoped BigOperators

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
  (Fus : CompleteZipperFusionFamily Λ p)

example (a b c d e : Λ) :
    Fus.leftAssocToLeftInnerPrintedFMatrix a b c d e *
      Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e = 1 :=
  Fus.leftAssocToLeftInner_mul_leftInnerToLeftAssocInverse a b c d e

example (a b c d e : Λ) :
    Fus.pairToRightAssocPrintedFMatrix a b c d e *
        Fus.leftAssocToPairPrintedFMatrix a b c d e *
        Fus.leftInnerToLeftAssocInversePrintedFMatrix a b c d e =
      Fus.middleToRightAssocPrintedFMatrix a b c d e *
        Fus.leftInnerToMiddlePrintedFMatrix a b c d e :=
  Fus.twoEdgePrintedFMatrix_mul_leftInnerToLeftAssocInverse a b c d e

/-- info:
'MPOTensor.CompleteZipperFusionFamily.leftAssocToLeftInner_mul_leftInnerToLeftAssocInverse'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.CompleteZipperFusionFamily.leftAssocToLeftInner_mul_leftInnerToLeftAssocInverse

/-- info:
'MPOTensor.CompleteZipperFusionFamily.twoEdgePrintedFMatrix_mul_leftInnerToLeftAssocInverse'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  MPOTensor.CompleteZipperFusionFamily.twoEdgePrintedFMatrix_mul_leftInnerToLeftAssocInverse

-- Exact row/column, factor, and summation order of the mixed pentagon.
-- No nonzero-multiplicity or scalar-channel hypothesis is available here.
example (a b c d e f g j i : Λ)
    (sigma : Fin (Fus.fusionMultiplicity b c f))
    (lambda : Fin (Fus.fusionMultiplicity a f g))
    (rho : Fin (Fus.fusionMultiplicity g d e))
    (gamma : Fin (Fus.fusionMultiplicity c d j))
    (delta : Fin (Fus.fusionMultiplicity b j i))
    (kappa : Fin (Fus.fusionMultiplicity a i e)) :
    (∑ k : Λ, ∑ tau : Fin (Fus.fusionMultiplicity k j e),
      ∑ mu : Fin (Fus.fusionMultiplicity a b k),
      ∑ nu : Fin (Fus.fusionMultiplicity k c g),
        Fus.printedFMatrix a b j e ⟨i, delta, kappa⟩ ⟨k, mu, tau⟩ *
          Fus.printedFMatrix k c d e ⟨j, gamma, tau⟩ ⟨g, nu, rho⟩ *
          Fus.inversePrintedFMatrix a b c g ⟨k, mu, nu⟩
            ⟨f, sigma, lambda⟩) =
      ∑ omega : Fin (Fus.fusionMultiplicity f d i),
        Fus.printedFMatrix b c d i ⟨j, gamma, delta⟩ ⟨f, sigma, omega⟩ *
          Fus.printedFMatrix a f d e ⟨i, omega, kappa⟩ ⟨g, lambda, rho⟩ :=
  Fus.printedFMatrix_mixed_pentagon a b c d e f g j i
    sigma lambda rho gamma delta kappa

/-- info:
'MPOTensor.CompleteZipperFusionFamily.printedFMatrix_mixed_pentagon'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.CompleteZipperFusionFamily.printedFMatrix_mixed_pentagon
