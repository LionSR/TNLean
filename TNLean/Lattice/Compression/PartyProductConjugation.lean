/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PartyProductPartialTrace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # Local conjugation and private traces of party products

Two families of local maps act on a product source matrix. Conjugation and the
final private trace are computed within each party, including for arbitrary
source matrices and distinct ket and bra maps.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 279–355 and 565–588.
-/
noncomputable section
open scoped Matrix
namespace TNLean.Lattice.PartyCircuit
variable {P : Type} [Fintype P]
variable {I O : P → Type}

/-- Two party-local maps conjugate a product source matrix separately at each
party. The maps and source matrices may be arbitrary.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588. -/
theorem piKronecker_mul_mul_conjTranspose [DecidableEq P] [∀ p, Fintype (I p)]
    (A B : (p : P) → Matrix (O p) (I p) ℂ)
    (X : (p : P) → Matrix (I p) (I p) ℂ) :
    Matrix.piKronecker A * Matrix.piKronecker X * (Matrix.piKronecker B)ᴴ =
      Matrix.piKronecker (fun p => A p * X p * (B p)ᴴ) := by
  rw [Matrix.conjTranspose_piKronecker, Matrix.piKronecker_mul, Matrix.piKronecker_mul]
open Classical in
/-- After two local maps act on a product source matrix, tracing all private
coordinates is exactly the product of the corresponding local physical matrices.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588. -/
theorem partialTraceRight_piKronecker_mul_mul_conjTranspose
    {Phys Priv : P → Type} [∀ p, Fintype (I p)] [∀ p, Fintype (Priv p)]
    (A B : (p : P) → Matrix (Phys p × Priv p) (I p) ℂ)
    (X : (p : P) → Matrix (I p) (I p) ℂ) :
    Matrix.partialTraceRight
      (fun (xi yj : ((p : P) → Phys p) × ((p : P) → Priv p)) =>
        (Matrix.piKronecker A * Matrix.piKronecker X * (Matrix.piKronecker B)ᴴ)
          (fun p => (xi.1 p, xi.2 p)) (fun p => (yj.1 p, yj.2 p))) =
      Matrix.piKronecker (fun p => Matrix.partialTraceRight (A p * X p * (B p)ᴴ)) := by
  simpa only [piKronecker_mul_mul_conjTranspose, Matrix.piKronecker_apply] using
    partialTraceRight_prod_eq_piKronecker (fun p => A p * X p * (B p)ᴴ)
end TNLean.Lattice.PartyCircuit
