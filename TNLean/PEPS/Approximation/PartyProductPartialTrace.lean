/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.PartialTrace
import TNLean.PEPS.DependentPhysicalProductRangeSupport

/-! # Partial trace of a product of party matrices

The private coordinates are summed within each party. No private coordinate
becomes a virtual tensor-network index.
Source: polynomial-PEPS, `04-compression.tex`, lines 574–579.
-/
noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type} [Fintype P] {X E : P → Type}
variable [∀ p, Fintype (E p)]

open Classical in
/-- Tracing the product of all private factors equals the product of the local
partial traces. Source: polynomial-PEPS, `04-compression.tex`, lines 574–579. -/
theorem partialTraceRight_partyProductMatrix
    (M : (p : P) → Matrix (X p × E p) (X p × E p) ℂ) :
    Matrix.partialTraceRight
      (fun (xi yj : ((p : P) → X p) × ((p : P) → E p)) =>
        ∏ p, M p (xi.1 p, xi.2 p) (yj.1 p, yj.2 p)) =
      dependentPhysicalProductFamilyMatrix (fun p => Matrix.partialTraceRight (M p)) := by
  ext x y
  change (∑ i : (p : P) → E p, ∏ p, M p (x p, i p) (y p, i p)) =
    ∏ p, ∑ i : E p, M p (x p, i) (y p, i)
  rw [Fintype.prod_sum]
end TNLean.PEPS.PairEffect
