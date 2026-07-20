/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.TraceNonincreasingDirectSum
import TNLean.MPS.MPDO.VerticalSectorDensityBlocks
import TNLean.MPS.MPDO.VerticalSectorGeneration

/-!
# Identity criterion for vertical-sector maps

A positive trace-preserving endomorphism of a finite product of matrix
algebras has a positive-definite fixed family when fixed factors generate the
identity by products of one positive length.  If its trace adjoint satisfies
the Schwarz inequality, the density-block description of its fixed points
then shows that the endomorphism is the identity.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1980--1995.
* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
  Equation (6.63).
-/

open scoped Matrix MatrixOrder ComplexOrder

noncomputable section

namespace MPOTensor

/-- A positive trace-preserving endomorphism of a vertical-sector algebra is
the identity if its trace adjoint satisfies the Schwarz inequality and it
fixes weighted bond contractions whose products span the sector algebra.

No product of fixed contractions is assumed to be fixed.  The fixed
contractions first give a positive-definite fixed family.  Wolf's
density-block description then bounds the dimension of the products of fixed
points, which forces every sector matrix to be fixed.

Source application: arXiv:1606.00608, Appendix C.4, lines 1980--1995. -/
theorem eq_id_of_weightedVerticalBondContractions_fixed_of_traceAdjointSchwarz
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (F : VerticalSectorAlgebra dim →ₗ[ℂ] VerticalSectorAlgebra dim)
    (hL : 0 < L)
    (hF : Matrix.IsPositiveDirectSumMap F)
    (hTP : Matrix.IsTracePreservingDirectSumMap F)
    (hSchwarz : Matrix.IsSchwarzDirectSumMap
      (Matrix.directSumTraceAdjointMap F))
    (hSpan : WeightedVerticalBondContractionProductSpanTop m A L)
    (hFixed : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      F (weightedVerticalBondContraction m A X) =
        weightedVerticalBondContraction m A X) :
    F = LinearMap.id := by
  have hOne :=
    one_mem_product_span_of_weightedVerticalBondContractions m A hSpan
  obtain ⟨ρ, hρ, hρFixed⟩ :=
    hF.exists_posDef_fixedFamily_of_fixed_product_span
      hTP (weightedVerticalBondContraction m A) L hL hFixed hOne
  apply eq_id_of_weightedVerticalBondContractions_fixed_of_productSpan_finrank_le
    m A F hSpan hFixed
  exact fixedPointProductSpan_finrank_le_of_densityBlocks
    hF hTP hSchwarz hρ hρFixed L hL

end MPOTensor
