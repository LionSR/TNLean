/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.TraceNonincreasingProductSpan
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

namespace Matrix

variable {ι J : Type*} [Fintype ι]
variable {n : ι → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]

/-- A positive trace-preserving endomorphism of a finite product of matrix
algebras has a positive-definite fixed family when the identity belongs to
the span of positive-length products of a fixed family.

No product of the fixed factors is assumed to be fixed.  The proof applies
the full-matrix maximal-support theorem to the canonical block-diagonal
extension and then takes its diagonal blocks.

Local finite-product consequence used to formalize arXiv:1606.00608,
Appendix C.4, lines 1980--1993.  CPSV16 instead applies Wolf's density-block
description directly, including its possible zero summand. -/
theorem IsPositiveDirectSumMap.exists_posDef_fixedFamily_of_fixed_product_span
    {F : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hF : IsPositiveDirectSumMap F)
    (hTP : IsTracePreservingDirectSumMap F)
    (V : J → (∀ k, Matrix (n k) (n k) ℂ))
    (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, F (V j) = V j)
    (hOne : (1 : ∀ k, Matrix (n k) (n k) ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J ↦
        (List.ofFn fun t ↦ V (x t)).prod)) :
    ∃ ρ : ∀ k, Matrix (n k) (n k) ℂ,
      (∀ k, (ρ k).PosDef) ∧ F ρ = ρ := by
  classical
  let E := directSumExtension F
  let W : J → Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ :=
    fun j ↦ directSumDiagonalEmbedding (V j)
  have hEpos : IsPositiveMap E :=
    hF.directSumExtension_isPositiveMap
  have hETP : IsTracePreservingMap E :=
    hTP.directSumExtension_isTracePreservingMap
  have hETNI : IsTraceNonincreasingMap E := by
    intro X _
    exact (hETP X).le
  have hWFixed (j : J) : E (W j) = W j := by
    exact (directSumExtension_embedding_eq_self_iff F (V j)).2 (hFixed j)
  have hEmbeddingProd (l : List J) :
      directSumDiagonalEmbedding (l.map V).prod = (l.map W).prod := by
    induction l with
    | nil =>
        simp only [List.map_nil, List.prod_nil]
        exact Matrix.blockDiagonal'_one
    | cons a l ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [directSumDiagonalEmbedding_mul, ih]
  let productSpan := Submodule.span ℂ
    (Set.range fun x : Fin L → J ↦ (List.ofFn fun t ↦ W (x t)).prod)
  have hOneEmbedded :
      directSumDiagonalEmbedding (1 : ∀ k, Matrix (n k) (n k) ℂ) = 1 :=
    Matrix.blockDiagonal'_one
  have hOneFull :
      (1 : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) ∈ productSpan := by
    rw [← hOneEmbedded]
    exact Submodule.span_induction (p := fun X _ ↦
        directSumDiagonalEmbedding X ∈ productSpan)
      (fun X hX ↦ by
        obtain ⟨x, rfl⟩ := hX
        apply Submodule.subset_span
        refine ⟨x, ?_⟩
        have hprod := hEmbeddingProd (List.ofFn x)
        rw [List.map_ofFn, List.map_ofFn] at hprod
        have hfun : V ∘ x = fun t ↦ V (x t) := rfl
        have hfunW : W ∘ x = fun t ↦ W (x t) := rfl
        simpa only [hfun, hfunW] using hprod.symm)
      (by
        rw [map_zero]
        exact Submodule.zero_mem productSpan)
      (fun X Y _ _ hX hY ↦ by
        rw [map_add]
        exact Submodule.add_mem productSpan hX hY)
      (fun c X _ hX ↦ by
        rw [_root_.map_smul]
        exact Submodule.smul_mem productSpan c hX)
      hOne
  obtain ⟨ρFull, hρFull, hρFullFixed⟩ :=
    hEpos.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span
      hETNI W L hL hWFixed hOneFull
  obtain ⟨ρ, hρFixed, hρFullEq⟩ :=
    (directSumExtension_apply_eq_self_iff F ρFull).mp hρFullFixed
  refine ⟨ρ, ?_, hρFixed⟩
  intro k
  have hρBlock : (directSumDiagonalCompression ρFull k).PosDef := by
    rw [directSumDiagonalCompression_apply]
    apply hρFull.submatrix
    intro a b hab
    simpa using hab
  rw [hρFullEq, directSumDiagonalCompression_embedding] at hρBlock
  exact hρBlock

end Matrix

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
