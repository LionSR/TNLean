/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairEffectElimination
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Finite coordinates for a finite family of pair sources

A finite family of vectors in an algebraic tensor product is supported on the
tensor product of two finite-dimensional subspaces. Orthonormal coordinates in
these subspaces give isometric inclusions and preserve every source vector exactly.
The ambient spaces need not be finite-dimensional, and zero coordinate dimensions
are allowed.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, common private source spaces at lines 253–267 and the
subsequent finite Schmidt decompositions at lines 279–299.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-commonsource-finitepair-pairsource.exists_finite_coordinates
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.exists_finite_coordinates
-/

noncomputable section

open scoped TensorProduct

namespace TNLean.PEPS.PairEffect.PairSource

/-- A finite family of algebraic pair-source vectors admits exact finite coordinates
in the same endpoint spaces for every member of the family. The inclusions are
isometric, so the coordinates preserve normalization.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–299. -/
theorem exists_finite_coordinates {ι : Type} [Finite ι] (U V : HSpace)
    (η : ι → U ⊗[ℂ] V) :
    ∃ a b : ℕ, ∃ f : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] U,
      ∃ g : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] V,
      ∃ η₀ : ι → EuclideanSpace ℂ (Fin a) ⊗[ℂ] EuclideanSpace ℂ (Fin b),
        (∀ ξ, TensorProduct.mapIsometry f g (η₀ ξ) = η ξ) ∧
        (∀ ξ, ‖η₀ ξ‖ = ‖η ξ‖) := by
  obtain ⟨U₀, V₀, hU, hV, hη⟩ :=
    TensorProduct.exists_finite_submodule_of_setFinite (Set.range η) (Set.finite_range η)
  choose ζ hζ using fun ξ ↦ hη (Set.mem_range_self ξ)
  let eU := (stdOrthonormalBasis ℂ U₀).repr
  let eV := (stdOrthonormalBasis ℂ V₀).repr
  refine ⟨_, _, U₀.subtypeₗᵢ.comp eU.symm.toLinearIsometry,
    V₀.subtypeₗᵢ.comp eV.symm.toLinearIsometry,
    fun ξ ↦ TensorProduct.mapIsometry eU.toLinearIsometry eV.toLinearIsometry (ζ ξ), ?_, ?_⟩
  · simpa [TensorProduct.mapIsometry_apply, TensorProduct.map_map,
      LinearIsometry.comp, LinearIsometryEquiv.toLinearIsometry,
      LinearMap.comp_assoc, TensorProduct.mapIncl] using hζ
  · exact fun ξ ↦ (TensorProduct.mapIsometry eU.toLinearIsometry eV.toLinearIsometry).norm_map
      (ζ ξ) |>.trans (((TensorProduct.mapInclIsometry U₀ V₀).norm_map (ζ ξ)).symm.trans
        (congrArg norm (hζ ξ)))

end TNLean.PEPS.PairEffect.PairSource
