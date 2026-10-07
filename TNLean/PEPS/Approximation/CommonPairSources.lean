/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyWord
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Common spaces for a finite family of pair sources

For each endpoint of a pair source, the orthogonal sum of its branch spaces
provides a common ambient space. Coordinate inclusions are isometric and
coordinate projections are contractions. Tensoring the two inclusions preserves
the source norm, and the corresponding projections recover the original vector.
No finite-dimensionality or completeness assumption is needed.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, the common private slot spaces at lines 253–267.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-commonsource-pairspaces-pairsource.commonspace
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.commonSpace

Provenance-ID: 8769-commonsource-pairspaces-pairsource.commoninclusion
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.commonInclusion

Provenance-ID: 8769-commonsource-pairspaces-pairsource.commonprojection
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.commonProjection

Provenance-ID: 8769-commonsource-pairspaces-pairsource.commonprojection_commoninclusion
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.commonProjection_commonInclusion

Provenance-ID: 8769-commonsource-pairspaces-pairsource.norm_commonprojection_le
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.norm_commonProjection_le

Provenance-ID: 8769-commonsource-pairspaces-pairsource.commonvector
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.commonVector

Provenance-ID: 8769-commonsource-pairspaces-pairsource.norm_commonvector
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.norm_commonVector

Provenance-ID: 8769-commonsource-pairspaces-pairsource.mapl_commonprojection_commonvector
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.mapL_commonProjection_commonVector
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.PairSource

variable {ι : Type} [Fintype ι]

/-- The finite orthogonal sum of the branch spaces at one endpoint of a source.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
def commonSpace (U : ι → HSpace) : HSpace := HSpace.of (PiLp 2 fun ξ ↦ U ξ)

/-- The isometric inclusion of one branch's endpoint space into the common space.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–260. -/
def commonInclusion (U : ι → HSpace) (ξ : ι) : U ξ →ₗᵢ[ℂ] commonSpace U := by
  classical
  exact
    { toLinearMap := (WithLp.linearEquiv 2 ℂ (∀ ξ, U ξ)).symm.toLinearMap.comp
        (LinearMap.single ℂ (fun ξ ↦ U ξ) ξ)
      norm_map' := fun x ↦ PiLp.norm_single 2 (fun ξ ↦ U ξ) ξ x }

/-- The contractive coordinate projection onto a branch's endpoint space.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 260–267. -/
def commonProjection (U : ι → HSpace) (ξ : ι) : commonSpace U →L[ℂ] U ξ :=
  PiLp.proj 2 (fun ξ ↦ U ξ) ξ

/-- Projecting the included branch vector recovers it exactly.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 260–267. -/
@[simp] theorem commonProjection_commonInclusion (U : ι → HSpace) (ξ : ι) (x : U ξ) :
    commonProjection U ξ (commonInclusion U ξ x) = x := by
  classical
  exact PiLp.single_eq_same (β := fun ξ ↦ (U ξ).carrier) 2 ξ x

/-- Every coordinate projection has operator norm at most one, including a zero
branch space. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 260–267. -/
theorem norm_commonProjection_le (U : ι → HSpace) (ξ : ι) :
    ‖commonProjection U ξ‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one ?_
  exact fun x ↦ (PiLp.norm_apply_le x ξ).trans_eq (one_mul ‖x‖).symm

/-- Embed a branch source into the common spaces at its two endpoints.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
def commonVector (U V : ι → HSpace) (η : ∀ ξ, U ξ ⊗[ℂ] V ξ) (ξ : ι) :
    commonSpace U ⊗[ℂ] commonSpace V :=
  TensorProduct.mapIsometry (commonInclusion U ξ) (commonInclusion V ξ) (η ξ)

/-- Embedding into the common spaces preserves the source norm, hence normalization.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–260. -/
@[simp] theorem norm_commonVector (U V : ι → HSpace) (η : ∀ ξ, U ξ ⊗[ℂ] V ξ) (ξ : ι) :
    ‖commonVector U V η ξ‖ = ‖η ξ‖ :=
  (TensorProduct.mapIsometry (commonInclusion U ξ) (commonInclusion V ξ)).norm_map _

/-- Projecting both halves of the embedded source recovers its original vector.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 260–267. -/
@[simp] theorem mapL_commonProjection_commonVector (U V : ι → HSpace)
    (η : ∀ ξ, U ξ ⊗[ℂ] V ξ) (ξ : ι) :
    TensorProduct.mapL (commonProjection U ξ) (commonProjection V ξ)
      (commonVector U V η ξ) = η ξ := by
  unfold commonVector
  induction η ξ using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end TNLean.PEPS.PairEffect.PairSource
