/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalSamplingOperation
import TNLean.MPS.AreaLaw.IndependentIntervalTree

/-!
# Joint measurability and coordinate dependence of the actual sampled tree

The output is the existing balanced interval space for the canonical
sampled operation. Its actual orthogonal projection is jointly Borel in
all interval choices. Its subspace depends only on coordinates whose
interval lengths do not exceed its own. In particular, the two shorter
children do not use the fresh coordinate of their parent.

Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817,
and Figure `fig:merge-prime`, lines 1668–1670. These are measurability
and dependence statements, not an adaptive probability bound.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem sampled_tree_measurable_and_dependsOn {L q width : ℕ}
    (D s : ℕ) (hwidth : 1 ≤ width) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := fun U ↦ balancedIntervalSpace
      (canonicalIntervalSamplingOperation D s N F xi U) width hwidth p r
    Measurable (fun U ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S U).starProjection) ∧
    DependsOn S {J : Fin (L + 1) × Fin (L + 1) | J.2.val - J.1.val ≤ r - p} := by
  unfold canonicalIntervalSamplingOperation
  exact measurable_projectionMatrix_and_dependsOn_independentIntervalTree
    (Ω := fun J ↦ Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s
      (F J) xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim
      D s (F J) xi W hW) hwidth p r hpr hrL

/-- The actual balanced sampled tree has a jointly Borel ambient projection.
The family and parameters are fixed before all interval coordinates.
Source: ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem measurable_projectionMatrix_canonicalIntervalSamplingTree {L q width : ℕ}
    (D s : ℕ) (hwidth : 1 ≤ width) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    Measurable (fun U : IntervalSamplingChoices L q ↦
      (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
          width hwidth p r).starProjection) :=
  (sampled_tree_measurable_and_dependsOn D s hwidth N F xi p r hpr hrL).1

/-- An actual retained interval space uses no sampling coordinate longer
than itself. This uses Mathlib's dependence predicate and the existing
balanced interval space, without defining a second tree.
Source: ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem dependsOn_canonicalIntervalSamplingTree {L q width : ℕ}
    (D s : ℕ) (hwidth : 1 ≤ width) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    DependsOn (fun U : IntervalSamplingChoices L q ↦
      balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
        width hwidth p r)
      {J : Fin (L + 1) × Fin (L + 1) | J.2.val - J.1.val ≤ r - p} :=
  (sampled_tree_measurable_and_dependsOn D s hwidth N F xi p r hpr hrL).2

/-- Replacing any strictly longer interval coordinate leaves the actual
retained space unchanged. In particular this applies to a parent's fresh
coordinate when considering either shorter child. Source: ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem canonicalIntervalSamplingTree_update_of_length_lt {L q width : ℕ}
    (D s : ℕ) (hwidth : 1 ≤ width) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L)
    (U : IntervalSamplingChoices L q) (J : Fin (L + 1) × Fin (L + 1))
    (v : Matrix.rankUnitaryProduct (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (hlong : r - p < J.2.val - J.1.val) :
    balancedIntervalSpace
      (canonicalIntervalSamplingOperation D s N F xi (Function.update U J v)) width hwidth p r =
    balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U) width hwidth p r := by
  classical
  apply dependsOn_canonicalIntervalSamplingTree D s hwidth N F xi p r hpr hrL
  intro I hI
  have hne : I ≠ J := by
    intro heq
    subst I
    exact (not_le_of_gt hlong) hI
  exact Function.update_of_ne hne v U

/-- The true viability event of the actual sampled root is Borel for the
same specified global target and the whole interval exterior. No measurable
comparison space or separate event is substituted. Source: ALVV,
arXiv:1602.08828v2, lines 1777–1817. -/
theorem measurableSet_isViable_canonicalIntervalSamplingTree {L q width : ℕ}
    (D s : ℕ) (hwidth : 1 ≤ width) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    MeasurableSet {U : IntervalSamplingChoices L q | Submodule.IsViable delta
      (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
        width hwidth p r)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)} :=
  Submodule.measurableSet_isViable_of_measurable_projectionMatrix
    (σ := interval L p r → Fin q) (β := ↥((interval L p r)ᶜ) → Fin q)
    (fun U ↦ balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
      width hwidth p r)
    (measurable_projectionMatrix_canonicalIntervalSamplingTree D s hwidth N F xi p r hpr hrL)
    delta _

end TNLean.MPS.AreaLaw
