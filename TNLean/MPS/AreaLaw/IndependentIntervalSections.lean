/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IndependentIntervalTree
import TNLean.MPS.AreaLaw.BalancedIntervalFailure

/-!
# Actual coordinate sections of independent interval operations

Changing a parent's coordinate leaves its shorter child spaces unchanged.
The resulting parent is the prescribed map of those same adjacent child
spaces and that fresh coordinate. These statements concern the existing
balanced interval recursion. Joint parent measurability is an explicit
analytic hypothesis. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable
  {L q width : ℕ} {Ω : Fin (L + 1) × Fin (L + 1) → Type*}
  [∀ J, MeasurableSpace (Ω J)]
  (parent : ∀ J : LongIntervalIndex L width,
    Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) →
    Ω (LongIntervalIndex.coordinate J) →
    Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
  (hparent : ∀ (J : LongIntervalIndex L width)
    (W : (∀ I, Ω I) →
    Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))),
    Measurable (fun U ↦ (Matrix.toEuclideanCLM
    (n := interval L J.val.1 J.val.2 → Fin q) (𝕜 := ℂ)).symm (W U).starProjection) →
    Measurable (fun x : (∀ I, Ω I) × Ω (LongIntervalIndex.coordinate J) ↦
    (Matrix.toEuclideanCLM (n := interval L J.val.1 J.val.2 → Fin q) (𝕜 := ℂ)).symm
      (parent J (W x.1) x.2).starProjection))
  (hwidth : 1 ≤ width)

include hparent

/-- A strictly longer coordinate cannot affect the actual retained space.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem independentIntervalTree_update_of_length_lt
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L)
    (U : ∀ I, Ω I) (J : Fin (L + 1) × Fin (L + 1))
    (v : Ω J) (hlong : r - p < J.2.val - J.1.val) :
    balancedIntervalSpace
      (independentIntervalOperation parent (Function.update U J v)) width hwidth p r =
    balancedIntervalSpace (independentIntervalOperation parent U) width hwidth p r := by
  classical
  apply (measurable_projectionMatrix_and_dependsOn_independentIntervalTree
    parent hparent hwidth p r hpr hrL).2
  intro I hI
  have hne : I ≠ J := by
    intro heq
    subst I
    exact (not_le_of_gt hlong) hI
  exact Function.update_of_ne hne v U

/-- Updating the parent's own coordinate gives the same actual parent map
of its unchanged two children. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817. -/
theorem independentIntervalTree_update_parent
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) (hlong : width < r - p) :
    let k := p + (r - p) / 2
    let hpk : p ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    let J : LongIntervalIndex L width := ⟨(p, r), hpr, hrL, hlong⟩
    ∀ (U : ∀ I, Ω I) (v : Ω (LongIntervalIndex.coordinate J)),
      balancedIntervalSpace
        (independentIntervalOperation parent
          (Function.update U (LongIntervalIndex.coordinate J) v)) width hwidth p r =
      parent J (adjacentIntervalMerge L q p k r hpk hkr
        (balancedIntervalSpace (independentIntervalOperation parent U) width hwidth p k)
        (balancedIntervalSpace (independentIntervalOperation parent U) width hwidth k r)) v := by
  classical
  intro k hpk hkr J U v
  have hleft := independentIntervalTree_update_of_length_lt parent hparent hwidth
    p k hpk (hkr.trans hrL) U (LongIntervalIndex.coordinate J) v
    (by dsimp only [k, J, LongIntervalIndex.coordinate]; omega)
  have hright := independentIntervalTree_update_of_length_lt parent hparent hwidth
    k r hkr hrL U (LongIntervalIndex.coordinate J) v
    (by dsimp only [k, J, LongIntervalIndex.coordinate]; omega)
  rw [balancedIntervalSpace, dite_eq_right (Nat.not_le.mpr hlong)]
  simp only [independentIntervalOperation, dite_eq_left hrL, dite_eq_left hlong]
  rw [hleft, hright, Function.update_self]

/-- The actual interval viability event is Borel for a fixed global target
and its full exterior. Parent measurability is an explicit analytic
hypothesis. Supporting ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem measurableSet_isViable_independentIntervalTree
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    MeasurableSet {U : ∀ I, Ω I | Submodule.IsViable delta
      (balancedIntervalSpace (independentIntervalOperation parent U) width hwidth p r)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)} :=
  Submodule.measurableSet_isViable_of_measurable_projectionMatrix
    (σ := interval L p r → Fin q) (β := ↥((interval L p r)ᶜ) → Fin q)
    (fun U ↦ balancedIntervalSpace (independentIntervalOperation parent U) width hwidth p r)
    (measurable_projectionMatrix_and_dependsOn_independentIntervalTree
      parent hparent hwidth p r hpr hrL).1 delta _

/-- The guarded failure event of the actual parent and its children is
Borel for the same global target. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817. -/
theorem measurableSet_guardedIntervalFailure_independentIntervalTree
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    MeasurableSet (guardedIntervalFailure
      (independentIntervalOperation parent) width hwidth P (p, r)) := by
  intro P
  dsimp only [guardedIntervalFailure]
  have hleft := measurableSet_isViable_independentIntervalTree parent hparent hwidth G
    delta p (p + (r - p) / 2) (by omega) (by omega)
  have hright := measurableSet_isViable_independentIntervalTree parent hparent hwidth G
    delta (p + (r - p) / 2) r (by omega) hrL
  have hnode := measurableSet_isViable_independentIntervalTree parent hparent hwidth G
    delta p r hpr hrL
  exact hleft.inter (hright.inter hnode.compl)

end TNLean.MPS.AreaLaw
