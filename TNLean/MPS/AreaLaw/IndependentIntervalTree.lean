/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IndependentIntervalOperation
import TNLean.MPS.AreaLaw.AdjacentIntervalMergeMeasurable
import Mathlib.Logic.Function.DependsOn

/-!
# Measurability for interval operations with independent coordinates

A jointly Borel parent construction gives Borel retained projections in
the existing balanced recursion. Each retained space uses only coordinates
of intervals no longer than itself. The coordinate may contain an entire
finite sequence of samples. This is a conditional analytic auxiliary for
ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. Parent
measurability is an explicit hypothesis; no sampling-success estimate is
assumed or concluded.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Joint parent measurability gives the actual balanced tree's Borel
projection and dependence only on no longer interval coordinates.
The parent hypothesis concerns its actual composition with a measurable
candidate, not a selected successful event. Conditional auxiliary for
ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem measurable_projectionMatrix_and_dependsOn_independentIntervalTree
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
    (hwidth : 1 ≤ width) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := fun U ↦ balancedIntervalSpace
      (independentIntervalOperation parent U) width hwidth p r
    Measurable (fun U ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S U).starProjection) ∧
    DependsOn S {J : Fin (L + 1) × Fin (L + 1) | J.2.val - J.1.val ≤ r - p} := by
  classical
  intro retained
  let S := fun (p r : ℕ) (U : (∀ I, Ω I)) ↦
    balancedIntervalSpace (independentIntervalOperation parent U) width hwidth p r
  suffices ∀ n p r : ℕ, r - p = n → p ≤ r → r ≤ L →
      Measurable (fun U ↦ (Matrix.toEuclideanCLM
        (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S p r U).starProjection) ∧
      DependsOn (S p r)
        {J : Fin (L + 1) × Fin (L + 1) | J.2.val - J.1.val ≤ r - p} from
    this (r - p) p r rfl hpr hrL
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen hpr hrL
    by_cases hshort : r - p ≤ width
    · have hS : S p r = fun _ ↦ ⊤ := by
        funext U
        exact balancedIntervalSpace_of_short _ hwidth hshort
      constructor
      · rw [hS]
        exact measurable_const
      · intro U V _hcoords
        rw [hS]
    · let k := p + (r - p) / 2
      have hpk : p ≤ k := by dsimp only [k]; omega
      have hkr : k ≤ r := by dsimp only [k]; omega
      have hlong : width < r - p := by omega
      obtain ⟨hleft, hleft_dep⟩ := ih (k - p) (by dsimp only [k]; omega)
        p k rfl hpk (hkr.trans hrL)
      obtain ⟨hright, hright_dep⟩ := ih (r - k) (by dsimp only [k]; omega)
        k r rfl hkr hrL
      let J : LongIntervalIndex L width := ⟨(p, r), hpr, hrL, hlong⟩
      let coord := LongIntervalIndex.coordinate J
      let W := fun U ↦ adjacentIntervalMerge L q p k r hpk hkr (S p k U) (S k r U)
      have hW := measurable_projectionMatrix_adjacentIntervalMerge hpk hkr
        (S p k) (S k r) hleft hright
      have hnode := hparent J W hW
      have hsample := hnode.comp (measurable_id.prodMk (measurable_pi_apply coord))
      have hvalue (U : (∀ I, Ω I)) : S p r U =
          parent J (W U) (U coord) := by
        change balancedIntervalSpace
          (independentIntervalOperation parent U) width hwidth p r = _
        rw [balancedIntervalSpace, dite_eq_right hshort]
        simp only [independentIntervalOperation, dite_eq_left hrL, dite_eq_left hlong]
        rfl
      constructor
      · simpa only [Function.comp_def, id_eq, hvalue] using hsample
      · intro U V hcoords
        have hleft_eq : S p k U = S p k V := hleft_dep fun I hI ↦
          hcoords I (hI.trans (by omega : k - p ≤ r - p))
        have hright_eq : S k r U = S k r V := hright_dep fun I hI ↦
          hcoords I (hI.trans (by omega : r - k ≤ r - p))
        have hcoord : U coord = V coord := hcoords coord (by
          change r - p ≤ r - p
          exact le_rfl)
        have hW_eq : W U = W V := by
          dsimp only [W]
          rw [hleft_eq, hright_eq]
        rw [hvalue U, hvalue V, hW_eq, hcoord]

end TNLean.MPS.AreaLaw
