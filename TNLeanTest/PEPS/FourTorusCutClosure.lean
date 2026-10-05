/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutClosureReconstruction
import TNLean.PEPS.RegularMatrixEquiv
import TNLean.Algebra.SemiRegularGroupAlgebra

/-! # Actual four-cut closure reconstruction regressions -/

open TNLean.PEPS
open scoped BigOperators Matrix

noncomputable section

-- Independent tensors and eight independent matching representations, with only
-- finite group, finite alphabets, semi-regularity and the local G-injective clauses.
example {G V Phys : Type*} [Group G] [Finite G] [Fintype V] [DecidableEq V] [Finite Phys]
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v, IsGInjective (torusMatchedLegRep Uh Uv v) (siteMap (a v))) :
    fourTorusCutSpace a = matchedCommutingClosureSpan Uh Uv a :=
  fourTorusCutSpace_eq_matchedCommutingClosureSpan Uh Uv hU a ha

-- Genuine nonregular input: Unit's regular representation has dimension one;
-- this representation has trivial multiplicity two.
private def nonregularBond : Unit →* Matrix (Fin 2) (Fin 2) ℂ := 1

private theorem nonregularBond_semiRegular : Representation.IsSemiRegular
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp nonregularBond) := by
  apply Representation.isSemiRegular_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have h := congrArg (fun L : Module.End ℂ (Fin 2 → ℂ) ↦ L (fun _ ↦ 1) 0) hc
  simpa [nonregularBond] using h

example : Fintype.card (Fin 2) ≠ Fintype.card Unit := by decide

example :
    fourTorusCutSpace (torusMatchedAveragingSites
      (fun _ : TorusVertex 2 2 ↦ nonregularBond) (fun _ ↦ nonregularBond)) =
      matchedCommutingClosureSpan (fun _ ↦ nonregularBond) (fun _ ↦ nonregularBond)
        (torusMatchedAveragingSites (fun _ ↦ nonregularBond) (fun _ ↦ nonregularBond)) :=
  fourTorusCutSpace_matchedAveraging_eq_commutingClosureSpan _ _
    ⟨fun _ ↦ nonregularBond_semiRegular, fun _ ↦ nonregularBond_semiRegular⟩

-- A nonflat bare bond product cannot satisfy all four canonical cut conditions:
-- extraction gives coefficient one, while the cut constraint forces zero.
example {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (p : TorusBondLabels 2 2 G) (hp : ¬IsTorusBondFlat p) :
    torusRepresentationBondProduct Uh Uv p ∉
      fourTorusCutSpace (torusMatchedAveragingSites Uh Uv) := by
  intro hmem
  have hz := torusBondCoefficientExtraction_eq_zero_of_mem_fourTorusCutSpace_not_flat
    Uh Uv hU p hp hmem
  have hbad : (1 : ℂ) = 0 := by
    simpa only [torusBondCoefficientExtraction_bondProduct Uh Uv hU, ite_true] using hz
  exact one_ne_zero hbad

-- A concrete nonabelian seam obstruction is retained by the exact eight-bond geometry.
example : ¬IsTorusBondFlat (torusBondClosureLabels (width := 2) (height := 2)
    (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2)) := by
  rw [isTorusBondFlat_closure_iff]
  change ¬(Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 =
    Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
  decide

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.fourTorusCutSpace_eq_matchedCommutingClosureSpan' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.fourTorusCutSpace_eq_matchedCommutingClosureSpan

/--
info: 'TNLean.PEPS.eq_sum_extracted_bondProducts_of_mem_fourTorusCutSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.eq_sum_extracted_bondProducts_of_mem_fourTorusCutSpace

/--
info: 'TNLean.PEPS.torusBondCoefficientExtraction_eq_zero_of_mem_fourTorusCutSpace_not_flat'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.torusBondCoefficientExtraction_eq_zero_of_mem_fourTorusCutSpace_not_flat
