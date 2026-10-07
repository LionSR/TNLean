/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.DependentRegionOperatorLift
import TNLean.PEPS.ParentHamiltonian.CoordinateRangeProjector

/-!
# Subspaces supported on a region

For a subspace \(S\) on a region \(R\), its cylinder consists of the global vectors
whose every complementary slice belongs to \(S\). Its orthogonal projector is the
identity extension of the orthogonal projector onto \(S\).

These are the cylinders used in the orthogonalization argument of the polynomial
PEPS approximation manuscript, `03-patches.tex`, lines 563–603 at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, 03-patches.tex.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex
sec:patches, prop:patch, eq:patch-cylinder-projection; independently formalized;
no upstream Lean proof text reused.
Manuscript commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript passage: lines 563–603.

Provenance-ID: orthogonalization8767-tnlean.peps.dependentregioncylinder
Downstream declaration: TNLean.PEPS.dependentRegionCylinder

Provenance-ID: orthogonalization8767-tnlean.peps.mem_dependentregioncylinder
Downstream declaration: TNLean.PEPS.mem_dependentRegionCylinder

Provenance-ID: orthogonalization8767-tnlean.peps.range_dependentregionoperatorlift
Downstream declaration: TNLean.PEPS.range_dependentRegionOperatorLift

Provenance-ID: orthogonalization8767-tnlean.peps.coordinaterangeprojector_dependentregioncylinder
Downstream declaration: TNLean.PEPS.coordinateRangeProjector_dependentRegionCylinder

Provenance-ID: orthogonalization8767-tnlean.peps.dependentregioncylinder_bot
Downstream declaration: TNLean.PEPS.dependentRegionCylinder_bot

Provenance-ID: orthogonalization8767-tnlean.peps.dependentregioncylinder_sup
Downstream declaration: TNLean.PEPS.dependentRegionCylinder_sup

Provenance-ID: orthogonalization8767-tnlean.peps.dependentregioncylinder_isup
Downstream declaration: TNLean.PEPS.dependentRegionCylinder_iSup

Provenance-ID: orthogonalization8767-tnlean.peps.dependentregioncylinder_subregion
Downstream declaration: TNLean.PEPS.dependentRegionCylinder_subregion

Provenance-ID: orthogonalization8767-tnlean.peps.dependentregioncylinder_map
Downstream declaration: TNLean.PEPS.dependentRegionCylinder_map

-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*}

/-- The cylinder over a regional subspace: every complementary slice belongs to it. -/
def dependentRegionCylinder (R : Finset V)
    (S : Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ)) :
    Submodule ℂ (((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ) :=
  ⨅ τ, S.comap (dependentRegionSlice R τ)

/-- Cylinder membership is membership of every complementary slice. -/
@[simp]
theorem mem_dependentRegionCylinder (R : Finset V)
    (S : Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ))
    (x : ((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ) :
    x ∈ dependentRegionCylinder R S ↔ ∀ τ, dependentRegionSlice R τ x ∈ S := by
  simp [dependentRegionCylinder]

/-- Extending a regional linear map by the identity extends its range to a cylinder. -/
theorem range_dependentRegionOperatorLift [∀ v, Fintype (Out v)] (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    (dependentRegionOperatorLift R K).mulVecLin.range =
      dependentRegionCylinder R K.mulVecLin.range := by
  classical
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine (mem_dependentRegionCylinder R _ _).mpr fun τ => ⟨dependentRegionSlice R τ y, ?_⟩
    exact (dependentRegionSlice_mulVec_dependentRegionOperatorLift R K y τ).symm
  · intro hx
    have h := (mem_dependentRegionCylinder R _ x).mp hx
    choose y hy using h
    let z := fun η => y ((dependentRegionConfigEquiv R η).2)
      ((dependentRegionConfigEquiv R η).1)
    refine ⟨z, ?_⟩
    funext η
    obtain ⟨⟨α, τ⟩, rfl⟩ := (dependentRegionConfigEquiv R).symm.surjective η
    have hz : dependentRegionSlice R τ z = y τ := by
      funext β
      exact congrArg (fun p => y p.2 p.1)
        ((dependentRegionConfigEquiv R).apply_symm_apply (β, τ))
    have he := dependentRegionSlice_mulVec_dependentRegionOperatorLift R K z τ
    rw [hz] at he
    exact congrFun (he.trans (hy τ)) α

/-- The cylinder projector is the identity extension of the inside projector. -/
theorem coordinateRangeProjector_dependentRegionCylinder [∀ v, Fintype (Out v)]
    (R : Finset V)
    (S : Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ)) :
    coordinateRangeProjector (dependentRegionCylinder R S) =
      dependentRegionOperatorLift R (coordinateRangeProjector S) := by
  symm
  apply eq_coordinateRangeProjector_of_range
    (dependentRegionOperatorLift_isStarProjection R _ (coordinateRangeProjector_isStarProjection S))
  rw [range_dependentRegionOperatorLift, range_coordinateRangeProjector]

/-- A zero inside subspace has a zero cylinder, even when the complement is empty. -/
@[simp]
theorem dependentRegionCylinder_bot (R : Finset V) :
    dependentRegionCylinder (Out := Out) R ⊥ = ⊥ := by
  ext x
  simp only [mem_dependentRegionCylinder, Submodule.mem_bot]
  constructor
  · intro h
    funext η
    obtain ⟨⟨α, τ⟩, rfl⟩ := (dependentRegionConfigEquiv R).symm.surjective η
    exact congrFun (h τ) α
  · rintro rfl
    simp

/-- Cylinders preserve sums of inside subspaces. -/
theorem dependentRegionCylinder_sup (R : Finset V)
    (S T : Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ)) :
    dependentRegionCylinder R (S ⊔ T) =
      dependentRegionCylinder R S ⊔ dependentRegionCylinder R T := by
  classical
  apply le_antisymm
  · intro x hx
    have h := (mem_dependentRegionCylinder R _ x).mp hx
    have h' : ∀ τ, ∃ s ∈ S, ∃ t ∈ T, s + t = dependentRegionSlice R τ x :=
      fun τ => Submodule.mem_sup.mp (h τ)
    choose s hs t ht hst using h'
    let a := fun η => s ((dependentRegionConfigEquiv R η).2)
      ((dependentRegionConfigEquiv R η).1)
    let b := fun η => t ((dependentRegionConfigEquiv R η).2)
      ((dependentRegionConfigEquiv R η).1)
    have ha : ∀ τ, dependentRegionSlice R τ a = s τ := by
      intro τ
      funext α
      exact congrArg (fun p => s p.2 p.1)
        ((dependentRegionConfigEquiv R).apply_symm_apply (α, τ))
    have hb : ∀ τ, dependentRegionSlice R τ b = t τ := by
      intro τ
      funext α
      exact congrArg (fun p => t p.2 p.1)
        ((dependentRegionConfigEquiv R).apply_symm_apply (α, τ))
    refine Submodule.mem_sup.mpr ⟨a, ?_, b, ?_, ?_⟩
    · exact (mem_dependentRegionCylinder R S a).mpr fun τ => (ha τ).symm ▸ hs τ
    · exact (mem_dependentRegionCylinder R T b).mpr fun τ => (hb τ).symm ▸ ht τ
    · funext η
      obtain ⟨⟨α, τ⟩, rfl⟩ := (dependentRegionConfigEquiv R).symm.surjective η
      have hsum : dependentRegionSlice R τ (a + b) = dependentRegionSlice R τ x := by
        rw [map_add, ha, hb, hst]
      exact congrFun hsum α
  · apply sup_le
    · intro x hx
      exact (mem_dependentRegionCylinder R _ x).mpr fun τ =>
        (show S ≤ S ⊔ T from le_sup_left) ((mem_dependentRegionCylinder R S x).mp hx τ)
    · intro x hx
      exact (mem_dependentRegionCylinder R _ x).mpr fun τ =>
        (show T ≤ S ⊔ T from le_sup_right) ((mem_dependentRegionCylinder R T x).mp hx τ)

/-- Cylinders preserve finite suprema of inside subspaces. -/
theorem dependentRegionCylinder_iSup {ι : Type*} [Finite ι] (R : Finset V)
    (S : ι → Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ)) :
    dependentRegionCylinder R (⨆ i, S i) = ⨆ i, dependentRegionCylinder R (S i) := by
  let := Fintype.ofFinite ι
  let f : SupBotHom (Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ))
      (Submodule ℂ (((w : {w : V // w ∈ Finset.univ}) → Out w.1) → ℂ)) :=
    { toFun := dependentRegionCylinder R
      map_bot' := dependentRegionCylinder_bot R
      map_sup' := dependentRegionCylinder_sup R }
  change f (⨆ i, S i) = ⨆ i, f (S i)
  simpa only [Finset.sup_univ_eq_iSup, Function.comp_def] using
    map_finset_sup f Finset.univ S

/-- A cylinder over a smaller region is also a cylinder over any containing region. -/
theorem dependentRegionCylinder_subregion [∀ v, Fintype (Out v)]
    (R U : Finset V) (hRU : R ⊆ U)
    (S : Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ)) :
    dependentRegionCylinder U
        (dependentSubregionOperatorLift R U hRU (coordinateRangeProjector S)).mulVecLin.range =
      dependentRegionCylinder R S := by
  rw [← range_dependentRegionOperatorLift, dependentRegionOperatorLift_subregion,
    range_dependentRegionOperatorLift, range_coordinateRangeProjector]

/-- The cylinder of a projected image is the corresponding image of the cylinder. -/
theorem dependentRegionCylinder_map [∀ v, Fintype (Out v)] (R : Finset V)
    (S : Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ))
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    dependentRegionCylinder R (S.map K.mulVecLin) =
      (dependentRegionCylinder R S).map (dependentRegionOperatorLift R K).mulVecLin := by
  nth_rw 1 [← range_coordinateRangeProjector S]
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul,
    ← range_dependentRegionOperatorLift, dependentRegionOperatorLift_mul,
    Matrix.mulVecLin_mul, LinearMap.range_comp,
    range_dependentRegionOperatorLift, range_coordinateRangeProjector]

end TNLean.PEPS
