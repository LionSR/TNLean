/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutBondSupport
import TNLean.PEPS.PhysicalProductFamilyRangeSupport

/-!
# Actual four-cut vectors lie in the bond representation span

The uncut bonds of the four canonical cuts cover all eight native bonds.
The resulting one-bond support conditions force the entire physical vector
into the product of the representation-matrix ranges. This proves, rather
than assumes, the existence of a coherent bond-label expansion.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height

/-- Every actual canonical cut vector has representation-matrix support on
each uncut bond, for arbitrary correlated boundary tensors. -/
theorem torusPhysicalBondSlice_mem_range_of_mem_torusCutSpace
    (Uh Uv : X → G →* Matrix V V ℂ) (c : ZMod width) (r : ZMod height)
    (e : X × Bool)
    (he : if e.2 then e.1.2 + 1 ≠ r else e.1.1 + 1 ≠ c)
    (τ : (X × Bool) → V × V)
    {ψ : (X → V × V × V × V) → ℂ}
    (hψ : ψ ∈ torusCutSpace (torusMatchedAveragingSites Uh Uv) c r) :
    torusPhysicalBondSlice e τ ψ ∈
      (Matrix.mulVecLin (representationBondMatrix (torusBondRepresentation Uh Uv e))).range := by
  classical
  let S := (Matrix.mulVecLin
    (representationBondMatrix (torusBondRepresentation Uh Uv e))).range.comap
    (torusPhysicalBondSlice e τ)
  have hle : torusCutSpace (torusMatchedAveragingSites Uh Uv) c r ≤ S := by
    rw [torusCutSpace_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨η, rfl⟩
    change torusPhysicalBondSlice e τ
      (torusCutMap (torusMatchedAveragingSites Uh Uv) c r (Pi.single η 1)) ∈
      (Matrix.mulVecLin (representationBondMatrix (torusBondRepresentation Uh Uv e))).range
    have hnet : torusCutMap (torusMatchedAveragingSites Uh Uv) c r (Pi.single η 1) =
        fun σ ↦ torusBondNetwork
          (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
            t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
          (fun v ↦ if v.1 + 1 = c then torusCutHorizontalUnit η v else 1)
          (fun v ↦ if v.2 + 1 = r then torusCutVerticalUnit η v else 1) :=
      funext (torusCutMap_single_eq_bondNetwork _ c r η)
    rw [hnet]
    apply torusPhysicalBondSlice_averagingSite_mem_range
    cases hb : e.2 <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
  exact hle hψ

/-- Simultaneous membership in the four literal two-by-two cut spaces forces
full bond-product support. No semi-regularity is needed for this support step. -/
theorem torusBondRegrouping_mem_product_range_of_mem_fourTorusCutSpace
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    {ψ : (TorusVertex 2 2 → V × V × V × V) → ℂ}
    (hψ : ψ ∈ fourTorusCutSpace (torusMatchedAveragingSites Uh Uv)) :
    torusBondRegrouping ψ ∈
      (physicalProductFamilyMap
        (fun e : TorusVertex 2 2 × Bool ↦
          representationBondMatrix (torusBondRepresentation Uh Uv e))).range := by
  classical
  apply (mem_range_physicalProductFamilyMap_iff _ _).mpr
  intro e τ
  change torusPhysicalBondSlice e τ ψ ∈ _
  have hcut : ψ ∈ torusCutSpace (torusMatchedAveragingSites Uh Uv) e.1.1 e.1.2 :=
    (mem_torusCutSpace_iff _ _ _ _).mpr ((mem_fourTorusCutSpace_iff _ _).mp hψ e.1.1 e.1.2)
  apply torusPhysicalBondSlice_mem_range_of_mem_torusCutSpace Uh Uv _ _ e _ τ hcut
  cases e.2 <;> simp

/-- Every vector in the actual four-cut intersection has a coherent expansion
in the complete bond-label family. This is the missing existence premise
needed before trace-dual coefficient comparison may be applied. -/
theorem exists_bondCoefficients_of_mem_fourTorusCutSpace
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    {ψ : (TorusVertex 2 2 → V × V × V × V) → ℂ}
    (hψ : ψ ∈ fourTorusCutSpace (torusMatchedAveragingSites Uh Uv)) :
    ∃ c : (TorusVertex 2 2 × Bool → G) → ℂ,
      ψ = ∑ q : TorusVertex 2 2 × Bool → G, c q •
        torusRepresentationBondProduct Uh Uv
          (fun v ↦ q (v, false), fun v ↦ q (v, true)) := by
  obtain ⟨c, hc⟩ := torusBondRegrouping_mem_product_range_of_mem_fourTorusCutSpace Uh Uv hψ
  refine ⟨c, ?_⟩
  apply torusBondRegrouping.injective
  rw [map_sum]
  simp_rw [map_smul]
  rw [← hc]
  funext β
  simp only [physicalProductFamilyMap_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [torusBondRegrouping_apply]
  simp only [representationBondMatrix, torusRepresentationBondProduct,
    torusSiteBondEndpointEquiv_symm_apply, add_sub_cancel_right]
  rw [← torusBond_product]
  simp only [torusBondRepresentation, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Combine the horizontal and vertical group assignments into one label per
actual bond, with `false` horizontal and `true` vertical. -/
def torusBondLabelConfigEquiv :
    TorusBondLabels width height G ≃ (X × Bool → G) where
  toFun p e := if e.2 then p.2 e.1 else p.1 e.1
  invFun q := (fun v ↦ q (v, false), fun v ↦ q (v, true))
  left_inv p := by cases p; rfl
  right_inv q := by funext ⟨v, b⟩; cases b <;> rfl

/-- The derived coherent expansion in horizontal/vertical bond-label coordinates. -/
theorem exists_labelCoefficients_of_mem_fourTorusCutSpace
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    {ψ : (TorusVertex 2 2 → V × V × V × V) → ℂ}
    (hψ : ψ ∈ fourTorusCutSpace (torusMatchedAveragingSites Uh Uv)) :
    ∃ c : TorusBondLabels 2 2 G → ℂ,
      ψ = ∑ p, c p • torusRepresentationBondProduct Uh Uv p := by
  obtain ⟨c, hc⟩ := exists_bondCoefficients_of_mem_fourTorusCutSpace Uh Uv hψ
  let e := torusBondLabelConfigEquiv (width := 2) (height := 2) (G := G)
  refine ⟨fun p ↦ c (e p), hc.trans ?_⟩
  exact (e.sum_comp (fun q ↦ c q • torusRepresentationBondProduct
    Uh Uv (fun v ↦ q (v, false), fun v ↦ q (v, true)))).symm

/-- For semi-regular bonds, the actual four-cut vector is reconstructed from
its trace-dual coefficients. No closure-span membership is assumed. -/
theorem eq_sum_extracted_bondProducts_of_mem_fourTorusCutSpace
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    {ψ : (TorusVertex 2 2 → V × V × V × V) → ℂ}
    (hψ : ψ ∈ fourTorusCutSpace (torusMatchedAveragingSites Uh Uv)) :
    ψ = ∑ p : TorusBondLabels 2 2 G,
      torusBondCoefficientExtraction Uh Uv p ψ •
        torusRepresentationBondProduct Uh Uv p := by
  obtain ⟨c, hc⟩ := exists_labelCoefficients_of_mem_fourTorusCutSpace Uh Uv hψ
  have hcoeff p : torusBondCoefficientExtraction Uh Uv p ψ = c p := by
    rw [hc, torusBondCoefficientExtraction_sum _ _ hU]
  simp_rw [hcoeff]
  exact hc

end TNLean.PEPS
