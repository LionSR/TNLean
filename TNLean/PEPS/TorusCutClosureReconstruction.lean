/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutFlatCoefficients
import TNLean.PEPS.TorusCutAverageProjection
import TNLean.PEPS.TorusMatchedCutClosureMembership

/-!
# Reconstructing commuting closures from the actual four cuts

Every canonical four-cut vector has a derived bond-product expansion.
Trace-dual extraction removes all nonflat bond coefficients. The product of
local invariant projectors fixes the vector and sends each remaining flat
bond product to a commuting native closure, by the actual labelled-torus
gauge classification. Local G-injective inverses transfer the equality to
four independently chosen physical tensors.

This proves the common-coordinate-alphabet case of SCP10, Theorem 5.5.
Every bond may carry its own matching semi-regular representation. Unitarity
is unnecessary for this algebraic equality. Arbitrary different virtual or
physical index types at different bonds or sites are not asserted here.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height

/-- Projecting a flat bond product gives one actual commuting closure. -/
theorem exists_averagingProjector_bondProduct_eq_matchedClosure
    (Uh Uv : X → G →* Matrix V V ℂ)
    (p : TorusBondLabels width height G) (hp : IsTorusBondFlat p) :
    ∃ g h : G, Commute g h ∧
      torusSitewiseAveragingProjector (torusMatchedLegRep Uh Uv)
          (torusRepresentationBondProduct Uh Uv p) =
        matchedTorusGClosure Uh Uv (torusMatchedAveragingSites Uh Uv) g h := by
  obtain ⟨q, g, h, hgh, hq⟩ := exists_torusBondGauge_eq_closure p hp
  refine ⟨g, h, hgh, ?_⟩
  rw [torusSitewiseAveragingProjector_bondProduct]
  funext σ
  have hnet := torusBondNetwork_matchedVertexGauge Uh Uv
    (torusMatchedAveragingSites Uh Uv)
    (fun v ↦ representationAveragingSite_invariant (torusMatchedLegRep Uh Uv v)) σ q
    (fun v ↦ Uh v (p.1 v)) (fun v ↦ Uv v (p.2 v))
  simp only [← map_mul] at hnet
  change torusBondNetwork
    (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
      t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v))
    (fun v ↦ Uh v ((torusBondGauge q p).1 v))
    (fun v ↦ Uv v ((torusBondGauge q p).2 v)) = _ at hnet
  rw [hq] at hnet
  simp only [torusBondClosureLabels, apply_ite, map_one] at hnet
  dsimp only [matchedTorusGClosure, torusMatchedHorizontalClosureAt,
    torusMatchedVerticalClosureAt, torusMatchedAveragingSites] at hnet ⊢
  exact hnet.symm

/-- A projected flat bond vector belongs to the actual commuting closure span. -/
theorem averagingProjector_bondProduct_mem_matchedClosureSpan
    (Uh Uv : X → G →* Matrix V V ℂ)
    (p : TorusBondLabels width height G) (hp : IsTorusBondFlat p) :
    torusSitewiseAveragingProjector (torusMatchedLegRep Uh Uv)
        (torusRepresentationBondProduct Uh Uv p) ∈
      matchedCommutingClosureSpan Uh Uv (torusMatchedAveragingSites Uh Uv) := by
  obtain ⟨g, h, hgh, heq⟩ :=
    exists_averagingProjector_bondProduct_eq_matchedClosure Uh Uv p hp
  rw [heq]
  apply Submodule.subset_span
  exact ⟨⟨(g, h), hgh⟩, rfl⟩

/-- The reverse four-cut inclusion follows from the derived coherent expansion,
coefficientwise flatness, and actual local averaging, without a parent-kernel
or closure-spanning hypothesis. -/
theorem fourTorusCutSpace_matchedAveraging_le_commutingClosureSpan
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv) :
    fourTorusCutSpace (torusMatchedAveragingSites Uh Uv) ≤
      matchedCommutingClosureSpan Uh Uv (torusMatchedAveragingSites Uh Uv) := by
  classical
  intro ψ hψ
  have hcut : ψ ∈ torusCutSpace (torusMatchedAveragingSites Uh Uv) 0 0 :=
    (mem_torusCutSpace_iff _ _ _ _).mpr ((mem_fourTorusCutSpace_iff _ _).mp hψ 0 0)
  have hfixed := torusSitewiseAveragingProjector_eq_self_of_mem_cut
    (torusMatchedLegRep Uh Uv) 0 0 hcut
  rw [← hfixed, eq_sum_extracted_bondProducts_of_mem_fourTorusCutSpace Uh Uv hU hψ, map_sum]
  apply Submodule.sum_mem
  intro p _
  rw [map_smul]
  by_cases hp : IsTorusBondFlat p
  · exact Submodule.smul_mem _ _
      (averagingProjector_bondProduct_mem_matchedClosureSpan Uh Uv p hp)
  · rw [torusBondCoefficientExtraction_eq_zero_of_mem_fourTorusCutSpace_not_flat Uh Uv hU p hp hψ,
      zero_smul]
    exact Submodule.zero_mem _

/-- Equality of the actual four canonical cut ranges and the commuting native
closure span, with independently matched semi-regular bond representations. -/
theorem fourTorusCutSpace_matchedAveraging_eq_commutingClosureSpan
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv) :
    fourTorusCutSpace (torusMatchedAveragingSites Uh Uv) =
      matchedCommutingClosureSpan Uh Uv (torusMatchedAveragingSites Uh Uv) :=
  le_antisymm (fourTorusCutSpace_matchedAveraging_le_commutingClosureSpan Uh Uv hU)
    (matchedCommutingClosureSpan_le_fourTorusCutSpace Uh Uv _
      (fun v ↦ representationAveragingSite_invariant (torusMatchedLegRep Uh Uv v)))

variable {Phys Out : Type*} [Fintype Phys]

omit [Fintype G] in
/-- Site-dependent physical maps preserve the actual matched closure insertions. -/
theorem torusSitewisePhysicalMap_matchedTorusGClosure
    (Uh Uv : X → G →* Matrix V V ℂ)
    (F : X → Matrix Out Phys ℂ)
    (a : X → V → V → V → V → Phys → ℂ) (g h : G) :
    torusSitewisePhysicalMap F (matchedTorusGClosure Uh Uv a g h) =
      matchedTorusGClosure Uh Uv (fun v ↦ physicalMapSite (F v) (a v)) g h :=
  torusSitewisePhysicalMap_torusBondNetwork F a _ _

omit [Fintype G] in
/-- The induced map sends the entire commuting closure span to the closure span
of the physically transformed tensors. -/
theorem map_matchedCommutingClosureSpan
    (Uh Uv : X → G →* Matrix V V ℂ)
    (F : X → Matrix Out Phys ℂ)
    (a : X → V → V → V → V → Phys → ℂ) :
    (matchedCommutingClosureSpan Uh Uv a).map (torusSitewisePhysicalMap F) =
      matchedCommutingClosureSpan Uh Uv (fun v ↦ physicalMapSite (F v) (a v)) := by
  simp only [matchedCommutingClosureSpan, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext p
  exact torusSitewisePhysicalMap_matchedTorusGClosure Uh Uv F a p.1.1 p.1.2

omit [Fintype Phys] in
/-- The original invariant tensors recover their actual commuting closure span
from the canonical span, with the matching bond representations retained. -/
theorem map_matchedCommutingClosureSpan_recover
    (Uh Uv : X → G →* Matrix V V ℂ)
    (a : X → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusMatchedLegRep Uh Uv v g = siteMap (a v)) :
    (matchedCommutingClosureSpan Uh Uv (torusMatchedAveragingSites Uh Uv)).map
        (torusSitewisePhysicalMap (fun v ↦ LinearMap.toMatrix' (siteMap (a v)))) =
      matchedCommutingClosureSpan Uh Uv a := by
  rw [map_matchedCommutingClosureSpan]
  congr 1
  funext v
  exact physicalMapSite_representationAveragingSite _ (a v) (ha v)

omit [Fintype G] [Fintype Phys] in
/-- The common-alphabet four-block closure theorem. The four tensors may differ,
and each of the eight actual bonds has its own matching semi-regular
representation. Source: SCP10, Theorem 5.5, with common coordinate alphabets.
No G-isometry, global-parent classification, or supplied spanning equality is used. -/
theorem fourTorusCutSpace_eq_matchedCommutingClosureSpan [Finite G] [Finite Phys]
    (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v, IsGInjective (torusMatchedLegRep Uh Uv v) (siteMap (a v))) :
    fourTorusCutSpace a = matchedCommutingClosureSpan Uh Uv a := by
  let := Fintype.ofFinite G
  rw [fourTorusCutSpace_eq_map_representationAveragingSite (torusMatchedLegRep Uh Uv) a ha,
    fourTorusCutSpace_matchedAveraging_eq_commutingClosureSpan Uh Uv hU,
    map_matchedCommutingClosureSpan_recover Uh Uv a (fun v ↦ (ha v).invariant)]

end TNLean.PEPS
