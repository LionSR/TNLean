/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionIntersection

/-!
# Regular intersection on the physical factors of the union

The ambient intersection theorem descends to a vector on the union alone.
The regional conditions on such a vector are the actual open-region range
conditions on every slice of the other core vertices. Exterior vertices are
absent from this physical space; all virtual half-edges crossing the union's
boundary remain independent inputs to its open-region map.

Source: the three-physical-factor intersection in SCP10, arXiv:1001.3807,
Theorem 5.4, restricted here to the regular averaging tensors.
-/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Fix the half-edge coordinates at the other vertices of a chosen ambient
region. For `R ⊆ T` this is the ordinary complementary slice inside `T`. -/
def regularSubregionSlice (R T : Finset V)
    (τ : RegionHalfEdgeConfig (Γ := Γ) G (T \ R)) :
    (RegionHalfEdgeConfig (Γ := Γ) G T → ℂ) →ₗ[ℂ]
      (RegionHalfEdgeConfig (Γ := Γ) G R → ℂ) where
  toFun x α := x (fun v => if hv : v.1 ∈ R then α ⟨v.1, hv⟩
    else τ ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual regional range condition on vectors with physical factors only
in `T`, imposed on every complementary slice inside `T`. -/
noncomputable def regularRegionRangeWithin (T R : Finset V) :
    Submodule ℂ (RegionHalfEdgeConfig (Γ := Γ) G T → ℂ) :=
  ⨅ τ : RegionHalfEdgeConfig (Γ := Γ) G (T \ R),
    (Matrix.mulVecLin (regularProjectorOpenRegionMatrix (Γ := Γ) (G := G) R)).range.comap
      (regularSubregionSlice R T τ)

/-- Extend a regional vector constantly in all exterior physical coordinates. -/
def regularRegionConstantExtension (T : Finset V) :
    (RegionHalfEdgeConfig (Γ := Γ) G T → ℂ) →ₗ[ℂ]
      (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) where
  toFun x α := x (restrictRegularRegionHalfEdges T α)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
private theorem constantExtension_slice (R T : Finset V)
    (τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R))
    (x : RegionHalfEdgeConfig (Γ := Γ) G T → ℂ) :
    dependentRegionSlice (Out := fun v => IncidentEdge Γ v → G) R τ
        (regularRegionConstantExtension T x) =
      regularSubregionSlice R T (fun v => τ ⟨v.1,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp v.2).2⟩⟩) x := by
  funext α
  apply congrArg x
  funext v
  rfl

/-- The slice condition inside a chosen physical region is exactly the
pullback of the ambient condition under constant exterior extension. -/
theorem regularRegionRangeWithin_eq_comap (T R : Finset V) :
    regularRegionRangeWithin (Γ := Γ) (G := G) T R =
      (regularGlobalRegionRange R).comap (regularRegionConstantExtension T) := by
  ext x
  simp only [regularRegionRangeWithin, Submodule.mem_iInf, Submodule.mem_comap,
    mem_regularGlobalRegionRange_iff, constantExtension_slice]
  constructor
  · intro h τ
    exact h _
  · intro h τ
    let τ' : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R) := fun v =>
      if hv : v.1 ∈ T then τ ⟨v.1,
        Finset.mem_sdiff.mpr ⟨hv, (Finset.mem_sdiff.mp v.2).2⟩⟩ else fun _ => 1
    convert h τ' using 1
    congr 2
    funext v
    simp [τ', (Finset.mem_sdiff.mp v.2).1]

/-- With no complementary core vertices, the condition is precisely the
range of the actual open-region matrix. -/
theorem regularRegionRangeWithin_self (T : Finset V) :
    regularRegionRangeWithin (Γ := Γ) (G := G) T T =
      (Matrix.mulVecLin (regularProjectorOpenRegionMatrix (Γ := Γ) (G := G) T)).range := by
  ext x
  rw [regularRegionRangeWithin_eq_comap]
  simp only [Submodule.mem_comap, mem_regularGlobalRegionRange_iff]
  have hs (τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ T)) :
      dependentRegionSlice (Out := fun v => IncidentEdge Γ v → G) T τ
        (regularRegionConstantExtension T x) = x := by
    funext α
    exact congrArg x (restrictRegularRegionHalfEdges_assemble T α τ)
  simp only [hs]
  exact ⟨fun h => h (fun _ _ => 1), fun h _ => h⟩

/-- The regular intersection identity on only the physical factors of the
union. Every boundary virtual leg remains open; no exterior physical factor
occurs in the conclusion. This is the regular-coordinate three-block step of
SCP10, Theorem 5.4. -/
theorem regularRegionRangeWithin_inf_eq_range {R S : Finset V} {b : V}
    (hoverlap : R ∩ S = {b})
    (hcross : ∀ u ∈ R \ S, ∀ v ∈ S \ R, ¬ Γ.Adj u v) :
    regularRegionRangeWithin (Γ := Γ) (G := G) (R ∪ S) R ⊓
        regularRegionRangeWithin (R ∪ S) S =
      (Matrix.mulVecLin
        (regularProjectorOpenRegionMatrix (Γ := Γ) (G := G) (R ∪ S))).range := by
  rw [regularRegionRangeWithin_eq_comap, regularRegionRangeWithin_eq_comap,
    ← Submodule.comap_inf, regularGlobalRegionRange_inf_eq_union hoverlap hcross,
    ← regularRegionRangeWithin_eq_comap, regularRegionRangeWithin_self]

end TNLean.PEPS
