/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRectangleRealization
import TNLean.PEPS.TorusPlaquetteFluxMeasurement

/-!
# Topology of native torus plaquettes

Every four-site plaquette has a connected induced graph and a simply connected
closed-cell realization, including across either periodic seam. Translation
identifies its realization with that of the origin two-by-two rectangle.
These are auxiliary geometric facts for the parent Hamiltonian in SCP10,
arXiv:1001.3807, Theorem 5.5.
-/

noncomputable section
open Set
namespace TNLean.PEPS

variable {width height : ℕ}

/-- Translation of native vertices translates their points in the real torus. -/
theorem torusVertexPoint_add (v w : TorusVertex width height) :
    torusVertexPoint (v + w) = torusVertexPoint v + torusVertexPoint w := by
  simp [torusVertexPoint, map_add]

/-- Translating a finite region translates its closed-cell realization. -/
theorem torusRegionRealization_image_add (v : TorusVertex width height)
    (R : Finset (TorusVertex width height)) :
    torusRegionRealization (R.image (v + ·)) =
      (fun p => torusVertexPoint v + p) '' torusRegionRealization R := by
  classical
  ext p
  simp only [torusRegionRealization, mem_iUnion, Finset.mem_image, exists_prop,
    torusClosedUnitCell, mem_image]
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, d, hd, rfl⟩
    exact ⟨_, ⟨z, hz, d, hd, rfl⟩, by rw [torusVertexPoint_add, add_assoc]⟩
  · rintro ⟨q, ⟨w, hw, d, hd, rfl⟩, rfl⟩
    exact ⟨v + w, ⟨w, hw, rfl⟩, d, hd, by rw [torusVertexPoint_add, add_assoc]⟩

variable [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The induced graph of a four-site plaquette is connected. -/
theorem connected_torusPlaquetteRegion (v : TorusVertex width height) :
    ((torusGraph width height).induce (torusPlaquetteRegion v : Set _)).Connected := by
  have hR : (torusPlaquetteRegion v : Set _) =
      {x | x ∈ (torusPlaquetteWalk v).support} := by
    ext x
    simp [torusPlaquetteRegion]
  rw [hR]
  exact (torusPlaquetteWalk v).connected_induce_support

/-- A native plaquette is the translate of the plaquette at the origin. -/
theorem torusPlaquetteRegion_eq_image_add (v : TorusVertex width height) :
    torusPlaquetteRegion v = (torusPlaquetteRegion (0 : TorusVertex width height)).image
      (v + ·) := by
  ext w
  simp [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
    Prod.add_def]

/-- The origin plaquette is the nonwrapping two-by-two coordinate rectangle. -/
theorem torusPlaquetteRegion_zero_eq_rectangle :
    torusPlaquetteRegion (0 : TorusVertex width height) =
      torusContiguousRectangle 0 0 2 2 := by
  ext v
  have hz {n : ℕ} [NeZero n] [Fact (1 < n)] (z : ZMod n) :
      z.val < 2 ↔ z = 0 ∨ z = 1 := by
    constructor
    · intro h
      have : z.val = 0 ∨ z.val = 1 := by omega
      rcases this with h | h
      · left; exact ZMod.val_injective n (by simpa [ZMod.val_one] using h)
      · right; exact ZMod.val_injective n (by simpa [ZMod.val_one] using h)
    · rintro (rfl | rfl) <;> simp [ZMod.val_one]
  simp only [mem_torusContiguousRectangle, zero_add, Nat.zero_le, true_and, hz]
  simp [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
    Prod.ext_iff]
  tauto

/-- Every native plaquette realization is simply connected, also at periodic seams.
This supplies the geometric hypothesis in the parent-kernel inclusion of SCP10,
Theorem 5.5, for the complete native plaquette family. -/
theorem isSimplyConnected_torusRegionRealization_plaquette
    (v : TorusVertex width height) :
    IsSimplyConnected (torusRegionRealization (torusPlaquetteRegion v)) := by
  rw [torusPlaquetteRegion_eq_image_add, torusRegionRealization_image_add]
  have h : IsSimplyConnected
      (torusRegionRealization (torusPlaquetteRegion (0 : TorusVertex width height))) := by
    rw [torusPlaquetteRegion_zero_eq_rectangle]
    exact isSimplyConnected_torusRegionRealization_rectangle 0 0 2 2
      (by omega) (by omega) Fact.out Fact.out
      (by have := Fact.out (p := 2 < width); omega)
      (by have := Fact.out (p := 2 < height); omega)
  exact (Homeomorph.addLeft (torusVertexPoint v)).isEmbedding.isSimplyConnected_image.mpr h

end TNLean.PEPS
