/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowComplement
import TNLean.PEPS.TorusEdgeBlockingCrossing

/-!
# Corner comparison regions at the minimal torus sizes

For positive rectangular window lengths L and K, let S be the rectangle of size
(L + 1) × (K + 1) starting at (L, K), and let R be S with its lower-left vertex removed.
If every L × K arc window is injective, then R, S and both complements are injective
when the torus has width at least 2L + 1 and height at least 2K + 1. The proof writes
R as the union of two rectangles and its complement as the union of the complement
of S and one L × K rectangle.

These are the one-site comparison regions used in arXiv:1804.04964, proof of
Theorem 3, lines 1544–1571 and the normal TI PEPS corollary. They allow the scalar
comparison without a separate lower bound of seven on either torus dimension.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {L K : ℕ}

/-- The (L + 1) × (K + 1) rectangle starting at (L, K). -/
def windowCornerRectangle (L K : ℕ) : Finset (TorusVertex width height) :=
  torusContiguousRectangle L K (L + 1) (K + 1)

/-- The comparison rectangle with its lower-left vertex omitted, expressed as two rectangles. -/
def windowCornerRegion (L K : ℕ) : Finset (TorusVertex width height) :=
  torusContiguousRectangle (L + 1) K L (K + 1) ∪
    torusContiguousRectangle L (K + 1) (L + 1) K

/-- The vertex (L, K) omitted from the comparison region. -/
def windowCornerVertex (L K : ℕ) : TorusVertex width height :=
  ((L : ZMod width), (K : ZMod height))

/-- Membership in the punctured comparison rectangle, expressed in coordinate values. -/
theorem mem_windowCornerRegion (v : TorusVertex width height) :
    v ∈ windowCornerRegion L K ↔
      (L + 1 ≤ v.1.val ∧ v.1.val < 2 * L + 1 ∧ K ≤ v.2.val ∧
        v.2.val < 2 * K + 1) ∨
      (L ≤ v.1.val ∧ v.1.val < 2 * L + 1 ∧ K + 1 ≤ v.2.val ∧
        v.2.val < 2 * K + 1) := by
  simp only [windowCornerRegion, Finset.mem_union, mem_torusContiguousRectangle]
  omega

/-- At the minimal size bounds, the corner vertex has precisely the coordinate values (L, K). -/
theorem eq_windowCornerVertex_iff (hw : 2 * L + 1 ≤ width)
    (hh : 2 * K + 1 ≤ height) (v : TorusVertex width height) :
    v = windowCornerVertex L K ↔ v.1.val = L ∧ v.2.val = K := by
  constructor
  · rintro rfl
    exact ⟨ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext (ZMod.val_injective width ?_) (ZMod.val_injective height ?_)
    · rw [h1]
      exact (ZMod.val_cast_of_lt (by omega : L < width)).symm
    · rw [h2]
      exact (ZMod.val_cast_of_lt (by omega : K < height)).symm

/-- The omitted corner vertex is outside the comparison region. -/
theorem windowCornerVertex_notMem (hw : 2 * L + 1 ≤ width)
    (hh : 2 * K + 1 ≤ height) :
    (windowCornerVertex L K : TorusVertex width height) ∉
      windowCornerRegion L K := by
  rw [mem_windowCornerRegion]
  have h1 : (windowCornerVertex L K : TorusVertex width height).1.val = L :=
    ZMod.val_cast_of_lt (by omega)
  have h2 : (windowCornerVertex L K : TorusVertex width height).2.val = K :=
    ZMod.val_cast_of_lt (by omega)
  omega

/-- Restoring the omitted vertex completes the comparison rectangle. -/
theorem insert_windowCornerVertex_windowCornerRegion (hw : 2 * L + 1 ≤ width)
    (hh : 2 * K + 1 ≤ height) :
    insert (windowCornerVertex L K : TorusVertex width height)
      (windowCornerRegion L K) = windowCornerRectangle L K := by
  ext v
  rw [Finset.mem_insert, mem_windowCornerRegion, eq_windowCornerVertex_iff hw hh,
    windowCornerRectangle, mem_torusContiguousRectangle]
  omega

/-- The complement is covered by the completed rectangle's complement and one window. -/
theorem compl_windowCornerRegion_eq_union (hL : 0 < L) (hK : 0 < K) :
    (Finset.univ \ windowCornerRegion L K : Finset (TorusVertex width height)) =
      (Finset.univ \ windowCornerRectangle L K) ∪
        torusContiguousRectangle 1 1 L K := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    mem_windowCornerRegion, windowCornerRectangle,
    mem_torusContiguousRectangle]
  omega

namespace NormalTorusArcWindowInjectivityHypotheses
variable {κ : RegionInjectivityData (TorusVertex width height)}

/-- A non-wrapping rectangle containing a full injective window is injective. -/
private theorem contiguousRectangle_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    {xStart yStart xLen yLen : ℕ} (hx : L ≤ xLen) (hy : K ≤ yLen)
    (hxw : xStart + xLen ≤ width) (hyh : yStart + yLen ≤ height) :
    κ.IsInjective (torusContiguousRectangle xStart yStart xLen yLen) := by
  rw [← torusArcRectangle_eq_torusContiguousRectangle xStart yStart xLen yLen
    (by omega) (by omega) hxw hyh]
  exact h.arcRectangle_injective hUnion hL hK hx hy (by omega) (by omega)

/-- The punctured comparison rectangle is injective by the union of its two rectangles. -/
theorem windowCornerRegion_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    κ.IsInjective (windowCornerRegion L K : Finset (TorusVertex width height)) := by
  unfold windowCornerRegion
  exact hUnion.union_injective
    (h.contiguousRectangle_injective hUnion hL hK (by omega) (by omega)
      (by omega) (by omega))
    (h.contiguousRectangle_injective hUnion hL hK (by omega) (by omega)
      (by omega) (by omega))

/-- The completed comparison rectangle is injective. -/
theorem windowCornerRectangle_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    κ.IsInjective (windowCornerRectangle L K : Finset (TorusVertex width height)) := by
  exact h.contiguousRectangle_injective hUnion hL hK (by omega) (by omega)
    (by omega) (by omega)

/-- The complement of the completed comparison rectangle is injective by two arc bands. -/
theorem compl_windowCornerRectangle_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    κ.IsInjective (Finset.univ \ (windowCornerRectangle L K :
      Finset (TorusVertex width height))) := by
  rw [windowCornerRectangle,
    ← torusArcRectangle_eq_torusContiguousRectangle L K (L + 1) (K + 1)
      (by omega) (by omega) (by omega) (by omega),
    compl_torusArcRectangle _ _ _ (by omega) (by omega)]
  exact hUnion.union_injective
    (h.arcRectangle_injective hUnion hL hK (by omega) (by omega) (by omega) (by omega))
    (h.arcRectangle_injective hUnion hL hK (by omega) (by omega) (by omega) (by omega))

/-- The complement of the punctured comparison rectangle is injective by adding one window. -/
theorem compl_windowCornerRegion_injective
    (h : NormalTorusArcWindowInjectivityHypotheses L K κ)
    (hUnion : RegionInjectivityUnionClosure κ) (hL : 0 < L) (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    κ.IsInjective (Finset.univ \ (windowCornerRegion L K :
      Finset (TorusVertex width height))) := by
  rw [compl_windowCornerRegion_eq_union hL hK]
  exact hUnion.union_injective
    (h.compl_windowCornerRectangle_injective hUnion hL hK hw hh)
    (h.contiguousRectangle_injective hUnion hL hK (by omega) (by omega)
      (by omega) (by omega))

end NormalTorusArcWindowInjectivityHypotheses

section BoundaryEdges
variable [Fact (1 < width)] [Fact (1 < height)]

/-- The upward edge from the omitted vertex crosses the punctured comparison region. -/
theorem isRegionBoundaryEdge_windowCornerRegion (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height) (windowCornerRegion L K)
      (torusUpEdge (windowCornerVertex L K : TorusVertex width height)) := by
  have h1 : (windowCornerVertex L K : TorusVertex width height).1.val = L :=
    ZMod.val_cast_of_lt (by omega)
  have h2 : (windowCornerVertex L K : TorusVertex width height).2.val = K :=
    ZMod.val_cast_of_lt (by omega)
  obtain ⟨hf, hs⟩ := torusUpEdge_endpoints_of_lt
    (p := windowCornerVertex L K) (by rw [h2]; omega)
  rw [IsRegionBoundaryEdge, hf, hs]
  refine Or.inr ⟨windowCornerVertex_notMem hw hh, ?_⟩
  rw [mem_windowCornerRegion]
  have h3 : ((windowCornerVertex L K : TorusVertex width height).2 + 1).val =
      K + 1 := by
    rw [show (windowCornerVertex L K : TorusVertex width height).2 + 1 =
        ((K + 1 : ℕ) : ZMod height) by simp [windowCornerVertex]]
    exact ZMod.val_cast_of_lt (by omega)
  dsimp only
  omega

/-- The upward edge just below the corner crosses the completed comparison rectangle. -/
theorem isRegionBoundaryEdge_windowCornerRectangle (hK : 0 < K)
    (hw : 2 * L + 1 ≤ width) (hh : 2 * K + 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height) (windowCornerRectangle L K)
      (torusUpEdge ((L : ZMod width), ((K - 1 : ℕ) : ZMod height))) := by
  have hx : (L : ZMod width).val = L := ZMod.val_cast_of_lt (by omega)
  have hy : ((K - 1 : ℕ) : ZMod height).val = K - 1 := ZMod.val_cast_of_lt (by omega)
  have heq : ((K - 1 : ℕ) : ZMod height) + 1 = (K : ZMod height) := by
    have hnat : K - 1 + 1 = K := by omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ ↦ (n : ZMod height)) hnat
  obtain ⟨hf, hs⟩ := torusUpEdge_endpoints_of_lt
    (p := ((L : ZMod width), ((K - 1 : ℕ) : ZMod height))) (by dsimp; rw [hy]; omega)
  rw [IsRegionBoundaryEdge, hf, hs]
  refine Or.inr ⟨?_, ?_⟩
  · rw [windowCornerRectangle, mem_torusContiguousRectangle]
    dsimp only
    omega
  · rw [windowCornerRectangle, mem_torusContiguousRectangle]
    dsimp only
    rw [heq, hx, ZMod.val_cast_of_lt (by omega : K < height)]
    omega

end BoundaryEdges

end TNLean.PEPS
