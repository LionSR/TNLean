/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionInjectivity
import TNLean.PEPS.GInjectiveRangeEquivalence
import TNLean.PEPS.TorusRectangleBoundaryCard

/-!
# A dimension obstruction for complete open-boundary images

An actual connected regular G-injective block with b > 0 crossing bonds has
physical image dimension |G|^(b-1). A block whose boundary coordinate space has
smaller dimension cannot contain this image after any linear physical map.
For a native two-site rectangle and a group of order six, six boundary legs of
dimension four give at most 4^6 image dimensions, whereas the regular image has
6^5 dimensions.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2977–3019. The source proves a closed
bondwise state equivalence. It does not assert equality of the complete images
for arbitrary open boundary tensors. These auxiliary dimension statements
clarify that distinction; no error in the source is asserted. The regular rank
is derived from connected-region G-injectivity and the invariant boundary
space, rather than assumed. The numerical specialization does not identify
any particular group's irreducible representations.
-/

open scoped Matrix ComplexOrder
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

/-- The complete physical boundary image of an actual connected regular
G-injective block has the dimension of its invariant boundary space.
Source: SCP10, Lemma 5.2 and the boundary count in Theorem 6.9,
lines 1318–1358 and 2027–2037. -/
theorem rank_regularOpenRegionMatrix_of_isGInjective_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) {b : ℕ} (hb : 0 < b)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (regularOpenRegionMatrix a R e).rank = Fintype.card G ^ (b - 1) := by
  classical
  rw [Matrix.rank,
    (isGInjective_regularOpenRegionMatrix_of_connected a ha R hR e).finrank_range]
  exact finrank_regularBoundaryInvariants b hb

/-- No linear physical image of a smaller boundary space contains the complete
image of this actual regular block. This is an auxiliary dimension comparison
for SCP10, Section 7, lines 2977–3019; it is not a claim made by the source. -/
theorem not_range_le_regularOpenRegionMatrix_of_small_boundary
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) {b : ℕ} (hb : 0 < b)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    {P B : Type*} [Fintype P] [Fintype B]
    (M : Matrix P B ℂ) (L : Matrix (RegionPhysicalConfig (d := d) R) P ℂ)
    (hdim : Fintype.card B < Fintype.card G ^ (b - 1)) :
    ¬ LinearMap.range (regularOpenRegionMatrix a R e).mulVecLin ≤
      LinearMap.range (L * M).mulVecLin := by
  classical
  intro h
  have hle : (regularOpenRegionMatrix a R e).rank ≤ (L * M).rank :=
    Submodule.finrank_mono h
  rw [rank_regularOpenRegionMatrix_of_isGInjective_of_connected a ha R hR hb e] at hle
  exact (not_le_of_gt hdim) (hle.trans ((Matrix.rank_mul_le_right L M).trans
    M.rank_le_card_width))

section Torus
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The native two-site rectangle has six actual crossing bonds. For a group
of order six, its complete regular boundary image cannot be contained in the
linear physical image of any block with four coordinates on each boundary leg.
The numerical comparison is 4^6 < 6^5; no irreducible-character table is assumed
or established. Auxiliary comparison for SCP10, Section 7, lines 2977–3019. -/
theorem exists_boundaryNumbering_twoSite_not_range_le
    (a : (v : TorusVertex width height) →
      (IncidentEdge (torusGraph width height) v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation
      (IncidentEdge (torusGraph width height) v)) (regularSiteMap (a v)))
    (hG : Fintype.card G = 6) {P : Type*} [Fintype P] :
    ∃ e : {f : Edge (torusGraph width height) //
        IsRegionBoundaryEdge (torusContiguousRectangle 0 0 2 1) f} ≃ Fin 6,
      ∀ (M : Matrix P (Fin 6 → Fin 4) ℂ)
        (L : Matrix (RegionPhysicalConfig (d := d)
          (torusContiguousRectangle 0 0 2 1 : Finset (TorusVertex width height))) P ℂ),
        ¬ LinearMap.range (regularOpenRegionMatrix a
          (torusContiguousRectangle 0 0 2 1) e).mulVecLin ≤
            LinearMap.range (L * M).mulVecLin := by
  classical
  have hw : 2 < width := Fact.out
  have hh : 2 < height := Fact.out
  have hcard : Fintype.card {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (torusContiguousRectangle 0 0 2 1) f} = 6 := by
    simpa using card_regionBoundaryEdge_torusRectangle (width := width) (height := height)
      0 0 2 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  let e := (Fintype.equivFin _).trans (finCongr hcard)
  refine ⟨e, fun M L => ?_⟩
  apply not_range_le_regularOpenRegionMatrix_of_small_boundary a ha _
    (torusGraph_rectangle_connected 0 0 2 1 (by omega) (by omega) (by omega) (by omega))
    (by omega) e M L
  simp only [Fintype.card_fun, Fintype.card_fin, hG]
  norm_num

end Torus
end TNLean.PEPS
