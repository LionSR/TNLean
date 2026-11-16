/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualCollarAvoidance
import TNLean.PEPS.TorusSimplyConnectedComplement

/-!
# An untwisted component containing all complementary boundary endpoints

The genuine simply connected planar lift has a connected safe exterior collar.
Project this graph into the physical complement. Every complementary boundary
endpoint lifts into this same collar. A native dual path avoiding every dual
plaquette with an observed corner has identity transport on its projected
edges, giving the untwisted component required by the noncentral contraction.

This is derived geometry for SCP10, arXiv:1001.3807v3, Theorem 6.9 and
Lemma 6.14, lines 1935–1990 and 2199–2214. The observation region's actual
closed-cell realization is simply connected, and an avoiding path is given;
endpoint exclusion alone is not a classification hypothesis. See
`docs/paper-gaps/scp10_untwisted_flux_boundary.tex`.
-/

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
local instance fluxBoundaryQuiver : Quiver X := torusDualQuiver width height
local instance fluxBoundaryWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance fluxBoundaryHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩

private def intVertex (a : ℤ × ℤ) : X := ((a.1 : ZMod width), (a.2 : ZMod height))

private theorem integer_adj {q r : ℤ × ℤ}
    (h : (SimpleGraph.addCayley {(1, 0), (0, 1)}).Adj q r) :
    (Γₜ).Adj (intVertex q) (intVertex r) := by
  obtain ⟨_, d, hd, he⟩ := (SimpleGraph.addCayley_adj' _ q r).mp h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl
  · rcases he with he | he
    · subst r
      simpa [intVertex] using torusGraph_adj_right
        (q.1 : ZMod width) (q.2 : ZMod height)
    · subst q
      simpa [intVertex] using (torusGraph_adj_right
        (r.1 : ZMod width) (r.2 : ZMod height)).symm
  · rcases he with he | he
    · subst r
      simpa [intVertex] using torusGraph_adj_up
        (q.1 : ZMod width) (q.2 : ZMod height)
    · subst q
      simpa [intVertex] using (torusGraph_adj_up
        (r.1 : ZMod width) (r.2 : ZMod height)).symm

private def collarProjection (R : Finset X) (L : {v // v ∈ R} → ℤ × ℤ)
    (hπ : ∀ x ∈ integerExteriorCollar (Finset.univ.image L),
      torusRealProjection width height x ∉ torusRegionRealization R) :
    integerExteriorBand (Finset.univ.image L) → {v : X // v ∈ Finset.univ \ R} := fun q =>
  ⟨intVertex q.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
    intro hv
    apply hπ (integerCellCenter q.1)
      ((integerCellCenter_mem_exteriorCollar_iff _ _).mpr q.2)
    simpa only [intVertex, torusVertexPoint_intCast, integerCellCenter] using
      torusVertexPoint_mem_torusRegionRealization R (intVertex q.1) hv⟩⟩

private theorem boundary_lifts (R : Finset X) (L : {v // v ∈ R} → ℤ × ℤ)
    (hL : IsTorusRegionIntegerLift R L)
    (hπ : ∀ x ∈ integerExteriorCollar (Finset.univ.image L),
      torusRealProjection width height x ∉ torusRegionRealization R)
    (v : {v : X // v ∈ Finset.univ \ R}) (hv : ∃ w ∈ R, (Γₜ).Adj v.1 w) :
    ∃ q : integerExteriorBand (Finset.univ.image L), collarProjection R L hπ q = v := by
  obtain ⟨w, hw, h⟩ := hv
  obtain ⟨b, hb, hc, _⟩ := exists_exterior_integerUnitStep_of_isTorusRegionIntegerLift
    hL ⟨w, hw⟩ v.1 (Finset.mem_sdiff.mp v.2).2 h.symm
  have hcollar : integerCellCenter b ∈ integerExteriorCollar (Finset.univ.image L) := by
    simpa only [integerExteriorCollar, integerCellCenter,
      integerClosedCellUnion_image_eq_torusRegionPlanarRealization] using hc
  refine ⟨⟨b, (integerCellCenter_mem_exteriorCollar_iff _ _).mp hcollar⟩, ?_⟩
  exact Subtype.ext hb

/-- The actual exterior collar supplies an untwisted complementary component
containing every complementary boundary endpoint of a simply connected physical
region. Only avoidance of the computed four-corner forbidden plaquettes is
assumed about the native path. The component, root and untwisted edges are
derived, without centrality or a density premise. Source: SCP10, Theorem 6.9
and Lemma 6.14, exterior-block construction. -/
theorem exists_torusFlux_untwisted_boundary_component {G : Type*} [Group G]
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    {s t : X} (p : TorusDualPath s t)
    (hp : ∀ v ∈ (torusDualPathGraphWalk p).support, v ∉ torusIncidentDualPlaquettes R)
    (g : G) :
    ∃ (U : SimpleGraph {v : X // v ∈ Finset.univ \ R})
      (hU : U ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
      (o : {v : X // v ∈ Finset.univ \ R}),
      (∀ {v w} (h : U.Adj v w), regularDirectedTransport (v := v.1) (w := w.1)
        (torusGraphRegularLabels (torusDualFluxLabels g p).1
          (torusDualFluxLabels g p).2) (hU h) = 1) ∧
      ∀ v : {v : X // v ∈ Finset.univ \ R},
        (∃ w ∈ R, (Γₜ).Adj v.1 w) → U.Reachable o v := by
  classical
  obtain ⟨L, hL, hA, hπ⟩ :=
    exists_integerLift_simplyConnected_exteriorCollar_of_isSimplyConnected R hSC
  let A := Finset.univ.image L
  let C := integerExteriorCollarGraph A
  have hC : C.Connected := integerExteriorCollarGraph_connected_of_isSimplyConnected A hA
  let f := collarProjection R L hπ
  let U := C.map f
  have hU : U ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X) := by
    intro v w hvw
    obtain ⟨_, q, r, hqr, rfl, rfl⟩ := hvw
    exact integer_adj hqr.1
  let F : C →g U := {
    toFun := f
    map_rel' := by
      intro q r h
      have hne : f q ≠ f r := by
        intro he
        exact (integer_adj h.1).ne (congrArg Subtype.val he)
      exact SimpleGraph.map_adj_apply' h hne }
  obtain ⟨q₀⟩ := hC.nonempty
  have hOcc : ∀ a ∈ A, ((a.1 : ZMod width), (a.2 : ZMod height)) ∈ R := by
    intro a ha
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha
    simpa only [hL.1 v] using v.2
  refine ⟨U, hU, f q₀, ?_, ?_⟩
  · intro v w h
    obtain ⟨_, q, r, hqr, rfl, rfl⟩ := h
    exact torusDualFlux_transport_eq_one_on_integerExteriorCollar
      R A hOcc p hp g hqr (integer_adj hqr.1)
  · intro v hv
    obtain ⟨q, hq⟩ := boundary_lifts R L hL hπ v hv
    obtain ⟨walk⟩ := hC.preconnected q₀ q
    have hreach := (walk.map F).reachable
    change U.Reachable (f q₀) (f q) at hreach
    exact hq ▸ hreach

end TNLean.PEPS
