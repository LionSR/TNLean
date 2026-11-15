/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusComplementPathReplacement

/-!
# Replacing torus walks outside a simply connected region

Every finite native torus graph walk whose two endpoints lie outside a region
with simply connected closed-cell realization has a complementary walk with
the same seam crossing numbers. The replacement is constructed one maximal
interior segment at a time using the genuine exterior collar.

Source: SCP10, arXiv:1001.3807v3, the geometric deformation in Lemma 6.14
and the exterior-collar construction in the proof of Theorem 6.9,
local source lines 1935–1990 and 2199–2214.

**Scope restriction (simply connected forbidden cells):** Both torus periods
are at least three. The forbidden region has simply connected closed-cell
realization, and the two endpoints are outside it. This is a site-graph walk
replacement theorem; the native dual-string incidence condition and physical
reduced-density comparison are separate. See
`docs/paper-gaps/scp10_dual_flux_avoidance.tex`.
-/

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

private theorem split_first_exit {u v : X} (p : (Γₜ).Walk u v)
    (R : Finset X) (hu : u ∈ R) (hv : v ∉ R) :
    ∃ (r : {v : X // v ∈ R}) (w : X) (_hw : w ∉ R)
      (h : (Γₜ).Adj r.1 w)
      (pR : ((Γₜ).induce (R : Set X)).Walk ⟨u, hu⟩ r)
      (pS : (Γₜ).Walk w v),
      p = (pR.map ⟨Subtype.val, fun {_ _} h ↦ h⟩).append (.cons h pS) := by
  revert hu hv
  induction p with
  | nil =>
    intro hu hv
    exact (hv hu).elim
  | @cons u z v h p ih =>
    intro hu hv
    by_cases hz : z ∈ R
    · obtain ⟨r, w, hw, hr, pR, pS, hp⟩ := ih hz hv
      refine ⟨r, w, hw, hr, .cons h pR, pS, ?_⟩
      simpa only [SimpleGraph.Walk.map_cons, SimpleGraph.Walk.cons_append] using
        congrArg (SimpleGraph.Walk.cons h) hp
    · exact ⟨⟨u, hu⟩, z, hz, h, .nil, p, rfl⟩

private theorem replace_region_segment
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    {v₀ v : {v : X // v ∈ R}} (p : ((Γₜ).induce (R : Set X)).Walk v₀ v)
    (w₀ w : {v : X // v ∈ Finset.univ \ R})
    (h₀ : (Γₜ).Adj v₀.1 w₀.1) (h : (Γₜ).Adj v.1 w.1) :
    ∃ q : ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk w₀ w,
      torusWalkWinding (q.map ⟨Subtype.val, fun {_ _} h ↦ h⟩) =
        torusWalkWinding
          ((SimpleGraph.Walk.cons h₀.symm
            (p.map ⟨Subtype.val, fun {_ _} h ↦ h⟩)).append (.cons h .nil)) := by
  obtain ⟨L, hL, hP, hπ⟩ :=
    exists_integerLift_simplyConnected_exteriorCollar_of_isSimplyConnected R hSC
  exact exists_complementWalk_of_integerExteriorCollarGraph_connected R L hL hπ
    (integerExteriorCollarGraph_connected_of_isSimplyConnected _ hP) p w₀ w h₀ h

/-- Every finite torus graph walk with endpoints outside a simply connected
forbidden region has a complementary walk with exactly the same seam crossing
numbers. The complementary walk is derived, not assumed. No graph connectivity
or collar hypothesis is supplied. Source: SCP10, Lemma 6.14 and the exterior
replacement argument in Theorem 6.9, lines 1935–1990 and 2199–2214. -/
theorem exists_complementWalk_same_winding_of_isSimplyConnected
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    {a b : X} (p : (Γₜ).Walk a b) (ha : a ∉ R) (hb : b ∉ R) :
    ∃ q : ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk
        ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
        ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩⟩,
      torusWalkWinding (q.map ⟨Subtype.val, fun {_ _} h ↦ h⟩) = torusWalkWinding p := by
  classical
  have H (n : ℕ) : ∀ {a b : X} (p : (Γₜ).Walk a b), p.length = n →
      ∀ (ha : a ∉ R) (hb : b ∉ R),
      ∃ q : ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk
          ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
          ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩⟩,
        torusWalkWinding (q.map ⟨Subtype.val, fun {_ _} h ↦ h⟩) = torusWalkWinding p := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b p hn ha hb
      cases p with
      | nil => exact ⟨.nil, rfl⟩
      | @cons a z b h p =>
        by_cases hz : z ∈ R
        · obtain ⟨r, w, hw, hr, pR, pS, hp⟩ := split_first_exit p R hz hb
          have hlen : pS.length < n := by
            have hl := congrArg SimpleGraph.Walk.length hp
            simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_map,
              SimpleGraph.Walk.length_cons] at hl
            simp only [SimpleGraph.Walk.length_cons] at hn
            omega
          obtain ⟨qS, hqS⟩ := ih pS.length hlen pS rfl hw hb
          obtain ⟨qR, hqR⟩ := replace_region_segment R hSC pR
            ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
            ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩⟩ h.symm hr
          refine ⟨qR.append qS, ?_⟩
          simp only [SimpleGraph.Walk.map_append, torusWalkWinding_append, hqR, hqS]
          rw [hp]
          simp only [torusWalkWinding_append, torusWalkWinding]
          abel
        · have hlen : p.length < n := by
            simp only [SimpleGraph.Walk.length_cons] at hn
            omega
          obtain ⟨q, hq⟩ := ih p.length hlen p rfl hz hb
          refine ⟨.cons h q, ?_⟩
          simp only [SimpleGraph.Walk.map_cons, torusWalkWinding, hq]
  exact H p.length p rfl ha hb

end TNLean.PEPS
