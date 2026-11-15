/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusComplementPathReplacement
import TNLean.PEPS.TorusDualWinding

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
realization, and the two endpoints are outside it. The native four-labelled
dual path retains its lifted displacement and avoids the forbidden plaquettes.
The physical crossed-bond incidence condition and reduced-density comparison
are separate. See
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
local instance : Quiver X := torusDualQuiver width height

private def dualStepWalk {a b : X} : TorusDualStep a b → (Γₜ).Walk a b
  | .east x y => .cons (torusGraph_adj_right x y) .nil
  | .west x y => .cons (torusGraph_adj_right x y).symm .nil
  | .north x y => .cons (torusGraph_adj_up x y) .nil
  | .south x y => .cons (torusGraph_adj_up x y).symm .nil

/-- Record the visited dual plaquettes as a walk in the native torus graph.
The four direction labels are retained when constructing this walk.
Source: SCP10, Definition 6.13 and Lemma 6.14. -/
def torusDualPathGraphWalk {a : X} : {b : X} → TorusDualPath a b → (Γₜ).Walk a b
  | _, .nil => .nil
  | _, .cons p e => (torusDualPathGraphWalk p).append (dualStepWalk e)

private theorem graphWalk_comp {a b c : X} (p : TorusDualPath a b) (q : TorusDualPath b c) :
    torusDualPathGraphWalk (p.comp q) =
      (torusDualPathGraphWalk p).append (torusDualPathGraphWalk q) := by
  induction q with
  | nil => simp [torusDualPathGraphWalk]
  | cons q e ih =>
    simp only [Quiver.Path.comp_cons, torusDualPathGraphWalk, ih,
      SimpleGraph.Walk.append_assoc]

private theorem exists_dualStep {a b : X} (h : (Γₜ).Adj a b) :
    ∃ e : TorusDualStep a b, dualStepWalk e = .cons h .nil := by
  rcases a with ⟨x, y⟩
  rcases b with ⟨u, v⟩
  rcases h with ⟨hy, hx | hx⟩ | ⟨hx, hy | hy⟩
  · cases hy
    cases hx
    exact ⟨.east x y, rfl⟩
  · cases hy
    cases hx
    exact ⟨.west u y, rfl⟩
  · cases hx
    cases hy
    exact ⟨.north x y, rfl⟩
  · cases hx
    cases hy
    exact ⟨.south x v, rfl⟩

private theorem exists_dualPath {a b : X} (p : (Γₜ).Walk a b) :
    ∃ q : TorusDualPath a b, torusDualPathGraphWalk q = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | cons h p ih =>
    obtain ⟨e, he⟩ := exists_dualStep h
    obtain ⟨q, hq⟩ := ih
    refine ⟨(Quiver.Hom.toPath e).comp q, ?_⟩
    rw [graphWalk_comp, hq]
    change (dualStepWalk e).append p = .cons h p
    rw [he]
    rfl

private theorem val_step {n : ℕ} [NeZero n] [Fact (1 < n)] (x : ZMod n) :
    ((x + 1).val : ℤ) - x.val + (n : ℤ) * (if x + 1 = 0 then 1 else 0) = 1 := by
  have hx := ZMod.val_lt x
  by_cases hlt : x.val + 1 < n
  · have hv : (x + 1).val = x.val + 1 := by
      simpa only [ZMod.val_one] using
        (ZMod.val_add_of_lt (a := x) (b := 1) (by simpa only [ZMod.val_one] using hlt))
    have hn : x + 1 ≠ 0 := by
      intro hz
      rw [hz, ZMod.val_zero] at hv
      omega
    simp [hn, hv]
  · have hle : n ≤ x.val + (1 : ZMod n).val := by
      simpa only [ZMod.val_one] using Nat.le_of_not_gt hlt
    have hv := ZMod.val_add_val_of_le hle
    have hz : (x + 1).val = 0 := by
      simp only [ZMod.val_one] at hv
      omega
    have hzero : x + 1 = 0 := (ZMod.val_eq_zero _).mp hz
    simp only [hzero, ite_true, ZMod.val_zero, mul_one]
    simp only [hzero, ZMod.val_one, ZMod.val_zero] at hv
    omega

private theorem step_displacement {a b : X} (e : TorusDualStep a b) :
    e.displacement =
      ((b.1.val : ℤ) - a.1.val + (width : ℤ) * (torusWalkWinding (dualStepWalk e)).1,
        (b.2.val : ℤ) - a.2.val + (height : ℤ) * (torusWalkWinding (dualStepWalk e)).2) := by
  cases e with
  | east x y =>
    have hx := val_step x
    ext <;> simp [dualStepWalk, torusWalkWinding, torusDirectedWinding_right,
      TorusDualStep.displacement] at * <;> linarith
  | west x y =>
    have hx := val_step x
    ext <;> simp [dualStepWalk, torusWalkWinding, torusDirectedWinding_symm,
      torusDirectedWinding_right, TorusDualStep.displacement, mul_neg] at * <;> linarith
  | north x y =>
    have hy := val_step y
    ext <;> simp [dualStepWalk, torusWalkWinding, torusDirectedWinding_up,
      TorusDualStep.displacement] at * <;> linarith
  | south x y =>
    have hy := val_step y
    ext <;> simp [dualStepWalk, torusWalkWinding, torusDirectedWinding_symm,
      torusDirectedWinding_up, TorusDualStep.displacement, mul_neg] at * <;> linarith

private theorem path_displacement {a b : X} (p : TorusDualPath a b) :
    torusDualPathDisplacement p =
      ((b.1.val : ℤ) - a.1.val + (width : ℤ) * (torusWalkWinding (torusDualPathGraphWalk p)).1,
        (b.2.val : ℤ) - a.2.val +
          (height : ℤ) * (torusWalkWinding (torusDualPathGraphWalk p)).2) := by
  induction p with
  | nil => simp [torusDualPathGraphWalk, torusWalkWinding]
  | cons p e ih =>
    simp only [torusDualPathDisplacement_cons, torusDualPathGraphWalk,
      torusWalkWinding_append, ih, step_displacement e]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

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
      refine ⟨r, w, hw, hr, .cons (show ((Γₜ).induce (R : Set X)).Adj ⟨u, hu⟩ ⟨z, hz⟩ from h) pR, pS, ?_⟩
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
          refine ⟨.cons (show ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Adj
            ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
            ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩⟩ from h) q, ?_⟩
          simp only [SimpleGraph.Walk.map_cons, torusWalkWinding, hq]
  exact H p.length p rfl ha hb

/-- A finite four-labelled dual path can be replaced by one avoiding any
simply connected forbidden plaquette region, with its lifted displacement
unchanged. Endpoint exclusion and actual simple connectedness are the geometric
hypotheses; no avoiding path or homotopy is supplied.
Source: SCP10, arXiv:1001.3807v3, Lemma 6.14. -/
theorem exists_torusDualPath_avoiding_of_isSimplyConnected
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    {a b : X} (p : TorusDualPath a b) (ha : a ∉ R) (hb : b ∉ R) :
    ∃ q : TorusDualPath a b,
      torusDualPathDisplacement q = torusDualPathDisplacement p ∧
        ∀ v ∈ (torusDualPathGraphWalk q).support, v ∉ R := by
  obtain ⟨r, hr⟩ := exists_complementWalk_same_winding_of_isSimplyConnected
    R hSC (torusDualPathGraphWalk p) ha hb
  obtain ⟨q, hq⟩ := exists_dualPath (r.map ⟨Subtype.val, fun {_ _} h ↦ h⟩)
  refine ⟨q, ?_, ?_⟩
  · rw [path_displacement q, path_displacement p, hq, hr]
  · intro v hv
    rw [hq, SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
    exact (Finset.mem_sdiff.mp w.2).2

end TNLean.PEPS
