/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellExteriorCollar
import TNLean.PEPS.TorusIntegerStepWinding
import TNLean.PEPS.TorusRegionWalkWinding
import TNLean.PEPS.TorusComplementCycleWords
import TNLean.PEPS.TorusRegionExteriorCollar

/-!
# Integer endpoints at the boundary of a torus region

The center of a native exterior site lies outside the actual closed-cell
region. Lifting a crossing step from its interior integer center therefore
gives a genuine exterior integer endpoint. These endpoints belong to the
exterior collar and retain the crossing numbers of the native boundary route.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the exterior block
construction in the proof of Theorem 6.9, local source lines 1935–1990.
This supplies endpoints for the geometric path argument, without asserting
path connectedness of the exterior collar.

**Scope restriction (simple torus graph):** The crossing-step and walk
statements use periods at least three; the center assertion needs only
positive periods. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open Set
open scoped Pointwise

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]

private theorem integer_eq_zero_of_mem_halfInterval (a : ℤ)
    (ha : (a : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2)) : a = 0 := by
  have hl : (-1 : ℤ) < a := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < -1 / 2) ha.1)
  have hr : a < (1 : ℤ) := by
    exact_mod_cast (lt_of_le_of_lt ha.2 (by norm_num : (1 / 2 : ℝ) < 1))
  omega

private theorem vertexPoint_injective :
    Function.Injective (torusVertexPoint (width := width) (height := height)) := by
  intro v w h
  have hp : torusRealProjection width height ((v.1.val : ℝ), (v.2.val : ℝ)) =
      torusRealProjection width height ((w.1.val : ℝ), (w.2.val : ℝ)) := by
    simpa only [← torusVertexPoint_eq_projection] using h
  obtain ⟨j, hj⟩ := (torusRealProjection_eq_iff_exists_periodVector _ _).mp hp
  apply Prod.ext
  · have hx := congrArg Prod.fst hj
    change (v.1.val : ℝ) = (w.1.val : ℝ) + (j.1 : ℝ) * (width : ℝ) at hx
    have hi : (v.1.val : ℤ) = (w.1.val : ℤ) + j.1 * (width : ℤ) := by
      exact_mod_cast hx
    simpa using congrArg (fun z : ℤ => (z : ZMod width)) hi
  · have hy := congrArg Prod.snd hj
    change (v.2.val : ℝ) = (w.2.val : ℝ) + (j.2 : ℝ) * (height : ℝ) at hy
    have hi : (v.2.val : ℤ) = (w.2.val : ℤ) + j.2 * (height : ℤ) := by
      exact_mod_cast hy
    simpa using congrArg (fun z : ℤ => (z : ZMod height)) hi

private theorem vertexPoint_mem_closedUnitCell_iff (v w : TorusVertex width height) :
    torusVertexPoint v ∈ torusClosedUnitCell w ↔ v = w := by
  constructor
  · rintro ⟨d, hd, hp⟩
    have hproj : torusRealProjection width height ((v.1.val : ℝ), (v.2.val : ℝ)) =
        torusRealProjection width height (((w.1.val : ℝ), (w.2.val : ℝ)) + d) := by
      rw [map_add]
      simpa only [← torusVertexPoint_eq_projection] using hp.symm
    obtain ⟨j, hj⟩ := (torusRealProjection_eq_iff_exists_periodVector _ _).mp hproj
    let k : ℤ × ℤ := ((v.1.val : ℤ) - w.1.val - j.1 * (width : ℤ),
      (v.2.val : ℤ) - w.2.val - j.2 * (height : ℤ))
    have hreal : ((k.1 : ℝ), (k.2 : ℝ)) = d := by
      apply Prod.ext
      · have hx := congrArg Prod.fst hj
        simp only [torusPeriodVector, Prod.fst_add] at hx
        dsimp [k]
        push_cast
        linarith
      · have hy := congrArg Prod.snd hj
        simp only [torusPeriodVector, Prod.snd_add] at hy
        dsimp [k]
        push_cast
        linarith
    have hk₁ : k.1 = 0 := integer_eq_zero_of_mem_halfInterval _
      (by simpa only [← hreal] using hd.1)
    have hk₂ : k.2 = 0 := integer_eq_zero_of_mem_halfInterval _
      (by simpa only [← hreal] using hd.2)
    have hd0 : d = 0 := by rw [← hreal, hk₁, hk₂]; simp
    apply vertexPoint_injective
    simpa only [hd0, map_zero, add_zero] using hp.symm
  · rintro rfl
    exact ⟨0, by constructor <;> constructor <;> norm_num, by simp⟩

/-- A native site center belongs to the actual closed-cell region exactly
when the site belongs to the region. Source: SCP10, block boundaries in the
proof of Theorem 6.9, lines 1935–1990; auxiliary cell geometry. -/
theorem torusVertexPoint_mem_torusRegionRealization_iff
    (R : Finset (TorusVertex width height)) (v : TorusVertex width height) :
    torusVertexPoint v ∈ torusRegionRealization R ↔ v ∈ R := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := mem_iUnion.mp hv
    obtain ⟨hwR, hcell⟩ := mem_iUnion.mp hw
    have he : v = w := (vertexPoint_mem_closedUnitCell_iff v w).mp hcell
    simpa only [he] using hwR
  · exact torusVertexPoint_mem_torusRegionRealization R v

omit [NeZero width] [NeZero height] in
private theorem projection_mem_of_mem_planarRealization
    {R : Finset (TorusVertex width height)} {L : {v // v ∈ R} → ℤ × ℤ}
    (hL : IsTorusRegionIntegerLift R L) {x : ℝ × ℝ}
    (hx : x ∈ torusRegionPlanarRealization R L) :
    torusRealProjection width height x ∈ torusRegionRealization R := by
  obtain ⟨v, d, hd, rfl⟩ := mem_iUnion.mp hx
  apply mem_iUnion.mpr
  refine ⟨v.1, mem_iUnion.mpr ⟨v.2, ?_⟩⟩
  refine ⟨d, hd, ?_⟩
  rw [map_add]
  have hp := torusVertexPoint_intCast (width := width) (height := height) (L v)
  rw [hL.1 v] at hp
  rw [← hp]

variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

private theorem exists_integerUnitStep (a : ℤ × ℤ) (w : TorusVertex width height)
    (h : (torusGraph width height).Adj
      ((a.1 : ZMod width), (a.2 : ZMod height)) w) :
    ∃ b : ℤ × ℤ, ((b.1 : ZMod width), (b.2 : ZMod height)) = w ∧
      (a + (1, 0) = b ∨ a = b + (1, 0) ∨
        a + (0, 1) = b ∨ a = b + (0, 1)) := by
  rcases h with ⟨hy, hx | hx⟩ | ⟨hx, hy | hy⟩
  · refine ⟨a + (1, 0), ?_, Or.inl rfl⟩
    exact Prod.ext (by simpa using hx) (by simpa using hy)
  · refine ⟨a - (1, 0), ?_, Or.inr (Or.inl ?_)⟩
    · apply Prod.ext
      · simpa using (eq_sub_iff_add_eq.mpr hx).symm
      · simpa using hy
    · abel
  · refine ⟨a + (0, 1), ?_, Or.inr (Or.inr (Or.inl rfl))⟩
    exact Prod.ext (by simpa using hx) (by simpa using hy)
  · refine ⟨a - (0, 1), ?_, Or.inr (Or.inr (Or.inr ?_))⟩
    · apply Prod.ext
      · simpa using hx
      · simpa using (eq_sub_iff_add_eq.mpr hy).symm
    · abel

omit [NeZero width] [NeZero height] [Fact (2 < width)] [Fact (2 < height)] in
private theorem unitStep_mem_collar
    {R : Finset (TorusVertex width height)} (L : {v // v ∈ R} → ℤ × ℤ)
    (v : {v // v ∈ R}) (b : ℤ × ℤ)
    (hb : L v + (1, 0) = b ∨ L v = b + (1, 0) ∨
      L v + (0, 1) = b ∨ L v = b + (0, 1)) :
    ((b.1 : ℝ), (b.2 : ℝ)) ∈ torusRegionPlanarRealization R L +
      (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4)) := by
  have hb' : |b.1 - (L v).1| ≤ 1 ∧ |b.2 - (L v).2| ≤ 1 := by
    rcases hb with h | h | h | h
    all_goals
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [Prod.fst_add, Prod.snd_add] at hx hy
      constructor <;> rw [abs_le] <;> constructor <;> omega
  have hc := mem_integerClosedCell_add_of_abs_le_one (L v) (integerCellCenter b)
    (by dsimp only [integerCellCenter]; exact_mod_cast hb')
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_add.mp hc
  exact Set.mem_add.mpr ⟨x, Set.mem_iUnion.mpr ⟨v, hx⟩, y, hy, hxy⟩


/-- A crossing step from a lifted interior site has an integer exterior
endpoint in the radius-three-quarters collar, with the actual native crossing
numbers. Source: SCP10, exterior block construction in Theorem 6.9,
lines 1935–1990; auxiliary boundary geometry. -/
theorem exists_exterior_integerUnitStep_of_isTorusRegionIntegerLift
    {R : Finset (TorusVertex width height)} {L : {v // v ∈ R} → ℤ × ℤ}
    (hL : IsTorusRegionIntegerLift R L) (v : {v // v ∈ R})
    (w : TorusVertex width height) (hw : w ∉ R)
    (h : (torusGraph width height).Adj v.1 w) :
    ∃ b : ℤ × ℤ,
      ((b.1 : ZMod width), (b.2 : ZMod height)) = w ∧
      ((b.1 : ℝ), (b.2 : ℝ)) ∈
        (torusRegionPlanarRealization R L +
          (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4))) \
          torusRegionPlanarRealization R L ∧
      torusDirectedWinding h = torusIntegerDeckCoordinate width height b -
        torusIntegerDeckCoordinate width height (L v) := by
  have hadj : (torusGraph width height).Adj
      (((L v).1 : ZMod width), ((L v).2 : ZMod height)) w := by
    simpa only [hL.1 v] using h
  obtain ⟨b, hb, hstep⟩ := exists_integerUnitStep (L v) w hadj
  refine ⟨b, hb, ⟨unitStep_mem_collar L v b hstep, ?_⟩, ?_⟩
  · intro hp
    have hproj := projection_mem_of_mem_planarRealization hL hp
    rw [← torusVertexPoint_intCast, hb] at hproj
    exact hw ((torusVertexPoint_mem_torusRegionRealization_iff R w).mp hproj)
  · have hstepAdj : (torusGraph width height).Adj
        (((L v).1 : ZMod width), ((L v).2 : ZMod height))
        ((b.1 : ZMod width), (b.2 : ZMod height)) := by
      simpa only [hL.1 v, hb] using h
    have he := torusDirectedWinding_eq_of_integerUnitStep (L v) b hstep hstepAdj
    simpa only [hL.1 v, hb] using he

/-- The exterior endpoints of a route through the region have exactly the
route's winding difference. This supplies the endpoints for a complementary
path, but does not assert that such a path exists. Source: SCP10,
proof of Theorem 6.9, lines 1935–1990. -/
theorem exists_exterior_integerEndpoints_of_regionWalk
    {R : Finset (TorusVertex width height)} {L : {v // v ∈ R} → ℤ × ℤ}
    (hL : IsTorusRegionIntegerLift R L) {v₀ v : {v // v ∈ R}}
    (p : ((torusGraph width height).induce (R : Set (TorusVertex width height))).Walk v₀ v)
    (w₀ w : TorusVertex width height) (hw₀ : w₀ ∉ R) (hw : w ∉ R)
    (h₀ : (torusGraph width height).Adj v₀.1 w₀)
    (h : (torusGraph width height).Adj v.1 w) :
    ∃ b₀ b : ℤ × ℤ,
      ((b₀.1 : ZMod width), (b₀.2 : ZMod height)) = w₀ ∧
      ((b.1 : ZMod width), (b.2 : ZMod height)) = w ∧
      ((b₀.1 : ℝ), (b₀.2 : ℝ)) ∈
        (torusRegionPlanarRealization R L +
          (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4))) \
          torusRegionPlanarRealization R L ∧
      ((b.1 : ℝ), (b.2 : ℝ)) ∈
        (torusRegionPlanarRealization R L +
          (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4))) \
          torusRegionPlanarRealization R L ∧
      torusWalkWinding
        ((SimpleGraph.Walk.cons h₀.symm
          (p.map ⟨Subtype.val, fun {_ _} h => h⟩)).append
          (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)) =
        torusIntegerDeckCoordinate width height b -
          torusIntegerDeckCoordinate width height b₀ := by
  obtain ⟨b₀, hb₀, hc₀, hd₀⟩ :=
    exists_exterior_integerUnitStep_of_isTorusRegionIntegerLift hL v₀ w₀ hw₀ h₀
  obtain ⟨b, hb, hc, hd⟩ :=
    exists_exterior_integerUnitStep_of_isTorusRegionIntegerLift hL v w hw h
  refine ⟨b₀, b, hb₀, hb, hc₀, hc, ?_⟩
  have hp : torusWalkWinding (p.map ⟨Subtype.val, fun {_ _} h => h⟩) =
      torusIntegerDeckCoordinate width height (L v) -
        torusIntegerDeckCoordinate width height (L v₀) := by
    exact torusWalkWinding_of_isTorusRegionIntegerLift hL p
  simp only [torusWalkWinding_append, torusWalkWinding, zero_add]
  rw [hp, torusDirectedWinding_symm h₀, hd₀, hd]
  change (torusIntegerDeckCoordinate width height (L v) -
      torusIntegerDeckCoordinate width height (L v₀)) +
      -(torusIntegerDeckCoordinate width height b₀ -
        torusIntegerDeckCoordinate width height (L v₀)) +
      (torusIntegerDeckCoordinate width height b -
        torusIntegerDeckCoordinate width height (L v)) = _
  abel

end TNLean.PEPS
