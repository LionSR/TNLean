/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionPeriodicLift

/-!
# Exterior collars of the genuine planar torus region

Closed unit squares with integer centers, when disjoint, are separated by at
least one unit in some coordinate. Thus enlarging one period copy of the lifted
region by a square of radius three quarters cannot meet any other period copy.
The part of this enlargement outside the original region projects outside the
actual torus cell union.

**Scope restriction (collar exclusion):** These are numerical and covering-space
consequences of a genuine region lift, supporting SCP10, Theorem 6.9, lines
1935–1990. Path connectedness of the exterior collar is not assumed or proved.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Pointwise
open Set

namespace TNLean.PEPS

private abbrev halfSquare : Set (ℝ × ℝ) :=
  Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)

private abbrev collarSquare : Set (ℝ × ℝ) :=
  Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4)

private def integerSquare (a : ℤ × ℤ) : Set (ℝ × ℝ) :=
  (fun d => ((a.1 : ℝ), (a.2 : ℝ)) + d) '' halfSquare

private theorem integerSquare_centers_separated (a b : ℤ × ℤ)
    (hab : Disjoint (integerSquare a) (integerSquare b)) :
    (2 : ℤ) ≤ |a.1 - b.1| ∨ (2 : ℤ) ≤ |a.2 - b.2| := by
  by_contra! h
  have h₁ : -1 ≤ a.1 - b.1 ∧ a.1 - b.1 ≤ 1 := by
    have := abs_le.mp (show |a.1 - b.1| ≤ 1 by omega)
    omega
  have h₂ : -1 ≤ a.2 - b.2 ∧ a.2 - b.2 ≤ 1 := by
    have := abs_le.mp (show |a.2 - b.2| ≤ 1 by omega)
    omega
  have hr₁ : (-1 : ℝ) ≤ (a.1 : ℝ) - (b.1 : ℝ) ∧
      (a.1 : ℝ) - (b.1 : ℝ) ≤ 1 := by exact_mod_cast h₁
  have hr₂ : (-1 : ℝ) ≤ (a.2 : ℝ) - (b.2 : ℝ) ∧
      (a.2 : ℝ) - (b.2 : ℝ) ≤ 1 := by exact_mod_cast h₂
  let d : ℝ × ℝ := (((b.1 : ℝ) - (a.1 : ℝ)) / 2,
    ((b.2 : ℝ) - (a.2 : ℝ)) / 2)
  have hd : d ∈ halfSquare := by
    constructor <;> constructor <;> dsimp [d] <;> linarith [hr₁.1, hr₁.2, hr₂.1, hr₂.2]
  have hnd : -d ∈ halfSquare := by
    constructor <;> constructor <;> dsimp [d] <;> linarith [hr₁.1, hr₁.2, hr₂.1, hr₂.2]
  apply Set.disjoint_left.mp hab
  · exact ⟨d, hd, rfl⟩
  · refine ⟨-d, hnd, ?_⟩
    apply Prod.ext <;> dsimp [d] <;> ring

private theorem disjoint_integerSquare_add_collarSquare (a b : ℤ × ℤ)
    (hab : Disjoint (integerSquare a) (integerSquare b)) :
    Disjoint (integerSquare a + collarSquare) (integerSquare b) := by
  rw [Set.disjoint_left]
  intro x hx hb
  obtain ⟨p, ⟨d, hd, rfl⟩, e, he, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨f, hf, hxf⟩ := hb
  have hx₁ := congrArg Prod.fst hxf
  have hx₂ := congrArg Prod.snd hxf
  change (b.1 : ℝ) + f.1 = (a.1 : ℝ) + d.1 + e.1 at hx₁
  change (b.2 : ℝ) + f.2 = (a.2 : ℝ) + d.2 + e.2 at hx₂
  have h₁ : |(a.1 : ℝ) - (b.1 : ℝ)| < 2 := by
    rw [abs_lt]
    constructor <;> linarith [hd.1.1, hd.1.2, he.1.1, he.1.2, hf.1.1, hf.1.2]
  have h₂ : |(a.2 : ℝ) - (b.2 : ℝ)| < 2 := by
    rw [abs_lt]
    constructor <;> linarith [hd.2.1, hd.2.2, he.2.1, he.2.2, hf.2.1, hf.2.2]
  have hi₁ : |a.1 - b.1| < (2 : ℤ) := by exact_mod_cast h₁
  have hi₂ : |a.2 - b.2| < (2 : ℤ) := by exact_mod_cast h₂
  rcases integerSquare_centers_separated a b hab with h | h <;> omega

private theorem integerSquare_periodTranslate (width height : ℕ) (b j : ℤ × ℤ) :
    (fun p => p + torusPeriodVector width height j) '' integerSquare b =
      integerSquare (b + (j.1 * (width : ℤ), j.2 * (height : ℤ))) := by
  ext x
  constructor
  · rintro ⟨p, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨d, hd, ?_⟩
    apply Prod.ext <;> simp [torusPeriodVector] <;> ring
  · rintro ⟨d, hd, rfl⟩
    refine ⟨((b.1 : ℝ), (b.2 : ℝ)) + d, ⟨d, hd, rfl⟩, ?_⟩
    apply Prod.ext <;> simp [torusPeriodVector] <;> ring

variable {width height : ℕ} [NeZero width] [NeZero height]
variable (R : Finset (TorusVertex width height))
variable (F : C(torusRegionRealization R, ℝ × ℝ))
variable (hF : ∀ p, torusRealProjection width height (F p) = p.1)
variable (L : {v // v ∈ R} → ℤ × ℤ)
variable (hL : ∀ v, (((L v).1 : ℝ), ((L v).2 : ℝ)) =
  F ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩)

include F hF hL

/-- Enlarging a genuine planar region by a square of radius three quarters
cannot meet another period copy. Source: SCP10, the exterior block geometry
in Theorem 6.9, lines 1935–1990; auxiliary numerical separation. -/
theorem disjoint_torusRegionPlanarRealization_add_collar_periodTranslate
    (j : ℤ × ℤ) (hj : j ≠ 0) :
    Disjoint (torusRegionPlanarRealization R L +
        (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4)))
      ((fun p => p + torusPeriodVector width height j) '' torusRegionPlanarRealization R L) := by
  rw [Set.disjoint_left]
  intro x hx hcopy
  obtain ⟨p, hp, d, hd, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨v, e, he, rfl⟩ := Set.mem_iUnion.mp hp
  obtain ⟨q, hq, hqx⟩ := hcopy
  obtain ⟨w, f, hf, rfl⟩ := Set.mem_iUnion.mp hq
  have hcell : Disjoint (integerSquare (L v))
      ((fun p => p + torusPeriodVector width height j) '' integerSquare (L w)) := by
    apply (torusRegionPlanarRealization_periodTranslate_disjoint R F hF L hL j hj).mono
    · intro y hy
      exact Set.mem_iUnion.mpr ⟨v, hy⟩
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨z, Set.mem_iUnion.mpr ⟨w, hz⟩, rfl⟩
  rw [integerSquare_periodTranslate] at hcell
  have hsep := disjoint_integerSquare_add_collarSquare (L v)
    (L w + (j.1 * (width : ℤ), j.2 * (height : ℤ))) hcell
  apply Set.disjoint_left.mp hsep
  · exact Set.add_mem_add ⟨e, he, rfl⟩ hd
  · rw [← integerSquare_periodTranslate]
    exact ⟨(( (L w).1 : ℝ), ((L w).2 : ℝ)) + f, ⟨f, hf, rfl⟩, hqx⟩

/-- Every point of the radius-three-quarters exterior collar projects outside
the actual torus cell region. No collar connectivity is assumed.
Source: SCP10, Theorem 6.9, lines 1935–1990; auxiliary exterior geometry. -/
theorem torusRealProjection_not_mem_of_mem_planarExteriorCollar {x : ℝ × ℝ}
    (hx : x ∈ (torusRegionPlanarRealization R L +
        (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4))) \
      torusRegionPlanarRealization R L) :
    torusRealProjection width height x ∉ torusRegionRealization R := by
  intro hp
  have hpre : x ∈ torusRealProjection width height ⁻¹' torusRegionRealization R := hp
  rw [preimage_torusRegionRealization_eq_iUnion_periodTranslate R F hF L hL] at hpre
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hpre
  by_cases hz : j = 0
  · subst j
    obtain ⟨p, hp, hpx⟩ := hj
    simp only [torusPeriodVector, Prod.fst_zero, Prod.snd_zero, Int.cast_zero,
      zero_mul, Prod.mk_zero_zero, add_zero] at hpx
    exact hx.2 (hpx ▸ hp)
  · exact Set.disjoint_left.mp
      (disjoint_torusRegionPlanarRealization_add_collar_periodTranslate R F hF L hL j hz)
      hx.1 hj

omit F hF L hL in
/-- Simple connectedness of the actual torus cell region supplies integer
coordinates whose exterior collar projects wholly outside that region.
This does not assert that the collar is path connected. Source: SCP10,
Theorem 6.9, lines 1935–1990; auxiliary geometric consequence. -/
theorem exists_integerLift_exteriorCollar_of_isSimplyConnected
    (hR : IsSimplyConnected (torusRegionRealization R)) (o : {v // v ∈ R}) :
    ∃ L : {v // v ∈ R} → ℤ × ℤ, IsTorusRegionIntegerLift R L ∧
      ∀ x ∈ (torusRegionPlanarRealization R L +
          (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4))) \
        torusRegionPlanarRealization R L,
        torusRealProjection width height x ∉ torusRegionRealization R := by
  obtain ⟨F, hF⟩ := exists_continuousLift_torusRegionRealization R hR o
  obtain ⟨L, hL, hreal, _⟩ := exists_integerLift_torusRegionPlanarRealization R F hF
  exact ⟨L, hL, fun _ hx =>
    torusRealProjection_not_mem_of_mem_planarExteriorCollar R F hF L hreal hx⟩

end TNLean.PEPS
