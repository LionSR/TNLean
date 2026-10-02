/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionLiftRealization

/-!
# Separation of the genuine planar region from its period translates

A continuous plane lift of the actual torus cell region is a section of the
torus projection. Its image is therefore disjoint from every translate by a
nonzero integer period vector. In particular the corresponding planar closed
cells belonging to distinct period copies cannot touch, even at a corner.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the topologically
trivial block and complement construction in §6.3, local source lines
1935–1990; auxiliary geometric statement.

**Scope restriction (covering-lift separation):** This is a consequence of the
genuine covering lift, not the exterior collar or path-existence theorem
needed for the unrestricted entropy argument. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ}

/-- An integer deck translation of the real square-lattice torus.
Source: SCP10, torus block domains, §6.3, lines 1935–1990. -/
def torusPeriodVector (width height : ℕ) (j : ℤ × ℤ) : ℝ × ℝ :=
  ((j.1 : ℝ) * (width : ℝ), (j.2 : ℝ) * (height : ℝ))

/-- A period translation projects to the zero point of the original torus. -/
theorem torusRealProjection_periodVector (j : ℤ × ℤ) :
    torusRealProjection width height (torusPeriodVector width height j) = 0 := by
  apply Prod.ext
  · change (((j.1 : ℝ) * (width : ℝ) : ℝ) : AddCircle (width : ℝ)) = 0
    exact (AddCircle.coe_eq_zero_iff (width : ℝ)).mpr ⟨j.1, by simp⟩
  · change (((j.2 : ℝ) * (height : ℝ) : ℝ) : AddCircle (height : ℝ)) = 0
    exact (AddCircle.coe_eq_zero_iff (height : ℝ)).mpr ⟨j.2, by simp⟩

/-- For positive torus periods, only the zero deck vector is the zero real
translation. -/
theorem torusPeriodVector_eq_zero_iff [NeZero width] [NeZero height] (j : ℤ × ℤ) :
    torusPeriodVector width height j = 0 ↔ j = 0 := by
  simp [torusPeriodVector, Prod.ext_iff,
    Nat.cast_ne_zero.mpr (NeZero.ne width), Nat.cast_ne_zero.mpr (NeZero.ne height)]

/-- Two plane points project to the same torus point exactly when they differ
by an integer period vector. -/
theorem torusRealProjection_eq_iff_exists_periodVector (p q : ℝ × ℝ) :
    torusRealProjection width height p = torusRealProjection width height q ↔
      ∃ j : ℤ × ℤ, p = q + torusPeriodVector width height j := by
  constructor
  · intro h
    have hz : torusRealProjection width height (p - q) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨i, hi⟩ := (AddCircle.coe_eq_zero_iff (width : ℝ)).mp
      (congrArg Prod.fst hz)
    obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff (height : ℝ)).mp
      (congrArg Prod.snd hz)
    refine ⟨(i, j), Prod.ext ?_ ?_⟩
    · change p.1 = q.1 + (i : ℝ) * (width : ℝ)
      simpa only [Prod.fst_sub, zsmul_eq_mul, sub_eq_iff_eq_add, add_comm] using hi.symm
    · change p.2 = q.2 + (j : ℝ) * (height : ℝ)
      simpa only [Prod.snd_sub, zsmul_eq_mul, sub_eq_iff_eq_add, add_comm] using hj.symm
  · rintro ⟨j, rfl⟩
    rw [map_add, torusRealProjection_periodVector, add_zero]

/-- The image of a genuine continuous covering lift is disjoint from every
nonzero integer period translate. Source: SCP10, topologically trivial block
domains, §6.3, lines 1935–1990; auxiliary separation statement. -/
theorem continuousLift_torusRegionRealization_periodTranslate_disjoint
    [NeZero width] [NeZero height] (R : Finset (TorusVertex width height))
    (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (j : ℤ × ℤ) (hj : j ≠ 0) :
    Disjoint (Set.range F)
      ((fun p => p + torusPeriodVector width height j) '' Set.range F) := by
  rw [Set.disjoint_left]
  intro p hp hq
  obtain ⟨v, rfl⟩ := hp
  obtain ⟨q, ⟨w, rfl⟩, hw⟩ := hq
  have hvw := congrArg (torusRealProjection width height) hw
  simp only [map_add, torusRealProjection_periodVector, add_zero, hF] at hvw
  have he : w = v := Subtype.ext hvw
  subst w
  have hz : torusPeriodVector width height j = 0 := by
    exact add_left_cancel (hw.trans (add_zero (F v)).symm)
  exact hj ((torusPeriodVector_eq_zero_iff j).mp hz)

/-- The exact planar closed-cell realization supplied by the covering lift is
disjoint from every nonzero period translate. Source: SCP10, block domains,
§6.3, lines 1935–1990; auxiliary geometric statement. -/
theorem torusRegionPlanarRealization_periodTranslate_disjoint
    [NeZero width] [NeZero height] (R : Finset (TorusVertex width height))
    (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (L : {v // v ∈ R} → ℤ × ℤ)
    (hL : ∀ v, (((L v).1 : ℝ), ((L v).2 : ℝ)) =
      F ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩)
    (j : ℤ × ℤ) (hj : j ≠ 0) :
    Disjoint (torusRegionPlanarRealization R L)
      ((fun p => p + torusPeriodVector width height j) '' torusRegionPlanarRealization R L) := by
  rw [← range_continuousLift_torusRegionRealization R F hF L hL]
  exact continuousLift_torusRegionRealization_periodTranslate_disjoint R F hF j hj

/-- The full plane preimage of the actual torus region is precisely the union
of the period translates of its lifted planar cell realization.
Source: SCP10, exterior block geometry, §6.3, lines 1935–1990. -/
theorem preimage_torusRegionRealization_eq_iUnion_periodTranslate
    [NeZero width] [NeZero height] (R : Finset (TorusVertex width height))
    (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (L : {v // v ∈ R} → ℤ × ℤ)
    (hL : ∀ v, (((L v).1 : ℝ), ((L v).2 : ℝ)) =
      F ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩) :
    torusRealProjection width height ⁻¹' torusRegionRealization R =
      ⋃ j : ℤ × ℤ, (fun p => p + torusPeriodVector width height j) ''
        torusRegionPlanarRealization R L := by
  ext p
  constructor
  · intro hp
    let v : torusRegionRealization R := ⟨torusRealProjection width height p, hp⟩
    obtain ⟨j, hj⟩ := (torusRealProjection_eq_iff_exists_periodVector p (F v)).mp
      (hF v).symm
    refine Set.mem_iUnion.mpr ⟨j, F v, ?_, hj.symm⟩
    rw [← range_continuousLift_torusRegionRealization R F hF L hL]
    exact Set.mem_range_self v
  · intro hp
    obtain ⟨j, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
    rw [← range_continuousLift_torusRegionRealization R F hF L hL] at hq
    obtain ⟨v, rfl⟩ := hq
    change torusRealProjection width height (F v + torusPeriodVector width height j) ∈
      torusRegionRealization R
    rw [map_add, torusRealProjection_periodVector, add_zero, hF]
    exact v.2

/-- Two individual closed cells in distinct period copies of a genuine lifted
region cannot meet, including along a side or at a corner. Source: SCP10,
exterior block geometry, §6.3, lines 1935–1990; auxiliary separation statement. -/
theorem torusRegionPlanarRealization_cell_periodTranslate_disjoint
    [NeZero width] [NeZero height] (R : Finset (TorusVertex width height))
    (F : C(torusRegionRealization R, ℝ × ℝ))
    (hF : ∀ p, torusRealProjection width height (F p) = p.1)
    (L : {v // v ∈ R} → ℤ × ℤ)
    (hL : ∀ v, (((L v).1 : ℝ), ((L v).2 : ℝ)) =
      F ⟨torusVertexPoint v.1, torusVertexPoint_mem_torusRegionRealization R v.1 v.2⟩)
    (j : ℤ × ℤ) (hj : j ≠ 0) (v w : {v // v ∈ R}) :
    Disjoint
      ((fun d : ℝ × ℝ => (((L v).1 : ℝ), ((L v).2 : ℝ)) + d) ''
        (Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Icc (-1 / 2 : ℝ) (1 / 2)))
      ((fun d : ℝ × ℝ => (((L w).1 : ℝ), ((L w).2 : ℝ)) + d +
          torusPeriodVector width height j) ''
        (Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Icc (-1 / 2 : ℝ) (1 / 2))) := by
  apply (torusRegionPlanarRealization_periodTranslate_disjoint R F hF L hL j hj).mono
  · unfold torusRegionPlanarRealization
    rintro p ⟨d, hd, rfl⟩
    exact Set.mem_iUnion.mpr ⟨v, ⟨d, hd, rfl⟩⟩
  · rintro p ⟨d, hd, rfl⟩
    exact ⟨(((L w).1 : ℝ), ((L w).2 : ℝ)) + d,
      Set.mem_iUnion.mpr ⟨w, ⟨d, hd, rfl⟩⟩, rfl⟩

/-- Simple connectedness of the actual torus cell region supplies an integer
unit-step lift whose planar closed-cell realization is disjoint from every
nonzero period translate. Source: SCP10, topologically trivial blocks, §6.3,
lines 1935–1990; auxiliary geometric statement. -/
theorem exists_integerLift_periodTranslate_disjoint_of_isSimplyConnected
    [NeZero width] [NeZero height] (R : Finset (TorusVertex width height))
    (hR : IsSimplyConnected (torusRegionRealization R)) (o : {v // v ∈ R}) :
    ∃ L : {v // v ∈ R} → ℤ × ℤ, IsTorusRegionIntegerLift R L ∧
      ∀ j : ℤ × ℤ, j ≠ 0 → Disjoint (torusRegionPlanarRealization R L)
        ((fun p => p + torusPeriodVector width height j) ''
          torusRegionPlanarRealization R L) := by
  obtain ⟨F, hF⟩ := exists_continuousLift_torusRegionRealization R hR o
  obtain ⟨L, hL, hreal, _⟩ := exists_integerLift_torusRegionPlanarRealization R F hF
  exact ⟨L, hL, fun j hj =>
    torusRegionPlanarRealization_periodTranslate_disjoint R F hF L hreal j hj⟩

end TNLean.PEPS
