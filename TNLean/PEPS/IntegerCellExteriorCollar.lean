/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellNoHoles
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Continuous paths in an exterior integer-cell collar

The occupied domain is the actual union of closed unit cells with integer
centers. Its exterior collar is obtained by adding the closed square of radius
three quarters and removing the occupied domain.

A safe exterior graph uses unoccupied centers at coordinate distance at most
one from an occupied center. Each four-neighbor edge must have one common
nearby occupied center. This extra condition guarantees that the entire straight
edge remains within the collar enlargement; ordinary exterior band edges need
not have this property. Safe graph walks give genuine continuous collar paths.

**Scope restriction (auxiliary collar paths):** Connectivity of the safe graph
is not proved here and is not adopted as a disk hypothesis. This is the continuous
geometric step in SCP10, arXiv:1001.3807, proof of Theorem 6.9, lines 1935–1990;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Pointwise unitInterval
open Set

namespace TNLean.PEPS

/-- The real point with a given integer lattice center. -/
def integerCellCenter (a : ℤ × ℤ) : ℝ × ℝ := ((a.1 : ℝ), (a.2 : ℝ))

/-- The actual closed unit cell at an integer center. -/
def integerClosedCell (a : ℤ × ℤ) : Set (ℝ × ℝ) :=
  (fun d => integerCellCenter a + d) ''
    (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))

/-- The radius-three-quarters collar outside the occupied closed cells. -/
def integerExteriorCollar (A : Finset (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  (integerClosedCellUnion A +
    (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4))) \ integerClosedCellUnion A

/-- Coordinate distance at most one between two integer centers. -/
def IsIntegerCellNear (q a : ℤ × ℤ) : Prop := |q.1 - a.1| ≤ 1 ∧ |q.2 - a.2| ≤ 1

/-- Unoccupied centers adjacent, including diagonally, to some occupied cell. -/
def integerExteriorBand (A : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {q | q ∉ A ∧ ∃ a ∈ A, IsIntegerCellNear q a}

/-- Four-neighbor exterior edges supported by one common nearby occupied cell. -/
def integerExteriorCollarGraph (A : Finset (ℤ × ℤ)) :
    SimpleGraph (integerExteriorBand A) where
  Adj q r := (SimpleGraph.addCayley {(1, 0), (0, 1)}).Adj q.1 r.1 ∧
    ∃ a ∈ A, IsIntegerCellNear q.1 a ∧ IsIntegerCellNear r.1 a
  symm := ⟨by
    rintro q r ⟨hqr, a, ha, hq, hr⟩
    exact ⟨hqr.symm, a, ha, hr, hq⟩⟩
  loopless := ⟨by intro q h; exact (SimpleGraph.ne_of_adj _ h.1) rfl⟩

/-- Membership in a closed cell is expressed by the two coordinate bounds. -/
theorem mem_integerClosedCell_iff (a : ℤ × ℤ) (x : ℝ × ℝ) :
    x ∈ integerClosedCell a ↔
      |x.1 - (a.1 : ℝ)| ≤ 1 / 2 ∧ |x.2 - (a.2 : ℝ)| ≤ 1 / 2 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa only [integerCellCenter, Prod.fst_add, Prod.snd_add,
      add_sub_cancel_left, abs_le, neg_div, mem_prod, mem_Icc] using hd
  · intro hx
    refine ⟨x - integerCellCenter a, ?_, add_sub_cancel _ _⟩
    simpa only [integerCellCenter, Prod.fst_sub, Prod.snd_sub,
      mem_prod, mem_Icc, ← abs_le, neg_div] using hx

private theorem integer_eq_of_abs_cast_sub_le_half (a b : ℤ)
    (h : |(a : ℝ) - (b : ℝ)| ≤ 1 / 2) : a = b := by
  have hr : |(a : ℝ) - (b : ℝ)| < 1 := by linarith
  have hi : |a - b| < 1 := by exact_mod_cast hr
  have := abs_lt.mp hi
  omega

private theorem integer_endpoint_of_unit_interval (q a : ℤ) (x : ℝ)
    (hx : (q : ℝ) ≤ x ∧ x ≤ (q : ℝ) + 1) (ha : |x - (a : ℝ)| ≤ 1 / 2) :
    a = q ∨ a = q + 1 := by
  have hb := abs_le.mp ha
  have hl : q - 1 < a := by
    exact_mod_cast (show (q : ℝ) - 1 < (a : ℝ) by linarith)
  have hu : a < q + 2 := by
    exact_mod_cast (show (a : ℝ) < (q : ℝ) + 2 by linarith)
  omega

private theorem integer_endpoint_of_unit_combination (q r a : ℤ) (hr : q + 1 = r)
    (m n : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m + n = 1)
    (ha : |m * (q : ℝ) + n * (r : ℝ) - (a : ℝ)| ≤ 1 / 2) :
    a = q ∨ a = r := by
  have hn1 : n ≤ 1 := by linarith
  have hq : m * (q : ℝ) + n * (r : ℝ) = (q : ℝ) + n := by
    rw [← hr, show m = 1 - n by linarith]
    push_cast
    ring
  have h := integer_endpoint_of_unit_interval q a
    (m * (q : ℝ) + n * (r : ℝ)) (by rw [hq]; constructor <;> linarith) ha
  simpa only [hr] using h

private theorem integer_same_of_combination (q r a : ℤ) (hr : q = r)
    (m n : ℝ) (hmn : m + n = 1)
    (ha : |m * (q : ℝ) + n * (r : ℝ) - (a : ℝ)| ≤ 1 / 2) : a = q := by
  rw [← hr, ← add_mul, hmn, one_mul, abs_sub_comm] at ha
  exact integer_eq_of_abs_cast_sub_le_half a q ha

private theorem occupiedCell_of_mem_unit_segment (q r a : ℤ × ℤ)
    (hqr : (SimpleGraph.addCayley {(1, 0), (0, 1)}).Adj q r)
    (m n : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m + n = 1)
    (hx : m • integerCellCenter q + n • integerCellCenter r ∈ integerClosedCell a) :
    a = q ∨ a = r := by
  obtain ⟨hx, hy⟩ := (mem_integerClosedCell_iff a _).mp hx
  change |m * (q.1 : ℝ) + n * (r.1 : ℝ) - (a.1 : ℝ)| ≤ 1 / 2 at hx
  change |m * (q.2 : ℝ) + n * (r.2 : ℝ) - (a.2 : ℝ)| ≤ 1 / 2 at hy
  obtain ⟨_, d, hd, he⟩ := (SimpleGraph.addCayley_adj' _ q r).mp hqr
  simp only [mem_insert_iff, mem_singleton_iff] at hd
  rcases hd with rfl | rfl
  · rcases he with he | he
    · have hxq : q.1 + 1 = r.1 := congrArg Prod.fst he
      have hyq : q.2 = r.2 := by simpa using congrArg Prod.snd he
      have hya := integer_same_of_combination q.2 r.2 a.2 hyq m n hmn hy
      rcases integer_endpoint_of_unit_combination q.1 r.1 a.1 hxq m n hm hn hmn hx with ha | ha
      · exact Or.inl (Prod.ext ha hya)
      · exact Or.inr (Prod.ext ha (hya.trans hyq))
    · have hxq : r.1 + 1 = q.1 := (congrArg Prod.fst he).symm
      have hyq : q.2 = r.2 := by simpa using congrArg Prod.snd he
      have hya := integer_same_of_combination q.2 r.2 a.2 hyq m n hmn hy
      have hxa : |n * (r.1 : ℝ) + m * (q.1 : ℝ) - (a.1 : ℝ)| ≤ 1 / 2 := by
        simpa only [add_comm] using hx
      rcases integer_endpoint_of_unit_combination r.1 q.1 a.1 hxq n m hn hm
          (by linarith) hxa with ha | ha
      · exact Or.inr (Prod.ext ha (hya.trans hyq))
      · exact Or.inl (Prod.ext ha hya)
  · rcases he with he | he
    · have hyq : q.2 + 1 = r.2 := congrArg Prod.snd he
      have hxq : q.1 = r.1 := by simpa using congrArg Prod.fst he
      have hxa := integer_same_of_combination q.1 r.1 a.1 hxq m n hmn hx
      rcases integer_endpoint_of_unit_combination q.2 r.2 a.2 hyq m n hm hn hmn hy with ha | ha
      · exact Or.inl (Prod.ext hxa ha)
      · exact Or.inr (Prod.ext (hxa.trans hxq) ha)
    · have hyq : r.2 + 1 = q.2 := (congrArg Prod.snd he).symm
      have hxq : q.1 = r.1 := by simpa using congrArg Prod.fst he
      have hxa := integer_same_of_combination q.1 r.1 a.1 hxq m n hmn hx
      have hya : |n * (r.2 : ℝ) + m * (q.2 : ℝ) - (a.2 : ℝ)| ≤ 1 / 2 := by
        simpa only [add_comm] using hy
      rcases integer_endpoint_of_unit_combination r.2 q.2 a.2 hyq n m hn hm
          (by linarith) hya with ha | ha
      · exact Or.inr (Prod.ext (hxa.trans hxq) ha)
      · exact Or.inl (Prod.ext hxa ha)

/-- Coordinate distance at most one places a point in the enlarged occupied
cell, by splitting its displacement into two equal offsets. This numerical
placement supports SCP10, proof of Theorem 6.9, lines 1935–1990. -/
theorem mem_integerClosedCell_add_of_abs_le_one (a : ℤ × ℤ) (x : ℝ × ℝ)
    (hx : |x.1 - (a.1 : ℝ)| ≤ 1 ∧ |x.2 - (a.2 : ℝ)| ≤ 1) :
    x ∈ integerClosedCell a +
      (Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4)) := by
  let d : ℝ × ℝ := ((x.1 - (a.1 : ℝ)) / 2, (x.2 - (a.2 : ℝ)) / 2)
  have hd : d ∈ Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2) := by
    have h₁ := abs_le.mp hx.1
    have h₂ := abs_le.mp hx.2
    constructor <;> constructor <;> dsimp [d] <;> linarith
  have he : d ∈ Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (-3 / 4 : ℝ) (3 / 4) := by
    constructor <;> constructor <;> linarith [hd.1.1, hd.1.2, hd.2.1, hd.2.2]
  refine Set.mem_add.mpr ⟨integerCellCenter a + d, ⟨d, hd, rfl⟩, d, he, ?_⟩
  apply Prod.ext <;> dsimp [integerCellCenter, d] <;> ring

private theorem combination_near_cell (a q r : ℤ × ℤ)
    (hq : IsIntegerCellNear q a) (hr : IsIntegerCellNear r a)
    (m n : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m + n = 1) :
    |(m • integerCellCenter q + n • integerCellCenter r).1 - (a.1 : ℝ)| ≤ 1 ∧
      |(m • integerCellCenter q + n • integerCellCenter r).2 - (a.2 : ℝ)| ≤ 1 := by
  have hq₁ : |(q.1 : ℝ) - (a.1 : ℝ)| ≤ 1 := by exact_mod_cast hq.1
  have hq₂ : |(q.2 : ℝ) - (a.2 : ℝ)| ≤ 1 := by exact_mod_cast hq.2
  have hr₁ : |(r.1 : ℝ) - (a.1 : ℝ)| ≤ 1 := by exact_mod_cast hr.1
  have hr₂ : |(r.2 : ℝ) - (a.2 : ℝ)| ≤ 1 := by exact_mod_cast hr.2
  have hb₁ := (convex_Icc (-1 : ℝ) 1) (abs_le.mp hq₁) (abs_le.mp hr₁) hm hn hmn
  have hb₂ := (convex_Icc (-1 : ℝ) 1) (abs_le.mp hq₂) (abs_le.mp hr₂) hm hn hmn
  have he (s t u : ℝ) : m * (s - u) + n * (t - u) = m * s + n * t - u := by
    rw [show m = 1 - n by linarith]
    ring
  constructor
  · simpa only [IsIntegerCellNear, integerCellCenter, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul, he, abs_le, mem_Icc] using hb₁
  · simpa only [IsIntegerCellNear, integerCellCenter, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul, he, abs_le, mem_Icc] using hb₂

/-- Every safe exterior edge is a straight segment contained in the genuine
radius-three-quarters collar. Source: SCP10, lines 1935–1990; auxiliary geometry. -/
theorem integerExteriorCollarGraph_segment_subset (A : Finset (ℤ × ℤ))
    {q r : integerExteriorBand A} (hqr : (integerExteriorCollarGraph A).Adj q r) :
    segment ℝ (integerCellCenter q.1) (integerCellCenter r.1) ⊆ integerExteriorCollar A := by
  rw [segment_subset_iff]
  intro m n hm hn hmn
  obtain ⟨hstep, a, ha, hq, hr⟩ := hqr
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy, d, hd, hxy⟩ := Set.mem_add.mp
      (mem_integerClosedCell_add_of_abs_le_one a _ (combination_near_cell a q.1 r.1 hq hr
        m n hm hn hmn))
    exact Set.mem_add.mpr ⟨y, mem_iUnion_of_mem a (mem_iUnion_of_mem ha hy), d, hd, hxy⟩
  · intro hx
    obtain ⟨b, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hb, hx⟩ := Set.mem_iUnion.mp hx
    rcases occupiedCell_of_mem_unit_segment q.1 r.1 b hstep m n hm hn hmn hx with h | h
    · exact q.2.1 (h ▸ hb)
    · exact r.2.1 (h ▸ hb)

/-- An integer center belongs to the occupied closed-cell domain precisely when
that center is occupied. -/
theorem integerCellCenter_mem_closedCellUnion_iff (A : Finset (ℤ × ℤ)) (q : ℤ × ℤ) :
    integerCellCenter q ∈ integerClosedCellUnion A ↔ q ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ha, hx⟩ := Set.mem_iUnion.mp hx
    have hb := (mem_integerClosedCell_iff a (integerCellCenter q)).mp hx
    have h₁ := integer_eq_of_abs_cast_sub_le_half q.1 a.1 hb.1
    have h₂ := integer_eq_of_abs_cast_sub_le_half q.2 a.2 hb.2
    exact (Prod.ext h₁ h₂).symm ▸ ha
  · intro hq
    apply mem_iUnion_of_mem q
    apply mem_iUnion_of_mem hq
    exact ⟨0, by constructor <;> constructor <;> norm_num, by simp [integerCellCenter]⟩

/-- Integer centers in the genuine radius-three-quarters exterior collar are
exactly the exterior band vertices. The radius includes diagonal neighbors and
excludes centers two lattice steps away in either coordinate. -/
theorem integerCellCenter_mem_exteriorCollar_iff (A : Finset (ℤ × ℤ)) (q : ℤ × ℤ) :
    integerCellCenter q ∈ integerExteriorCollar A ↔ q ∈ integerExteriorBand A := by
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨fun hq => hnot ((integerCellCenter_mem_closedCellUnion_iff A q).mpr hq), ?_⟩
    obtain ⟨y, hy, e, he, hxy⟩ := Set.mem_add.mp hx
    obtain ⟨a, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨ha, d, hd, rfl⟩ := Set.mem_iUnion.mp hy
    have h₁ := congrArg Prod.fst hxy
    have h₂ := congrArg Prod.snd hxy
    change (a.1 : ℝ) + d.1 + e.1 = (q.1 : ℝ) at h₁
    change (a.2 : ℝ) + d.2 + e.2 = (q.2 : ℝ) at h₂
    have hr₁ : (-2 : ℝ) < (q.1 : ℝ) - (a.1 : ℝ) ∧
        (q.1 : ℝ) - (a.1 : ℝ) < 2 := by
      constructor <;> linarith [hd.1.1, hd.1.2, he.1.1, he.1.2]
    have hr₂ : (-2 : ℝ) < (q.2 : ℝ) - (a.2 : ℝ) ∧
        (q.2 : ℝ) - (a.2 : ℝ) < 2 := by
      constructor <;> linarith [hd.2.1, hd.2.2, he.2.1, he.2.2]
    have hi₁ : (-2 : ℤ) < q.1 - a.1 ∧ q.1 - a.1 < 2 := by exact_mod_cast hr₁
    have hi₂ : (-2 : ℤ) < q.2 - a.2 ∧ q.2 - a.2 < 2 := by exact_mod_cast hr₂
    refine ⟨a, ha, ?_⟩
    constructor <;> rw [abs_le] <;> omega
  · rintro ⟨hq, a, ha, hnear⟩
    refine ⟨?_, fun hx => hq ((integerCellCenter_mem_closedCellUnion_iff A q).mp hx)⟩
    have hb : |(q.1 : ℝ) - (a.1 : ℝ)| ≤ 1 ∧ |(q.2 : ℝ) - (a.2 : ℝ)| ≤ 1 := by
      exact_mod_cast hnear
    obtain ⟨y, hy, d, hd, hxy⟩ := Set.mem_add.mp
      (mem_integerClosedCell_add_of_abs_le_one a (integerCellCenter q) hb)
    exact Set.mem_add.mpr ⟨y, mem_iUnion_of_mem a (mem_iUnion_of_mem ha hy), d, hd, hxy⟩

/-- A safe exterior graph walk gives a genuine continuous path inside the
radius-three-quarters collar between its lattice centers. Connectivity is a
separate combinatorial assertion, not a hypothesis defining a disk.
Source: SCP10, proof of Theorem 6.9, lines 1935–1990. -/
theorem joinedIn_integerExteriorCollar_of_reachable (A : Finset (ℤ × ℤ))
    {q r : integerExteriorBand A} (hqr : (integerExteriorCollarGraph A).Reachable q r) :
    JoinedIn (integerExteriorCollar A) (integerCellCenter q.1) (integerCellCenter r.1) := by
  obtain ⟨p⟩ := hqr
  induction p with
  | @nil q => exact JoinedIn.refl ((integerCellCenter_mem_exteriorCollar_iff A q.1).mpr q.2)
  | cons h p ih =>
    exact (JoinedIn.of_segment_subset (integerExteriorCollarGraph_segment_subset A h)).trans ih

end TNLean.PEPS
