/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ambient square cells and their uniform local count

A translated half-open square grid in `ℝ × ℝ`, equipped with the product (maximum)
metric, has a unique owner cell for every point. Its cells have diameter at most their
side length. A finite cover by radius-`R * s` squares bounds the number of cells of side
`d * s` touching a radius-`r * s` enlargement by
`F.card * (2 * ⌈(R + r) / d⌉₊ + 3) ^ 2`, independently of `s`.

This is the ambient grid and bounded-square-cover step in `02-information.tex`, lines
685–717, of *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, source revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The Lean construction and proofs are original; no upstream Lean proof text is reused.
This does not formalize the later recursive cell-count argument.
-/

namespace TNLean.PEPS.Approximation.AngularGrid

noncomputable section

/-- The actual translated half-open ambient square with integer index `i`. -/
def cell (o : ℝ × ℝ) (q : ℝ) (i : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {x | o.1 + (i.1 : ℝ) * q ≤ x.1 ∧ x.1 < o.1 + ((i.1 : ℝ) + 1) * q ∧
    o.2 + (i.2 : ℝ) * q ≤ x.2 ∧ x.2 < o.2 + ((i.2 : ℝ) + 1) * q}

/-- The grid owner, defined by coordinatewise integer floors. -/
def owner (o : ℝ × ℝ) (q : ℝ) (x : ℝ × ℝ) : ℤ × ℤ :=
  (⌊(x.1 - o.1) / q⌋, ⌊(x.2 - o.2) / q⌋)

/-- An ambient enlargement expressed using a witness in the original set. -/
def near (r : ℝ) (A : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {y | ∃ x ∈ A, dist y x ≤ r}

/-- A cell is selected precisely when it touches the indicated ambient enlargement. -/
def touches (o : ℝ × ℝ) (q r : ℝ) (A : Set (ℝ × ℝ)) (i : ℤ × ℤ) : Prop :=
  ∃ y ∈ cell o q i, y ∈ near r A

private theorem floor_cell_bounds (o x : ℝ) {q : ℝ} (hq : 0 < q) :
    o + (⌊(x - o) / q⌋ : ℝ) * q ≤ x ∧
      x < o + ((⌊(x - o) / q⌋ : ℝ) + 1) * q := by
  constructor
  · have h := (le_div_iff₀ hq).mp (Int.floor_le ((x - o) / q))
    linarith
  · have h := (div_lt_iff₀ hq).mp (Int.lt_floor_add_one ((x - o) / q))
    linarith

/-- Every ambient point belongs to its floor-indexed cell, including grid boundaries. -/
theorem mem_cell_owner {o x : ℝ × ℝ} {q : ℝ} (hq : 0 < q) :
    x ∈ cell o q (owner o q x) := by
  obtain ⟨h₁, h₂⟩ := floor_cell_bounds o.1 x.1 hq
  obtain ⟨h₃, h₄⟩ := floor_cell_bounds o.2 x.2 hq
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- Membership recovers the unique cell owner. -/
theorem owner_eq_of_mem_cell {o x : ℝ × ℝ} {q : ℝ} {i : ℤ × ℤ}
    (hq : 0 < q) (hx : x ∈ cell o q i) : owner o q x = i := by
  rcases hx with ⟨h₁, h₂, h₃, h₄⟩
  apply Prod.ext
  · apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ hq).mpr
      linarith
    · apply (div_lt_iff₀ hq).mpr
      linarith
  · apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ hq).mpr
      linarith
    · apply (div_lt_iff₀ hq).mpr
      linarith

/-- These squares form a partition, rather than an arbitrary family of small sets. -/
theorem cell_index_unique {o x : ℝ × ℝ} {q : ℝ} {i j : ℤ × ℤ}
    (hq : 0 < q) (hi : x ∈ cell o q i) (hj : x ∈ cell o q j) : i = j :=
  (owner_eq_of_mem_cell hq hi).symm.trans (owner_eq_of_mem_cell hq hj)

/-- Two points of a side-`q` cell are at distance at most `q` in the ambient maximum metric. -/
theorem dist_le_of_mem_cell {o x y : ℝ × ℝ} {q : ℝ} {i : ℤ × ℤ}
    (hq : 0 < q) (hx : x ∈ cell o q i) (hy : y ∈ cell o q i) : dist x y ≤ q := by
  rcases hx with ⟨hx₁, hx₂, hx₃, hx₄⟩
  rcases hy with ⟨hy₁, hy₂, hy₃, hy₄⟩
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

/-- A finite index square, with one extra cell on each side to handle grid boundaries. -/
def indexBox (j : ℤ × ℤ) (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (j.1 - (N : ℤ) - 1) (j.1 + (N : ℤ) + 1)).product
    (Finset.Icc (j.2 - (N : ℤ) - 1) (j.2 + (N : ℤ) + 1))

/-- The index square has an exact, translation-independent count. -/
theorem card_indexBox (j : ℤ × ℤ) (N : ℕ) :
    (indexBox j N).card = (2 * N + 3) ^ 2 := by
  rw [indexBox, Finset.card_product, Int.card_Icc, Int.card_Icc]
  have h₁ : j.1 + (N : ℤ) + 1 + 1 - (j.1 - (N : ℤ) - 1) =
      ((2 * N + 3 : ℕ) : ℤ) := by omega
  have h₂ : j.2 + (N : ℤ) + 1 + 1 - (j.2 - (N : ℤ) - 1) =
      ((2 * N + 3 : ℕ) : ℤ) := by omega
  rw [h₁, h₂]
  simp [pow_two]

private theorem coordinate_index_bounds {o x c q t : ℝ} {i j : ℤ} {N : ℕ}
    (hq : 0 < q)
    (hx₀ : o + (i : ℝ) * q ≤ x) (hx₁ : x < o + ((i : ℝ) + 1) * q)
    (hc₀ : o + (j : ℝ) * q ≤ c) (hc₁ : c < o + ((j : ℝ) + 1) * q)
    (hxc : |x - c| ≤ t) (ht : t ≤ (N : ℝ) * q) :
    j - (N : ℤ) - 1 ≤ i ∧ i ≤ j + (N : ℤ) + 1 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hxc
  have hleft : ((j : ℝ) - (N : ℝ) - 1) * q < (i : ℝ) * q := by
    nlinarith
  have hright : (i : ℝ) * q < ((j : ℝ) + (N : ℝ) + 1) * q := by
    nlinarith
  have hleft' := le_of_lt ((mul_lt_mul_right hq).mp hleft)
  have hright' := le_of_lt ((mul_lt_mul_right hq).mp hright)
  constructor
  · exact_mod_cast hleft'
  · exact_mod_cast hright'

/-- A cell touching a bounded-radius square has its index in an explicit finite index square. -/
theorem mem_indexBox_of_dist_le {o x c : ℝ × ℝ} {q t : ℝ} {i : ℤ × ℤ} {N : ℕ}
    (hq : 0 < q) (hx : x ∈ cell o q i) (hxc : dist x c ≤ t)
    (ht : t ≤ (N : ℝ) * q) : i ∈ indexBox (owner o q c) N := by
  obtain ⟨hx₁, hx₂, hx₃, hx₄⟩ := hx
  obtain ⟨hc₁, hc₂, hc₃, hc₄⟩ := mem_cell_owner (o := o) (x := c) hq
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hxc
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr (coordinate_index_bounds hq hx₁ hx₂ hc₁ hc₂ hxc.1 ht),
      Finset.mem_Icc.mpr (coordinate_index_bounds hq hx₃ hx₄ hc₃ hc₄ hxc.2 ht)⟩

/-- Candidate indices supplied by a finite collection of real, not necessarily lattice, centers. -/
def candidateIndices (o : ℝ × ℝ) (q : ℝ) (F : Finset (ℝ × ℝ)) (N : ℕ) :
    Finset (ℤ × ℤ) :=
  F.biUnion fun c ↦ indexBox (owner o q c) N

/-- The candidates have a bound uniform in the grid origin, mesh, and center locations. -/
theorem card_candidateIndices_le (o : ℝ × ℝ) (q : ℝ) (F : Finset (ℝ × ℝ)) (N : ℕ) :
    (candidateIndices o q F N).card ≤ F.card * (2 * N + 3) ^ 2 := by
  unfold candidateIndices
  calc
    _ ≤ ∑ c ∈ F, (indexBox (owner o q c) N).card := Finset.card_biUnion_le
    _ = F.card * (2 * N + 3) ^ 2 := by simp [card_indexBox]

/-- A radius-`R` finite cover captures every cell touching the radius-`r` enlargement. -/
theorem touches_mem_candidateIndices {o : ℝ × ℝ} {q R r : ℝ}
    {A : Set (ℝ × ℝ)} {F : Finset (ℝ × ℝ)} {N : ℕ} {i : ℤ × ℤ}
    (hq : 0 < q) (hcover : ∀ x ∈ A, ∃ c ∈ F, dist x c ≤ R)
    (hbound : R + r ≤ (N : ℝ) * q) (hi : touches o q r A i) :
    i ∈ candidateIndices o q F N := by
  obtain ⟨y, hy, x, hx, hyx⟩ := hi
  obtain ⟨c, hc, hxc⟩ := hcover x hx
  apply Finset.mem_biUnion.mpr
  refine ⟨c, hc, mem_indexBox_of_dist_le hq hy ?_ hbound⟩
  calc
    dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
    _ ≤ r + R := add_le_add hyx hxc
    _ = R + r := add_comm _ _

/-- The actual selected cells form a finite set with the same uniform cardinal bound. -/
theorem exists_selectedIndices_of_cover {o : ℝ × ℝ} {q R r : ℝ}
    {A : Set (ℝ × ℝ)} {F : Finset (ℝ × ℝ)} {N : ℕ}
    (hq : 0 < q) (hcover : ∀ x ∈ A, ∃ c ∈ F, dist x c ≤ R)
    (hbound : R + r ≤ (N : ℝ) * q) :
    ∃ S : Finset (ℤ × ℤ), (∀ i, i ∈ S ↔ touches o q r A i) ∧
      S.card ≤ F.card * (2 * N + 3) ^ 2 := by
  classical
  refine ⟨(candidateIndices o q F N).filter (touches o q r A), ?_, ?_⟩
  · intro i
    simp only [Finset.mem_filter]
    exact ⟨fun hi ↦ hi.2, fun hi ↦
      ⟨touches_mem_candidateIndices hq hcover hbound hi, hi⟩⟩
  · exact (Finset.card_filter_le _ _).trans (card_candidateIndices_le o q F N)

/-- Scaling both the cover and mesh leaves the finite candidate bound unchanged. -/
theorem touches_mem_candidateIndices_scaled {o : ℝ × ℝ} {d s R r : ℝ}
    {A : Set (ℝ × ℝ)} {F : Finset (ℝ × ℝ)} {i : ℤ × ℤ}
    (hd : 0 < d) (hs : 0 < s)
    (hcover : ∀ x ∈ A, ∃ c ∈ F, dist x c ≤ R * s)
    (hi : touches o (d * s) (r * s) A i) :
    i ∈ candidateIndices o (d * s) F ⌈(R + r) / d⌉₊ := by
  apply touches_mem_candidateIndices (mul_pos hd hs) hcover ?_ hi
  have h := (div_le_iff₀ hd).mp (Nat.le_ceil ((R + r) / d))
  calc
    R * s + r * s = (R + r) * s := by ring
    _ ≤ ((⌈(R + r) / d⌉₊ : ℝ) * d) * s := mul_le_mul_of_nonneg_right h hs.le
    _ = (⌈(R + r) / d⌉₊ : ℝ) * (d * s) := by ring

/-- A shape-independent cell count for a finitely covered scaled layer.
The displayed bound depends on `F.card`, `R`, `r`, and `d`, and not on `s`. -/
theorem exists_selectedIndices_scaled {o : ℝ × ℝ} {d s R r : ℝ}
    {A : Set (ℝ × ℝ)} {F : Finset (ℝ × ℝ)}
    (hd : 0 < d) (hs : 0 < s)
    (hcover : ∀ x ∈ A, ∃ c ∈ F, dist x c ≤ R * s) :
    ∃ S : Finset (ℤ × ℤ), (∀ i, i ∈ S ↔ touches o (d * s) (r * s) A i) ∧
      S.card ≤ F.card * (2 * ⌈(R + r) / d⌉₊ + 3) ^ 2 := by
  apply exists_selectedIndices_of_cover (mul_pos hd hs) hcover
  have h := (div_le_iff₀ hd).mp (Nat.le_ceil ((R + r) / d))
  calc
    R * s + r * s = (R + r) * s := by ring
    _ ≤ ((⌈(R + r) / d⌉₊ : ℝ) * d) * s := mul_le_mul_of_nonneg_right h hs.le
    _ = (⌈(R + r) / d⌉₊ : ℝ) * (d * s) := by ring

end

end TNLean.PEPS.Approximation.AngularGrid
