/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionWalkWinding
import TNLean.PEPS.TorusIntegerStepWinding
import Mathlib.Algebra.Order.Round
import Mathlib.Combinatorics.SimpleGraph.Cayley

/-!
# Exterior lattice walks from supplied continuous paths

A continuous plane path whose torus projection avoids the actual closed-cell
region can be replaced by a native walk in the induced complement. Its integer
endpoint displacement determines the seam crossing numbers of the resulting
walk. The construction uses only one-cell, two-cell, and four-cell open
rectangles; at a grid corner, all four touching cells are exterior.

**Scope restriction (supplied exterior paths):** This is an auxiliary geometric
step for the complement argument of SCP10, Theorem 6.9, lines 1935–1990.
The existence of the supplied exterior path from a disk hypothesis remains a
separate theorem; no disk, flatness, or boundary-word relation is assumed here.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section

namespace TNLean.PEPS

private theorem interval_cell_cover (x : ℝ) :
    ∃ l r : ℤ, (r = l ∨ r = l + 1) ∧
      x ∈ Set.Ioo ((l : ℝ) - 1 / 2) ((r : ℝ) + 1 / 2) ∧
      ∀ j : ℤ, l ≤ j → j ≤ r → |x - (j : ℝ)| ≤ 1 / 2 := by
  let r := round x
  have hr := (round_eq_iff (x := x) (n := r)).mp rfl
  by_cases hx : x = (r : ℝ) - 1 / 2
  · refine ⟨r - 1, r, Or.inr (by omega), ?_, ?_⟩
    · simp only [Int.cast_sub, Int.cast_one]
      constructor <;> linarith [hr.2]
    · intro j hjl hjr
      have hj : j = r - 1 ∨ j = r := by omega
      rcases hj with rfl | rfl
      · rw [hx]
        norm_num
      · rw [hx]
        norm_num
  · refine ⟨r, r, Or.inl rfl, ⟨lt_of_le_of_ne hr.1 (Ne.symm hx), hr.2⟩, ?_⟩
    intro j hjl hjr
    have hj : j = r := by omega
    subst j
    exact abs_sub_round x

private def integerVertex {width height : ℕ} (a : ℤ × ℤ) : TorusVertex width height :=
  ((a.1 : ZMod width), (a.2 : ZMod height))

variable {width height : ℕ}

private theorem touching_center_exterior (R : Finset (TorusVertex width height))
    (x : ℝ × ℝ) (hx : torusRealProjection width height x ∉ torusRegionRealization R)
    (a : ℤ × ℤ) (ha₁ : |x.1 - (a.1 : ℝ)| ≤ 1 / 2)
    (ha₂ : |x.2 - (a.2 : ℝ)| ≤ 1 / 2) : integerVertex a ∉ R := by
  intro ha
  apply hx
  apply Set.mem_iUnion_of_mem (integerVertex a)
  apply Set.mem_iUnion_of_mem ha
  refine ⟨x - ((a.1 : ℝ), (a.2 : ℝ)), ?_, ?_⟩
  · constructor
    · change -1 / 2 ≤ x.1 - (a.1 : ℝ) ∧ x.1 - (a.1 : ℝ) ≤ 1 / 2
      constructor <;> linarith [(abs_le.mp ha₁).1, (abs_le.mp ha₁).2]
    · change -1 / 2 ≤ x.2 - (a.2 : ℝ) ∧ x.2 - (a.2 : ℝ) ≤ 1 / 2
      constructor <;> linarith [(abs_le.mp ha₂).1, (abs_le.mp ha₂).2]
  · change torusVertexPoint ((a.1 : ZMod width), (a.2 : ZMod height)) +
      torusRealProjection width height (x - ((a.1 : ℝ), (a.2 : ℝ))) = _
    rw [torusVertexPoint_intCast, ← map_add]
    congr 1
    abel

private structure ExteriorCellBox (R : Finset (TorusVertex width height)) where
  lower : ℤ × ℤ
  upper : ℤ × ℤ
  horizontal : upper.1 = lower.1 ∨ upper.1 = lower.1 + 1
  vertical : upper.2 = lower.2 ∨ upper.2 = lower.2 + 1
  exterior : ∀ a : ℤ × ℤ, lower.1 ≤ a.1 → a.1 ≤ upper.1 →
    lower.2 ≤ a.2 → a.2 ≤ upper.2 → integerVertex a ∉ R

private def ExteriorCellBox.openSet {R : Finset (TorusVertex width height)}
    (B : ExteriorCellBox R) : Set (ℝ × ℝ) :=
  Set.Ioo ((B.lower.1 : ℝ) - 1 / 2) ((B.upper.1 : ℝ) + 1 / 2) ×ˢ
    Set.Ioo ((B.lower.2 : ℝ) - 1 / 2) ((B.upper.2 : ℝ) + 1 / 2)

private theorem ExteriorCellBox.isOpen_openSet {R : Finset (TorusVertex width height)}
    (B : ExteriorCellBox R) : IsOpen B.openSet := isOpen_Ioo.prod isOpen_Ioo

private theorem exists_exteriorCellBox (R : Finset (TorusVertex width height))
    (x : ℝ × ℝ) (hx : torusRealProjection width height x ∉ torusRegionRealization R) :
    ∃ B : ExteriorCellBox R, x ∈ B.openSet := by
  obtain ⟨l₁, r₁, h₁, hx₁, hc₁⟩ := interval_cell_cover x.1
  obtain ⟨l₂, r₂, h₂, hx₂, hc₂⟩ := interval_cell_cover x.2
  exact ⟨⟨(l₁, l₂), (r₁, r₂), h₁, h₂, fun a hl₁ hr₁ hl₂ hr₂ =>
    touching_center_exterior R x hx a (hc₁ a.1 hl₁ hr₁) (hc₂ a.2 hl₂ hr₂)⟩,
      hx₁, hx₂⟩

private def integerLatticeGraph : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.addCayley {(1, 0), (0, 1)}

private def integerExteriorGraph (R : Finset (TorusVertex width height)) :
    SimpleGraph {a : ℤ × ℤ // integerVertex a ∉ R} :=
  integerLatticeGraph.induce {a | integerVertex a ∉ R}

private def roundedPoint (x : ℝ × ℝ) : ℤ × ℤ := (round x.1, round x.2)

private theorem rounded_mem_interval (l r : ℤ) (x : ℝ)
    (hx : x ∈ Set.Ioo ((l : ℝ) - 1 / 2) ((r : ℝ) + 1 / 2)) :
    l ≤ round x ∧ round x ≤ r := by
  have hl : (l : ℝ) - 1 < (round x : ℝ) := by linarith [hx.1, sub_half_lt_round x]
  have hr : (round x : ℝ) < (r : ℝ) + 1 := by linarith [hx.2, round_le_add_half x]
  have hl' : l - 1 < round x := by exact_mod_cast hl
  have hr' : round x < r + 1 := by exact_mod_cast hr
  omega

private theorem ExteriorCellBox.rounded_bounds {R : Finset (TorusVertex width height)}
    (B : ExteriorCellBox R) {x : ℝ × ℝ} (hx : x ∈ B.openSet) :
    B.lower.1 ≤ (roundedPoint x).1 ∧ (roundedPoint x).1 ≤ B.upper.1 ∧
      B.lower.2 ≤ (roundedPoint x).2 ∧ (roundedPoint x).2 ≤ B.upper.2 := by
  exact ⟨(rounded_mem_interval _ _ _ hx.1).1, (rounded_mem_interval _ _ _ hx.1).2,
    (rounded_mem_interval _ _ _ hx.2).1, (rounded_mem_interval _ _ _ hx.2).2⟩

private theorem reachable_of_unit_step {R : Finset (TorusVertex width height)}
    (a b : {a : ℤ × ℤ // integerVertex a ∉ R}) (d : ℤ × ℤ)
    (hd : d ∈ ({(1, 0), (0, 1)} : Set (ℤ × ℤ)))
    (hab : a.1 + d = b.1 ∨ a.1 = b.1 + d) : (integerExteriorGraph R).Reachable a b := by
  by_cases heq : a = b
  · rw [heq]
  · apply SimpleGraph.Adj.reachable
    exact (SimpleGraph.addCayley_adj' _ _ _).mpr
      ⟨fun h => heq (Subtype.ext h), d, hd, hab⟩

private theorem ExteriorCellBox.reachable {R : Finset (TorusVertex width height)}
    (B : ExteriorCellBox R) (a b : {a : ℤ × ℤ // integerVertex a ∉ R})
    (ha : B.lower.1 ≤ a.1.1 ∧ a.1.1 ≤ B.upper.1 ∧
      B.lower.2 ≤ a.1.2 ∧ a.1.2 ≤ B.upper.2)
    (hb : B.lower.1 ≤ b.1.1 ∧ b.1.1 ≤ B.upper.1 ∧
      B.lower.2 ≤ b.1.2 ∧ b.1.2 ≤ B.upper.2) :
    (integerExteriorGraph R).Reachable a b := by
  let c : {a : ℤ × ℤ // integerVertex a ∉ R} :=
    ⟨(b.1.1, a.1.2), B.exterior _ hb.1 hb.2.1 ha.2.2.1 ha.2.2.2⟩
  have hac : (integerExteriorGraph R).Reachable a c := by
    by_cases hx : a.1.1 = b.1.1
    · have h : a = c := Subtype.ext (Prod.ext hx rfl)
      rw [h]
    · apply reachable_of_unit_step a c (1, 0) (by simp)
      have hh := B.horizontal
      have h : a.1.1 + 1 = b.1.1 ∨ a.1.1 = b.1.1 + 1 := by omega
      rcases h with h | h
      · exact Or.inl (Prod.ext h (by simp [c]))
      · exact Or.inr (Prod.ext h (by simp [c]))
  have hcb : (integerExteriorGraph R).Reachable c b := by
    by_cases hy : a.1.2 = b.1.2
    · have h : c = b := Subtype.ext (Prod.ext rfl hy)
      rw [h]
    · apply reachable_of_unit_step c b (0, 1) (by simp)
      have hv := B.vertical
      have h : a.1.2 + 1 = b.1.2 ∨ a.1.2 = b.1.2 + 1 := by omega
      rcases h with h | h
      · exact Or.inl (Prod.ext (by simp [c]) h)
      · exact Or.inr (Prod.ext (by simp [c]) h)
  exact hac.trans hcb

private theorem exists_integerExteriorWalk (R : Finset (TorusVertex width height))
    (a b : {a : ℤ × ℤ // integerVertex a ∉ R})
    (γ : Path ((a.1.1 : ℝ), (a.1.2 : ℝ)) ((b.1.1 : ℝ), (b.1.2 : ℝ)))
    (hγ : ∀ t, torusRealProjection width height (γ t) ∉ torusRegionRealization R) :
    Nonempty ((integerExteriorGraph R).Walk a b) := by
  let q (t : unitInterval) : {a : ℤ × ℤ // integerVertex a ∉ R} :=
    ⟨roundedPoint (γ t), touching_center_exterior R (γ t) (hγ t)
      (roundedPoint (γ t)) (abs_sub_round _) (abs_sub_round _)⟩
  obtain ⟨t, ht₀, ht, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun B : ExteriorCellBox R => γ ⁻¹' B.openSet)
      (fun B => B.isOpen_openSet.preimage γ.continuous) (by
        intro s _
        obtain ⟨B, hB⟩ := exists_exteriorCellBox R (γ s) (hγ s)
        exact Set.mem_iUnion.mpr ⟨B, hB⟩)
  have hwalk (n : ℕ) : (integerExteriorGraph R).Reachable (q (t 0)) (q (t n)) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      obtain ⟨B, hB⟩ := hsub n
      have h₀ : γ (t n) ∈ B.openSet := hB ⟨le_rfl, ht n.le_succ⟩
      have h₁ : γ (t (n + 1)) ∈ B.openSet := hB ⟨ht n.le_succ, le_rfl⟩
      exact ih.trans (B.reachable _ _ (B.rounded_bounds h₀) (B.rounded_bounds h₁))
  have hqa : q 0 = a := by
    apply Subtype.ext
    simp only [q, roundedPoint, Path.source, round_intCast]
  have hqb : q 1 = b := by
    apply Subtype.ext
    simp only [q, roundedPoint, Path.target, round_intCast]
  simpa only [ht₀, hN N le_rfl, hqa, hqb, SimpleGraph.Reachable] using hwalk N

variable [NeZero width] [NeZero height] [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

private theorem integerLatticeGraph_adj_cases {a b : ℤ × ℤ}
    (hab : integerLatticeGraph.Adj a b) :
    a + (1, 0) = b ∨ a = b + (1, 0) ∨ a + (0, 1) = b ∨ a = b + (0, 1) := by
  obtain ⟨_, d, hd, h⟩ := (SimpleGraph.addCayley_adj' _ _ _).mp hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl
  · exact h.elim Or.inl (fun h => Or.inr (Or.inl h))
  · exact Or.inr (Or.inr h)

private def integerExteriorProjection (R : Finset (TorusVertex width height)) :
    integerExteriorGraph R →g
      (torusGraph width height).induce ((Finset.univ \ R : Finset _) : Set _) where
  toFun a := ⟨integerVertex (width := width) (height := height) a.1,
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, a.2⟩⟩
  map_rel' := by
    intro a b hab
    change (torusGraph width height).Adj (integerVertex a.1) (integerVertex b.1)
    rcases integerLatticeGraph_adj_cases (a := a.1) (b := b.1) hab with h | h | h | h
    · rw [← h]
      simp [integerVertex, torusHorizontalNeighbor, torusVerticalNeighbor]
    · rw [h]
      simp [integerVertex, torusHorizontalNeighbor, torusVerticalNeighbor]
    · rw [← h]
      simp [integerVertex, torusHorizontalNeighbor, torusVerticalNeighbor]
    · rw [h]
      simp [integerVertex, torusHorizontalNeighbor, torusVerticalNeighbor]

private theorem projected_step_winding (a b : ℤ × ℤ)
    (hab : integerLatticeGraph.Adj a b)
    (h : (torusGraph width height).Adj (integerVertex a) (integerVertex b)) :
    torusDirectedWinding h =
      torusIntegerDeckCoordinate width height b - torusIntegerDeckCoordinate width height a :=
  torusDirectedWinding_eq_of_integerUnitStep a b (integerLatticeGraph_adj_cases hab) h

private theorem projected_walk_winding (R : Finset (TorusVertex width height))
    {a b : {a : ℤ × ℤ // integerVertex a ∉ R}} (p : (integerExteriorGraph R).Walk a b) :
    torusWalkWinding (p.map ((SimpleGraph.Embedding.induce (G := torusGraph width height)
        ((Finset.univ \ R : Finset _) : Set (TorusVertex width height))).toHom.comp
          (integerExteriorProjection R))) =
      torusIntegerDeckCoordinate width height b.1 -
        torusIntegerDeckCoordinate width height a.1 := by
  induction p with
  | nil => simp [torusWalkWinding]
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.map_cons, torusWalkWinding, ih]
    have hs := projected_step_winding u.1 v.1 h
      (((SimpleGraph.Embedding.induce (G := torusGraph width height)
        ((Finset.univ \ R : Finset _) : Set (TorusVertex width height))).toHom.comp
          (integerExteriorProjection R)).map_adj h)
    calc
      _ = torusIntegerDeckCoordinate width height w.1 -
          torusIntegerDeckCoordinate width height v.1 +
          (torusIntegerDeckCoordinate width height v.1 -
            torusIntegerDeckCoordinate width height u.1) :=
        congrArg (torusIntegerDeckCoordinate width height w.1 -
          torusIntegerDeckCoordinate width height v.1 + ·) hs
      _ = _ := by abel

private theorem winding_copy {u v u' v' : TorusVertex width height}
    (p : (torusGraph width height).Walk u v) (hu : u = u') (hv : v = v') :
    torusWalkWinding (p.copy hu hv) = torusWalkWinding p := by
  subst u' v'
  rfl

/-- A supplied continuous plane path avoiding the actual periodic closed-cell
region gives an induced-complement lattice walk with exactly its endpoint deck
coordinate difference. Source: SCP10, the complement-path argument of
Theorem 6.9, lines 1935–1990; auxiliary supplied-path approximation. -/
theorem exists_complementWalk_of_exterior_planePath
    (R : Finset (TorusVertex width height))
    (v w : {v : TorusVertex width height // v ∈ Finset.univ \ R})
    (a b : ℤ × ℤ)
    (ha : ((a.1 : ZMod width), (a.2 : ZMod height)) = v.1)
    (hb : ((b.1 : ZMod width), (b.2 : ZMod height)) = w.1)
    (γ : Path ((a.1 : ℝ), (a.2 : ℝ)) ((b.1 : ℝ), (b.2 : ℝ)))
    (hγ : ∀ t, torusRealProjection width height (γ t) ∉ torusRegionRealization R) :
    ∃ p : ((torusGraph width height).induce
        ((Finset.univ \ R : Finset _) : Set (TorusVertex width height))).Walk v w,
      torusWalkWinding (p.map (SimpleGraph.Embedding.induce
          ((Finset.univ \ R : Finset _) : Set (TorusVertex width height))).toHom) =
        (b.1 / (width : ℤ) - a.1 / (width : ℤ),
          b.2 / (height : ℤ) - a.2 / (height : ℤ)) := by
  let a' : {a : ℤ × ℤ // integerVertex a ∉ R} := ⟨a, by
    change ((a.1 : ZMod width), (a.2 : ZMod height)) ∉ R
    rw [ha]
    exact (Finset.mem_sdiff.mp v.2).2⟩
  let b' : {a : ℤ × ℤ // integerVertex a ∉ R} := ⟨b, by
    change ((b.1 : ZMod width), (b.2 : ZMod height)) ∉ R
    rw [hb]
    exact (Finset.mem_sdiff.mp w.2).2⟩
  obtain ⟨p⟩ := exists_integerExteriorWalk R a' b' γ hγ
  have hav : integerExteriorProjection R a' = v := Subtype.ext ha
  have hbw : integerExteriorProjection R b' = w := Subtype.ext hb
  refine ⟨(p.map (integerExteriorProjection R)).copy hav hbw, ?_⟩
  rw [SimpleGraph.Walk.map_copy, winding_copy, SimpleGraph.Walk.map_map]
  exact projected_walk_winding R p

end TNLean.PEPS
