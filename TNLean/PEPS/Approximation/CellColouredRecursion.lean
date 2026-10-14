/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CellColouredGeneration

/-!
# The recursion of coloured partitions of a cell

The plane is tiled by the half-open squares of side `s` with lower-left corners
`o + m s`, `m ∈ ℤ²`. One cell `m₀` is chosen; every other cell `m` receives the
forbidden colour `c m`, where the cells of colour `0` make up the conditioning
set. The initial generation (`initialGeneration`) has the chosen cell as its only
active square, of side `s`, with its four sides as chamber lines. It satisfies the
generation invariant regardless of the exterior colours
(`initialGeneration_isValid`).

The recursion iterates `Generation.next` (`gen`). This module records:

* labels change only from allowed to forbidden (`gen_colour_of_ne_none`), and a
  tile point keeps the colour of its family in all later generations
  (`gen_colour_of_mem_tile`);
* the lattice samples of the tiles of the first `m` generations, listed by
  generation, then by active square, then family `0` before family `1`
  (`pieceList`), are pairwise disjoint, and each tile is at distance greater than
  `t₀ = u ^ γ` from every earlier tile of its family (`pairwise_pieceList`);
* there are at most `25 ^ g` active squares in generation `g`
  (`length_gen_squares_le`), hence at most `2 ∑_{g < m} 25 ^ g` tiles.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
  lines 162–188 and 224–311.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.CellPartition

open TNLean.PEPS.AreaLaw.Geometry

/-! ### The grid of cells -/

/-- The lower-left corner of the grid cell `m` of side `s` with origin `o`.
Source: Lemma 3.2, `02-information.tex`, lines 165–166. -/
def cellCorner (o : ℝ × ℝ) (s : ℝ) (m : ℤ × ℤ) : ℝ × ℝ := (o.1 + m.1 * s, o.2 + m.2 * s)

/-- The grid cell containing an ambient point. -/
def cellIndex (o : ℝ × ℝ) (s : ℝ) (p : ℝ × ℝ) : ℤ × ℤ :=
  (⌊(p.1 - o.1) / s⌋, ⌊(p.2 - o.2) / s⌋)

/-- The lattice sample of the grid cell `m`. Source: Lemma 3.2, `02-information.tex`,
lines 166–167. -/
def cellSample (o : ℝ × ℝ) (s : ℝ) (m : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  latticeBox (cellCorner o s m) s

theorem floor_div_eq_of_le_of_lt {a o s : ℝ} (hs : 0 < s) {n : ℤ} (h₁ : o + n * s ≤ a)
    (h₂ : a < o + n * s + s) : ⌊(a - o) / s⌋ = n := by
  rw [Int.floor_eq_iff, le_div_iff₀ hs, div_lt_iff₀ hs]
  constructor <;> linarith

theorem cellIndex_eq_iff {o : ℝ × ℝ} {s : ℝ} (hs : 0 < s) {p : ℝ × ℝ} {m : ℤ × ℤ} :
    cellIndex o s p = m ↔ p ∈ box (cellCorner o s m) s := by
  have key : ∀ a o' : ℝ, ∀ n : ℤ, ⌊(a - o') / s⌋ = n ↔ o' + n * s ≤ a ∧ a < o' + n * s + s := by
    intro a o' n
    rw [Int.floor_eq_iff, le_div_iff₀ hs, div_lt_iff₀ hs]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [cellIndex, Prod.ext_iff, key, key]
  simp only [box, cellCorner, Set.mem_ofPred_eq]
  tauto

theorem mem_cellSample {o : ℝ × ℝ} {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ} {p : ℤ × ℤ} :
    p ∈ cellSample o s m ↔ cellIndex o s (integerPoint p) = m := by
  rw [cellSample, mem_latticeBox, cellIndex_eq_iff hs]

open Classical in
/-- The initial labels: the chosen cell is allowed and every other cell `m` has
forbidden colour `c m`. Source: Lemma 3.2, `02-information.tex`, lines 181–184. -/
def initialColouring (o : ℝ × ℝ) (s : ℝ) (m₀ : ℤ × ℤ) (c : ℤ × ℤ → Fin 2) : Colouring :=
  fun p ↦ if cellIndex o s p = m₀ then none else some (c (cellIndex o s p))

/-- The chosen cell as the initial active square, with its sides as chamber lines.
Source: Lemma 3.2, `02-information.tex`, lines 233–236. -/
def initialSquare (o : ℝ × ℝ) (s : ℝ) (m₀ : ℤ × ℤ) : ActiveSquare :=
  ⟨cellCorner o s m₀, {(cellCorner o s m₀).1, (cellCorner o s m₀).1 + s},
    {(cellCorner o s m₀).2, (cellCorner o s m₀).2 + s}⟩

/-- The initial generation: one active square, the chosen cell, with `u = s`.
Source: Lemma 3.2, `02-information.tex`, lines 233–236. -/
def initialGeneration (o : ℝ × ℝ) (s : ℝ) (m₀ : ℤ × ℤ) (c : ℤ × ℤ → Fin 2) : Generation :=
  ⟨s, [initialSquare o s m₀], initialColouring o s m₀ c⟩

/-- In the padding of a cell, the cell index in one coordinate is decided by the two
sides of the cell. -/
private theorem floor_div_eq_of_sameSide {o s a b : ℝ} {n : ℤ} (hs : 0 < s)
    (ha : o + n * s - s ≤ a) (ha' : a < o + n * s - s + 3 * s) (hb : o + n * s - s ≤ b)
    (hb' : b < o + n * s - s + 3 * s) (h₁ : o + n * s ≤ a ↔ o + n * s ≤ b)
    (h₂ : o + n * s + s ≤ a ↔ o + n * s + s ≤ b) : ⌊(a - o) / s⌋ = ⌊(b - o) / s⌋ := by
  by_cases hA : o + n * s + s ≤ a
  · have hB := h₂.mp hA
    rw [floor_div_eq_of_le_of_lt hs (n := n + 1) (by push_cast; linarith)
        (by push_cast; linarith),
      floor_div_eq_of_le_of_lt hs (n := n + 1) (by push_cast; linarith)
        (by push_cast; linarith)]
  · have hB : ¬o + n * s + s ≤ b := fun h ↦ hA (h₂.mpr h)
    push Not at hA hB
    by_cases hA' : o + n * s ≤ a
    · have hB' := h₁.mp hA'
      rw [floor_div_eq_of_le_of_lt hs hA' hA, floor_div_eq_of_le_of_lt hs hB' hB]
    · have hB' : ¬o + n * s ≤ b := fun h ↦ hA' (h₁.mpr h)
      push Not at hA' hB'
      rw [floor_div_eq_of_le_of_lt hs (n := n - 1) (by push_cast; linarith)
          (by push_cast; linarith),
        floor_div_eq_of_le_of_lt hs (n := n - 1) (by push_cast; linarith)
          (by push_cast; linarith)]

/-- **The initial invariant.** The padded window of the chosen cell meets only the
two grid lines through each pair of its sides, so the invariant holds for every
choice of exterior colours. Source: Lemma 3.2, `02-information.tex`, lines 233–236. -/
theorem initialGeneration_isValid {o : ℝ × ℝ} {s : ℝ} (hs : 0 < s) (m₀ : ℤ × ℤ)
    (c : ℤ × ℤ → Fin 2) : (initialGeneration o s m₀ c).IsValid where
  side_pos := hs
  separated := List.pairwise_singleton _ _
  chamber := by
    intro Q hQ
    rw [initialGeneration, List.mem_singleton] at hQ
    subst hQ
    have hsp : ∀ a : ℝ, ∀ x ∈ ({a, a + s} : Finset ℝ), ∀ x' ∈ ({a, a + s} : Finset ℝ),
        x ≠ x' → s / 8 ≤ |x - x'| := by
      intro a x hx x' hx' hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;>
        first
        | exact absurd rfl hne
        | exact le_abs.mpr (Or.inl (by linarith))
        | exact le_abs.mpr (Or.inr (by linarith))
    refine ⟨by simp [initialSquare, initialGeneration], by simp [initialSquare, initialGeneration],
      hsp _, hsp _,
      Finset.card_le_two.trans (by norm_num), Finset.card_le_two.trans (by norm_num), ?_⟩
    intro p hp q hq hpq
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
    simp only [initialSquare, cellCorner] at hp1 hp2 hp3 hp4 hq1 hq2 hq3 hq4 hpq
    have hidx : cellIndex o s p = cellIndex o s q := by
      refine Prod.ext (floor_div_eq_of_sameSide hs hp1 hp2 hq1 hq2 (hpq.1 _ (by simp))
        (hpq.1 _ (by simp))) (floor_div_eq_of_sameSide hs hp3 hp4 hq3 hq4 (hpq.2 _ (by simp))
        (hpq.2 _ (by simp)))
    simp only [initialGeneration, initialColouring, hidx]
  allowed := by
    intro p hp
    simp only [initialGeneration, initialColouring] at hp
    split_ifs at hp with h
    · exact ⟨_, List.mem_singleton_self _, (cellIndex_eq_iff hs).mp h⟩

/-! ### Iterating generations -/

/-- The `g`-th generation of the recursion from `S₀`.
Source: Lemma 3.2, `02-information.tex`, lines 238–300. -/
def gen (γ : ℝ) (S₀ : Generation) (g : ℕ) : Generation := (Generation.next γ)^[g] S₀

variable {γ : ℝ} {S₀ : Generation}

theorem gen_zero : gen γ S₀ 0 = S₀ := rfl

theorem gen_succ (g : ℕ) : gen γ S₀ (g + 1) = (gen γ S₀ g).next γ :=
  Function.iterate_succ_apply' _ _ _

/-- The side in generation `g` is the `g`-th iterate of `u ↦ 8 u ^ γ`. -/
theorem gen_side (g : ℕ) : (gen γ S₀ g).side = (cellChildSide γ)^[g] S₀.side := by
  induction g with
  | zero => rfl
  | succ g ih => rw [gen_succ, Function.iterate_succ_apply', ← ih]; rfl

/-- Forbidden labels persist in all later generations. -/
theorem gen_colour_of_ne_none {p : ℝ × ℝ} {g g' : ℕ} (hgg : g ≤ g')
    (hp : (gen γ S₀ g).colour p ≠ none) : (gen γ S₀ g').colour p = (gen γ S₀ g).colour p := by
  induction g', hgg using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    rw [gen_succ, Generation.next_colour_of_ne_none (by rw [ih]; exact hp), ih]

theorem gen_colour_eq_none_of_le {p : ℝ × ℝ} {g g' : ℕ} (hgg : g ≤ g')
    (hp : (gen γ S₀ g').colour p = none) : (gen γ S₀ g).colour p = none := by
  by_contra h
  rw [gen_colour_of_ne_none hgg h] at hp
  exact h hp

/-- The invariant holds in every generation up to the first terminal one, when all
earlier sides are at least a threshold above which `1000 u ^ γ ≤ u`. -/
theorem gen_isValid (hS₀ : S₀.IsValid) {ustar : ℝ}
    (hlarge : ∀ u, ustar ≤ u → 1000 * u ^ γ ≤ u) {m : ℕ}
    (hm : ∀ i < m, ustar ≤ (gen γ S₀ i).side) : ∀ g ≤ m, (gen γ S₀ g).IsValid := by
  intro g hg
  induction g with
  | zero => exact hS₀
  | succ g ih =>
    rw [gen_succ]
    exact (ih (by omega)).next (hlarge _ (hm g (by omega)))

/-- A tile point keeps the colour of its family in every later generation.
Source: Lemma 3.2, `02-information.tex`, lines 184–186. -/
theorem gen_colour_of_mem_tile {g g' : ℕ} (hgg : g < g') (hval : (gen γ S₀ g).IsValid)
    {Q : ActiveSquare} (hQ : Q ∈ (gen γ S₀ g).squares) {f : Fin 2} {p : ℝ × ℝ}
    (hp : p ∈ tile (gen γ S₀ g).colour Q (gen γ S₀ g).side ((gen γ S₀ g).side ^ γ) f) :
    (gen γ S₀ g').colour p = some f := by
  have h1 : (gen γ S₀ (g + 1)).colour p = some f := by
    rw [gen_succ]; exact hval.next_colour_of_mem_tile hQ hp
  rw [gen_colour_of_ne_none hgg (by rw [h1]; simp), h1]

/-! ### The ordered list of tiles -/

/-- The tiles of one generation with their families and the generation side, listed
by active square, family `0` before family `1`.
Source: Lemma 3.2, `02-information.tex`, lines 254–262. -/
def genPieces (γ : ℝ) (S : Generation) : List (Finset (ℤ × ℤ) × Fin 2 × ℝ) :=
  S.squares.flatMap fun Q ↦
    [(tileSample S.colour Q S.side (S.side ^ γ) 0, 0, S.side),
      (tileSample S.colour Q S.side (S.side ^ γ) 1, 1, S.side)]

/-- The tiles of the first `m` generations in creation order.
Source: Lemma 3.2, `02-information.tex`, lines 189–191 and 259–262. -/
def pieceList (γ : ℝ) (S₀ : Generation) (m : ℕ) : List (Finset (ℤ × ℤ) × Fin 2 × ℝ) :=
  (List.range m).flatMap fun g ↦ genPieces γ (gen γ S₀ g)

theorem mem_genPieces {S : Generation} {e : Finset (ℤ × ℤ) × Fin 2 × ℝ} :
    e ∈ genPieces γ S ↔
      ∃ Q ∈ S.squares, ∃ f, e = (tileSample S.colour Q S.side (S.side ^ γ) f, f, S.side) := by
  simp only [genPieces, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨Q, hQ, h | h⟩
    · exact ⟨Q, hQ, 0, h⟩
    · exact ⟨Q, hQ, 1, h⟩
  · rintro ⟨Q, hQ, f, rfl⟩
    refine ⟨Q, hQ, ?_⟩
    fin_cases f
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem mem_pieceList {m : ℕ} {e : Finset (ℤ × ℤ) × Fin 2 × ℝ} :
    e ∈ pieceList γ S₀ m ↔ ∃ g < m, e ∈ genPieces γ (gen γ S₀ g) := by
  simp [pieceList]

theorem pieceList_succ (m : ℕ) :
    pieceList γ S₀ (m + 1) = pieceList γ S₀ m ++ genPieces γ (gen γ S₀ m) := by
  simp [pieceList, List.range_succ, List.flatMap_append]

theorem mem_tileSample {col : Colouring} {Q : ActiveSquare} {u t : ℝ} {f : Fin 2}
    {x : ℤ × ℤ} : x ∈ tileSample col Q u t f ↔
      x ∈ latticeBox Q.corner u ∧ integerPoint x ∈ tile col Q u t f := by
  simp [tileSample]

/-- The relation between an earlier and a later tile: they are disjoint, and if they
belong to the same family, every point of the later tile is at distance greater than
`t₀` of its generation from the earlier tile. -/
def PieceRel (γ : ℝ) (e e' : Finset (ℤ × ℤ) × Fin 2 × ℝ) : Prop :=
  Disjoint e.1 e'.1 ∧
    (e.2.1 = e'.2.1 → ∀ x ∈ e'.1, ∀ y ∈ e.1, e'.2.2 ^ γ < dist (integerPoint x) (integerPoint y))

/-- **Disjointness and same-family clearance of the ordered tiles.** Tiles of earlier
generations carry the forbidden colour of their family, so a new tile clears them by
the one-colour observation; tiles of one generation in different active squares are
more than `10 u` apart. Source: Lemma 3.2, `02-information.tex`, lines 254–273. -/
theorem pairwise_pieceList (hS₀ : S₀.IsValid) {ustar : ℝ}
    (hlarge : ∀ u, ustar ≤ u → 1000 * u ^ γ ≤ u) {m : ℕ}
    (hm : ∀ i < m, ustar ≤ (gen γ S₀ i).side) : (pieceList γ S₀ m).Pairwise (PieceRel γ) := by
  have hval := gen_isValid hS₀ hlarge hm
  unfold pieceList
  rw [List.pairwise_flatMap]
  refine ⟨fun g hg ↦ ?_, List.pairwise_lt_range.imp_of_mem fun {g g'} _ hg' hlt ↦ ?_⟩
  · rw [List.mem_range] at hg
    set S := gen γ S₀ g
    have hS : S.IsValid := hval g hg.le
    have hl : 1000 * S.side ^ γ ≤ S.side := hlarge _ (hm g hg)
    have ht : 0 < S.side ^ γ := hS.rpow_side_pos γ
    unfold genPieces
    rw [List.pairwise_flatMap]
    refine ⟨fun Q _ ↦ ?_, hS.separated.imp fun {Q Q'} hsep e he e' he' ↦ ?_⟩
    · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
      refine ⟨Finset.disjoint_left.mpr fun x hx hx' ↦ ?_, fun h ↦ absurd h (by simp)⟩
      exact Generation.not_mem_tile_zero_and_one (mem_tileSample.mp hx).2
        (mem_tileSample.mp hx').2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he he'
      have hbox : ∀ {Q'' : ActiveSquare} {e'' : Finset (ℤ × ℤ) × Fin 2 × ℝ},
          (e'' = (tileSample S.colour Q'' S.side (S.side ^ γ) 0, 0, S.side) ∨
            e'' = (tileSample S.colour Q'' S.side (S.side ^ γ) 1, 1, S.side)) →
          (∀ x ∈ e''.1, integerPoint x ∈ box Q''.corner S.side) ∧ e''.2.2 = S.side := by
        rintro Q'' e'' (rfl | rfl) <;>
          exact ⟨fun x hx ↦ (mem_tileSample.mp hx).2.1, rfl⟩
      obtain ⟨hb, -⟩ := hbox he
      obtain ⟨hb', hs'⟩ := hbox he'
      refine ⟨Finset.disjoint_left.mpr fun x hx hx' ↦ ?_, fun _ x hx y hy ↦ ?_⟩
      · have := hsep _ (hb x hx) _ (hb' x hx')
        rw [dist_self] at this
        linarith [hS.side_pos]
      · rw [hs', dist_comm]
        have := hsep _ (hb y hy) _ (hb' x hx)
        linarith [hS.side_pos]
  · intro e he e' he'
    rw [List.mem_range] at hg'
    obtain ⟨Q, hQ, f, rfl⟩ := mem_genPieces.mp he
    obtain ⟨Q', hQ', f', rfl⟩ := mem_genPieces.mp he'
    have hSg : (gen γ S₀ g).IsValid := hval g (by omega)
    have hSg' : (gen γ S₀ g').IsValid := hval g' hg'.le
    refine ⟨Finset.disjoint_left.mpr fun x hx hx' ↦ ?_, fun hff x hx y hy ↦ ?_⟩
    · have h1 := gen_colour_of_mem_tile hlt hSg hQ (mem_tileSample.mp hx).2
      rw [(mem_tileSample.mp hx').2.2.1] at h1
      exact absurd h1 (by simp)
    · have h1 := gen_colour_of_mem_tile hlt hSg hQ (mem_tileSample.mp hy).2
      dsimp only at hff ⊢
      rw [hff] at h1
      exact (hSg'.chamber Q' hQ').lt_dist_of_mem_tile
        (hSg'.rpow_side_pos γ) (hlarge _ (hm g' hg'))
        (mem_tileSample.mp hx).2 h1

/-! ### Counting -/

theorem length_flatMap_le {α β : Type*} {l : List α} {f : α → List β} {k : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    omega

/-- **Bounded branching.** Every active square has at most `25` children, so
generation `g` has at most `25 ^ g` active squares when there was at most one initially.
Source: Lemma 3.2, `02-information.tex`, lines 302–309. -/
theorem length_gen_squares_le (hS₀ : S₀.IsValid) (h₀ : S₀.squares.length ≤ 1) {ustar : ℝ}
    (hlarge : ∀ u, ustar ≤ u → 1000 * u ^ γ ≤ u) {m : ℕ}
    (hm : ∀ i < m, ustar ≤ (gen γ S₀ i).side) :
    ∀ g ≤ m, (gen γ S₀ g).squares.length ≤ 25 ^ g := by
  have hval := gen_isValid hS₀ hlarge hm
  intro g hg
  induction g with
  | zero => rw [gen_zero, pow_zero]; exact h₀
  | succ g ih =>
    rw [gen_succ, pow_succ, mul_comm]
    refine (length_flatMap_le fun Q hQ ↦ ?_).trans
      (Nat.mul_le_mul_left _ (ih (by omega)))
    rw [children, List.length_map, Finset.length_toList]
    exact card_holes_le ((hval g (by omega)).chamber Q hQ) _

/-- The number of tiles of the first `m` generations. -/
theorem length_pieceList_le (hS₀ : S₀.IsValid) (h₀ : S₀.squares.length ≤ 1) {ustar : ℝ}
    (hlarge : ∀ u, ustar ≤ u → 1000 * u ^ γ ≤ u) {m : ℕ}
    (hm : ∀ i < m, ustar ≤ (gen γ S₀ i).side) :
    ∀ k ≤ m, (pieceList γ S₀ k).length ≤ ∑ j ∈ Finset.range k, 2 * 25 ^ j := by
  have hsq := length_gen_squares_le hS₀ h₀ hlarge hm
  intro k hk
  induction k with
  | zero => simp [pieceList]
  | succ k ih =>
    rw [pieceList_succ, List.length_append, Finset.sum_range_succ]
    refine Nat.add_le_add (ih (by omega)) ?_
    unfold genPieces
    exact (length_flatMap_le (k := 2) fun Q _ ↦ le_of_eq rfl).trans
      (Nat.mul_le_mul_left 2 (hsq k (by omega)))

end TNLean.PEPS.Approximation.CellPartition
