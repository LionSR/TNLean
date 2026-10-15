/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CellColouredStep
import TNLean.PEPS.Approximation.CellPartitionCount

/-!
# One generation of the recursive coloured partition

A generation of the recursion in the proof of the conditional information bound
for one cell consists of a common side `u`, a list of active squares and the
current labels of ambient points. The next generation (`Generation.next`) puts
`t₀ = u ^ γ`, assigns the tiles of every active square to their families, and
takes the reserved holes as the new active squares, of side `u' = 8 t₀`.

The generation invariant (`Generation.IsValid`) asks that the side be positive,
distinct active squares be at mutual distance greater than `10 u`, every active
square satisfy the chamber invariant, and every allowed point lie in an active
square. Above the scale where `1000 u ^ γ ≤ u`, the invariant passes to the next
generation (`Generation.IsValid.next`). Labels only change from allowed to a
forbidden colour, and each tile receives the forbidden colour of its family.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
  lines 181–188 and 224–300.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.CellPartition

/-- One generation: the common side, the active squares and the current labels.
Source: Lemma 3.2, `02-information.tex`, lines 228–233. -/
structure Generation where
  /-- The common side `u` of the active squares. -/
  side : ℝ
  /-- The active squares, in a fixed order. -/
  squares : List ActiveSquare
  /-- The labels of ambient points at the start of the generation. -/
  colour : Colouring

/-- Two active squares of side `u` are at mutual distance greater than `10 u`.
Source: Lemma 3.2, `02-information.tex`, lines 229–230. -/
def AreSeparated (u : ℝ) (Q Q' : ActiveSquare) : Prop :=
  ∀ p ∈ box Q.corner u, ∀ q ∈ box Q'.corner u, 10 * u < dist p q

/-- The children of an active square: one square of side `8 t` per reserved hole.
Source: Lemma 3.2, `02-information.tex`, lines 274–280. -/
def children (Q : ActiveSquare) (u t : ℝ) : List ActiveSquare :=
  (holes Q u t).toList.map (child t)

open Classical in
/-- **The next generation.** With `t₀ = u ^ γ`, every tile of every active square is
given the forbidden colour of its family, and the reserved holes become the active
squares, of side `8 t₀`. Source: Lemma 3.2, `02-information.tex`, lines 184–186,
238–257 and 274–280. -/
def Generation.next (γ : ℝ) (S : Generation) : Generation where
  side := cellChildSide γ S.side
  squares := S.squares.flatMap fun Q ↦ children Q S.side (S.side ^ γ)
  colour := fun p ↦
    if ∃ Q ∈ S.squares, p ∈ tile S.colour Q S.side (S.side ^ γ) 1 then some 1
    else if ∃ Q ∈ S.squares, p ∈ tile S.colour Q S.side (S.side ^ γ) 0 then some 0
    else S.colour p

/-- **The generation invariant.** Source: Lemma 3.2, `02-information.tex`,
lines 227–233. -/
structure Generation.IsValid (S : Generation) : Prop where
  side_pos : 0 < S.side
  separated : S.squares.Pairwise (AreSeparated S.side)
  chamber : ∀ Q ∈ S.squares, IsChamberSquare S.colour S.side Q
  allowed : ∀ p, S.colour p = none → ∃ Q ∈ S.squares, p ∈ box Q.corner S.side

theorem AreSeparated.symm {u : ℝ} {Q Q' : ActiveSquare} (h : AreSeparated u Q Q') :
    AreSeparated u Q' Q := fun p hp q hq ↦ by rw [dist_comm]; exact h q hq p hp

instance (u : ℝ) : Std.Symm (AreSeparated u) := ⟨fun _ _ ↦ AreSeparated.symm⟩

namespace Generation

variable {γ : ℝ} {S : Generation}

/-- The scale `t₀ = u ^ γ` of a valid generation is positive. -/
theorem IsValid.rpow_side_pos (hS : S.IsValid) (γ : ℝ) : 0 < S.side ^ γ :=
  Real.rpow_pos_of_pos hS.side_pos γ

/-- An active square containing a point near a given active square is that square. -/
theorem IsValid.eq_of_dist_le (hS : S.IsValid) {Q Q' : ActiveSquare} (hQ : Q ∈ S.squares)
    (hQ' : Q' ∈ S.squares) {a p : ℝ × ℝ} (ha : a ∈ box Q.corner S.side)
    (hp : p ∈ box Q'.corner S.side) (hpa : dist p a ≤ 10 * S.side) : Q' = Q := by
  by_contra hne
  have := hS.separated.forall hQ' hQ hne p hp a ha
  linarith

theorem tile_subset_box {col : Colouring} {Q : ActiveSquare} {u t : ℝ} {f : Fin 2} :
    tile col Q u t f ⊆ box Q.corner u := fun _ hp ↦ hp.1

theorem not_mem_tile_zero_and_one {col : Colouring} {Q : ActiveSquare} {u t : ℝ}
    {p : ℝ × ℝ} (h₀ : p ∈ tile col Q u t 0) (h₁ : p ∈ tile col Q u t 1) : False := by
  have := h₀.2.2.2.mp (h₁.2.2.2.mpr rfl)
  exact absurd this (by decide)

/-- A tile point receives the forbidden colour of its family.
Source: Lemma 3.2, `02-information.tex`, lines 184–186. -/
theorem IsValid.next_colour_of_mem_tile (hS : S.IsValid) {Q : ActiveSquare}
    (hQ : Q ∈ S.squares) {f : Fin 2} {p : ℝ × ℝ}
    (hp : p ∈ tile S.colour Q S.side (S.side ^ γ) f) : (S.next γ).colour p = some f := by
  simp only [next]
  obtain rfl | rfl : f = 0 ∨ f = 1 := by omega
  · have h1 : ¬∃ Q' ∈ S.squares, p ∈ tile S.colour Q' S.side (S.side ^ γ) 1 := by
      rintro ⟨Q', hQ', hp'⟩
      obtain rfl := hS.eq_of_dist_le hQ hQ' hp.1 hp'.1 (by
        rw [dist_self]; exact mul_nonneg (by norm_num) hS.side_pos.le)
      exact not_mem_tile_zero_and_one hp hp'
    rw [ite_eq_right h1, ite_eq_left ⟨Q, hQ, hp⟩]
  · rw [ite_eq_left ⟨Q, hQ, hp⟩]

/-- Away from all tiles the label does not change. -/
theorem next_colour_of_forall_not_mem_tile {p : ℝ × ℝ}
    (hp : ∀ Q ∈ S.squares, ∀ f, p ∉ tile S.colour Q S.side (S.side ^ γ) f) :
    (S.next γ).colour p = S.colour p := by
  simp only [next]
  rw [ite_eq_right fun ⟨Q, hQ, h⟩ ↦ hp Q hQ 1 h, ite_eq_right fun ⟨Q, hQ, h⟩ ↦ hp Q hQ 0 h]

/-- Forbidden labels are never changed. Source: Lemma 3.2, `02-information.tex`,
lines 184–186 and 243–244. -/
theorem next_colour_of_ne_none {p : ℝ × ℝ} (hp : S.colour p ≠ none) :
    (S.next γ).colour p = S.colour p :=
  next_colour_of_forall_not_mem_tile fun _ _ _ h ↦ hp h.2.1

/-- A point allowed in the next generation was allowed and lies in no new tile. -/
theorem IsValid.of_next_colour_eq_none (hS : S.IsValid) {p : ℝ × ℝ}
    (hp : (S.next γ).colour p = none) :
    S.colour p = none ∧ ∀ Q ∈ S.squares, ∀ f, p ∉ tile S.colour Q S.side (S.side ^ γ) f := by
  have htile : ∀ Q ∈ S.squares, ∀ f, p ∉ tile S.colour Q S.side (S.side ^ γ) f :=
    fun Q hQ f h ↦ by rw [hS.next_colour_of_mem_tile hQ h] at hp; exact absurd hp (by simp)
  refine ⟨?_, htile⟩
  rw [← next_colour_of_forall_not_mem_tile htile]
  exact hp

/-- Near an active square, the next labels are those obtained from that square's
tiles alone. -/
theorem IsValid.next_colour_eq_localNext (hS : S.IsValid) {Q : ActiveSquare}
    (hQ : Q ∈ S.squares) {p a : ℝ × ℝ} (ha : a ∈ box Q.corner S.side)
    (hpa : dist p a ≤ 10 * S.side) :
    (S.next γ).colour p = localNext S.colour Q S.side (S.side ^ γ) p := by
  unfold localNext
  by_cases h1 : p ∈ tile S.colour Q S.side (S.side ^ γ) 1
  · rw [ite_eq_left h1, hS.next_colour_of_mem_tile hQ h1]
  · rw [ite_eq_right h1]
    by_cases h0 : p ∈ tile S.colour Q S.side (S.side ^ γ) 0
    · rw [ite_eq_left h0, hS.next_colour_of_mem_tile hQ h0]
    · rw [ite_eq_right h0]
      refine next_colour_of_forall_not_mem_tile fun Q' hQ' f hp ↦ ?_
      obtain rfl := hS.eq_of_dist_le hQ hQ' ha hp.1 hpa
      obtain rfl | rfl : f = 0 ∨ f = 1 := by omega
      · exact h0 hp
      · exact h1 hp

theorem mem_children {Q C : ActiveSquare} {u t : ℝ} :
    C ∈ children Q u t ↔ ∃ z ∈ holes Q u t, child t z = C := by
  simp [children]

/-- Every point of a child square lies within `14 t` of its parent square. -/
theorem exists_dist_le_of_mem_child {Q : ActiveSquare} {u t : ℝ} {z p : ℝ × ℝ}
    (hz : z ∈ holes Q u t) (hp : p ∈ box (child t z).corner (8 * t)) :
    ∃ a ∈ box Q.corner u, dist p a ≤ 14 * t := by
  obtain ⟨-, a, ha, hza⟩ := mem_holes.mp hz
  exact ⟨a, ha, (dist_triangle p z a).trans (by
    have := dist_le_of_mem_holeBox hp; linarith)⟩

/-- **The invariant passes to the next generation.** Above the scale where
`1000 u ^ γ ≤ u`, the children are separated by more than `10 u'`, satisfy the
chamber invariant, and contain every remaining allowed point.
Source: Lemma 3.2, `02-information.tex`, lines 274–300. -/
theorem IsValid.next (hS : S.IsValid) (hlarge : 1000 * S.side ^ γ ≤ S.side) :
    (S.next γ).IsValid := by
  set u := S.side with hu
  set t := u ^ γ with htdef
  have ht : 0 < t := hS.rpow_side_pos γ
  have hside : (S.next γ).side = 8 * t := rfl
  refine ⟨by rw [hside]; positivity, ?_, ?_, ?_⟩
  · change (S.squares.flatMap fun Q ↦ children Q u t).Pairwise (AreSeparated (8 * t))
    rw [List.pairwise_flatMap]
    refine ⟨fun Q hQ ↦ ?_, hS.separated.imp fun {Q Q'} hsep C hC C' hC' ↦ ?_⟩
    · unfold children
      rw [List.pairwise_map]
      refine List.Nodup.pairwise_of_forall_ne (Finset.nodup_toList _) fun z hz z' hz' hne ↦ ?_
      rw [Finset.mem_toList] at hz hz'
      intro p hp q hq
      have hpz := dist_le_of_mem_holeBox hp
      have hqz := dist_le_of_mem_holeBox hq
      have h1 := abs_fst_sub_le_dist p z
      have h2 := abs_snd_sub_le_dist p z
      have h3 := abs_fst_sub_le_dist q z'
      have h4 := abs_snd_sub_le_dist q z'
      have h5 := abs_fst_sub_le_dist p q
      have h6 := abs_snd_sub_le_dist p q
      have t1 := abs_sub_le z.1 p.1 z'.1
      have t2 := abs_sub_le p.1 q.1 z'.1
      have t3 := abs_sub_le z.2 p.2 z'.2
      have t4 := abs_sub_le p.2 q.2 z'.2
      rw [abs_sub_comm z.1 p.1] at t1
      rw [abs_sub_comm z.2 p.2] at t3
      rcases (hS.chamber Q hQ).hole_sep hz hz' hne with h | h <;> linarith
    · obtain ⟨z, hz, rfl⟩ := mem_children.mp hC
      obtain ⟨z', hz', rfl⟩ := mem_children.mp hC'
      intro p hp q hq
      obtain ⟨a, ha, hpa⟩ := exists_dist_le_of_mem_child hz hp
      obtain ⟨a', ha', hqa'⟩ := exists_dist_le_of_mem_child hz' hq
      have := hsep a ha a' ha'
      have := dist_triangle4 a p q a'
      rw [dist_comm a p] at this
      linarith
  · intro C hC
    obtain ⟨Q, hQ, hCQ⟩ := List.mem_flatMap.mp hC
    obtain ⟨z, hz, rfl⟩ := mem_children.mp hCQ
    exact (hS.chamber Q hQ).isChamberSquare_child ht hlarge hz fun p a ha hpa ↦
      hS.next_colour_eq_localNext hQ ha (hpa.trans (by linarith))
  · intro p hp
    obtain ⟨hnone, htile⟩ := hS.of_next_colour_eq_none hp
    obtain ⟨Q, hQ, hpQ⟩ := hS.allowed p hnone
    have hhole : InHole Q u t p := by
      by_contra hh
      by_cases hn : NearZero S.colour t p
      · exact htile Q hQ 1 ⟨hpQ, hnone, hh, iff_of_true hn rfl⟩
      · exact htile Q hQ 0 ⟨hpQ, hnone, hh, iff_of_false hn (by decide)⟩
    obtain ⟨z, hz, hpz⟩ := hhole
    exact ⟨child t z, List.mem_flatMap.mpr ⟨Q, hQ, mem_children.mpr ⟨z, hz, rfl⟩⟩, hpz⟩

end Generation

end TNLean.PEPS.Approximation.CellPartition
