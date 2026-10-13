/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLevelSchedule
import TNLean.PEPS.Approximation.DyadicLifetimeIncidence
import TNLean.PEPS.Approximation.DyadicTrueVertices

/-!
# The active-label invariant for block parties

The invariant on active labels `eq:geometry-active-labels` of the polynomial-PEPS manuscript
says that at the start of level `n` only `2n`-block main labels occur, during it only `2n`- and
`n`-block main labels and the placeholder, and at its end only `n`-block main labels. The source
draws from it (`06-geometry.tex:610–618`) that a block party of side `m` occurs in linked gates
only at levels `m` and `m / 2`, and only at repaintings or junction resizes within distance
`O(m)` of its block.

Here the block parties are indexed by their scale and block indices, `x = (j, r, s)`, through an
injective labelling `party`, distinct from the placeholder `ph`. At level `2 ^ j'` the label of
the `2 ^ j'`-block `Q` is its new party `(j', Q)` or the old party of its parent,
`(j' + 1, Q / 2)`. This file proves:

* the invariant in party form: a block label of level `2 ^ j'` that is a block party belongs to
  scale `j'` or `j' + 1`, and owns the block; at the start of the level only scale `j' + 1`
  occurs, and once every block of the root square is repainted only scale `j'`;
* the labels a repainting uses: the labels of the blocks that differ from the repainted square by
  at most one in each index (the labels `A`, `B`, `C_e` of its edge diagrams and the four labels
  at each corner) are owned by its *used parties*; the labels incident at a grid corner of a
  block guide, among them its tag holder, are those of the four blocks at the corner, the parties
  a junction resize uses;
* a used party of a repainting or a junction resize is near it, at distance constant `c = 0` in
  the sense of `TNLean.PEPS.Approximation.DyadicSquare.Near`;
* hence the lifetime bound: if every repainting and every junction resize consists of at most `G`
  gates and each gate involves only parties its event uses, every block party participates in at
  most `64 G` gates.

The gates of the protocol are not constructed; that a gate involves only the parties its event
uses is the hypothesis of the final count.

## Main results

* `TNLean.PEPS.Approximation.levelLabels_eq_party`: the invariant in party form.
* `TNLean.PEPS.Approximation.repaintingUses_of_levelLabels`,
  `TNLean.PEPS.Approximation.junctionUses_of_incidentLabels`: the parties of the labels used.
* `TNLean.PEPS.Approximation.RepaintingUses.near`, `TNLean.PEPS.Approximation.JunctionUses.near`:
  used parties are near.
* `TNLean.PEPS.Approximation.card_gates_le_of_uses`: the lifetime participation bound.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the repainting by levels
  (lines 82–100), tags (lines 119–125), the resizing of holes (lines 127–131), and the party
  lifetimes (lines 572–631).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Finset

/-! ### Owners and used parties -/

/-- The block party `x = (j, r, s)` owns the `2 ^ j'`-block `Q` at level `2 ^ j'`: it is the new
party of `Q`, at scale `j'`, or the old party of its parent `2 ^ (j' + 1)`-block.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–90, 585–586`. -/
def OwnsLevelBlock (j' : ℕ) (Q : ℕ × ℕ) (x : ℕ × ℕ × ℕ) : Prop :=
  x = (j', Q) ∨ x = (j' + 1, Q.1 / 2, Q.2 / 2)

/-- The block parties used by the repainting of the square of scale `j'` with indices
`(r', s')`: the owners of the blocks that differ from it by at most one in each index, whose
labels are those of its edge and corner diagrams.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “every active main owner is an `n`- or
`2n`-block owner. On the affected footprints those blocks lie at distance `O(n)` from the
repainted square”, `06-geometry.tex:585–592`. -/
def RepaintingUses (j' r' s' : ℕ) (x : ℕ × ℕ × ℕ) : Prop :=
  ∃ q t : ℕ, q ≤ r' + 1 ∧ r' ≤ q + 1 ∧ t ≤ s' + 1 ∧ s' ≤ t + 1 ∧ OwnsLevelBlock j' (q, t) x

/-- The block parties used by the resize of the hole at the grid corner `(2 ^ j u, 2 ^ j v)` of
the guide uniform on `2 ^ j`-blocks: the parties of the four blocks at the corner.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “Resizing uses the current block labels near
its junction”, `06-geometry.tex:127–131, 594`. -/
def JunctionUses (j u v : ℕ) (x : ℕ × ℕ × ℕ) : Prop :=
  x.1 = j ∧ x.2.1 ≤ u ∧ u ≤ x.2.1 + 1 ∧ x.2.2 ≤ v ∧ v ≤ x.2.2 + 1

/-- The block parties used by the repainting of a square of the hierarchy. -/
def DyadicSquare.Uses {k : ℕ} (S : DyadicSquare k) (x : ℕ × ℕ × ℕ) : Prop :=
  RepaintingUses S.1 S.2.1 S.2.2 x

/-- The block parties used by the resize at a junction of the hierarchy. -/
def DyadicJunction.Uses {k : ℕ} (P : DyadicJunction k) (x : ℕ × ℕ × ℕ) : Prop :=
  JunctionUses P.1 P.2.1 P.2.2 x

/-! ### The invariant in party form -/

section Parties

variable {ι : Type*} {party : ℕ × ℕ × ℕ → ι} {ph : ι}

/-- The old labels of level `2 ^ j'`: the parties of the `2 ^ (j' + 1)`-blocks. -/
def oldParty (party : ℕ × ℕ × ℕ → ι) (j' : ℕ) (Q : ℤ × ℤ) : ι :=
  party (j' + 1, Q.1.toNat, Q.2.toNat)

/-- The new labels of level `2 ^ j'`: the parties of the `2 ^ j'`-blocks. -/
def newParty (party : ℕ × ℕ × ℕ → ι) (j' : ℕ) (Q : ℤ × ℤ) : ι :=
  party (j', Q.1.toNat, Q.2.toNat)

/-- **Active labels in party form.** During the pass to level `2 ^ j'`, a block label that is the
block party `x` labels a block `Q` of the root square owned by `x`; in particular `x` has scale
`j'` or `j' + 1`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-active-labels`,
`06-geometry.tex:597–609`. -/
theorem levelLabels_eq_party (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph) (M : ℤ)
    (j' : ℕ) (done : Set (ℤ × ℤ)) {Q : ℤ × ℤ} {x : ℕ × ℕ × ℕ}
    (h : levelLabels M (oldParty party j') (newParty party j') ph done Q = party x) :
    InRoot M Q ∧ OwnsLevelBlock j' (Q.1.toNat, Q.2.toNat) x := by
  classical
  unfold levelLabels at h
  split_ifs at h with hQ hd
  · exact ⟨hQ, Or.inl (hp h).symm⟩
  · refine ⟨hQ, Or.inr ?_⟩
    rw [← hp h]
    simp only [Prod.mk.injEq, true_and]
    obtain ⟨h1, -, h2, -⟩ := hQ
    omega
  · exact absurd h.symm (hph x)

/-- An owner of a block at level `2 ^ j'` has scale `j'` or `j' + 1`. -/
theorem OwnsLevelBlock.scale {j' : ℕ} {Q : ℕ × ℕ} {x : ℕ × ℕ × ℕ}
    (h : OwnsLevelBlock j' Q x) : j' ≤ x.1 ∧ x.1 ≤ j' + 1 := by
  rcases h with rfl | rfl <;> simp

/-- **Start of a level in party form.** Before any repainting of level `2 ^ j'`, only parties of
the `2 ^ (j' + 1)`-blocks label blocks.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-active-labels`,
`06-geometry.tex:603`. -/
theorem levelLabels_empty_eq_party (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph)
    (M : ℤ) (j' : ℕ) {Q : ℤ × ℤ} {x : ℕ × ℕ × ℕ}
    (h : levelLabels M (oldParty party j') (newParty party j') ph ∅ Q = party x) :
    x.1 = j' + 1 := by
  obtain ⟨y, hy⟩ := levelLabels_empty_mem M (oldParty party j') (newParty party j') ph Q
    |>.resolve_left (by rw [h]; exact hph x)
  rw [← hp (hy.trans h)]

/-- **End of a level in party form.** Once every block of the root square is repainted at level
`2 ^ j'`, only parties of the `2 ^ j'`-blocks label blocks: a party of side `2 ^ (j' + 1)` has
disappeared from every main guide region.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-active-labels`,
`06-geometry.tex:606, 611–612`. -/
theorem levelLabels_eq_party_of_subset (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph)
    (M : ℤ) (j' : ℕ) {done : Set (ℤ × ℤ)} (hd : {Q | InRoot M Q} ⊆ done) {Q : ℤ × ℤ}
    {x : ℕ × ℕ × ℕ}
    (h : levelLabels M (oldParty party j') (newParty party j') ph done Q = party x) :
    x.1 = j' := by
  obtain ⟨y, hy⟩ := levelLabels_mem_of_subset M (oldParty party j') (newParty party j') ph hd Q
    |>.resolve_left (by rw [h]; exact hph x)
  rw [← hp (hy.trans h)]

/-- **Labels of a repainting.** During the pass to level `2 ^ j'`, the label of a block `Q` that
differs from the repainted square `S` of the root square by at most one in each index, such as
`A = lab S`, `B = new S` and `C_e = lab (nbrBlock e S)` and the labels at the corners of `S`, is
the placeholder or a party used by the repainting of `S`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:585–596`. -/
theorem repaintingUses_of_levelLabels (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph)
    (M : ℤ) (j' : ℕ) (done : Set (ℤ × ℤ)) {S Q : ℤ × ℤ} (hS : InRoot M S)
    (hQ : |Q.1 - S.1| ≤ 1 ∧ |Q.2 - S.2| ≤ 1) {x : ℕ × ℕ × ℕ}
    (h : levelLabels M (oldParty party j') (newParty party j') ph done Q = party x) :
    RepaintingUses j' S.1.toNat S.2.toNat x := by
  obtain ⟨hQ', hx⟩ := levelLabels_eq_party hp hph M j' done h
  obtain ⟨h1, h2⟩ := hQ
  rw [abs_le] at h1 h2
  obtain ⟨-, -, -, -⟩ := hS
  obtain ⟨-, -, -, -⟩ := hQ'
  exact ⟨Q.1.toNat, Q.2.toNat, by omega, by omega, by omega, by omega, hx⟩

end Parties

/-! ### Labels at a junction -/

/-- **Labels at a grid corner.** The labels incident at the grid corner `(n u, n v)` of the guide
uniform on `n`-blocks, among them the tag holder there, are those of the four blocks at the
corner.

Source: Polynomial-PEPS manuscript (Sept 24 2026), tags held by incident labels and the resize at
a junction, `06-geometry.tex:119–131, 590–594`. -/
theorem incidentLabels_blockGuide_corner {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι)
    (u v : ℤ) {l : ι} (hl : l ∈ incidentLabels (blockGuide n lab) ((n * u, n * v) : ℝ × ℝ)) :
    ∃ Q : ℤ × ℤ, (Q.1 = u - 1 ∨ Q.1 = u) ∧ (Q.2 = v - 1 ∨ Q.2 = v) ∧ lab Q = l := by
  have key : ∀ (w : ℤ) (y : ℝ), |y - n * w| < n / 2 → ⌊y / n⌋ = w - 1 ∨ ⌊y / n⌋ = w := by
    intro w y hy
    rw [abs_lt] at hy
    have hlo : (w : ℝ) - 1 < y / n := by
      rw [lt_div_iff₀ hn]; nlinarith
    have hhi : y / n < (w : ℝ) + 1 := by
      rw [div_lt_iff₀ hn]; nlinarith
    have a := Int.floor_le (y / n)
    have b := Int.lt_floor_add_one (y / n)
    have c1 : ⌊y / n⌋ < w + 1 := by exact_mod_cast a.trans_lt hhi
    have c2 : w - 1 < ⌊y / n⌋ + 1 := by exact_mod_cast hlo.trans b
    omega
  have hV : ball ((n * u, n * v) : ℝ × ℝ) (n / 2) ∈ nhds ((n * u, n * v) : ℝ × ℝ) :=
    ball_mem_nhds _ (half_pos hn)
  refine incidentLabels_subset hV (s := {l | ∃ Q : ℤ × ℤ, (Q.1 = u - 1 ∨ Q.1 = u) ∧
    (Q.2 = v - 1 ∨ Q.2 = v) ∧ lab Q = l}) (fun p hp => ?_) hl
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hp
  exact ⟨blockIndex n p, key u p.1 hp.1, key v p.2 hp.2, rfl⟩

/-- **Parties at a junction.** At the end of the pass to level `2 ^ j`, a block party incident at
the grid corner `(2 ^ j u, 2 ^ j v)` of the block guide, for example its tag holder, is used by
the resize of the hole there before the next level.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “Resizing uses the current block labels near
its junction”, `06-geometry.tex:127–131, 594`. -/
theorem junctionUses_of_incidentLabels {ι : Type*} {party : ℕ × ℕ × ℕ → ι} {ph : ι}
    (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph) (M : ℤ) (j : ℕ)
    {done : Set (ℤ × ℤ)} (hd : {Q | InRoot M Q} ⊆ done) {u v : ℕ} {x : ℕ × ℕ × ℕ}
    (hl : party x ∈ incidentLabels
      (blockGuide (2 ^ j) (levelLabels M (oldParty party j) (newParty party j) ph done))
      (((2 : ℝ) ^ j * ((u : ℤ) : ℝ), (2 : ℝ) ^ j * ((v : ℤ) : ℝ)) : ℝ × ℝ)) :
    JunctionUses j u v x := by
  obtain ⟨Q, hQ1, hQ2, hQ⟩ := incidentLabels_blockGuide_corner (pow_pos two_pos j) _ _ _ hl
  have hs := levelLabels_eq_party_of_subset hp hph M j hd hQ
  obtain ⟨⟨h1, -, h2, -⟩, hx | hx⟩ := levelLabels_eq_party hp hph M j done hQ
  · subst hx
    refine ⟨rfl, ?_⟩
    dsimp only
    omega
  · rw [hx] at hs
    simp at hs

/-! ### Used parties are near -/

/-- An index bound `a ≤ b + 1`, scaled by the side `2 ^ j`. -/
private theorem pow_mul_le_of_le {j a b : ℕ} (h : a ≤ b + 1) : 2 ^ j * a ≤ 2 ^ j * b + 2 ^ j := by
  have := Nat.mul_le_mul_left (2 ^ j) h
  rwa [mul_add, mul_one] at this

/-- **Near repaintings.** A party used by the repainting of the square of scale `j'` with indices
`(r', s')` has scale `j'` or `j' + 1`, and its block is near the square, at distance constant
zero: a block party of side `m` is used only by repaintings at levels `m` and `m / 2` of
squares adjacent to its block or to one of its children.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “this party can occur in linked gates only at
levels `m` and `m/2`”, `06-geometry.tex:597–618`. -/
theorem RepaintingUses.near {j' r' s' j r s : ℕ} (h : RepaintingUses j' r' s' (j, r, s)) :
    j' ≤ j ∧ j ≤ j' + 1 ∧ BlockNear j r j' r' 0 ∧ BlockNear j s j' s' 0 := by
  obtain ⟨q, t, hq1, hq2, ht1, ht2, hx | hx⟩ := h <;> simp only [Prod.mk.injEq] at hx <;>
    obtain ⟨hj, hr, hs⟩ := hx <;> subst hj hr hs
  · exact ⟨le_rfl, Nat.le_succ _, ⟨by simpa using pow_mul_le_of_le hq2,
      by simpa using pow_mul_le_of_le hq1⟩, by simpa using pow_mul_le_of_le ht2,
      by simpa using pow_mul_le_of_le ht1⟩
  · simp only [BlockNear, add_zero, pow_succ]
    refine ⟨Nat.le_succ _, le_rfl, ⟨?_, ?_⟩, ?_, ?_⟩
    · have := pow_mul_le_of_le (j := j') (show r' ≤ 2 * (q / 2) + 1 + 1 by omega)
      rw [mul_add] at this; linarith
    · have := pow_mul_le_of_le (j := j') (show 2 * (q / 2) ≤ r' + 1 by omega); linarith
    · have := pow_mul_le_of_le (j := j') (show s' ≤ 2 * (t / 2) + 1 + 1 by omega)
      rw [mul_add] at this; linarith
    · have := pow_mul_le_of_le (j := j') (show 2 * (t / 2) ≤ s' + 1 by omega); linarith

/-- **Near junctions.** A party used by the resize at the grid corner `(2 ^ j' u, 2 ^ j' v)` has
scale `j'`, and the corner is near its block, at distance constant zero.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:594, 615–618`. -/
theorem JunctionUses.near {j' u v j r s : ℕ} (h : JunctionUses j' u v (j, r, s)) :
    j' ≤ j ∧ j ≤ j' + 1 ∧ CornerNear j r j' u 0 ∧ CornerNear j s j' v 0 := by
  obtain ⟨hj, h1, h2, h3, h4⟩ := h
  dsimp only at hj h1 h2 h3 h4
  subst hj
  exact ⟨le_rfl, Nat.le_succ _, ⟨by simpa using pow_mul_le_of_le h2,
    by simpa using Nat.mul_le_mul_left (2 ^ j) h1⟩, by simpa using pow_mul_le_of_le h4,
    by simpa using Nat.mul_le_mul_left (2 ^ j) h3⟩

/-! ### Lifetime participation -/

/-- **Bounded lifetime participation.** Let the gates `Γ` of a schedule on the hierarchy of
`[0, 2 ^ k] ^ 2` belong to repaintings and junction resizes, `ev γ`, with at most `G` gates for
each. If every gate in which the block party `x` participates belongs to a repainting or junction
resize that uses `x`, then `x` participates in at most `64 G` gates. The bound depends only on
`G`, not on `k` or the party.

That a gate involves only parties its event uses is the hypothesis here; the gates of the protocol
are not constructed. The used parties are those of the labels the event reads: the block labels
next to the repainted square (`repaintingUses_of_levelLabels`) and the labels incident at the
junction (`junctionUses_of_incidentLabels`).

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex:31–32`, and the lifetime argument, `06-geometry.tex:572–631`. -/
theorem card_gates_le_of_uses {k : ℕ} {Γ : Type*} [Fintype Γ]
    (ev : Γ → DyadicSquare k ⊕ DyadicJunction k) {G : ℕ}
    (hG : ∀ e, (univ.filter fun γ => ev γ = e).card ≤ G) (x : ℕ × ℕ × ℕ) (P : Γ → Prop)
    [DecidablePred P]
    (hP : ∀ γ, P γ → Sum.elim (fun S => S.Uses x) (fun J => J.Uses x) (ev γ)) :
    (univ.filter P).card ≤ 64 * G := by
  obtain ⟨j, r, s⟩ := x
  have := card_gates_le_of_near ev hG j r s 0 P fun γ hγ => by
    have h := hP γ hγ
    rcases hev : ev γ with S | J <;> rw [hev] at h
    · obtain ⟨h1, h2, h3, h4⟩ := RepaintingUses.near h
      exact ⟨h1, h2, by simpa using h3, by simpa using h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := JunctionUses.near h
      exact ⟨h1, h2, by simpa using h3, by simpa using h4⟩
  norm_num at this
  linarith

end TNLean.PEPS.Approximation
