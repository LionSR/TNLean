/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLargeRepaintingGates
import TNLean.PEPS.Approximation.DyadicProtocolSchedule
import TNLean.PEPS.Approximation.DyadicRoutingPEPS

/-!
# The parties of the dyadic distribution protocol

Proposition 7.1 (`prop:protocol`), item 1, asks for “one [party] for each square in a padded
dyadic hierarchy and at most a fixed number of additional parties for each repainting of a
square” (`06-geometry.tex, lines 19–21`). The additional party of a repainting is its
placeholder: during the repainting of a square the exterior label is “represented by a fresh
additional party attached to the square being repainted”, whose identity may be replaced at the
next repainting (lines 91–95). This file fixes the parties and proves the bounds of items 1–3
that depend only on which events use which parties.

* `ProtocolParty k` has one block party for each square of the hierarchy of `[0, 2 ^ k] ^ 2` and
  one placeholder for each repainted (non-root) square. A placeholder has the scale and address
  of its square (lines 36–37, 643). There are fewer than `32 L ^ 2 / 3` parties when
  `2 ^ k < 2 L`, at most two at each square, and every party lies in the padded square.
* The guides of `TNLean.PEPS.Approximation.DyadicLevelSchedule` carry labels in a type with an
  injective block labelling and a placeholder label. Here that type is
  `GuideLabel = (ℕ × ℕ × ℕ) ⊕ Unit`, and a label is read as a party of a repainting by
  `labelParty`, which is injective on the labels of genuine squares and the placeholder; the
  block labels of every level take only such labels (`levelLabels_mem_validLabels`).
* `EventUses e p`: a block party is used by the events of `DyadicActiveLabelParties`, and the
  placeholder of a square only by the repainting of that square (lines 91–95, 627–630). If
  every gate in which a party participates belongs to an event using it, then the party
  participates in at most `64 G` gates, where `G` bounds the gates of one event
  (`participation_le_of_eventUses`); with the patch data of each gate this is
  `participation_le_of_repaintingRewrites`.
* Two parties used by one event have equal or adjacent scales and anchors within `12` times the
  side of either square in each coordinate (lines 34–37, 633–647).

That every gate of the protocol involves only parties its event uses is a hypothesis here, the
conclusion of the small-patch rewrite, birth and exchange lemmas for the constructed gates.

## Main results

* `TNLean.PEPS.Approximation.ProtocolParty`, `TNLean.PEPS.Approximation.protocolPlacement`,
  `TNLean.PEPS.Approximation.protocolPlacement_inGrid`,
  `TNLean.PEPS.Approximation.protocolPlacement_blockBounded`,
  `TNLean.PEPS.Approximation.three_mul_card_protocolParty_lt`.
* `TNLean.PEPS.Approximation.labelParty`, `TNLean.PEPS.Approximation.labelParty_injOn`,
  `TNLean.PEPS.Approximation.levelLabels_mem_validLabels`.
* `TNLean.PEPS.Approximation.participation_le_of_eventUses`,
  `TNLean.PEPS.Approximation.participation_le_of_repaintingRewrites`.
* `TNLean.PEPS.Approximation.EventUses.scale_le`,
  `TNLean.PEPS.Approximation.EventUses.anchor_dist_le`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: Proposition 7.1
  `prop:protocol` (lines 12–53), the placeholder (lines 91–100), the party lifetimes and
  locality (lines 585–631), the addresses (lines 633–647), and the counts (lines 649–652).
-/

namespace TNLean.PEPS.Approximation

open Finset

/-! ### Squares as triples -/

/-- The scale and block indices of a square of the hierarchy. -/
def DyadicSquare.toTriple {k : ℕ} (S : DyadicSquare k) : ℕ × ℕ × ℕ := (S.1, S.2.1, S.2.2)

theorem DyadicSquare.toTriple_injective (k : ℕ) :
    Function.Injective (DyadicSquare.toTriple (k := k)) := by
  rintro ⟨j, r, s⟩ ⟨j', r', s'⟩ h
  simp only [toTriple, Prod.mk.injEq] at h
  obtain ⟨hj, hr, hs⟩ := h
  obtain rfl : j = j' := Fin.ext hj
  obtain rfl : r = r' := Fin.ext hr
  obtain rfl : s = s' := Fin.ext hs
  rfl

/-- The square with given scale and block indices, if these index a square of the hierarchy. -/
def DyadicSquare.ofTriple (k : ℕ) (x : ℕ × ℕ × ℕ) : Option (DyadicSquare k) :=
  if h : x.1 < k + 1 ∧ x.2.1 < 2 ^ (k - x.1) ∧ x.2.2 < 2 ^ (k - x.1) then
    some ⟨⟨x.1, h.1⟩, ⟨x.2.1, h.2.1⟩, ⟨x.2.2, h.2.2⟩⟩
  else none

@[simp]
theorem DyadicSquare.ofTriple_toTriple {k : ℕ} (S : DyadicSquare k) :
    DyadicSquare.ofTriple k S.toTriple = some S := by
  obtain ⟨j, r, s⟩ := S
  simp [ofTriple, toTriple, j.isLt, r.isLt, s.isLt]

/-! ### Parties -/

/-- A repainted square: a square of the hierarchy other than the root square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–84`. -/
abbrev RepaintedSquare (k : ℕ) : Type := {S : DyadicSquare k // (S.1 : ℕ) < k}

/-- The parties of the protocol: a block party for every square of the hierarchy, and the
placeholder party of the repainting of every non-root square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 1,
`06-geometry.tex, lines 19–21`, and the fresh placeholder, lines 91–95. -/
abbrev ProtocolParty (k : ℕ) : Type := DyadicSquare k ⊕ RepaintedSquare k

/-- The square to which a party is attached: its own block, or the square whose repainting a
placeholder serves.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 36–37, 643`:
“additional parties have the scale and address of the square to whose repainting they
belong.” -/
def ProtocolParty.square {k : ℕ} : ProtocolParty k → DyadicSquare k
  | .inl S => S
  | .inr S => S.1

/-- The dyadic placement of the parties at their squares.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-addresses`,
`06-geometry.tex, lines 633–643`. -/
def protocolPlacement (k : ℕ) : DyadicPlacement (ProtocolParty k) where
  scale p := p.square.1
  blockX p := p.square.2.1
  blockY p := p.square.2.2

@[simp] theorem protocolPlacement_scale {k : ℕ} (p : ProtocolParty k) :
    (protocolPlacement k).scale p = p.square.1 := rfl

@[simp] theorem protocolPlacement_blockX {k : ℕ} (p : ProtocolParty k) :
    (protocolPlacement k).blockX p = p.square.2.1 := rfl

@[simp] theorem protocolPlacement_blockY {k : ℕ} (p : ProtocolParty k) :
    (protocolPlacement k).blockY p = p.square.2.2 := rfl

/-- Every party lies in the padded square `[0, 2 ^ k] ^ 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 645–646`. -/
theorem protocolPlacement_inGrid (k : ℕ) : (protocolPlacement k).InGrid (2 ^ k) := by
  have key : ∀ (j : Fin (k + 1)) (x : Fin (2 ^ (k - j))), 2 ^ (j : ℕ) * ((x : ℕ) + 1) ≤ 2 ^ k :=
    fun j x => calc 2 ^ (j : ℕ) * ((x : ℕ) + 1) ≤ 2 ^ (j : ℕ) * 2 ^ (k - j) :=
          Nat.mul_le_mul_left _ x.isLt
      _ = 2 ^ k := by rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 j.isLt)]
  exact fun p => ⟨key _ p.square.2.1, key _ p.square.2.2⟩

/-- At most two parties are attached to any square: its block party and its placeholder.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 1,
`06-geometry.tex, lines 19–21`. -/
theorem protocolPlacement_blockBounded (k : ℕ) : (protocolPlacement k).BlockBounded 2 := by
  intro j r s
  set A : Finset (DyadicSquare k) := univ.filter fun S => S.toTriple = (j, r, s)
  have hA : A.card ≤ 1 := card_le_one.2 fun S hS S' hS' =>
    DyadicSquare.toTriple_injective k ((mem_filter.1 hS).2.trans (mem_filter.1 hS').2.symm)
  have hsub : (univ.filter fun p : ProtocolParty k => (protocolPlacement k).scale p = j ∧
      (protocolPlacement k).blockX p = r ∧ (protocolPlacement k).blockY p = s) ⊆
      A.disjSum (A.subtype fun S => (S.1 : ℕ) < k) := by
    rintro (S | S) hS <;> obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hS
    · exact Finset.inl_mem_disjSum.2
        (Finset.mem_filter.2 ⟨mem_univ _, Prod.ext h1 (Prod.ext h2 h3)⟩)
    · exact Finset.inr_mem_disjSum.2 (Finset.mem_subtype.2
        (Finset.mem_filter.2 ⟨mem_univ _, Prod.ext h1 (Prod.ext h2 h3)⟩))
  refine (card_le_card hsub).trans ?_
  rw [card_disjSum, card_subtype]
  have := card_filter_le A fun S : DyadicSquare k => (S.1 : ℕ) < k
  omega

/-- The number of parties is at most twice the number of squares. -/
theorem card_protocolParty_le (k : ℕ) :
    Fintype.card (ProtocolParty k) ≤ 2 * Fintype.card (DyadicSquare k) := by
  rw [Fintype.card_sum, two_mul]
  exact Nat.add_le_add_left (Fintype.card_subtype_le _) _

/-- **`O(L ^ 2)` parties.** With `2 ^ k < 2 L`, there are fewer than `32 L ^ 2 / 3` parties.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 1,
`06-geometry.tex, lines 19–21`, and the counts, lines 649–652. -/
theorem three_mul_card_protocolParty_lt {k L : ℕ} (hk : 2 ^ k < 2 * L) :
    3 * Fintype.card (ProtocolParty k) < 32 * L ^ 2 := by
  have h1 := card_protocolParty_le k
  have h2 := three_mul_card_dyadicSquare_lt hk
  omega

/-! ### Guide labels -/

/-- The labels of the guides: the block labels `(j, r, s)` and the placeholder. The labels of
squares outside the hierarchy never occur in the schedule's guides
(`levelLabels_mem_validLabels`); they let the geometry of
`TNLean.PEPS.Approximation.DyadicLevelSchedule` use an injective block labelling.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–95`. -/
abbrev GuideLabel : Type := (ℕ × ℕ × ℕ) ⊕ Unit

/-- The placeholder label. -/
def guidePlaceholder : GuideLabel := .inr ()

theorem inl_ne_guidePlaceholder (x : ℕ × ℕ × ℕ) : (.inl x : GuideLabel) ≠ guidePlaceholder :=
  Sum.inl_ne_inr

/-- The labels that occur in the schedule's guides: the placeholder and the block labels of the
squares of the hierarchy. -/
def validLabels (k : ℕ) : Set GuideLabel :=
  insert guidePlaceholder (Set.range fun S : DyadicSquare k => .inl S.toTriple)

/-- The party holding a label during the repainting of `S`: a block label is held by its block
party and the placeholder by the placeholder party of `S`. A label outside `validLabels k` is
sent to the placeholder party of `S`; it does not occur in the schedule's guides.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 91–95`: “During that
repainting it is represented by a fresh additional party attached to the square being
repainted.” -/
def labelParty {k : ℕ} (S : RepaintedSquare k) : GuideLabel → ProtocolParty k
  | .inl x => match DyadicSquare.ofTriple k x with
    | some Q => .inl Q
    | none => .inr S
  | .inr _ => .inr S

@[simp]
theorem labelParty_toTriple {k : ℕ} (S : RepaintedSquare k) (Q : DyadicSquare k) :
    labelParty S (.inl Q.toTriple) = .inl Q := by
  simp [labelParty]

@[simp]
theorem labelParty_guidePlaceholder {k : ℕ} (S : RepaintedSquare k) :
    labelParty S guidePlaceholder = .inr S := rfl

/-- The label map of a repainting is injective on the labels of the schedule's guides. -/
theorem labelParty_injOn {k : ℕ} (S : RepaintedSquare k) :
    Set.InjOn (labelParty S) (validLabels k) := by
  rintro l (rfl | ⟨Q, rfl⟩) l' (rfl | ⟨Q', rfl⟩) h <;>
    simp_all

/-- **Valid labels of a level.** At level `2 ^ j'` with `j' < k`, every block label of the
level is the placeholder or the label of a square of the hierarchy of `[0, 2 ^ k] ^ 2`: the
parent of a block of the root square, or the block itself.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–95`. -/
theorem levelLabels_mem_validLabels {k j' : ℕ} (hj : j' < k) (done : Set (ℤ × ℤ))
    (Q : ℤ × ℤ) :
    levelLabels ((2 : ℤ) ^ (k - j')) (oldParty Sum.inl j') (newParty Sum.inl j')
      guidePlaceholder done Q ∈ validLabels k := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, k - j' = m + 1 := ⟨k - j' - 1, by omega⟩
  have hM : (2 : ℤ) ^ (k - j') = 2 * ((2 ^ m : ℕ) : ℤ) := by rw [hm, pow_succ]; push_cast; ring
  unfold levelLabels
  split_ifs with hQ hd
  · obtain ⟨h1, h2, h3, h4⟩ := hQ
    rw [hM] at h2 h4
    have hr : Q.1.toNat < 2 ^ (k - j') := by rw [hm, pow_succ]; omega
    have hs : Q.2.toNat < 2 ^ (k - j') := by rw [hm, pow_succ]; omega
    exact Or.inr ⟨⟨⟨j', by omega⟩, ⟨Q.1.toNat, hr⟩, ⟨Q.2.toNat, hs⟩⟩, rfl⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hQ
    rw [hM] at h2 h4
    have hk : k - (j' + 1) = m := by omega
    have hr : (Q.1 / 2).toNat < 2 ^ (k - (j' + 1)) := by rw [hk]; omega
    have hs : (Q.2 / 2).toNat < 2 ^ (k - (j' + 1)) := by rw [hk]; omega
    exact Or.inr ⟨⟨⟨j' + 1, by omega⟩, ⟨(Q.1 / 2).toNat, hr⟩, ⟨(Q.2 / 2).toNat, hs⟩⟩, rfl⟩
  · exact Or.inl rfl

/-! ### Uses of an event -/

/-- The parties an event uses: a block party is used by the events that use its block, in the
sense of `DyadicSquare.Uses` and `DyadicJunction.Uses`, and the placeholder of a square only by
the repainting of that square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 585–596, 627–630`:
“The same applies to a retired placeholder party. A fresh placeholder identity at the next
repainting has no raw main register or persistent main tag to inherit.” -/
def EventUses {k : ℕ} : ProtocolEvent k → ProtocolParty k → Prop
  | e, .inl Q => Sum.elim (fun S => S.Uses Q.toTriple) (fun J => J.Uses Q.toTriple) e
  | e, .inr S => e = .inl S.1

/-- **Bounded lifetime participation.** Let the gates `Γ` of a schedule belong to events `ev γ`,
at most `G` gates to each. If every gate in which the party `p` participates belongs to an event
that uses `p`, then `p` participates in at most `64 G` gates: a block party by the active-label
invariant, a placeholder because it serves a single repainting.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex, lines 31–32`, and the lifetime argument, lines 572–631. -/
theorem participation_le_of_eventUses {k : ℕ} {Γ : Type*} [Fintype Γ]
    (ev : Γ → ProtocolEvent k) {G : ℕ} (hG : ∀ e, #{γ | ev γ = e} ≤ G) (p : ProtocolParty k)
    (P : Γ → Prop) [DecidablePred P] (hP : ∀ γ, P γ → EventUses (ev γ) p) :
    #{γ | P γ} ≤ 64 * G := by
  rcases p with Q | S
  · exact card_gates_le_of_uses ev hG Q.toTriple P hP
  · refine (card_le_card fun γ hγ => ?_).trans ((hG (.inl S.1)).trans (by omega))
    simp only [mem_filter, mem_univ, true_and] at hγ ⊢
    exact hP γ hγ

/-- **Bounded lifetime participation from patch data.** Let the gates `Γ` of a schedule belong
to events `ev γ`, at most `G` gates to each, and let each gate carry patch data `rw γ` on the
guide labels: a direct repainting or a large-scale repainting step for a repainting, a resize
for a junction. If a block party participates in a gate only when its label is a party of the
gate's patch data, and a placeholder only in gates of its own repainting, then every party
participates in at most `64 G` gates.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex, lines 31–32`, and the lifetime argument, lines 572–631. -/
theorem participation_le_of_repaintingRewrites {k : ℕ} {Γ : Type*} [Fintype Γ]
    (ev : Γ → ProtocolEvent k) {G : ℕ} (hG : ∀ e, #{γ | ev γ = e} ≤ G)
    (rw : Γ → GuidePatchRewrite GuideLabel)
    (hrw : ∀ γ, Sum.elim
      (fun S => (rw γ).IsDirectRepainting Sum.inl guidePlaceholder ((2 : ℤ) ^ (k - (S.1 : ℕ)))
          S.1 S.2.1 S.2.2 ∨
        (rw γ).IsLargeRepaintingStep Sum.inl guidePlaceholder ((2 : ℤ) ^ (k - (S.1 : ℕ))) S.1
          S.2.1 S.2.2)
      (fun J => (rw γ).IsJunctionResize Sum.inl guidePlaceholder ((2 : ℤ) ^ (k - (J.1 : ℕ))) J.1
        J.2.1 J.2.2)
      (ev γ))
    (p : ProtocolParty k) (P : Γ → Prop) [DecidablePred P]
    (hP : ∀ γ, P γ → Sum.elim
      (fun Q => (.inl Q.toTriple : GuideLabel) ∈ (rw γ).parties guidePlaceholder)
      (fun S => ev γ = .inl S.1) p) :
    #{γ | P γ} ≤ 64 * G := by
  rcases p with Q | S
  · exact card_gates_le_of_repaintingRewrites Sum.inl_injective inl_ne_guidePlaceholder ev hG rw
      hrw Q.toTriple P hP
  · exact participation_le_of_eventUses ev hG (.inr S) P hP

/-! ### Locality of the parties of an event -/

/-- A party used by the repainting of the square `S` of scale `j'` has scale `j'` or `j' + 1`,
and in each coordinate its anchor is within `6 · 2 ^ j'` of the anchor of `S`. -/
private theorem near_of_eventUses_repaint {k : ℕ} {S : DyadicSquare k} {p : ProtocolParty k}
    (h : EventUses (.inl S) p) :
    (S.1 : ℕ) ≤ (protocolPlacement k).scale p ∧ (protocolPlacement k).scale p ≤ S.1 + 1 ∧
      Nat.dist ((protocolPlacement k).anchor p).1 (dyadicAnchor S.1 S.2.1) < 6 * 2 ^ (S.1 : ℕ) ∧
      Nat.dist ((protocolPlacement k).anchor p).2 (dyadicAnchor S.1 S.2.2) <
        6 * 2 ^ (S.1 : ℕ) := by
  have hP : 3 * 2 ^ ((S.1 : ℕ) + 1) = 6 * 2 ^ (S.1 : ℕ) := by rw [pow_succ]; ring
  rcases p with Q | ⟨Q, hQ⟩
  · obtain ⟨q, t, hq1, hq2, ht1, ht2, hown⟩ := h
    have hj := hown.scale
    simp only [DyadicPlacement.anchor, protocolPlacement_scale, protocolPlacement_blockX,
      protocolPlacement_blockY, ProtocolParty.square]
    have h₁ : ((Q.1 : ℕ) = S.1 ∧ (Q.2.1 : ℕ) = q) ∨ ((Q.1 : ℕ) = S.1 + 1 ∧ (Q.2.1 : ℕ) = q / 2) :=
      by rcases hown with h | h <;> simp only [DyadicSquare.toTriple, Prod.mk.injEq] at h <;>
        simp [h]
    have h₂ : ((Q.1 : ℕ) = S.1 ∧ (Q.2.2 : ℕ) = t) ∨ ((Q.1 : ℕ) = S.1 + 1 ∧ (Q.2.2 : ℕ) = t / 2) :=
      by rcases hown with h | h <;> simp only [DyadicSquare.toTriple, Prod.mk.injEq] at h <;>
        simp [h]
    have a := dyadicAnchor_dist_lt_of_adjacent hq1 hq2 h₁ (Or.inl ⟨rfl, rfl⟩)
    have b := dyadicAnchor_dist_lt_of_adjacent ht1 ht2 h₂ (Or.inl ⟨rfl, rfl⟩)
    simp only [DyadicSquare.toTriple] at hj
    refine ⟨hj.1, hj.2, ?_, ?_⟩ <;> rw [Nat.dist] <;> omega
  · obtain rfl : S = Q := Sum.inl_injective (show (.inl S : ProtocolEvent k) = .inl Q from h)
    simp [DyadicPlacement.anchor, ProtocolParty.square, Nat.dist_self]

/-- A party used by the resize at the junction `J` of scale `j` has scale `j`, and in each
coordinate its anchor is within `6 · 2 ^ j` of the anchor of a fixed block at the junction. -/
private theorem near_of_eventUses_resize {k : ℕ} {J : DyadicJunction k} {p : ProtocolParty k}
    (h : EventUses (.inr J) p) :
    (protocolPlacement k).scale p = J.1 ∧
      Nat.dist ((protocolPlacement k).anchor p).1 (dyadicAnchor J.1 (J.2.1 - 1)) <
        6 * 2 ^ (J.1 : ℕ) ∧
      Nat.dist ((protocolPlacement k).anchor p).2 (dyadicAnchor J.1 (J.2.2 - 1)) <
        6 * 2 ^ (J.1 : ℕ) := by
  have hP : 3 * 2 ^ ((J.1 : ℕ) + 1) = 6 * 2 ^ (J.1 : ℕ) := by rw [pow_succ]; ring
  rcases p with Q | S
  · obtain ⟨hj, h1, h2, h3, h4⟩ := h
    simp only [DyadicSquare.toTriple] at hj h1 h2 h3 h4
    simp only [DyadicPlacement.anchor, protocolPlacement_scale, protocolPlacement_blockX,
      protocolPlacement_blockY, ProtocolParty.square, hj]
    have a := dyadicAnchor_dist_lt_of_adjacent (j := J.1) (q := Q.2.1) (q' := J.2.1 - 1)
      (j₁ := J.1) (a₁ := Q.2.1) (j₂ := J.1) (a₂ := J.2.1 - 1) (by omega) (by omega)
      (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
    have b := dyadicAnchor_dist_lt_of_adjacent (j := J.1) (q := Q.2.2) (q' := J.2.2 - 1)
      (j₁ := J.1) (a₁ := Q.2.2) (j₂ := J.1) (a₂ := J.2.2 - 1) (by omega) (by omega)
      (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
    refine ⟨trivial, ?_, ?_⟩ <;> rw [Nat.dist] <;> omega
  · exact absurd h Sum.inr_ne_inl

/-- **Equal or adjacent scales.** Two parties used by one event have equal or adjacent scales.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 3,
`06-geometry.tex, lines 34–35`, and lines 585–596, 643–645. -/
theorem EventUses.scale_le {k : ℕ} {e : ProtocolEvent k} {p p' : ProtocolParty k}
    (h : EventUses e p) (h' : EventUses e p') :
    (protocolPlacement k).scale p ≤ (protocolPlacement k).scale p' + 1 := by
  rcases e with S | J
  · have a := near_of_eventUses_repaint h
    have b := near_of_eventUses_repaint h'
    omega
  · have a := near_of_eventUses_resize h
    have b := near_of_eventUses_resize h'
    omega

/-- **Address locality.** Two parties used by one event have anchors within `12` times the side
of the square of either party, in each coordinate.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 3,
`06-geometry.tex, lines 35–37`, and lines 585–596, 643–645: “The preceding locality statement
gives `O(n)` address distances for parties sharing a gate.” -/
theorem EventUses.anchor_dist_le {k : ℕ} {e : ProtocolEvent k} {p p' : ProtocolParty k}
    (h : EventUses e p) (h' : EventUses e p') :
    Nat.dist ((protocolPlacement k).anchor p).1 ((protocolPlacement k).anchor p').1 ≤
        12 * 2 ^ (protocolPlacement k).scale p ∧
      Nat.dist ((protocolPlacement k).anchor p).2 ((protocolPlacement k).anchor p').2 ≤
        12 * 2 ^ (protocolPlacement k).scale p := by
  rcases e with S | J
  · obtain ⟨hs, -, a1, a2⟩ := near_of_eventUses_repaint h
    obtain ⟨-, -, b1, b2⟩ := near_of_eventUses_repaint h'
    have hpow : 2 ^ (S.1 : ℕ) ≤ 2 ^ (protocolPlacement k).scale p :=
      Nat.pow_le_pow_right two_pos hs
    rw [Nat.dist_comm] at b1 b2
    exact ⟨(Nat.dist.triangle_inequality _ (dyadicAnchor S.1 S.2.1) _).trans (by omega),
      (Nat.dist.triangle_inequality _ (dyadicAnchor S.1 S.2.2) _).trans (by omega)⟩
  · obtain ⟨hs, a1, a2⟩ := near_of_eventUses_resize h
    obtain ⟨-, b1, b2⟩ := near_of_eventUses_resize h'
    rw [hs]
    rw [Nat.dist_comm] at b1 b2
    exact ⟨(Nat.dist.triangle_inequality _ (dyadicAnchor J.1 (J.2.1 - 1)) _).trans (by omega),
      (Nat.dist.triangle_inequality _ (dyadicAnchor J.1 (J.2.2 - 1)) _).trans (by omega)⟩

end TNLean.PEPS.Approximation
