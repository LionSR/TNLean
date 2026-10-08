/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicAnchors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Interval.Finset.Nat

/-!
# Horizontal-then-vertical routing on dyadic anchors

Parties sit at the anchors of dyadic blocks of the padded square. Each link, oriented
arbitrarily, is routed horizontally from the anchor of its first party, then vertically to
the anchor of its second party. Assume

* at most `B` parties are attached to any dyadic block,
* every party has at most `Δ` incident links, and
* the two anchors of every link are at distance at most `c` times the side of either
  endpoint block (in the maximum norm).

Then every horizontal or vertical unit edge of the padded square is traversed by at most
`2 (2 c + 1) B Δ` walk steps, counted with repetition. The constant depends only on
`c`, `B` and `Δ`, not on the side of the square or on the number of dyadic levels.

The proof follows the source. A horizontal step lies on the row of the anchor of its first
party. A nonunit anchor row `2 ^ (j - 1) (2 s + 1)` determines the scale `j` and the block
row `s` by its two-adic valuation, and since anchors of one scale are `2 ^ j` apart, only
`2 c + 1` blocks of that scale are close enough to reach a given edge. Unit-scale parties
contribute a separate bound of the same form. Vertical steps use the column of the second
party in the same way.

The source additionally records that the two endpoint scales of a link are equal or adjacent.
The bound below does not use that information, so it is not assumed.

**Scope restriction (party-network bounds as hypotheses):** Lemma 8.2 `lem:routing`
(`07-assembly.tex:122–127`) has no hypotheses; it concerns the party network of
Proposition 7.1 `prop:protocol` (`06-geometry.tex:12–53`), from which the source derives the
block bound, the degree bound and the separation bound. Here `load_horizontal_le` and
`load_vertical_le` take these three bounds (`BlockBounded`, `DegreeBounded`,
`SeparationBounded`) as hypotheses on an arbitrary placement, so they are a conditional form of
the lemma. Documented in `docs/paper-gaps/polypeps_routing_network_bounds.tex`; the hypotheses
are discharged once Proposition 7.1 is formalized.

## Main results

* `TNLean.PEPS.Approximation.DyadicPlacement.load_horizontal_le`,
  `TNLean.PEPS.Approximation.DyadicPlacement.load_vertical_le`: the constant edge congestion
  of the padded routing.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Lemma 8.2 `lem:routing` and its proof,
  `07-assembly.tex:122–147`.
-/

namespace TNLean.PEPS.Approximation

open Finset

/-! ### Monotone walks on the padded square -/

/-- The monotone walk from `a` towards `b` on a line, after `n` unit steps. -/
def lineWalk (a b n : ℕ) : ℕ := if a ≤ b then a + n else a - n

/-- The number of unit steps of the horizontal-then-vertical walk from `a` to `b`. -/
def hvLength (a b : ℕ × ℕ) : ℕ := Nat.dist a.1 b.1 + Nat.dist a.2 b.2

/-- The horizontal-then-vertical walk from `a` to `b`: first along the row of `a`, then
along the column of `b`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:129–130`. -/
def hvRoute (a b : ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  if i ≤ Nat.dist a.1 b.1 then (lineWalk a.1 b.1 i, a.2)
  else (b.1, lineWalk a.2 b.2 (i - Nat.dist a.1 b.1))

/-- The step from `p` to `q` traverses the unit edge with endpoints `e₁` and `e₂`. -/
def IsUnitCrossing (p q e₁ e₂ : ℕ × ℕ) : Prop := (p = e₁ ∧ q = e₂) ∨ (p = e₂ ∧ q = e₁)

instance (p q e₁ e₂ : ℕ × ℕ) : Decidable (IsUnitCrossing p q e₁ e₂) := by
  unfold IsUnitCrossing; infer_instance

/-- The steps from `p` to `q` are unit steps of the square lattice. -/
def IsUnitStep (p q : ℕ × ℕ) : Prop :=
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)) ∨ (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2))

/-- The walk starts at `a`. -/
@[simp] theorem hvRoute_zero (a b : ℕ × ℕ) : hvRoute a b 0 = a := by
  simp [hvRoute, lineWalk]

/-- The walk ends at `b` after `hvLength a b` steps. -/
theorem hvRoute_hvLength (a b : ℕ × ℕ) : hvRoute a b (hvLength a b) = b := by
  unfold hvRoute hvLength lineWalk Nat.dist
  ext <;> split_ifs <;> simp <;> omega

/-- Every step of the walk is a unit step. -/
theorem hvRoute_isUnitStep (a b : ℕ × ℕ) {i : ℕ} (hi : i < hvLength a b) :
    IsUnitStep (hvRoute a b i) (hvRoute a b (i + 1)) := by
  unfold IsUnitStep hvRoute hvLength lineWalk Nat.dist at *
  split_ifs <;> simp <;> omega

/-- The walk stays below any bound satisfied by both endpoints. -/
theorem hvRoute_lt {a b : ℕ × ℕ} {M : ℕ} (ha : a.1 < M ∧ a.2 < M) (hb : b.1 < M ∧ b.2 < M)
    {i : ℕ} (hi : i ≤ hvLength a b) : (hvRoute a b i).1 < M ∧ (hvRoute a b i).2 < M := by
  unfold hvRoute hvLength lineWalk Nat.dist at *
  split_ifs <;> simp <;> omega

/-- A step of the walk traversing a horizontal unit edge lies on the row of the first
endpoint, inside the horizontal travel range, and is unique. -/
theorem hvRoute_cross_horizontal {a b : ℕ × ℕ} {x y i : ℕ}
    (h : IsUnitCrossing (hvRoute a b i) (hvRoute a b (i + 1)) (x, y) (x + 1, y)) :
    a.2 = y ∧ Nat.dist a.1 x ≤ Nat.dist a.1 b.1 ∧
      i = if a.1 ≤ b.1 then x - a.1 else a.1 - x - 1 := by
  unfold IsUnitCrossing hvRoute lineWalk Nat.dist at *
  split_ifs at h ⊢ <;> simp only [Prod.mk.injEq] at h <;> omega

/-- A step of the walk traversing a vertical unit edge lies on the column of the second
endpoint, inside the vertical travel range, and is unique. -/
theorem hvRoute_cross_vertical {a b : ℕ × ℕ} {x y i : ℕ} (hi : i < hvLength a b)
    (h : IsUnitCrossing (hvRoute a b i) (hvRoute a b (i + 1)) (x, y) (x, y + 1)) :
    b.1 = x ∧ Nat.dist b.2 y ≤ Nat.dist a.2 b.2 ∧
      i = Nat.dist a.1 b.1 + if a.2 ≤ b.2 then y - a.2 else a.2 - y - 1 := by
  unfold IsUnitCrossing hvRoute hvLength lineWalk Nat.dist at *
  split_ifs at h ⊢ <;> simp only [Prod.mk.injEq] at h <;> omega

/-! ### Counting anchors near an edge -/

/-- If `a` is within `c m` of `x`, its block index `a / m` lies within `c` of `x / m`. -/
theorem div_mem_Icc_of_dist_le {a x m c : ℕ} (hm : 0 < m) (h : Nat.dist a x ≤ c * m) :
    a / m ∈ Icc (x / m - c) (x / m + c) := by
  unfold Nat.dist at h
  have h1 : a ≤ x + c * m := by omega
  have h2 : x ≤ a + c * m := by omega
  have k1 : a / m ≤ x / m + c := by
    calc a / m ≤ (x + c * m) / m := Nat.div_le_div_right h1
      _ = x / m + c := Nat.add_mul_div_right _ _ hm
  have k2 : x / m ≤ a / m + c := by
    calc x / m ≤ (a + c * m) / m := Nat.div_le_div_right h2
      _ = a / m + c := Nat.add_mul_div_right _ _ hm
  exact mem_Icc.2 ⟨tsub_le_iff_right.2 k2, k1⟩

/-- The parties of a dyadic placement: scale and block indices. -/
structure DyadicPlacement (P : Type*) where
  /-- The scale `j` of the block of side `2 ^ j` to which a party is attached. -/
  scale : P → ℕ
  /-- The horizontal block index. -/
  blockX : P → ℕ
  /-- The vertical block index. -/
  blockY : P → ℕ

namespace DyadicPlacement

variable {P : Type*} [Fintype P] [DecidableEq P] (A : DyadicPlacement P)

/-- The anchor of a party: the anchor of its dyadic block.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:anchors` and
`07-assembly.tex:113–114`. -/
def anchor (p : P) : ℕ × ℕ :=
  (dyadicAnchor (A.scale p) (A.blockX p), dyadicAnchor (A.scale p) (A.blockY p))

/-- At most `B` parties are attached to any dyadic block.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:113–114`. -/
def BlockBounded (B : ℕ) : Prop :=
  ∀ j r s, #{p | A.scale p = j ∧ A.blockX p = r ∧ A.blockY p = s} ≤ B

omit [DecidableEq P] in
/-- Counting parties whose anchor lies on a fixed line and within `c` block sides of a fixed
point on that line. The line coordinate is `u`, the transverse one `v`. -/
theorem card_near_line_le {u v : P → ℕ} {B c : ℕ}
    (hB : ∀ j r s, #{p | A.scale p = j ∧ v p = r ∧ u p = s} ≤ B) (x y : ℕ) :
    #{p | dyadicAnchor (A.scale p) (u p) = y ∧
        Nat.dist (dyadicAnchor (A.scale p) (v p)) x ≤ c * 2 ^ A.scale p} ≤
      2 * ((2 * c + 1) * B) := by
  classical
  set S := ({p | dyadicAnchor (A.scale p) (u p) = y ∧
        Nat.dist (dyadicAnchor (A.scale p) (v p)) x ≤ c * 2 ^ A.scale p} : Finset P)
  -- Parties of one scale and one transverse block with nearby anchors.
  have key : ∀ (T : Finset P) (J s₀ : ℕ),
      (∀ p ∈ T, p ∈ S ∧ A.scale p = J ∧ u p = s₀) → #T ≤ (2 * c + 1) * B := by
    intro T J s₀ hT
    let f : P → ℕ × ℕ × ℕ := fun p => (A.scale p, v p, u p)
    let I := Icc (x / 2 ^ J - c) (x / 2 ^ J + c)
    have hmaps : ∀ p ∈ T, f p ∈ I.image fun r => (J, r, s₀) := by
      intro p hp
      obtain ⟨hpS, hJ, hs⟩ := hT p hp
      simp only [S, mem_filter, mem_univ, true_and] at hpS
      have hmem := div_mem_Icc_of_dist_le (Nat.pow_pos two_pos) hpS.2
      rw [dyadicAnchor_div, hJ] at hmem
      exact mem_image.2 ⟨v p, hmem, by simp [f, hJ, hs]⟩
    have hfib : ∀ b ∈ I.image (fun r => (J, r, s₀)), #{p ∈ T | f p = b} ≤ B := by
      intro b _
      refine le_trans (card_le_card ?_) (hB b.1 b.2.1 b.2.2)
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      obtain ⟨_, rfl⟩ := hp
      exact ⟨rfl, rfl, rfl⟩
    calc #T ≤ B * #(I.image fun r => (J, r, s₀)) :=
          card_le_mul_card_image_of_maps_to hmaps B hfib
      _ ≤ B * #I := Nat.mul_le_mul_left _ card_image_le
      _ ≤ (2 * c + 1) * B := by
        rw [mul_comm]; exact Nat.mul_le_mul_right _ (by simp [I, Nat.card_Icc]; omega)
  -- Split by unit and nonunit scale.
  rw [← card_filter_add_card_filter_not (s := S) (fun p => A.scale p = 0)]
  have h0 : #(S.filter fun p => A.scale p = 0) ≤ (2 * c + 1) * B := by
    refine key _ 0 y fun p hp => ?_
    rw [mem_filter] at hp
    refine ⟨hp.1, hp.2, ?_⟩
    have := hp.1
    simp only [S, mem_filter, mem_univ, true_and] at this
    simpa [dyadicAnchor, hp.2] using this.1
  have h1 : #(S.filter fun p => ¬A.scale p = 0) ≤ (2 * c + 1) * B := by
    rcases (S.filter fun p => ¬A.scale p = 0).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
    · simp [he]
    refine key _ (A.scale p₀) (u p₀) fun p hp => ?_
    rw [mem_filter] at hp hp₀
    have hpS := hp.1
    have hp₀S := hp₀.1
    simp only [S, mem_filter, mem_univ, true_and] at hpS hp₀S
    obtain ⟨hj, hs⟩ := dyadicAnchor_inj hp.2 hp₀.2 (hpS.1.trans hp₀S.1.symm)
    exact ⟨hp.1, hj, hs⟩
  omega

/-- Counting links whose chosen endpoint satisfies a condition, by the degree bound. -/
theorem card_link_le {Λ : Type*} [Fintype Λ] (f : Λ → P) {Δ : ℕ}
    (hdeg : ∀ p, #{ℓ | f ℓ = p} ≤ Δ) (Q : P → Prop) [DecidablePred Q] :
    #{ℓ | Q (f ℓ)} ≤ Δ * #{p | Q p} := by
  classical
  refine card_le_mul_card_image_of_maps_to (f := f) (t := ({p | Q p} : Finset P)) ?_ Δ ?_
  · intro ℓ hℓ
    simpa using hℓ
  · intro p _
    refine le_trans (card_le_card ?_) (hdeg p)
    intro ℓ hℓ
    simp only [mem_filter, mem_univ, true_and] at hℓ ⊢
    exact hℓ.2

end DyadicPlacement

/-! ### The padded routing and its congestion -/

namespace DyadicPlacement

variable {P Λ : Type*} [Fintype P] [DecidableEq P] [Fintype Λ]

variable (src tgt : Λ → P)

/-- Every party has at most `Δ` incident links.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:61–62` and
`07-assembly.tex:140–141`. -/
def DegreeBounded (Δ : ℕ) : Prop := ∀ p, #{ℓ | src ℓ = p ∨ tgt ℓ = p} ≤ Δ

omit [Fintype P] in
variable {src tgt} in
/-- Under a degree bound, every party is the first endpoint of at most `Δ` links. -/
theorem DegreeBounded.src_le {Δ : ℕ} (h : DegreeBounded src tgt Δ) (p : P) :
    #{ℓ | src ℓ = p} ≤ Δ :=
  le_trans (card_le_card fun ℓ => by simp +contextual) (h p)

omit [Fintype P] in
variable {src tgt} in
/-- Under a degree bound, every party is the second endpoint of at most `Δ` links. -/
theorem DegreeBounded.tgt_le {Δ : ℕ} (h : DegreeBounded src tgt Δ) (p : P) :
    #{ℓ | tgt ℓ = p} ≤ Δ :=
  le_trans (card_le_card fun ℓ => by simp +contextual) (h p)

variable (A : DyadicPlacement P)

/-- The two anchors of every link are at distance at most `c` times the side of either
endpoint block, in the maximum norm.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:130–132`: “the endpoint
scales are equal or adjacent and their separation is at most a fixed multiple of either
scale.” -/
def SeparationBounded (c : ℕ) : Prop :=
  ∀ ℓ p, (p = src ℓ ∨ p = tgt ℓ) →
    Nat.dist (A.anchor (src ℓ)).1 (A.anchor (tgt ℓ)).1 ≤ c * 2 ^ A.scale p ∧
      Nat.dist (A.anchor (src ℓ)).2 (A.anchor (tgt ℓ)).2 ≤ c * 2 ^ A.scale p

/-- The number of steps of the padded walk of a link. -/
def linkLength (ℓ : Λ) : ℕ := hvLength (A.anchor (src ℓ)) (A.anchor (tgt ℓ))

/-- The padded walk of a link. -/
def linkRoute (ℓ : Λ) (i : ℕ) : ℕ × ℕ := hvRoute (A.anchor (src ℓ)) (A.anchor (tgt ℓ)) i

/-- The number of walk steps, over all links and counted with repetition, traversing the unit
edge with endpoints `e₁` and `e₂`. -/
def load (e₁ e₂ : ℕ × ℕ) : ℕ :=
  #{t : Σ ℓ, Fin (A.linkLength src tgt ℓ) |
    IsUnitCrossing (A.linkRoute src tgt t.1 t.2) (A.linkRoute src tgt t.1 (t.2 + 1)) e₁ e₂}

/-- **Horizontal congestion.** Every horizontal unit edge of the padded square is traversed
by at most `2 (2 c + 1) B Δ` walk steps.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:134–142`. -/
theorem load_horizontal_le {B Δ c : ℕ} (hB : A.BlockBounded B)
    (hΔ : DegreeBounded src tgt Δ) (hsep : A.SeparationBounded src tgt c) (x y : ℕ) :
    A.load src tgt (x, y) (x + 1, y) ≤ 2 * (2 * c + 1) * B * Δ := by
  classical
  let Q : P → Prop := fun p => dyadicAnchor (A.scale p) (A.blockY p) = y ∧
    Nat.dist (dyadicAnchor (A.scale p) (A.blockX p)) x ≤ c * 2 ^ A.scale p
  calc A.load src tgt (x, y) (x + 1, y) ≤ #{ℓ | Q (src ℓ)} := by
        refine card_le_card_of_injOn Sigma.fst (fun t ht => ?_) (fun t ht t' ht' htt => ?_)
        · simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ht ⊢
          obtain ⟨hy, hx, -⟩ := hvRoute_cross_horizontal ht
          exact ⟨hy, hx.trans ((hsep t.1 _ (Or.inl rfl)).1)⟩
        · simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ht ht'
          obtain ⟨ℓ, i⟩ := t
          obtain ⟨ℓ', i'⟩ := t'
          dsimp only at htt
          subst htt
          have e1 := (hvRoute_cross_horizontal ht).2.2
          have e2 := (hvRoute_cross_horizontal ht').2.2
          exact Sigma.ext rfl (heq_of_eq (Fin.ext (e1.trans e2.symm)))
    _ ≤ Δ * #{p | Q p} := DyadicPlacement.card_link_le src hΔ.src_le Q
    _ ≤ Δ * (2 * ((2 * c + 1) * B)) :=
        Nat.mul_le_mul_left _ (A.card_near_line_le (u := A.blockY) (v := A.blockX) hB x y)
    _ = 2 * (2 * c + 1) * B * Δ := by ring

/-- **Vertical congestion.** Every vertical unit edge of the padded square is traversed by at
most `2 (2 c + 1) B Δ` walk steps.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:142–145`. -/
theorem load_vertical_le {B Δ c : ℕ} (hB : A.BlockBounded B)
    (hΔ : DegreeBounded src tgt Δ) (hsep : A.SeparationBounded src tgt c) (x y : ℕ) :
    A.load src tgt (x, y) (x, y + 1) ≤ 2 * (2 * c + 1) * B * Δ := by
  classical
  let Q : P → Prop := fun p => dyadicAnchor (A.scale p) (A.blockX p) = x ∧
    Nat.dist (dyadicAnchor (A.scale p) (A.blockY p)) y ≤ c * 2 ^ A.scale p
  calc A.load src tgt (x, y) (x, y + 1) ≤ #{ℓ | Q (tgt ℓ)} := by
        refine card_le_card_of_injOn Sigma.fst (fun t ht => ?_) (fun t ht t' ht' htt => ?_)
        · simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ht ⊢
          obtain ⟨hx, hy, -⟩ := hvRoute_cross_vertical t.2.2 ht
          exact ⟨hx, hy.trans ((hsep t.1 _ (Or.inr rfl)).2)⟩
        · simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ht ht'
          obtain ⟨ℓ, i⟩ := t
          obtain ⟨ℓ', i'⟩ := t'
          dsimp only at htt
          subst htt
          have e1 := (hvRoute_cross_vertical i.2 ht).2.2
          have e2 := (hvRoute_cross_vertical i'.2 ht').2.2
          exact Sigma.ext rfl (heq_of_eq (Fin.ext (e1.trans e2.symm)))
    _ ≤ Δ * #{p | Q p} := DyadicPlacement.card_link_le tgt hΔ.tgt_le Q
    _ ≤ Δ * (2 * ((2 * c + 1) * B)) :=
        Nat.mul_le_mul_left _ (A.card_near_line_le (u := A.blockX) (v := A.blockY) (c := c)
          (fun j r s => (card_le_card fun p hp => by
            simp only [mem_filter, mem_univ, true_and] at hp ⊢; tauto).trans (hB j s r)) y x)
    _ = 2 * (2 * c + 1) * B * Δ := by ring

end DyadicPlacement

end TNLean.PEPS.Approximation
