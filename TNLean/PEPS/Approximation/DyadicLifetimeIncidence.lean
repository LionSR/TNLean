/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finset.Sum
import TNLean.PEPS.Approximation.DyadicHierarchyCounts

/-!
# Bounded lifetime incidence in the padded dyadic hierarchy

Proposition 7.1 (`prop:protocol`), item 2, asserts that each party of the distribution protocol
participates in at most a fixed number of gates involving other parties over its entire
lifetime. The source proves it in two steps (`06-geometry.tex:597–631`). The active-label
invariant `eq:geometry-active-labels` shows that a block party of side `m` occurs in linked
gates only at levels `m` and `m / 2` and their intervening transition, and only at repaintings
or junction resizes within distance `O(m)` of its block. Then: “At these scales there are only a
fixed number of repaintings or junctions within distance `O(m)` of its block.”

This file proves the second step in two dimensions. Fix a block of side `2 ^ j` with block
indices `(r, s)` and a constant `c`. A square of the hierarchy at scale `j'` is *near* the block
when `j' ∈ {j - 1, j}` and, in each coordinate, the closed intervals of the two squares are
within distance `c · 2 ^ j`; a junction (grid corner) at scale `j'` is near when `j' ∈ {j - 1, j}`
and each corner coordinate is within `c · 2 ^ j` of the closed interval of the block.

* there are at most `2 (4 c + 4) ^ 2` near squares and at most `2 (4 c + 4) ^ 2` near junctions,
  whatever the depth `k` of the hierarchy;
* hence, if every repainting and every junction resize consists of at most `G` gates, a party
  all of whose gates belong to near repaintings and junction resizes participates in at most
  `4 G (4 c + 4) ^ 2` gates.

The bound depends only on `c` and `G`. The first step, that the gates of a block party belong
to near repaintings and junction resizes, needs the gates of the protocol, which are not
constructed here; the guide part of the invariant is in
`TNLean.PEPS.Approximation.DyadicLevelSchedule`.

## Main results

* `TNLean.PEPS.Approximation.card_range_blockNear_le`: one coordinate of the count.
* `TNLean.PEPS.Approximation.card_dyadicSquare_near_le`,
  `TNLean.PEPS.Approximation.card_dyadicJunction_near_le`: the near squares and junctions.
* `TNLean.PEPS.Approximation.card_gates_le_of_near`: the lifetime participation bound.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: Proposition 7.1
  `prop:protocol`, item 2 (lines 24–32), and the lifetime argument (lines 572–631).
-/

namespace TNLean.PEPS.Approximation

open Finset

/-! ### One coordinate -/

/-- One coordinate of nearness of two squares: the closed intervals `[2 ^ j r, 2 ^ j (r + 1)]`
and `[2 ^ j' r', 2 ^ j' (r' + 1)]` are within distance `g`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “within distance `O(m)` of its block”,
`06-geometry.tex:617–618`. -/
def BlockNear (j r j' r' g : ℕ) : Prop :=
  2 ^ j' * r' ≤ 2 ^ j * r + 2 ^ j + g ∧ 2 ^ j * r ≤ 2 ^ j' * r' + 2 ^ j' + g

instance (j r j' r' g : ℕ) : Decidable (BlockNear j r j' r' g) := by
  unfold BlockNear; infer_instance

/-- One coordinate of nearness of a grid corner to a square: the corner coordinate `2 ^ j' u`
is within distance `g` of the closed interval `[2 ^ j r, 2 ^ j (r + 1)]`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “repaintings or junctions within distance
`O(m)` of its block”, `06-geometry.tex:617–618`. -/
def CornerNear (j r j' u g : ℕ) : Prop :=
  2 ^ j' * u ≤ 2 ^ j * r + 2 ^ j + g ∧ 2 ^ j * r ≤ 2 ^ j' * u + g

instance (j r j' u g : ℕ) : Decidable (CornerNear j r j' u g) := by
  unfold CornerNear; infer_instance

theorem CornerNear.blockNear {j r j' u g : ℕ} (h : CornerNear j r j' u g) :
    BlockNear j r j' u g :=
  ⟨h.1, h.2.trans (Nat.add_le_add_right (Nat.le_add_right _ _) _)⟩

/-- **Near blocks, one coordinate.** At a scale `j'` with `j ≤ j' + 1`, at most `4 c + 4` blocks
of side `2 ^ j'` have closed intervals within distance `g ≤ c · 2 ^ j` of the interval
`[2 ^ j r, 2 ^ j (r + 1)]`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:611–618`. -/
theorem card_range_blockNear_le {j j' r g c : ℕ} (hj : j ≤ j' + 1) (hg : g ≤ c * 2 ^ j)
    (M : ℕ) : ((range M).filter fun r' => BlockNear j r j' r' g).card ≤ 4 * c + 4 := by
  have hb : 0 < 2 ^ j' := pow_pos two_pos j'
  have hn : 2 ^ j ≤ 2 * 2 ^ j' := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right two_pos hj
  have hsub : ((range M).filter fun r' => BlockNear j r j' r' g) ⊆
      (range M).filter fun r' => 2 ^ j * r - g ≤ 2 ^ j' * (r' + 1) ∧
        2 ^ j' * r' ≤ 2 ^ j * r + 2 ^ j + g := by
    intro r' hr'
    rw [mem_filter] at hr' ⊢
    obtain ⟨hM, h1, h2⟩ := hr'
    refine ⟨hM, ?_, h1⟩
    rw [mul_add, mul_one]
    omega
  refine (card_le_card hsub).trans ((card_blocks_meeting_le hb _ _ M).trans ?_)
  -- `b ⌊U / b⌋ ≤ U ≤ V + n + 2 g < b (⌊V / b⌋ + 1) + b (4 c + 2)`, with `b = 2 ^ j'`, `n = 2 ^ j`
  have h1 := Nat.mul_div_le (2 ^ j * r + 2 ^ j + g) (2 ^ j')
  have h2 := Nat.lt_mul_div_succ (2 ^ j * r - g) hb
  have h3 : 2 ^ j + 2 * g ≤ 2 ^ j' * (4 * c + 2) := by
    have : 2 ^ j * (1 + 2 * c) ≤ 2 * 2 ^ j' * (1 + 2 * c) := Nat.mul_le_mul_right _ hn
    nlinarith
  have h4 : 2 ^ j' * ((2 ^ j * r + 2 ^ j + g) / 2 ^ j') <
      2 ^ j' * ((2 ^ j * r - g) / 2 ^ j' + 4 * c + 3) := by
    have : 2 ^ j * r + 2 ^ j + g ≤ 2 ^ j * r - g + 2 ^ j + 2 * g := by omega
    nlinarith
  have := Nat.lt_of_mul_lt_mul_left h4
  omega

/-- **Near grid corners, one coordinate.** At a scale `j'` with `j ≤ j' + 1`, at most `4 c + 4`
grid corners `2 ^ j' u` lie within distance `g ≤ c · 2 ^ j` of the interval
`[2 ^ j r, 2 ^ j (r + 1)]`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:611–618`. -/
theorem card_range_cornerNear_le {j j' r g c : ℕ} (hj : j ≤ j' + 1) (hg : g ≤ c * 2 ^ j)
    (M : ℕ) : ((range M).filter fun u => CornerNear j r j' u g).card ≤ 4 * c + 4 :=
  (card_le_card fun u hu => by
    rw [mem_filter] at hu ⊢; exact ⟨hu.1, hu.2.blockNear⟩).trans
    (card_range_blockNear_le hj hg M)

/-! ### Two dimensions -/

private theorem card_fin_filter_le {M : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun r : Fin M => P r).card ≤ ((range M).filter P).card :=
  card_le_card_of_injOn (fun r : Fin M => (r : ℕ))
    (by intro r hr; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr
        simp [r.isLt, hr])
    (fun _ _ _ _ h => Fin.ext h)

/-- The scales `j' ≤ k` with `j' ∈ {j - 1, j}` number at most two. -/
private theorem card_scales_le (k j : ℕ) :
    (univ.filter fun j' : Fin (k + 1) => (j' : ℕ) ≤ j ∧ j ≤ j' + 1).card ≤ 2 := by
  refine (card_le_card_of_injOn (fun j' : Fin (k + 1) => (j' : ℕ)) (t := Icc (j - 1) j) ?_
    (fun _ _ _ _ h => Fin.ext h)).trans ?_
  · intro j' hj'
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj'
    simp only [coe_Icc, Set.mem_Icc]
    omega
  · rw [Nat.card_Icc]; omega

/-- A square of the hierarchy of `[0, 2 ^ k] ^ 2` is near the block of side `2 ^ j` with indices
`(r, s)`, at distance constant `c`, when its scale is `j` or `j - 1` and, in each coordinate, its
closed interval is within distance `c · 2 ^ j` of the block's.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “only at levels `m` and `m/2` … within
distance `O(m)` of its block”, `06-geometry.tex:615–618`. -/
def DyadicSquare.Near {k : ℕ} (j r s c : ℕ) (S : DyadicSquare k) : Prop :=
  (S.1 : ℕ) ≤ j ∧ j ≤ S.1 + 1 ∧ BlockNear j r S.1 S.2.1 (c * 2 ^ j) ∧
    BlockNear j s S.1 S.2.2 (c * 2 ^ j)

instance {k : ℕ} (j r s c : ℕ) : DecidablePred (DyadicSquare.Near (k := k) j r s c) := by
  intro S; unfold DyadicSquare.Near; infer_instance

/-- A junction of the hierarchy of `[0, 2 ^ k] ^ 2` is near the block of side `2 ^ j` with
indices `(r, s)`, at distance constant `c`, when its scale is `j` or `j - 1` and each of its
coordinates is within distance `c · 2 ^ j` of the block's closed interval.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:615–618`. -/
def DyadicJunction.Near {k : ℕ} (j r s c : ℕ) (P : DyadicJunction k) : Prop :=
  (P.1 : ℕ) ≤ j ∧ j ≤ P.1 + 1 ∧ CornerNear j r P.1 P.2.1 (c * 2 ^ j) ∧
    CornerNear j s P.1 P.2.2 (c * 2 ^ j)

instance {k : ℕ} (j r s c : ℕ) : DecidablePred (DyadicJunction.Near (k := k) j r s c) := by
  intro P; unfold DyadicJunction.Near; infer_instance

/-- Squares or junctions at scales `j' ∈ {j - 1, j}` whose two coordinates each satisfy a
condition met by at most `4 c + 4` indices number at most `2 (4 c + 4) ^ 2`. -/
private theorem card_sigma_near_le {k c j : ℕ} {m : ℕ → ℕ}
    (p q : ∀ j' : Fin (k + 1), Fin (m j') → Prop) [∀ j', DecidablePred (p j')]
    [∀ j', DecidablePred (q j')]
    (hp : ∀ j' : Fin (k + 1), j ≤ j' + 1 → (univ.filter (p j')).card ≤ 4 * c + 4)
    (hq : ∀ j' : Fin (k + 1), j ≤ j' + 1 → (univ.filter (q j')).card ≤ 4 * c + 4) :
    (univ.filter fun S : Σ j' : Fin (k + 1), Fin (m j') × Fin (m j') =>
      (S.1 : ℕ) ≤ j ∧ j ≤ S.1 + 1 ∧ p S.1 S.2.1 ∧ q S.1 S.2.2).card ≤ 2 * (4 * c + 4) ^ 2 := by
  set T := univ.filter fun j' : Fin (k + 1) => (j' : ℕ) ≤ j ∧ j ≤ j' + 1
  have hsub : (univ.filter fun S : Σ j' : Fin (k + 1), Fin (m j') × Fin (m j') =>
      (S.1 : ℕ) ≤ j ∧ j ≤ S.1 + 1 ∧ p S.1 S.2.1 ∧ q S.1 S.2.2) ⊆
      T.sigma fun j' => univ.filter (p j') ×ˢ univ.filter (q j') := by
    rintro ⟨j', a, b⟩ h
    simp only [mem_filter, mem_univ, true_and] at h
    simp [T, mem_sigma, h]
  refine (card_le_card hsub).trans ?_
  rw [card_sigma]
  calc ∑ j' ∈ T, (univ.filter (p j') ×ˢ univ.filter (q j')).card
      ≤ ∑ _j' ∈ T, (4 * c + 4) ^ 2 := by
        refine sum_le_sum fun j' hj' => ?_
        simp only [T, mem_filter, mem_univ, true_and] at hj'
        rw [card_product, sq]
        exact Nat.mul_le_mul (hp j' hj'.2) (hq j' hj'.2)
    _ = T.card * (4 * c + 4) ^ 2 := by rw [sum_const, smul_eq_mul]
    _ ≤ 2 * (4 * c + 4) ^ 2 := Nat.mul_le_mul_right _ (card_scales_le k j)

/-- **Near repaintings.** At most `2 (4 c + 4) ^ 2` squares of the hierarchy are near a block, at
every depth `k`: the repaintings at levels `m` and `m / 2` within distance `O(m)` of a block of
side `m` number at most a constant.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:615–618`. -/
theorem card_dyadicSquare_near_le (k j r s c : ℕ) :
    (univ.filter (DyadicSquare.Near (k := k) j r s c)).card ≤ 2 * (4 * c + 4) ^ 2 := by
  have h : ∀ (j' : Fin (k + 1)) (r : ℕ), j ≤ j' + 1 →
      (univ.filter fun r' : Fin (2 ^ (k - j')) => BlockNear j r j' r' (c * 2 ^ j)).card ≤
        4 * c + 4 := fun j' r hj =>
    (card_fin_filter_le _).trans (card_range_blockNear_le hj le_rfl _)
  exact card_sigma_near_le (m := fun j' => 2 ^ (k - j'))
    (fun j' r' => BlockNear j r j' r' (c * 2 ^ j)) (fun j' s' => BlockNear j s j' s' (c * 2 ^ j))
    (fun j' hj => h j' r hj) (fun j' hj => h j' s hj)

/-- **Near junction resizes.** At most `2 (4 c + 4) ^ 2` junctions of the hierarchy are near a
block, at every depth `k`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:615–618`. -/
theorem card_dyadicJunction_near_le (k j r s c : ℕ) :
    (univ.filter (DyadicJunction.Near (k := k) j r s c)).card ≤ 2 * (4 * c + 4) ^ 2 := by
  have h : ∀ (j' : Fin (k + 1)) (r : ℕ), j ≤ j' + 1 →
      (univ.filter fun u : Fin (2 ^ (k - j') + 1) => CornerNear j r j' u (c * 2 ^ j)).card ≤
        4 * c + 4 := fun j' r hj =>
    (card_fin_filter_le _).trans (card_range_cornerNear_le hj le_rfl _)
  exact card_sigma_near_le (m := fun j' => 2 ^ (k - j') + 1)
    (fun j' u => CornerNear j r j' u (c * 2 ^ j)) (fun j' v => CornerNear j s j' v (c * 2 ^ j))
    (fun j' hj => h j' r hj) (fun j' hj => h j' s hj)

/-! ### Lifetime participation -/

/-- **Bounded lifetime participation.** Let the gates `Γ` of a schedule on the hierarchy of
`[0, 2 ^ k] ^ 2` belong to repaintings and junction resizes, `ev γ`, with at most `G` gates for
each. If every gate in which a party participates belongs to a repainting or junction resize
near the block of side `2 ^ j` with indices `(r, s)`, at distance constant `c`, then the party
participates in at most `4 G (4 c + 4) ^ 2` gates. The bound depends only on `G` and `c`, not on
`k`, `j` or the block.

The hypothesis on the party, that it occurs in linked gates only at levels `2 ^ j` and
`2 ^ (j - 1)` within distance `O(2 ^ j)` of its block, is the conclusion the source draws from
the active-label invariant `eq:geometry-active-labels`; it is not proved here.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex:31–32`, and the lifetime argument, `06-geometry.tex:572–579, 611–618`. -/
theorem card_gates_le_of_near {k : ℕ} {Γ : Type*} [Fintype Γ]
    (ev : Γ → DyadicSquare k ⊕ DyadicJunction k) {G : ℕ}
    (hG : ∀ e, (univ.filter fun γ => ev γ = e).card ≤ G) (j r s c : ℕ) (P : Γ → Prop)
    [DecidablePred P]
    (hP : ∀ γ, P γ → Sum.elim (DyadicSquare.Near j r s c) (DyadicJunction.Near j r s c) (ev γ)) :
    (univ.filter P).card ≤ G * (4 * (4 * c + 4) ^ 2) := by
  set T := (univ.filter (DyadicSquare.Near (k := k) j r s c)).disjSum
    (univ.filter (DyadicJunction.Near (k := k) j r s c))
  have hT : T.card ≤ 4 * (4 * c + 4) ^ 2 := by
    rw [card_disjSum]
    have := card_dyadicSquare_near_le k j r s c
    have := card_dyadicJunction_near_le k j r s c
    omega
  have hmaps : ∀ γ ∈ univ.filter P, ev γ ∈ T := by
    intro γ hγ
    have h := hP γ (mem_filter.1 hγ).2
    rcases hev : ev γ with S | J <;> rw [hev] at h <;> simpa [T] using h
  refine (card_le_mul_card_image_of_maps_to hmaps G fun e _ => ?_).trans
    (Nat.mul_le_mul_left G hT)
  exact (card_le_card (monotone_filter_left _ (filter_subset _ _))).trans (hG e)

end TNLean.PEPS.Approximation
