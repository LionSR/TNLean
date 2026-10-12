/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.AreaLaw.Geometry.MixedDyadicSquares
import TNLean.PEPS.AreaLaw.Geometry.QuotientIntervals

/-!
# Mixed dyadic cells of an integer rectangle

A mixed cell meets both the rectangle and its complement. Its index lies
on one of the two endpoint columns or endpoint rows. Counting these four
lines gives a bound independent of the rectangle's aspect ratio.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, the boundary-line count in the proof of Proposition 9.5,
`08-scanner.tex`, lines 717–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Total side length of mixed cells of a native rectangle is bounded by
its four boundary lines. No aspect-ratio assumption is needed.
Source: the rectangle boundary-line count in `08-scanner.tex`, lines 717–729,
in the proof of Proposition 9.5 (`prop:small-box`). -/
theorem IntRect.card_mixedDyadicIndices_toFinset_le (Q : IntRect) (k : ℕ) :
    2 ^ k * (Geometry.mixedDyadicIndices Q.toFinset k).card ≤
      4 * Q.size + 8 * 2 ^ k := by
  let u : ℤ := 2 ^ k
  have hu : 0 < u := by dsimp [u]; positivity
  have hboundary : Geometry.mixedDyadicIndices Q.toFinset k ⊆
      ({Q.x₀ / u, Q.x₁ / u} : Finset ℤ).product (Finset.Icc (Q.y₀ / u) (Q.y₁ / u)) ∪
        (Finset.Icc (Q.x₀ / u) (Q.x₁ / u)).product {Q.y₀ / u, Q.y₁ / u} := by
    intro z hz
    obtain ⟨⟨p, hp, hpQ⟩, r, hr, hrQ⟩ :=
      (Geometry.mem_mixedDyadicIndices Q.toFinset k z).mp hz
    obtain ⟨hpx₀, hpx₁, hpy₀, hpy₁⟩ := IntRect.mem_toFinset.mp hpQ
    have hpidx : p.1 / u = z.1 ∧ p.2 / u = z.2 :=
      Prod.mk.inj ((Geometry.mem_latticeDyadicCell k z p).mp hp)
    have hridx : r.1 / u = z.1 ∧ r.2 / u = z.2 :=
      Prod.mk.inj ((Geometry.mem_latticeDyadicCell k z r).mp hr)
    have hbox : Q.x₀ / u ≤ z.1 ∧ z.1 ≤ Q.x₁ / u ∧
        Q.y₀ / u ≤ z.2 ∧ z.2 ≤ Q.y₁ / u := by
      rw [← hpidx.1, ← hpidx.2]
      exact ⟨Int.ediv_le_ediv hu hpx₀, Int.ediv_le_ediv hu hpx₁,
        Int.ediv_le_ediv hu hpy₀, Int.ediv_le_ediv hu hpy₁⟩
    have hout : r.1 < Q.x₀ ∨ Q.x₁ < r.1 ∨ r.2 < Q.y₀ ∨ Q.y₁ < r.2 := by
      have hnot := mt IntRect.mem_toFinset.mpr hrQ
      omega
    simp only [Finset.product_eq_sprod, Finset.mem_union, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]
    rcases hout with h | h | h | h
    all_goals have hd := Int.ediv_le_ediv hu (le_of_lt h)
    all_goals simp only [hridx] at hd
    all_goals omega
  have hcard := Finset.card_le_card hboundary
  have hunion := hcard.trans (Finset.card_union_le _ _)
  simp only [Finset.product_eq_sprod, Finset.card_product] at hunion
  have hcount : (Geometry.mixedDyadicIndices Q.toFinset k).card ≤
      2 * (Finset.Icc (Q.x₀ / u) (Q.x₁ / u)).card +
        2 * (Finset.Icc (Q.y₀ / u) (Q.y₁ / u)).card := by
    have hxp : ({Q.x₀ / u, Q.x₁ / u} : Finset ℤ).card ≤ 2 := Finset.card_le_two
    have hyp : ({Q.y₀ / u, Q.y₁ / u} : Finset ℤ).card ≤ 2 := Finset.card_le_two
    have hleft := Nat.mul_le_mul hxp
      (Nat.le_refl (Finset.Icc (Q.y₀ / u) (Q.y₁ / u)).card)
    have hright := Nat.mul_le_mul
      (Nat.le_refl (Finset.Icc (Q.x₀ / u) (Q.x₁ / u)).card) hyp
    have hsum := hunion.trans (Nat.add_le_add hleft hright)
    omega
  have hcountInt : ((Geometry.mixedDyadicIndices Q.toFinset k).card : ℤ) ≤
      2 * ((Finset.Icc (Q.x₀ / u) (Q.x₁ / u)).card : ℤ) +
        2 * ((Finset.Icc (Q.y₀ / u) (Q.y₁ / u)).card : ℤ) := by
    exact_mod_cast hcount
  have hm := mul_le_mul_of_nonneg_left hcountInt (le_of_lt hu)
  have hx := Geometry.quotient_interval_card Q.x₀ Q.x₁ u hu Q.hx
  have hy := Geometry.quotient_interval_card Q.y₀ Q.y₁ u hu Q.hy
  have hfinal : u * ((Geometry.mixedDyadicIndices Q.toFinset k).card : ℤ) ≤
      4 * (Q.size : ℤ) + 8 * u := by
    nlinarith only [hm, hx, hy, Q.width_le_size, Q.height_le_size]
  dsimp only [u] at hfinal
  exact_mod_cast hfinal

end TNLean.PEPS.AreaLaw
