/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolTerminalCoordinates
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Lengths and physical dimensions in the chain sweep

The completed blocks have length `20w`, and the final suffix has length in
`[60w,80w)`. The estimates concern the main registers. The auxiliary registers
retain their original labels and owners.

These are geometric intermediate results for the one-dimensional note,
Part II, `part2b_mps_protocol.tex`, Construction `con:sweep` and Proposition
`prop:sweep`, lines 329–396. They do not construct the band operations.

**Local fix (terminal auxiliary registers):** Physical dimensions count only
main registers. The correction is recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

/-- The final suffix consists of three full blocks and the Euclidean remainder.
Source: Part II, `prop:sweep`, proof, lines 373–375. -/
theorem terminal_length_eq (L w : ℕ) (hL : 3 * (20 * w) ≤ L) :
    L = stageCount L w * (20 * w) + 3 * (20 * w) + L % (20 * w) := by
  have hdiv := Nat.div_add_mod L (20 * w)
  by_cases hw : w = 0
  · subst w
    simp [stageCount]
  have ht : 0 < 20 * w := by omega
  have hthree : 3 ≤ L / (20 * w) := (Nat.le_div_iff_mul_le ht).2 hL
  have hn : L / (20 * w) = stageCount L w + 3 := by
    unfold stageCount
    omega
  rw [hn] at hdiv
  nlinarith

/-- The final block has between three and four block lengths.
Source: Part II, `prop:sweep`, proof, lines 373–375. -/
theorem terminal_length_bounds (L w : ℕ) (hw : 1 ≤ w)
    (hL : 3 * (20 * w) ≤ L) :
    3 * (20 * w) ≤ L - stageCount L w * (20 * w) ∧
      L - stageCount L w * (20 * w) < 4 * (20 * w) := by
  have h := terminal_length_eq L w hL
  have hr := Nat.mod_lt L (show 0 < 20 * w by omega)
  omega

/-- Before every actual stage there are at least four block lengths left.
Source: Part II, `con:sweep`, and `prop:sweep`, proof, lines 363–375. -/
theorem stage_right_margin (L w : ℕ) (hL : 3 * (20 * w) ≤ L)
    (k : Fin (stageCount L w)) :
    (k.val + 4) * (20 * w) ≤ L := by
  have h := terminal_length_eq L w hL
  have hk : k.val + 1 ≤ stageCount L w := k.isLt
  have hm := Nat.mul_le_mul_right (20 * w) hk
  nlinarith [Nat.zero_le (L % (20 * w))]

/-- A noninitial left band has the required eight-width completed-block margin.
Source: Part II, `prop:sweep`, proof, lines 368–372. -/
theorem stage_left_margin (w k : ℕ) (hk : 1 ≤ k) :
    8 * w ≤ k * (20 * w) := by
  have h := Nat.mul_le_mul_right (20 * w) hk
  nlinarith

private theorem mainOwner_inr_div_eq {L w : ℕ} {x : Fin L}
    {j : Fin (stageCount L w)} (h : mainOwner L w x = Sum.inr j) :
    x.val / (20 * w) = j.val := by
  unfold mainOwner at h
  split at h
  · exact congrArg Fin.val (Sum.inr.inj h)
  · contradiction

private theorem mainOwner_inl_mul_le {L w : ℕ} {x : Fin L}
    {j : Fin (stageCount L w + 1)} (h : mainOwner L w x = Sum.inl j) :
    stageCount L w * (20 * w) ≤ x.val := by
  unfold mainOwner at h
  split at h
  · contradiction
  · omega

/-- A completed party holds at most one block of main sites.
Source: Part II, `con:sweep`, lines 329–342. -/
theorem card_mainSites_inr_le (L w : ℕ) (hw : 1 ≤ w)
    (j : Fin (stageCount L w)) :
    Fintype.card (MainSites L w (Sum.inr j)) ≤ 20 * w := by
  let f : MainSites L w (Sum.inr j) → Fin (20 * w) :=
    fun x ↦ ⟨x.val.val % (20 * w), Nat.mod_lt _ (by omega)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hx := mainOwner_inr_div_eq x.property
    have hy := mainOwner_inr_div_eq y.property
    have hm : x.val.val % (20 * w) = y.val.val % (20 * w) := congrArg Fin.val hxy
    have hdx := Nat.div_add_mod x.val.val (20 * w)
    have hdy := Nat.div_add_mod y.val.val (20 * w)
    rw [hx] at hdx
    rw [hy] at hdy
    apply Subtype.ext
    apply Fin.ext
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- A remainder party holds at most the final suffix of main sites.
Source: Part II, `prop:sweep`, proof, lines 373–375. -/
theorem card_mainSites_inl_lt (L w : ℕ) (hw : 1 ≤ w)
    (hL : 3 * (20 * w) ≤ L) (j : Fin (stageCount L w + 1)) :
    Fintype.card (MainSites L w (Sum.inl j)) < 4 * (20 * w) := by
  let f : MainSites L w (Sum.inl j) → Fin (L - stageCount L w * (20 * w)) :=
    fun x ↦ ⟨x.val.val - stageCount L w * (20 * w), by
      have hm := mainOwner_inl_mul_le x.property
      have hx := x.val.isLt
      omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hx := mainOwner_inl_mul_le x.property
    have hy := mainOwner_inl_mul_le y.property
    have hm : x.val.val - stageCount L w * (20 * w) =
        y.val.val - stageCount L w * (20 * w) := congrArg Fin.val hxy
    apply Subtype.ext
    apply Fin.ext
    omega
  have hc : Fintype.card (MainSites L w (Sum.inl j)) ≤
      L - stageCount L w * (20 * w) := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact hc.trans_lt (terminal_length_bounds L w hw hL).2

/-- The conservative source bound on the total number of nonprivate operations
is at most the chain length. This is an arithmetic estimate; constructing and
counting the actual operations is separate.
Source: Part II, `prop:sweep`, item 2, lines 349–354. -/
theorem twenty_mul_stageCount_le (L w : ℕ) (hw : 1 ≤ w)
    (hL : 3 * (20 * w) ≤ L) : 20 * stageCount L w ≤ L := by
  have heq := terminal_length_eq L w hL
  have ht : 20 ≤ 20 * w := by omega
  have hm := Nat.mul_le_mul_left (stageCount L w) ht
  nlinarith [Nat.zero_le (L % (20 * w))]

/-- The specified party set satisfies the source party-count bound.
Source: Part II, `prop:sweep`, item 1, lines 349–351. -/
theorem card_party_le (L w : ℕ) (hw : 1 ≤ w)
    (hL : 3 * (20 * w) ≤ L) : Fintype.card (Party L w) ≤ 2 * L := by
  have h := twenty_mul_stageCount_le L w hw hL
  have hp : 1 ≤ L := by omega
  simp only [Party, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Every physical output has dimension at most `q^(80w)`.
This includes scalar physical factors at parties with no main sites.
Source: Part II, `prop:sweep`, item 3, lines 355–360. -/
theorem physicalDimension_le (L w q : ℕ) (hw : 1 ≤ w) (hq : 1 ≤ q)
    (hL : 3 * (20 * w) ≤ L) (p : Party L w) :
    physicalDimension L w q p ≤ q ^ (4 * (20 * w)) := by
  apply pow_le_pow_right' hq
  rcases p with j | j
  · exact (card_mainSites_inl_lt L w hw hL j).le
  · have h := card_mainSites_inr_le L w hw j
    omega

end TNLean.MPS.AreaLaw.ChainSweep
