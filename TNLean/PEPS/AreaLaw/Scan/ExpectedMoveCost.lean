/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.GoodSampling
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Expected nonnegative cost of actual charge moves

For each band, the splitting incidences are pairs of a side and an interaction
label. Equal anchors do not identify labels. A realized side-slot choice selects
at most one such incidence in that band, and its actual move is the selected
ball's old middle part. Summing these disjoint labelled events and then the bands
gives a lower bound for any nonnegative side-dependent cost of the actual moves.

The physical specialization derives the needed selected slots from good actual
histories, ambient clearance, row bounds, and anchor multiplicity. This is a
classical finite expectation inequality. Identifying its costs with transported
quantum entropy quantities is a separate step; no entropy sampling assertion is
proved here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 212–219 and 331–337, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- Side-label incidences that meet both the receiving side and the old middle.
Distinct labels remain distinct even when their anchors or balls coincide. -/
noncomputable def splitIncidences {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) : Finset (Bool × I) :=
  Finset.univ.filter fun p ↦
    (S.ball p.2 ∩ receiving (S.oldChargeState h g) p.1).Nonempty ∧
      (S.ball p.2 ∩ middle (S.oldChargeState h g)).Nonempty

@[simp]
theorem mem_splitIncidences {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (p : Bool × I) :
    p ∈ S.splitIncidences h g ↔
      (S.ball p.2 ∩ receiving (S.oldChargeState h g) p.1).Nonempty ∧
        (S.ball p.2 ∩ middle (S.oldChargeState h g)).Nonempty := by
  classical
  simp [splitIncidences]

/-- The side-dependent cost of the old middle sites actually moved by a charge. -/
noncomputable def chargeMoveCost {k : ℕ} (h : History S.K S.m S.M k)
    (cost : Fin S.K → Bool → Finset V → ℝ) (c : ChargeChoices S.K S.M) : ℝ :=
  ∑ g, cost g (c g).1 (middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g))

/-- The sum of costs over all splitting band-side-label incidences. No uniqueness
of a splitting band for a label is assumed. -/
noncomputable def splitIncidenceCost {k : ℕ} (h : History S.K S.m S.M k)
    (cost : Fin S.K → Bool → Finset V → ℝ) : ℝ :=
  ∑ g, ∑ p ∈ S.splitIncidences h g,
    cost g p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g))

private theorem selected_split_cost_le {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (cost : Bool → Finset V → ℝ) (hcost : ∀ side B, 0 ≤ cost side B)
    (c : ChargeChoices S.K S.M) :
    (∑ p ∈ S.splitIncidences h g,
      if (c g).1 = p.1 ∧ S.selected g (h.1 g) (k + 1) (c g) = some p.2
      then cost p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g)) else 0) ≤
      cost (c g).1 (middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g)) := by
  classical
  cases hs : S.selected g (h.1 g) (k + 1) (c g) with
  | none =>
    simpa using hcost (c g).1
      (middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g))
  | some i =>
    have heq (p : Bool × I) :
        ((c g).1 = p.1 ∧ i = p.2) ↔ p = ((c g).1, i) := by
      simp only [Prod.ext_iff]
      exact ⟨fun hp ↦ ⟨hp.1.symm, hp.2.symm⟩, fun hp ↦ ⟨hp.1.symm, hp.2.symm⟩⟩
    simp only [Option.some.injEq]
    simp_rw [heq]
    by_cases hi : ((c g).1, i) ∈ S.splitIncidences h g
    · have hsplit : (S.ball i ∩ receiving (S.oldChargeState h g) (c g).1).Nonempty ∧
          (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty :=
        (S.mem_splitIncidences h g ((c g).1, i)).mp hi
      have hmove : middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g) =
          S.ball i ∩ middle (S.oldChargeState h g) := by
        rw [S.state_extendHistory]
        exact S.chargeStep_moves_middle_part g (h.1 g) (k + 1) (c g)
          (S.oldChargeState h g) i hs hsplit
      simp only [Finset.sum_ite_eq', hi, ↓reduceIte, hmove, le_refl]
    · simpa only [Finset.sum_ite_eq', hi, ↓reduceIte] using
        hcost (c g).1 (middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g))

/-- Actual selected-slot availability implies the one-band expected move-cost
bound. The hypothesis concerns the scanner's labelled candidate list, not an
assumed probability or quantum sampling inequality. -/
theorem splitIncidenceCost_band_le_expected_chargeMoveCost {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (cost : Bool → Finset V → ℝ)
    (hcost : ∀ side B, 0 ≤ cost side B)
    (hslots : ∀ p ∈ S.splitIncidences h g, ∃ slot : Fin S.M,
      S.selected g (h.1 g) (k + 1) (p.1, slot) = some p.2) :
    (1 / (2 * (S.M : ℝ))) *
        (∑ p ∈ S.splitIncidences h g,
          cost p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g))) ≤
      ∑ c : ChargeChoices S.K S.M, chargeWeight c *
        cost (c g).1 (middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g)) := by
  classical
  have hevent (p : Bool × I) (hp : p ∈ S.splitIncidences h g) :
      (1 / (2 * (S.M : ℝ))) * cost p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g)) ≤
        ∑ c : ChargeChoices S.K S.M, chargeWeight c *
          (if (c g).1 = p.1 ∧ S.selected g (h.1 g) (k + 1) (c g) = some p.2
          then cost p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g)) else 0) := by
    obtain ⟨slot, hs⟩ := hslots p hp
    rw [← sum_chargeWeight_band (Nat.zero_lt_of_lt slot.isLt) g (p.1, slot),
      Finset.sum_mul]
    apply Finset.sum_le_sum
    intro c _
    by_cases hc : c g = (p.1, slot)
    · simp [hc, hs]
    · simp only [hc, ↓reduceIte, zero_mul]
      apply mul_nonneg (chargeWeight_nonneg c)
      split_ifs
      · exact hcost p.1 _
      · exact le_rfl
  calc
    _ = ∑ p ∈ S.splitIncidences h g,
        (1 / (2 * (S.M : ℝ))) * cost p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ S.splitIncidences h g, ∑ c : ChargeChoices S.K S.M, chargeWeight c *
        (if (c g).1 = p.1 ∧ S.selected g (h.1 g) (k + 1) (c g) = some p.2
        then cost p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g)) else 0) :=
      Finset.sum_le_sum hevent
    _ = ∑ c : ChargeChoices S.K S.M, chargeWeight c *
        (∑ p ∈ S.splitIncidences h g,
          if (c g).1 = p.1 ∧ S.selected g (h.1 g) (k + 1) (c g) = some p.2
          then cost p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g)) else 0) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun c _ ↦
      mul_le_mul_of_nonneg_left (S.selected_split_cost_le h g cost hcost c)
        (chargeWeight_nonneg c)

/-- Summing the disjoint incidence events within each band gives the expected
cost of the actual simultaneous charge. Distinct bands contribute additively. -/
theorem splitIncidenceCost_le_expected_chargeMoveCost {k : ℕ}
    (h : History S.K S.m S.M k) (cost : Fin S.K → Bool → Finset V → ℝ)
    (hcost : ∀ g side B, 0 ≤ cost g side B)
    (hslots : ∀ g, ∀ p ∈ S.splitIncidences h g, ∃ slot : Fin S.M,
      S.selected g (h.1 g) (k + 1) (p.1, slot) = some p.2) :
    (1 / (2 * (S.M : ℝ))) * S.splitIncidenceCost h cost ≤
      ∑ c : ChargeChoices S.K S.M, chargeWeight c * S.chargeMoveCost h cost c := by
  classical
  unfold splitIncidenceCost chargeMoveCost
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ g, ∑ c : ChargeChoices S.K S.M, chargeWeight c *
        cost g (c g).1 (middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g)) :=
      Finset.sum_le_sum fun g _ ↦
        S.splitIncidenceCost_band_le_expected_chargeMoveCost h g (cost g) (hcost g) (hslots g)
    _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]

/-- For a good actual history in the physical domain graph, every splitting
incidence contributes its old-middle cost with probability at least `c / (nD)`,
where `c = 1 / (2(C₁ + 1)) > 0`. The factor `2` is the independent uniform side
choice. Ambient geometry supplies all selected slots; no sampling certificate
is assumed (`08-scanner.tex`, lines 331–337). -/
theorem good_splitIncidenceCost_le_expected_chargeMoveCost_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (cost : Fin S.K → Bool → Finset (Site Λ) → ℝ)
    (hcost : ∀ g side B, 0 ≤ cost g side B)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hgood : S.IsGoodOldHistory h) :
    0 < 1 / (2 * (S.C₁ + 1)) ∧
      ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)) * S.splitIncidenceCost h cost ≤
        ∑ c : ChargeChoices S.K S.M, chargeWeight c * S.chargeMoveCost h cost c := by
  classical
  have hslots (g : Fin S.K) (p : Bool × I) (hp : p ∈ S.splitIncidences h g) :
      ∃ slot : Fin S.M, S.selected g (h.1 g) (k + 1) (p.1, slot) = some p.2 := by
    obtain ⟨slot, hs, _⟩ := good_split_sampling_domainGraph hT S hgraph hdepth h g p.1 p.2
      hn hm hk hr hD hDpos hL hC hrows hmult hclear hgood
      ((S.mem_splitIncidences h g p).mp hp)
    exact ⟨slot, hs.1⟩
  have hexact := S.splitIncidenceCost_le_expected_chargeMoveCost h cost hcost hslots
  have hCnonneg : 0 ≤ S.C₁ :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg μ)).trans hC
  refine ⟨by positivity, ?_⟩
  by_cases hI : Nonempty I
  · obtain ⟨i⟩ := hI
    have hμ : 1 ≤ μ :=
      (Finset.one_le_card.mpr ⟨i, by simp⟩).trans (hmult (S.anchor i))
    have hCpos : 0 < S.C₁ := by
      have hμreal : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
      linarith
    have hbound := (chargeSlotWeight_lower_bound hCpos (by omega : 1 ≤ S.n) hDpos).2
    have hsum : 0 ≤ S.splitIncidenceCost h cost :=
      Finset.sum_nonneg fun g _ ↦ Finset.sum_nonneg fun p _ ↦ hcost g p.1 _
    exact (mul_le_mul_of_nonneg_right hbound hsum).trans hexact
  · have hzero : S.splitIncidenceCost h cost = 0 := by
      apply Finset.sum_eq_zero
      intro g _
      apply Finset.sum_eq_zero
      intro p _
      exact (hI ⟨p.2⟩).elim
    simpa only [hzero, mul_zero] using hexact

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
