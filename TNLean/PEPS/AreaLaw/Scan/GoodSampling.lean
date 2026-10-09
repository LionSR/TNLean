/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualHistory
import TNLean.PEPS.AreaLaw.Scan.SupportLocalization
import TNLean.PEPS.AreaLaw.Scan.BandMargins

/-!
# Good-history sampling by the actual scanner

A good old history bounds the oriented lead of every assigned site in the chosen
color. For a graph ball lying in that color and meeting both a side and the
middle, the actual completed-row invariant supplies its lower anchor bound.
Goodness supplies its upper bound. Thus its label occupies one unique padded
slot, and the independent side-and-slot event has exactly probability `1/(2M)`.
The resulting physical move is exactly the ball's old unassigned part.

The domain-graph specialization uses actual ambient target depth and ambient
layer cardinalities. No depth-variation or sampling certificate is assumed in
that specialization. These results establish good-history sampling, not the
probability of a bad history or the complete histories lemma.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 212–219 and 331–337, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- Goodness is the actual assigned-site lead bound. Doubling gives exactly the
real inequality `depth ≤ front + D/2`, without rounding the half-width. -/
def IsGoodOldHistory {k : ℕ} (h : History S.K S.m S.M k) : Prop :=
  ∀ (g : Fin S.K) (side : Bool) (x : V), x ∈ S.A →
    S.oldChargeState h g x = some side →
      2 * orientedDepth S.depth side x ≤ 2 * S.front g (h.1 g) (k + 1) side + S.D

/-- The lower anchor bound comes from completed actual fill rows; the upper bound
comes from an assigned site and goodness (`08-scanner.tex`, lines 331–334). -/
theorem good_split_anchor_bounds {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (side : Bool) (i : I) (hn : 0 < S.n) (hr : 2 * S.r₀ ≤ S.D)
    (hgood : S.IsGoodOldHistory h) (hball : S.ball i ⊆ S.A)
    (hrow : ∀ x, S.oldChargeState h g x = none →
      (depthRow S.depth (S.depth x)).length ≤ S.n)
    (hdepth : ∀ x ∈ S.ball i, |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hsplit : (S.ball i ∩ receiving (S.oldChargeState h g) side).Nonempty ∧
      (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty) :
    S.front g (h.1 g) (k + 1) side - S.r₀ ≤ orientedDepth S.depth side (S.anchor i) ∧
      orientedDepth S.depth side (S.anchor i) ≤ S.front g (h.1 g) (k + 1) side + S.D := by
  have hvariation (x : V) (hx : x ∈ S.ball i) :
      |orientedDepth S.depth side x - orientedDepth S.depth side (S.anchor i)| ≤ S.r₀ := by
    cases side <;>
      simpa only [orientedDepth, Bool.false_eq_true, ↓reduceIte, neg_sub_neg, abs_sub_comm]
        using hdepth x hx
  obtain ⟨x, hx⟩ := hsplit.2
  obtain ⟨y, hy⟩ := hsplit.1
  obtain ⟨hxb, hxm⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyb, hyr⟩ := Finset.mem_inter.mp hy
  have hxnone : S.oldChargeState h g x = none := (Finset.mem_filter.mp hxm).2
  have hysome : S.oldChargeState h g y = some side := (Finset.mem_filter.mp hyr).2
  have hrowx : (orientedRow S.depth side (orientedDepth S.depth side x)).length ≤ S.n := by
    cases side <;> simpa [orientedRow, orientedDepth] using hrow x hxnone
  have hfront := S.oldChargeState_front_le h g side x hn hrowx hxnone
  have hlead := hgood g side y (hball hyb) hysome
  have hxdepth := (abs_le.mp (hvariation x hxb))
  have hydepth := (abs_le.mp (hvariation y hyb))
  omega

/-- Actual band margins, physical row bounds, and bounded label multiplicity supply
the unique padded slot for every anchor in the sampling interval. -/
theorem existsUnique_selected_of_bounds {k L μ : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrow : ∀ t ∈ Finset.Icc (1 : ℤ) L,
      (Finset.univ.filter fun x ↦ S.depth x = t).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hanchor : S.front g (h.1 g) (k + 1) side - S.r₀ ≤
        orientedDepth S.depth side (S.anchor i) ∧
      orientedDepth S.depth side (S.anchor i) ≤ S.front g (h.1 g) (k + 1) side + S.D) :
    ∃! slot : Fin S.M, S.selected g (h.1 g) (k + 1) (side, slot) = some i := by
  apply existsUnique_orderedChargeSlot _ _ _ _ _ hanchor
  exact card_bandChargeCandidates_le_chargeSlotCount S.depth S.anchor hn hm g.isLt
    (h.1 g).isLt hk hr hD hDpos hL hC hrow hmult side

/-- Selecting the unique labelled slot has its exact product-law marginal and
moves precisely the old middle part (`08-scanner.tex`, lines 335–337). -/
theorem selected_split_sampling {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (side : Bool) (i : I) (slot : Fin S.M)
    (hn : 1 ≤ S.n) (hD : 1 ≤ S.D) (hC : 0 < S.C₁)
    (hselect : S.selected g (h.1 g) (k + 1) (side, slot) = some i)
    (hsplit : (S.ball i ∩ receiving (S.oldChargeState h g) side).Nonempty ∧
      (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty) :
    (∀ c : ChargeChoices S.K S.M, c g = (side, slot) →
      middle (S.oldChargeState h g) \
        middle (S.state (extendHistory h c) g) =
          S.ball i ∩ middle (S.oldChargeState h g)) ∧
    (∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0) =
      1 / (2 * (S.M : ℝ)) ∧
    0 < 1 / (2 * (S.C₁ + 1)) ∧
    (1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D) ≤
      ∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0 := by
  have hM : 0 < S.M := chargeSlotCount_pos hC hn hD
  have hprob := sum_chargeWeight_band hM g (side, slot)
  have hbound := chargeSlotWeight_lower_bound hC hn hD
  refine ⟨?_, hprob, hbound.1, ?_⟩
  · intro c hc
    rw [S.state_extendHistory, hc]
    exact S.chargeStep_moves_middle_part g (h.1 g) (k + 1) (side, slot)
      (S.oldChargeState h g) i hselect hsplit
  · rw [hprob]
    exact hbound.2

/-- Every site in the actual old middle has positive physical depth at most `L`.
The estimate follows from the original band cutoffs, even after arbitrary charges. -/
theorem oldChargeState_depth_bounds {k L : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) (x : V)
    (hx : S.oldChargeState h g x = none) : S.depth x ∈ Finset.Icc (1 : ℤ) L := by
  have hinit := S.oldChargeState_initial_none h g x hx
  have hlo := (initial_middle_depth S.A S.depth _ _ hinit false).2
  have hhi := (initial_middle_depth S.A S.depth _ _ hinit true).2
  have hoffset := (h.1 g).isLt
  have hupper : 8 * g.val * S.m + 5 * S.m + (h.1 g).val ≤ L := by
    calc
      _ ≤ 8 * g.val * S.m + 8 * S.m := by omega
      _ = 8 * (g.val + 1) * S.m := by ring
      _ ≤ 8 * S.K * S.m := Nat.mul_le_mul_right S.m (Nat.mul_le_mul_left 8 g.isLt)
      _ ≤ L := hL
  simp only [initialFront, orientedDepth, Bool.false_eq_true, ↓reduceIte, lower, upper] at *
  rw [Finset.mem_Icc]
  constructor <;> omega

/-- Good split balls in the induced physical graph are selected with the exact
side-slot probability, and their old middle part is the actual history extension's
move. Only the manuscript's ambient row bound is used for row padding; graph-ball
depth variation and containment in the chosen color follow from the physical
graph and the ambient clearance. -/
theorem good_split_sampling_domainGraph {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hgood : S.IsGoodOldHistory h)
    (hsplit : (S.ball i ∩ receiving (S.oldChargeState h g) side).Nonempty ∧
      (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty) :
    ∃! slot : Fin S.M,
      S.selected g (h.1 g) (k + 1) (side, slot) = some i ∧
      (∀ c : ChargeChoices S.K S.M, c g = (side, slot) →
        middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g) =
          S.ball i ∩ middle (S.oldChargeState h g)) ∧
      (∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0) =
        1 / (2 * (S.M : ℝ)) ∧
      0 < 1 / (2 * (S.C₁ + 1)) ∧
      (1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D) ≤
        ∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0 := by
  have hrow (t : ℤ) (ht : t ∈ Finset.Icc (1 : ℤ) L) :
      (Finset.univ.filter fun x ↦ S.depth x = t).card ≤ S.n := by
    have htnat : (t.toNat : ℤ) = t := by simp only [Finset.mem_Icc] at ht; omega
    have ht1 : 1 ≤ t.toNat := by simp only [Finset.mem_Icc] at ht; omega
    have htL : t.toNat ≤ L := by simp only [Finset.mem_Icc] at ht; omega
    have hb := depthRow_ambientDepth_length_le_of_row_bound T hT
      (Subtype.val : Site Λ → ℤ × ℤ) Subtype.val_injective hrows ht1 htL
    simpa only [depthRow, Finset.length_toList, htnat, hdepth] using hb
  have hball : S.ball i ⊆ S.A := by
    obtain ⟨y, hy⟩ := hsplit.2
    obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
    have hynone : S.oldChargeState h g y = none := (Finset.mem_filter.mp hym).2
    have hyA := (initial_middle_depth S.A S.depth _ _
      (S.oldChargeState_initial_none h g y hynone) false).1
    have hydepth := (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL y hynone)).2
    have hb := domainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
      ⟨y, hyA, by simpa only [hdepth] using hydepth,
        by simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hyb⟩
    simpa only [ball, hgraph] using hb
  have hanchor := S.good_split_anchor_bounds h g side i (by omega) hr hgood hball
    (fun x hx ↦ by
      simpa only [depthRow, Finset.length_toList] using
        hrow (S.depth x) (S.oldChargeState_depth_bounds h g hL x hx))
    (fun x hx ↦ by
      have hxgraph : (domainGraph Λ).edist (S.anchor i) x ≤ (S.r₀ : ℕ∞) := by
        simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hx
      simpa only [hdepth, abs_sub_comm] using abs_ambientDepth_sub_le_domainGraph T hT hxgraph)
    hsplit
  obtain ⟨slot, hs, hu⟩ := S.existsUnique_selected_of_bounds h g side i hn hm hk
    (by omega) hD hDpos hL hC hrow hmult hanchor
  have hμ : 1 ≤ μ := (Finset.one_le_card.mpr ⟨i, by simp⟩).trans (hmult (S.anchor i))
  have hCpos : 0 < S.C₁ := by
    have hμreal : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
    linarith
  exact ⟨slot, ⟨hs, S.selected_split_sampling h g side i slot (by omega) hDpos hCpos hs hsplit⟩,
    fun slot' hslot' ↦ hu slot' hslot'.1⟩

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
