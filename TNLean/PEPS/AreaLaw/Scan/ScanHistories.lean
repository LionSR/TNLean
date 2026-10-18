/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadOldHistoryDecay
import TNLean.PEPS.AreaLaw.Scan.DesignatedDilution
import TNLean.PEPS.AreaLaw.Scan.PhysicalBandCommutation
import TNLean.PEPS.AreaLaw.Scan.SplitCounting
import TNLean.PEPS.AreaLaw.Scan.StatusCutBounds
import TNLean.PEPS.AreaLaw.Scan.AssignedLead
import TNLean.PEPS.AreaLaw.Scan.TerminalSplits

/-!
# Geometry and probabilities of the collar scan

This module states Lemma 9.1 (`scanner:histories`) of the area-law manuscript
for the actual finite collar scan. The structure `CollarScan.HistoryProperties`
lists the four assertions for one scanner, with explicit constants. The theorem
`eventually_historyProperties` proves them at the source scales
`L = ⌊n^(1-ℓ)⌋`, `m = ⌊n^μ⌋`, `K = ⌊L/(8m)⌋`, `D = ⌈n^κ⌉`, `r₀ = ⌈C_r log² n⌉`
and `M = ⌈C₁ n D⌉`, under the test geometry `scanner:test-geometry`, for all
sufficiently large `n`.

The threshold on `n` depends only on the exponents, the radius coefficient, the
padding constant, the target-size constant, the anchor multiplicity and the
inverse power. It is chosen before the finite domain, the cut, the target, the
interaction labels and the scanner.

The constants are explicit: prefix comparisons differ by at most `3nD` sites,
status cuts have at most `40nD` edges, at most `10bKnD` labelled terms split,
the split probability is at most `10D/m`, and a split term is sampled with
probability at least `c/(nD)` for `c = 1/(2(C₁+1))`. Here `b` bounds the number
of labels with a fixed anchor; the source's padding constant `C₁` is taken large
enough for every candidate list by requiring `3b ≤ C₁`.

All probabilities are classical path probabilities of the finite history tree.
No transported replica state enters these statements.

The proofs are independently written from the manuscript; no Lean declaration
or proof is copied or adapted from OpenAI's implementation.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 9.1, `08-scanner.tex`, lines 195–221 (statement) and 223–347 (proof),
at `openai/math@adc7f124`.
-/

open Filter TensorPower TensorPower.ReplicaTransport
open scoped BigOperators symmDiff
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

universe u

namespace CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

open Classical in
/-- The four assertions of Lemma 9.1 (`scanner:histories`, `08-scanner.tex`,
lines 195–221) for one actual collar scan with collar depth `L`, anchor
multiplicity `μ`, and inverse power `p` in the bad-history estimate. Completed
statuses after `k ≤ nm` fill–charge pairs and pre-charge statuses with
`k + 1 ≤ nm` are both covered. -/
structure HistoryProperties {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (L μ : ℕ) (p : ℝ) : Prop where
  /-- Item 1: a splitting designated support of a completed status is its graph
  `r₀`-ball, and this ball lies in `A`. -/
  support_eq_ball : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (i : I), S.designatedSplitIncidence (S.state h g) L i side →
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i ∧
        S.ball i ⊆ S.A
  /-- Item 1 for pre-charge statuses. -/
  old_support_eq_ball : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (i : I), S.designatedSplitIncidence (S.oldChargeState h g) L i side →
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i ∧
        S.ball i ⊆ S.A
  /-- Item 1: a support splits at most one band, on one side. -/
  split_unique : ∀ {k : ℕ} (h : History S.K S.m S.M k), k ≤ S.n * S.m →
    ∀ (g g' : Fin S.K) (side side' : Bool) (i : I),
      S.designatedSplitIncidence (S.state h g) L i side →
      S.designatedSplitIncidence (S.state h g') L i side' → g = g' ∧ side = side'
  /-- Item 1 for pre-charge statuses. -/
  old_split_unique : ∀ {k : ℕ} (h : History S.K S.m S.M k), k + 1 ≤ S.n * S.m →
    ∀ (g g' : Fin S.K) (side side' : Bool) (i : I),
      S.designatedSplitIncidence (S.oldChargeState h g) L i side →
      S.designatedSplitIncidence (S.oldChargeState h g') L i side' → g = g' ∧ side = side'
  /-- Item 1: in its band, a splitting support meets `Y` and exactly one side, and it
  lies in one part of every other band. -/
  terminal_split : ∀ {k : ℕ} (h : History S.K S.m S.M k), k ≤ S.n * S.m →
    ∀ (g : Fin S.K) (side : Bool) (i : I),
      S.designatedSplitIncidence (S.state h g) L i side →
      IsTerminalSplit (S.state h)
        (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) g side
  /-- Item 1 for pre-charge statuses. -/
  old_terminal_split : ∀ {k : ℕ} (h : History S.K S.m S.M k), k + 1 ≤ S.n * S.m →
    ∀ (g : Fin S.K) (side : Bool) (i : I),
      S.designatedSplitIncidence (S.oldChargeState h g) L i side →
      IsTerminalSplit (S.oldChargeState h)
        (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) g side
  /-- Item 1: the metrics of all statuses of distinct bands commute on the symmetric
  replica space, for arbitrary histories, times and completed or pre-charge
  statuses. -/
  band_commute : ∀ {k k' : ℕ} (h : History S.K S.m S.M k) (h' : History S.K S.m S.M k')
    (g g' : Fin S.K), g < g' → ∀ (preCharge preCharge' : Bool)
    (q : Site Λ ⊕ Bool → ℕ) [∀ v, NeZero (q v)] {t : ℝ}, 0 ≤ t → ∀ replicas : ℕ,
      Commute (symBandMetric q t replicas (S.quantumHistoryPartition h g preCharge))
        (symBandMetric q t replicas (S.quantumHistoryPartition h' g' preCharge'))
  /-- Item 2: every assigned site of `A` has oriented depth at most `j + D + r₀` on
  its side. -/
  assigned_lead : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (x : Site Λ), x ∈ S.A → S.state h g x = some side →
      orientedDepth S.depth side x ≤ S.front g (h.1 g) k side + S.D + S.r₀
  /-- Item 2 for pre-charge statuses. -/
  old_assigned_lead : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (x : Site Λ), x ∈ S.A → S.oldChargeState h g x = some side →
      orientedDepth S.depth side x ≤ S.front g (h.1 g) (k + 1) side + S.D + S.r₀
  /-- Item 2: `U` contains, and `UY` is contained in, a deterministic positive-depth
  prefix, and each differs from it by at most `3nD` sites. -/
  prefix_comparison : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K),
    k ≤ S.n * S.m →
    positiveDepthPrefix S.A S.depth (S.front g (h.1 g) k false - 1) ⊆
        positiveNear S.depth (S.state h g) ∧
      positiveNearMiddle S.depth (S.state h g) ⊆
        positiveDepthPrefix S.A S.depth (-S.front g (h.1 g) k true) ∧
      ((positiveNear S.depth (S.state h g)) ∆
        positiveDepthPrefix S.A S.depth (S.front g (h.1 g) k false - 1)).card ≤
          3 * S.n * S.D ∧
      ((positiveNearMiddle S.depth (S.state h g)) ∆
        positiveDepthPrefix S.A S.depth (-S.front g (h.1 g) k true)).card ≤
          3 * S.n * S.D
  /-- Item 2 for pre-charge statuses. -/
  old_prefix_comparison : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K),
    k + 1 ≤ S.n * S.m →
    positiveDepthPrefix S.A S.depth (S.front g (h.1 g) (k + 1) false - 1) ⊆
        positiveNear S.depth (S.oldChargeState h g) ∧
      positiveNearMiddle S.depth (S.oldChargeState h g) ⊆
        positiveDepthPrefix S.A S.depth (-S.front g (h.1 g) (k + 1) true) ∧
      ((positiveNear S.depth (S.oldChargeState h g)) ∆
        positiveDepthPrefix S.A S.depth (S.front g (h.1 g) (k + 1) false - 1)).card ≤
          3 * S.n * S.D ∧
      ((positiveNearMiddle S.depth (S.oldChargeState h g)) ∆
        positiveDepthPrefix S.A S.depth (-S.front g (h.1 g) (k + 1) true)).card ≤
          3 * S.n * S.D
  /-- Item 2: the cuts of `U`, `UY`, `Y`, `P₀` and `V` have at most `40nD` edges. -/
  cut_bounds : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K), k ≤ S.n * S.m →
    (edgeBoundary Λ (positiveNear S.depth (S.state h g))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ (positiveNearMiddle S.depth (S.state h g))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ (middle (S.state h g))).card ≤ 40 * S.n * S.D ∧
    (edgeBoundary Λ (receiving (S.state h g) false)).card ≤ 16 * S.n * S.D ∧
    (edgeBoundary Λ (receiving (S.state h g) true)).card ≤ 16 * S.n * S.D
  /-- Item 2 for pre-charge statuses. -/
  old_cut_bounds : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K),
    k + 1 ≤ S.n * S.m →
    (edgeBoundary Λ (positiveNear S.depth (S.oldChargeState h g))).card ≤ 20 * S.n * S.D ∧
    (edgeBoundary Λ (positiveNearMiddle S.depth (S.oldChargeState h g))).card ≤
      20 * S.n * S.D ∧
    (edgeBoundary Λ (middle (S.oldChargeState h g))).card ≤ 40 * S.n * S.D ∧
    (edgeBoundary Λ (receiving (S.oldChargeState h g) false)).card ≤ 16 * S.n * S.D ∧
    (edgeBoundary Λ (receiving (S.oldChargeState h g) true)).card ≤ 16 * S.n * S.D
  /-- Item 2: at most `10μKnD` labelled terms split, counted over bands and sides. -/
  split_count : ∀ {k : ℕ} (h : History S.K S.m S.M k), k ≤ S.n * S.m →
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦ S.designatedSplitIncidence (S.state h g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ
  /-- Item 2 for pre-charge statuses. -/
  old_split_count : ∀ {k : ℕ} (h : History S.K S.m S.M k), k + 1 ≤ S.n * S.m →
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦
        S.designatedSplitIncidence (S.oldChargeState h g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ
  /-- Item 3 at a charge round: for every label and every common parameter, the
  terminal-leaf probability of a split is at most `10D/m`. -/
  charge_dilution : ∀ (k : ℕ) (i : I) {q : ℝ}, 0 ≤ q → q ≤ 1 →
    (1 - q) * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) +
    q * (∑ h : History S.K S.m S.M (k + 1),
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m
  /-- Item 3 at a fill round. -/
  fill_dilution : ∀ (k : ℕ) (i : I) {q : ℝ}, 0 ≤ q → q ≤ 1 →
    (1 - q) * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) +
    q * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m
  /-- Item 4: the probability that a full history fails goodness at some time is at
  most `n^(-p)`. -/
  bad_history : (∑ h : History S.K S.m S.M (S.n * S.m),
    if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤ (S.n : ℝ) ^ (-p)
  /-- Item 4: at a charge round on a good old history, each split term is sampled on
  its splitting side, by a unique slot, with probability at least
  `1/(2(C₁+1)nD)`, and the sampled move is exactly the old `Y`-part of its designated support. -/
  good_sampling : ∀ {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool)
    (i : I), k + 1 ≤ S.n * S.m → S.IsGoodOldHistory h →
    S.designatedSplitIncidence (S.oldChargeState h g) L i side →
    ∃! slot : Fin S.M,
      S.selected g (h.1 g) (k + 1) (side, slot) = some i ∧
      (∀ c : ChargeChoices S.K S.M, c g = (side, slot) →
        middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g) =
          designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
            middle (S.oldChargeState h g)) ∧
      (∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0) =
        1 / (2 * (S.M : ℝ)) ∧
      0 < 1 / (2 * (S.C₁ + 1)) ∧
      (1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D) ≤
        ∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0

omit [Fintype I] [LinearOrder I] in
/-- A splitting graph ball lies in `A`, once its middle witness lies in the
compact collar. -/
private theorem ball_subset_of_middle {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {L : ℕ}
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (σ : PhysicalPartition (Site Λ)) (hsub : middle σ ⊆ S.truncationSet L) (i : I)
    (hsplit : (S.ball i ∩ middle σ).Nonempty) : S.ball i ⊆ S.A := by
  obtain ⟨y, hy⟩ := hsplit
  obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
  obtain ⟨hyA, hydepth⟩ := Finset.mem_filter.mp (hsub hym)
  have hb := domainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
    ⟨y, hyA, by simpa only [hdepth] using hydepth,
      by simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hyb⟩
  simpa only [ball, hgraph] using hb

/-- The middle of a completed status lies in the compact collar. -/
private theorem middle_state_subset_truncationSet {V : Type*} [Fintype V] [DecidableEq V]
    (S : CollarScan V I) {k L : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K)
    (hL : 8 * S.K * S.m ≤ L) : middle (S.state h g) ⊆ S.truncationSet L := by
  intro x hx
  have hn := (Finset.mem_filter.mp hx).2
  have hA := (initial_middle_depth S.A S.depth _ _
    (S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) x hn).1 false).1
  exact Finset.mem_filter.mpr ⟨hA, (Finset.mem_Icc.mp (S.state_depth_bounds h g hL x hn)).2⟩

open Classical in
/-- Lemma 9.1 for one scanner, from the finite scale inequalities that the source
scales satisfy for large `n` and from the bad-history bound `hbad`, which is the
first assertion of item 4 (`08-scanner.tex`, lines 195–347). -/
theorem historyProperties_of_scales {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {L μ : ℕ} {p : ℝ}
    (hn : 2 ≤ S.n) (hr : 2 * S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hC : 3 * (μ : ℝ) ≤ S.C₁) (hCpos : 0 < S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hbad : (∑ h : History S.K S.m S.M (S.n * S.m),
      if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤ (S.n : ℝ) ^ (-p)) :
    S.HistoryProperties L μ p := by
  have hn0 : 0 < S.n := by omega
  have hr0 : S.r₀ ≤ S.D := by omega
  have hD : 4 * S.D ≤ S.m := by omega
  have hm : 2 ≤ S.m := by omega
  have hm0 : 0 < S.m := by omega
  have hball_depth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀ :=
    fun i x hx ↦ abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT S hgraph hdepth i x hx
  refine
    { support_eq_ball := ?_
      old_support_eq_ball := ?_
      split_unique := fun h hk g g' side side' i hs hs' ↦
        state_designatedSplitIncidence_unique_domainGraph hT S hgraph hdepth h hn0 hk hr0
          hDpos hD hL hrows hclear g g' side side' i hs hs'
      old_split_unique := fun h hk g g' side side' i hs hs' ↦
        old_designatedSplitIncidence_unique_domainGraph hT S hgraph hdepth h hn0 hk hr0
          hDpos hD hL hrows hclear g g' side side' i hs hs'
      terminal_split := fun h hk g side i hs ↦
        state_designatedSplitIncidence_isTerminalSplit_domainGraph hT S hgraph hdepth h hn0
          hk hr0 hDpos hD hL hrows hclear g side i hs
      old_terminal_split := fun h hk g side i hs ↦
        old_designatedSplitIncidence_isTerminalSplit_domainGraph hT S hgraph hdepth h hn0
          hk hr0 hDpos hD hL hrows hclear g side i hs
      band_commute := fun h h' g g' hg preCharge preCharge' q _ _ ht replicas ↦
        S.commute_quantumHistoryPartition h h' g g' hg preCharge preCharge' q ht replicas
      assigned_lead := fun h g side x hxA hx ↦
        S.bandState_assigned_lead g (h.1 g) _ (fun t ↦ h.2 t g) hball_depth side x hxA hx
      old_assigned_lead := fun h g side x hxA hx ↦
        S.oldChargeState_assigned_lead h g hball_depth side x hxA hx
      prefix_comparison := fun h g hk ↦ by
        obtain ⟨h1, h2, -, -, h5, h6⟩ := state_prefix_approximation_domainGraph hT S hgraph
          hdepth h g hn0 hk hr0 hDpos hD hL hrows
        exact ⟨h1, h2, h5, h6⟩
      old_prefix_comparison := fun h g hk ↦ by
        obtain ⟨h1, h2, -, -, h5, h6⟩ := oldChargeState_prefix_approximation_domainGraph hT S
          hgraph hdepth h g hn0 hk hr0 hDpos hD hL hrows
        exact ⟨h1, h2, h5, h6⟩
      cut_bounds := fun h g hk ↦
        state_cut_bounds_domainGraph hT S hgraph hdepth h g hn0 hk hr0 hDpos hD hL hrows
          hclear
      old_cut_bounds := fun h g hk ↦
        oldChargeState_cut_bounds_domainGraph hT S hgraph hdepth h g hn0 hk hr0 hDpos hD hL
          hrows hclear
      split_count := fun h hk ↦
        sum_card_state_designatedSplitIncidence_le_domainGraph hT S hgraph hdepth h hn hm hk
          hr0 hDpos hmargin hL hrows hmult hclear
      old_split_count := fun h hk ↦
        sum_card_old_designatedSplitIncidence_le_domainGraph hT S hgraph hdepth h hn hm hk
          hr0 hDpos hmargin hL hrows hmult hclear
      charge_dilution := fun k i _ hq0 hq1 ↦
        designated_split_mixture_dilution_domainGraph (k := k) hT S hgraph hdepth i hn0 hm0
          hr0 hD hDpos hCpos hL hrows hclear hq0 hq1
      fill_dilution := fun k i _ hq0 hq1 ↦
        fill_split_mixture_dilution_domainGraph (k := k) hT S hgraph hdepth i hn0 hm0 hr0 hD
          hDpos hCpos hL hrows hclear hq0 hq1
      bad_history := hbad
      good_sampling := fun h g side i hk hgood hs ↦
        S.good_designated_split_sampling_domainGraph hT hgraph hdepth h g side i hn hm hk hr
          hD hDpos hL hC hrows hmult hclear hgood hs }
  · intro k h g side i hs
    have heq := S.designatedSupport_eq_ball_of_state_split h g side i hL hs
    refine ⟨heq, ball_subset_of_middle hT S hgraph hdepth hclear _
      (middle_state_subset_truncationSet S h g hL) i ?_⟩
    simpa only [heq] using hs.2
  · intro k h g side i hs
    have heq := S.designatedSupport_eq_ball_of_split h g side i hL hs
    refine ⟨heq, ball_subset_of_middle hT S hgraph hdepth hclear _
      (S.middle_subset_truncationSet h g hL) i ?_⟩
    simpa only [heq] using hs.2

end CollarScan

open Classical in
/-- **Lemma 9.1** (`scanner:histories`, `08-scanner.tex`, lines 195–221): under
the source scales `scanner:scales` and the test geometry `scanner:test-geometry`,
the actual collar scan has the four properties of `CollarScan.HistoryProperties`
for all sufficiently large `n`.

The exponents satisfy `0 < ℓ`, `0 < κ < μ < 1 - ℓ`; the radius is
`r₀ = ⌈C_r log² n⌉` with `C_r > 0`; the target satisfies `|T| ≤ C_T n²`, its
ambient layers `T_d \ T_{d-1}` have at most `n` sites for `1 ≤ d ≤ L`, and its
sup-norm distance to the endpoints of the cut edges exceeds `2L + 10r₀`. The
padding constant `C₁ > 0` with `3b ≤ C₁` is the source's uniform constant large
enough for every labelled candidate list, where `b` bounds the anchor
multiplicity. The threshold depends only on these fixed constants and on the
inverse power `p`. -/
theorem eventually_historyProperties {ell kappa mu Cr C1 Ct : ℝ} (hell : 0 < ell)
    (hkappa : 0 < kappa) (hkappamu : kappa < mu) (hmu : mu < 1 - ell) (hCr : 0 < Cr)
    (hC1 : 0 < C1) (hCt : 0 ≤ Ct) (b : ℕ) (hb : 3 * (b : ℝ) ≤ C1) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (I : Type u) [Fintype I] [LinearOrder I]
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan (Site Λ) I),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n → S.C₁ = C1 →
      (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - ell)⌋₊ + 10 * S.r₀ : ℕ) : ℤ) <
          ambientSupDistance t z) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ b) →
      S.HistoryProperties ⌊(n : ℝ) ^ (1 - ell)⌋₊ b p := by
  filter_upwards [eventually_bad_history_probability_le.{u} hell hkappa hkappamu hmu hCr
      hC1 hCt b p,
    eventually_split_counting_scale_separation (ell := ell) hCr.le hkappa hkappamu,
    eventually_const_mul_roundedLogRadius_le_rpow hCr.le hkappa 2]
    with n hbad hscale hr2
  intro I _ _ Λ T hT S hSn hm hK hD hR hC ht hgraph hdepth hrows hclear hmult
  dsimp only at hscale
  obtain ⟨hn, -, hDpos, hmargin, -⟩ := hscale
  have hM : S.M = ⌈C1 * n * S.D⌉₊ := by
    simp only [CollarScan.M, chargeSlotCount, hC, hSn]
  have hbad' := hbad I Λ T hT S hSn hm hK hD hR hM ht hgraph hdepth hclear hrows hmult
  subst hSn
  have hr : 2 * S.r₀ ≤ S.D := by
    have hceil : (S.n : ℝ) ^ kappa ≤ (⌈(S.n : ℝ) ^ kappa⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (2 * S.r₀ : ℝ) ≤ S.D := by
      rw [hR, hD]
      linarith
    exact_mod_cast h2
  have hKL : 8 * S.K * S.m ≤ ⌊(S.n : ℝ) ^ (1 - ell)⌋₊ := by
    rw [hK]
    exact eight_mul_bandCount_mul_le _ _
  exact S.historyProperties_of_scales hT hgraph hdepth hn hr (by rw [hD]; exact hDpos)
    (by rw [hD, hR, hm]; exact hmargin) hKL (by rw [hC]; exact hb) (by rw [hC]; exact hC1)
    hrows hmult hclear hbad'

end TNLean.PEPS.AreaLaw.Scan
