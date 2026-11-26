/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scanner.Histories.ActualHistory
import TNLean.PEPS.AreaLaw.Scanner.Histories.BandMargins
import QICLean.ManyBody.Sites.Lattice.SupDistance
import TNLean.PEPS.AreaLaw.Collar.PhysicalPartition
import TNLean.PEPS.AreaLaw.Polygons.Squares.CellCounting

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

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Scan.planeDomainGraph_ball_subset_of_clearance`,
  `TNLean.PEPS.AreaLaw.Scan.depthRow_length_le_of_ambientRows`: localization of scan balls inside
  the fixed cut.
-/

section SupportLocalization

/-!
## Localization of scan balls inside the fixed cut

A graph ball of radius `r₀` meeting `A ∩ T_L` lies wholly in `A` when the
ambient target is separated from the physical cut endpoints by more than
`2L + 10r₀`. A path between two points of the ball has length at most `2r₀`;
if it leaves `A`, its first crossing produces an actual cut endpoint of
ambient depth at most `L + 2r₀`, contradicting that separation.

This proves the spatial localization step for actual graph balls. Identifying
a splitting truncated designated support with such a ball is a separate
accepted result, `truncationRadius_eq_of_mem_crossingTerms` in
`CrossingBudget`: its hypothesis requires that the crossed compact set lie
inside the truncation set. This module does not identify an arbitrary
truncated support with the fixed-radius ball used by a charge.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 43–48 and 225–233, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open ManyBody (ambientDilation planeDomainGraph abs_ambientDepth_sub_le_planeDomainGraph
  ambientDepth supDist exists_mem_ambientDepth_eq supDist_comm)

namespace TNLean.PEPS.AreaLaw.Scan

/-- A radius-`r₀` graph ball meeting `A ∩ T_L` cannot leave the fixed cut.
The clearance is stated on the actual ambient endpoints of physical cut edges,
exactly as in `scanner:test-geometry`. Source: `08-scanner.tex`, lines 225–233. -/
theorem planeDomainGraph_ball_subset_of_clearance (Λ T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (A : Finset ↥Λ) (L r₀ : ℕ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < (supDist t z : ℤ))
    {anchor : ↥Λ}
    (hmeet : ∃ y ∈ A, ambientDepth T hT y.val ≤ L ∧
      (planeDomainGraph Λ).edist anchor y ≤ (r₀ : ℕ∞)) :
    (Finset.univ.filter fun x ↦ (planeDomainGraph Λ).edist anchor x ≤ (r₀ : ℕ∞)) ⊆ A := by
  classical
  intro x hx
  obtain ⟨y, hyA, hydepth, hy⟩ := hmeet
  have hxball := (Finset.mem_filter.mp hx).2
  by_contra hxA
  have hyx : (planeDomainGraph Λ).edist y x ≤ ((2 * r₀ : ℕ) : ℕ∞) := by
    calc
      (planeDomainGraph Λ).edist y x ≤
          (planeDomainGraph Λ).edist y anchor + (planeDomainGraph Λ).edist anchor x :=
        SimpleGraph.edist_triangle
      _ ≤ (r₀ : ℕ∞) + r₀ :=
        add_le_add (by simpa only [SimpleGraph.edist_comm] using hy) hxball
      _ = ((2 * r₀ : ℕ) : ℕ∞) := by simp [two_mul]
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top (2 * r₀)) hyx)
  obtain ⟨u, w, -, -, hcut, p', hp'⟩ := ManyBody.exists_edgeBoundary_of_walk p hyA hxA
  have hyd : (planeDomainGraph Λ).edist y u ≤ ((2 * r₀ : ℕ) : ℕ∞) := by
    calc
      (planeDomainGraph Λ).edist y u ≤ p'.length := SimpleGraph.edist_le _
      _ ≤ p.length := by exact_mod_cast hp'
      _ = (planeDomainGraph Λ).edist y x := hp
      _ ≤ ((2 * r₀ : ℕ) : ℕ∞) := hyx
  have hvariation := abs_ambientDepth_sub_le_planeDomainGraph T hT hyd
  have hz : u.val ∈ Geometry.boundaryEndpoints Λ A := by
    refine Finset.mem_image.mpr ⟨u, ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨s(u, w), hcut, by simp⟩
  obtain ⟨t, ht, hmin⟩ := exists_mem_ambientDepth_eq T hT u.val
  have hseparate := hclear t ht u.val hz
  have hdeep : ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientDepth T hT u.val := by
    rw [hmin, supDist_comm]
    exact hseparate
  rw [abs_le] at hvariation
  omega

/-- Under the ambient row assumption, every physical depth row of index in `[1, L]` has at
most `n` sites. Source: `08-scanner.tex`, lines 43–48 and 83–87. -/
theorem depthRow_length_le_of_ambientRows {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    {depth : ↥Λ → ℤ} (hdepth : depth = fun x ↦ ambientDepth T hT x.val) {n L : ℕ}
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    {d : ℤ} (hd : d ∈ Finset.Icc (1 : ℤ) L) :
    (depthRow depth d).length ≤ n := by
  obtain ⟨h1, hL⟩ := Finset.mem_Icc.mp hd
  have hb := depthRow_ambientDepth_length_le_of_row_bound T hT
    (Subtype.val : ↥Λ → ℤ × ℤ) Subtype.val_injective hrows
    (show 1 ≤ d.toNat by omega) (show d.toNat ≤ L by omega)
  simpa only [← hdepth, Int.toNat_of_nonneg (show 0 ≤ d by omega)] using hb

end TNLean.PEPS.AreaLaw.Scan

end SupportLocalization

section GoodSampling

open ManyBody (ambientDilation planeDomainGraph abs_ambientDepth_sub_le_planeDomainGraph
  ambientDepth supDist)

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

omit [Fintype I] [LinearOrder I] in
/-- Within a charge ball in the induced physical graph, ambient depth differs
from its value at the anchor by at most the charge radius. -/
theorem abs_depth_sub_anchor_le_planeDomainGraph_of_mem_ball
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (i : I) (y : ↥Λ) (hy : y ∈ S.ball i) :
    |S.depth y - S.depth (S.anchor i)| ≤ S.r₀ := by
  have hball : (planeDomainGraph Λ).edist (S.anchor i) y ≤ (S.r₀ : ℕ∞) := by
    simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hy
  simpa only [hdepth, abs_sub_comm] using abs_ambientDepth_sub_le_planeDomainGraph T hT hball

omit [Fintype I] [LinearOrder I] in
/-- A charge ball in the induced physical graph that meets the cut `A` at depth at most `L`
lies wholly in `A`, under the clearance of the target from the cut endpoints.
Source: `08-scanner.tex`, lines 225–233. -/
theorem ball_subset_of_mem_ball_planeDomainGraph {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {L : ℕ}
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ))
    {i : I} {y : ↥Λ} (hyb : y ∈ S.ball i) (hyA : y ∈ S.A) (hyL : S.depth y ≤ L) :
    S.ball i ⊆ S.A := by
  have hb := planeDomainGraph_ball_subset_of_clearance Λ T hT S.A L S.r₀ hclear
    ⟨y, hyA, by simpa only [hdepth] using hyL,
      by simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hgraph] using hyb⟩
  simpa only [ball, hgraph] using hb

omit [Fintype I] [LinearOrder I] in
/-- A charge ball meeting the middle of a partition lies in `A`, once every middle site lies
in `A` at depth at most `L`. Source: `08-scanner.tex`, lines 225–233. -/
theorem ball_subset_of_middle_planeDomainGraph {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {L : ℕ}
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ))
    (σ : PhysicalPartition ↥Λ) (i : I)
    (hmiddle : ∀ x, σ x = none → x ∈ S.A ∧ S.depth x ≤ L)
    (hsplit : (S.ball i ∩ middle σ).Nonempty) : S.ball i ⊆ S.A := by
  obtain ⟨y, hy⟩ := hsplit
  obtain ⟨hyb, hym⟩ := Finset.mem_inter.mp hy
  obtain ⟨hyA, hyL⟩ := hmiddle y (Finset.mem_filter.mp hym).2
  exact ball_subset_of_mem_ball_planeDomainGraph hT S hgraph hdepth hclear hyb hyA hyL

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

/-- A charge ball meeting the actual old middle of a band lies in `A`.
Source: `08-scanner.tex`, lines 225–233. -/
theorem ball_subset_of_oldChargeState_middle_planeDomainGraph {Λ T : Finset (ℤ × ℤ)}
    (hT : T.Nonempty) (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ))
    (h : History S.K S.m S.M k) (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) (i : I)
    (hsplit : (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty) : S.ball i ⊆ S.A :=
  ball_subset_of_middle_planeDomainGraph hT S hgraph hdepth hclear _ i
    (fun x hx ↦ ⟨(initial_middle_depth S.A S.depth _ _
      (S.oldChargeState_initial_none h g x hx) false).1,
      (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL x hx)).2⟩) hsplit

/-- Good split balls in the induced physical graph are selected with the exact
side-slot probability, and their old middle part is the actual history extension's
move. Only the manuscript's ambient row bound is used for row padding; graph-ball
depth variation and containment in the chosen color follow from the physical
graph and the ambient clearance. -/
theorem good_split_sampling_planeDomainGraph {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ))
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
    simpa only [depthRow, Finset.length_toList] using
      depthRow_length_le_of_ambientRows hT hdepth hrows ht
  have hball := ball_subset_of_oldChargeState_middle_planeDomainGraph hT S hgraph hdepth hclear
    h g hL i hsplit.2
  have hanchor := S.good_split_anchor_bounds h g side i (by omega) hr hgood hball
    (fun x hx ↦ by
      simpa only [depthRow, Finset.length_toList] using
        hrow (S.depth x) (S.oldChargeState_depth_bounds h g hL x hx))
    (S.abs_depth_sub_anchor_le_planeDomainGraph_of_mem_ball hT hgraph hdepth i)
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

end GoodSampling
