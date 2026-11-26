/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scanner.Histories.SplitIntervals
import TNLean.PEPS.AreaLaw.Scanner.Histories.OffsetDilution
import TNLean.PEPS.AreaLaw.Scanner.Histories.DesignatedSampling
import TNLean.PEPS.AreaLaw.Scanner.Histories.BandMargins

/-!
# Dilution of actual designated split incidences

For every designated interaction label, the total classical history weight of
meeting the middle and a receiving side in some band is at most `10D/m`.
This holds separately before and after a charge and for their common convex
mixture. No good-history assumption or independence of the physical event is
used. The finite offset marginal and separated band centers give the bound.

This incidence event contains the manuscript's terminal split event, which
additionally requires exactly one receiving side and containment in one part
of every other band. It does not assert dilution for the entropy cut
`U = P₀ \\ X`, whose fixed inner boundary is not a terminal metric split.
Quantum state transport and the small bad-history probability remain separate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 274–284, and `06-transport.tex`, lines 336–352,
at `openai/math@adc7f124`.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.front_intervals_opposite_disjoint`,
  `TNLean.PEPS.AreaLaw.Scan.CollarScan.front_intervals_unique`: uniqueness of an actual splitting
  band and side.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_card_state_designatedSplitIncidence_le_planeDomainGraph`,
  `TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_card_old_designatedSplitIncidence_le_planeDomainGraph`:
  labelled split counts in actual collar histories.
-/

open ManyBody (designatedSupport)

section DesignatedDilution

open ManyBody (ambientDilation planeDomainGraph ambientDepth supDist)

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- A designated support's incidence with an actual receiving side and middle.
The source terminal split condition implies this event and has extra restrictions. -/
def designatedSplitIncidence (σ : PhysicalPartition V) (L : ℕ) (i : I) (side : Bool) : Prop :=
  (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩ receiving σ side).Nonempty ∧
    (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩ middle σ).Nonempty

/-- In a completed history, a designated support incident with the middle is
an actual base-radius ball, including the variable-radius truncation case. -/
theorem designatedSupport_eq_ball_of_state_split {k L : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hL : 8 * S.K * S.m ≤ L) (hsplit : S.designatedSplitIncidence (S.state h g) L i side) :
    designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i := by
  have hsub : middle (S.state h g) ⊆ S.truncationSet L := by
    intro x hx
    have hn := (Finset.mem_filter.mp hx).2
    have hA := (initial_middle_depth S.A S.depth _ _
      (S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) x hn).1 false).1
    exact Finset.mem_filter.mpr ⟨hA, (Finset.mem_Icc.mp (S.state_depth_bounds h g hL x hn)).2⟩
  exact S.designatedSupport_eq_ball_of_incidence _ side i hsub hsplit

private theorem dilution_constant {m D r₀ : ℕ} (hr : r₀ ≤ D) (hD : 1 ≤ D) :
    2 * (((r₀ : ℝ) + (D + 2 * r₀ : ℕ) + 1) / m) ≤ 10 * (D : ℝ) / m := by
  have hr' : (r₀ : ℝ) ≤ D := by exact_mod_cast hr
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  push_cast
  linarith

open Classical in
/-- Unconditional dilution for the old physical leaf distribution. The bounded
event is a superset of the actual terminal split condition. -/
theorem old_designated_split_dilution_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ} (i : I)
    (hn : 0 < S.n) (hm : 0 < S.m) (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hDpos : 1 ≤ S.D) (hC : 0 < S.C₁) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ)) :
    (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m := by
  have hM : 0 < S.M := chargeSlotCount_pos hC hn hDpos
  apply le_trans (S.sum_historyWeight_exists_band_side_le hm hM (k + 1)
    (fun side ↦ orientedDepth S.depth side (S.anchor i)) S.r₀ (S.D + 2 * S.r₀)
    (fun h g side ↦ S.designatedSplitIncidence (S.oldChargeState h g) L i side) ?_ ?_)
    (dilution_constant hr hDpos)
  · intro h g side hs
    have heq := S.designatedSupport_eq_ball_of_split h g side i hL hs
    have hi := old_split_anchor_bounds_planeDomainGraph hT S hgraph hdepth h g side i hn hL hrows
      hclear (by simpa only [designatedSplitIncidence, heq] using hs)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hi
  · exact fun side g g' r r' hi hi' ↦
      Fin.ext (S.split_interval_band_unique hm (by omega) r.isLt r'.isLt side hi hi')

open Classical in
/-- Unconditional dilution for completed actual histories, hence for the new
leaves after a charge. No goodness or independence of splitting is assumed. -/
theorem state_designated_split_dilution_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ} (i : I)
    (hn : 0 < S.n) (hm : 0 < S.m) (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hDpos : 1 ≤ S.D) (hC : 0 < S.C₁) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ)) :
    (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m := by
  have hM : 0 < S.M := chargeSlotCount_pos hC hn hDpos
  apply le_trans (S.sum_historyWeight_exists_band_side_le hm hM k
    (fun side ↦ orientedDepth S.depth side (S.anchor i)) S.r₀ (S.D + 2 * S.r₀)
    (fun h g side ↦ S.designatedSplitIncidence (S.state h g) L i side) ?_ ?_)
    (dilution_constant hr hDpos)
  · intro h g side hs
    have heq := S.designatedSupport_eq_ball_of_state_split h g side i hL hs
    have hi := state_split_anchor_bounds_planeDomainGraph hT S hgraph hdepth h g side i hn hL hrows
      hclear (by simpa only [designatedSplitIncidence, heq] using hs)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hi
  · exact fun side g g' r r' hi hi' ↦
      Fin.ext (S.split_interval_band_unique hm (by omega) r.isLt r'.isLt side hi hi')

open Classical in
/-- Old and new leaves with the same mixture parameter retain the same dilution
constant. This is the classical common-`p` mixture, before quantum transport. -/
theorem designated_split_mixture_dilution_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ} (i : I)
    (hn : 0 < S.n) (hm : 0 < S.m) (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hDpos : 1 ≤ S.D) (hC : 0 < S.C₁) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) +
    p * (∑ h : History S.K S.m S.M (k + 1),
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m := by
  have ho := old_designated_split_dilution_planeDomainGraph hT S hgraph hdepth (k := k)
    i hn hm hr hD hDpos hC hL hrows hclear
  have hn' := state_designated_split_dilution_planeDomainGraph hT S hgraph hdepth (k := k + 1)
    i hn hm hr hD hDpos hC hL hrows hclear
  have hpo := mul_le_mul_of_nonneg_left ho (sub_nonneg.mpr hp1)
  have hpn := mul_le_mul_of_nonneg_left hn' hp0
  nlinarith

open Classical in
/-- A deterministic fill round also preserves dilution under its common mixture
parameter: its old state is completed, and its new state is the next pre-charge state. -/
theorem fill_split_mixture_dilution_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ} (i : I)
    (hn : 0 < S.n) (hm : 0 < S.m) (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hDpos : 1 ≤ S.D) (hC : 0 < S.C₁) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) +
    p * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m := by
  have ho := state_designated_split_dilution_planeDomainGraph hT S hgraph hdepth (k := k)
    i hn hm hr hD hDpos hC hL hrows hclear
  have hn' := old_designated_split_dilution_planeDomainGraph hT S hgraph hdepth (k := k)
    i hn hm hr hD hDpos hC hL hrows hclear
  have hpo := mul_le_mul_of_nonneg_left ho (sub_nonneg.mpr hp1)
  have hpn := mul_le_mul_of_nonneg_left hn' hp0
  nlinarith

end CollarScan

end TNLean.PEPS.AreaLaw.Scan

end DesignatedDilution

section BandUniqueness

/-!
## Uniqueness of an actual splitting band and side

The two front intervals of one band and those of different bands are disjoint
throughout the prescribed `nm` fills. Therefore a labelled designated support
incident with a middle and a receiving side has a unique such band and side.
No goodness or independence of the split event is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(1), at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan
namespace CollarScan

variable {V I : Type*} (S : CollarScan V I)

/-- Oppositely oriented front intervals cannot contain the same physical depth
in any two bands, throughout the source horizon. -/
theorem front_intervals_opposite_disjoint {g g' r r' k : ℕ} {z : ℤ}
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) (hoff : r < S.m) (hoff' : r' < S.m)
    (hsame : g = g' → r = r')
    (hne : S.front g r k false - S.r₀ ≤ z ∧
      z ≤ S.front g r k false + S.D + 2 * S.r₀)
    (hfar : S.front g' r' k true - S.r₀ ≤ -z ∧
      -z ≤ S.front g' r' k true + S.D + 2 * S.r₀) : False := by
  have hnearShift := fillCount_div_le_window hn hk false
  have hfarShift := fillCount_div_le_window hn hk true
  have hn0 : (0 : ℤ) ≤ (fillCount k false / S.n : ℕ) := by positivity
  have hf0 : (0 : ℤ) ≤ (fillCount k true / S.n : ℕ) := by positivity
  have hn1 : ((fillCount k false / S.n : ℕ) : ℤ) ≤ S.m := by exact_mod_cast hnearShift
  have hf1 : ((fillCount k true / S.n : ℕ) : ℤ) ≤ S.m := by exact_mod_cast hfarShift
  have hm : (4 : ℤ) * S.D ≤ S.m := by exact_mod_cast hD
  have hdp : (1 : ℤ) ≤ S.D := by exact_mod_cast hDpos
  have hrad : (S.r₀ : ℤ) ≤ S.D := by exact_mod_cast hr
  have ho : (r : ℤ) < S.m := by exact_mod_cast hoff
  have ho' : (r' : ℤ) < S.m := by exact_mod_cast hoff'
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hr0' : (0 : ℤ) ≤ r' := by positivity
  simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hne hfar
  rcases lt_trichotomy g g' with hgg | hgg | hgg
  · have hgg' : (g : ℤ) + 1 ≤ g' := by exact_mod_cast hgg
    nlinarith
  · have hrr := hsame hgg
    subst g'; subst r'; omega
  · have hgg' : (g' : ℤ) + 1 ≤ g := by exact_mod_cast hgg
    nlinarith

/-- At one actual history's offsets, a physical depth belongs to at most one
band-side split interval during the prescribed horizon. -/
theorem front_intervals_unique {k : ℕ} (offset : Fin S.K → Fin S.m)
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (g g' : Fin S.K) (side side' : Bool) (z : ℤ)
    (h : S.front g (offset g) k side - S.r₀ ≤ (if side then -z else z) ∧
      (if side then -z else z) ≤ S.front g (offset g) k side + S.D + 2 * S.r₀)
    (h' : S.front g' (offset g') k side' - S.r₀ ≤ (if side' then -z else z) ∧
      (if side' then -z else z) ≤ S.front g' (offset g') k side' + S.D + 2 * S.r₀) :
    g = g' ∧ side = side' := by
  have hs (he : g.val = g'.val) : (offset g).val = (offset g').val := by
    have : g = g' := Fin.ext he
    simp [this]
  have hm : 0 < S.m := by omega
  cases side <;> cases side'
  · exact ⟨Fin.ext (S.split_interval_band_unique (k := k) (z := z) (a := S.r₀) (b := S.D + 2 * S.r₀)
      hm (by omega)
      (offset g).isLt (offset g').isLt false
      (by simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h)
      (by simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h')), rfl⟩
  · exact (S.front_intervals_opposite_disjoint hn hk hr hDpos hD
      (offset g).isLt (offset g').isLt hs h h').elim
  · have hs' (he : g'.val = g.val) : (offset g').val = (offset g).val :=
      (hs he.symm).symm
    exact (S.front_intervals_opposite_disjoint hn hk hr hDpos hD
      (offset g').isLt (offset g).isLt hs' h' h).elim
  · exact ⟨Fin.ext (S.split_interval_band_unique (k := k) (z := -z)
      (a := S.r₀) (b := S.D + 2 * S.r₀)
      hm (by omega)
      (offset g).isLt (offset g').isLt true
      (by simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h)
      (by simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h')), rfl⟩

end CollarScan
end TNLean.PEPS.AreaLaw.Scan

end BandUniqueness

section SplitCounting

/-!
## Labelled split counts in actual collar histories

Every split incidence has its labelled anchor in one of the two narrow front
intervals. Counting actual positive-depth rows and retaining anchor multiplicity
bounds the number of incidences by `10 K n D μ`, where `μ` bounds the number of
interaction labels per anchor. This bounds the source terminal split count as
well, without identifying repeated anchors or assuming goodness.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), at `openai/math@adc7f124`.
-/

open ManyBody (ambientDilation planeDomainGraph ambientDepth supDist)

namespace TNLean.PEPS.AreaLaw.Scan
namespace CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

open Classical in
omit [LinearOrder I] in
private theorem sum_card_incidence_le
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {t L μ : ℕ}
    (offset : Fin S.K → Fin S.m) (σ : Fin S.K → PhysicalPartition ↥Λ)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (ht : t ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hbound : ∀ g side i, S.designatedSplitIncidence (σ g) L i side →
      S.front g (offset g) t side - S.r₀ ≤ orientedDepth S.depth side (S.anchor i) ∧
      orientedDepth S.depth side (S.anchor i) ≤
        S.front g (offset g) t side + S.D + 2 * S.r₀) :
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦ S.designatedSplitIncidence (σ g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ := by
  have hper (g : Fin S.K) (side : Bool) :
      (Finset.univ.filter fun i ↦ S.designatedSplitIncidence (σ g) L i side).card ≤
        5 * S.D * S.n * μ := by
    let j := S.front g (offset g) t side
    have hsub : (Finset.univ.filter fun i ↦
        S.designatedSplitIncidence (σ g) L i side) ⊆
        chargeCandidates (orientedDepth S.depth side) S.anchor
          (j - S.r₀) (j + (S.D + 2 * S.r₀ : ℕ)) := by
      intro i hi
      have hs := (Finset.mem_filter.mp hi).2
      have hb := hbound g side i hs
      simpa only [mem_chargeCandidates, j, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        add_assoc] using hb
    have hcount := card_chargeCandidates_le (orientedDepth S.depth side) S.anchor
      (j - S.r₀) (j + (S.D + 2 * S.r₀ : ℕ)) S.n μ
      (fun d hd ↦ bandChargeInterval_row_bound S.depth hn hm g.isLt (offset g).isLt ht
        (show S.r₀ ≤ S.D + 2 * S.r₀ by omega) hmargin hL
        (fun d hd ↦ by simpa only [depthRow, Finset.length_toList] using
          depthRow_length_le_of_ambientRows hT hdepth hrows hd) side hd) hmult
    have hlen : (j + (S.D + 2 * S.r₀ : ℕ) - (j - S.r₀) + 1).toNat ≤ 5 * S.D := by
      push_cast
      omega
    exact (Finset.card_le_card hsub).trans
      (hcount.trans (Nat.mul_le_mul_right μ (Nat.mul_le_mul_right S.n hlen)))
  calc
    _ ≤ ∑ _g : Fin S.K, ∑ _side : Bool, 5 * S.D * S.n * μ := by
      exact Finset.sum_le_sum fun g _ ↦ Finset.sum_le_sum fun side _ ↦ hper g side
    _ = _ := by simp; ring

open Classical in
/-- The number of actual designated split incidences at all bands and both sides
is at most `10 K n D μ`. Multiplicity counts interaction labels, not anchor sites. -/
theorem sum_card_state_designatedSplitIncidence_le_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (hn : 2 ≤ S.n) (hm : 2 ≤ S.m)
    (hk : k ≤ S.n * S.m) (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ)) :
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦ S.designatedSplitIncidence (S.state h g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ := by
  apply sum_card_incidence_le hT S hdepth h.1 (S.state h) hn hm hk hr hDpos hmargin hL
    hrows hmult
  intro g side i hs
  have heq := S.designatedSupport_eq_ball_of_state_split h g side i hL hs
  exact state_split_anchor_bounds_planeDomainGraph hT S hgraph hdepth h g side i
    (by omega) hL hrows hclear
    (by simpa only [designatedSplitIncidence, heq] using hs)

open Classical in
/-- The number of actual designated split incidences at all bands and both sides
is at most `10 K n D μ`. Multiplicity counts interaction labels, not anchor sites. -/
theorem sum_card_old_designatedSplitIncidence_le_planeDomainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan ↥Λ I) (hgraph : S.graph = planeDomainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (hn : 2 ≤ S.n) (hm : 2 ≤ S.m)
    (hk : k + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ)) :
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦
        S.designatedSplitIncidence (S.oldChargeState h g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ := by
  apply sum_card_incidence_le hT S hdepth h.1 (S.oldChargeState h)
    hn hm hk hr hDpos hmargin hL
    hrows hmult
  intro g side i hs
  have heq := S.designatedSupport_eq_ball_of_split h g side i hL hs
  exact old_split_anchor_bounds_planeDomainGraph hT S hgraph hdepth h g side i
    (by omega) hL hrows hclear
    (by simpa only [designatedSplitIncidence, heq] using hs)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan

end SplitCounting
