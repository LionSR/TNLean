/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SplitIntervals
import TNLean.PEPS.AreaLaw.Scan.OffsetDilution
import TNLean.PEPS.AreaLaw.Scan.DesignatedSampling

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
-/

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
theorem old_designated_split_dilution_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ} (i : I)
    (hn : 0 < S.n) (hm : 0 < S.m) (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hDpos : 1 ≤ S.D) (hC : 0 < S.C₁) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
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
    have hb : (S.ball i ∩ receiving (S.oldChargeState h g) side).Nonempty ∧
        (S.ball i ∩ middle (S.oldChargeState h g)).Nonempty := by
      simpa only [designatedSplitIncidence, heq] using hs
    have hi := old_split_anchor_bounds_domainGraph hT S hgraph hdepth
      h g side i hn hL hrows hclear hb
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hi
  · intro side g g' r r' hi hi'
    apply Fin.ext
    exact S.split_interval_band_unique hm (by omega) r.isLt r'.isLt side hi hi'

open Classical in
/-- Unconditional dilution for completed actual histories, hence for the new
leaves after a charge. No goodness or independence of splitting is assumed. -/
theorem state_designated_split_dilution_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ} (i : I)
    (hn : 0 < S.n) (hm : 0 < S.m) (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hDpos : 1 ≤ S.D) (hC : 0 < S.C₁) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
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
    have hb : (S.ball i ∩ receiving (S.state h g) side).Nonempty ∧
        (S.ball i ∩ middle (S.state h g)).Nonempty := by
      simpa only [designatedSplitIncidence, heq] using hs
    have hi := state_split_anchor_bounds_domainGraph hT S hgraph hdepth
      h g side i hn hL hrows hclear hb
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] using hi
  · intro side g g' r r' hi hi'
    apply Fin.ext
    exact S.split_interval_band_unique hm (by omega) r.isLt r'.isLt side hi hi'

open Classical in
/-- Old and new leaves with the same mixture parameter retain the same dilution
constant. This is the classical common-`p` mixture, before quantum transport. -/
theorem designated_split_mixture_dilution_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ} (i : I)
    (hn : 0 < S.n) (hm : 0 < S.m) (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hDpos : 1 ≤ S.D) (hC : 0 < S.C₁) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) +
    p * (∑ h : History S.K S.m S.M (k + 1),
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m := by
  have ho := old_designated_split_dilution_domainGraph hT S hgraph hdepth (k := k)
    i hn hm hr hD hDpos hC hL hrows hclear
  have hn' := state_designated_split_dilution_domainGraph hT S hgraph hdepth (k := k + 1)
    i hn hm hr hD hDpos hC hL hrows hclear
  have hpo := mul_le_mul_of_nonneg_left ho (sub_nonneg.mpr hp1)
  have hpn := mul_le_mul_of_nonneg_left hn' hp0
  nlinarith

open Classical in
/-- A deterministic fill round also preserves dilution under its common mixture
parameter: its old state is completed, and its new state is the next pre-charge state. -/
theorem fill_split_mixture_dilution_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ} (i : I)
    (hn : 0 < S.n) (hm : 0 < S.m) (hr : S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hDpos : 1 ≤ S.D) (hC : 0 < S.C₁) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.state h g) L i side
      then historyWeight h else 0) +
    p * (∑ h : History S.K S.m S.M k,
      if ∃ g side, S.designatedSplitIncidence (S.oldChargeState h g) L i side
      then historyWeight h else 0) ≤ 10 * (S.D : ℝ) / S.m := by
  have ho := state_designated_split_dilution_domainGraph hT S hgraph hdepth (k := k)
    i hn hm hr hD hDpos hC hL hrows hclear
  have hn' := old_designated_split_dilution_domainGraph hT S hgraph hdepth (k := k)
    i hn hm hr hD hDpos hC hL hrows hclear
  have hpo := mul_le_mul_of_nonneg_left ho (sub_nonneg.mpr hp1)
  have hpn := mul_le_mul_of_nonneg_left hn' hp0
  nlinarith

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
