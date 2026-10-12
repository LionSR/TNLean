/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BandUniqueness

/-!
# Labelled split counts in actual collar histories

Every split incidence has its labelled anchor in one of the two narrow front
intervals. Counting actual positive-depth rows and retaining anchor multiplicity
bounds the number of incidences by `10 K n D μ`, where `μ` bounds the number of
interaction labels per anchor. This bounds the source terminal split count as
well, without identifying repeated anchors or assuming goodness.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(2), at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan
namespace CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
private theorem physical_row_bound {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    {L : ℕ} (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (d : ℤ) (hd : d ∈ Finset.Icc (1 : ℤ) L) :
    (Finset.univ.filter fun x ↦ S.depth x = d).card ≤ S.n := by
  have hdn : ((d.toNat : ℕ) : ℤ) = d := by have := Finset.mem_Icc.mp hd; omega
  have hb := depthRow_ambientDepth_length_le_of_row_bound T hT
    (Subtype.val : Site Λ → ℤ × ℤ) Subtype.val_injective hrows
    (show 1 ≤ d.toNat by have := Finset.mem_Icc.mp hd; omega)
    (show d.toNat ≤ L by have := Finset.mem_Icc.mp hd; omega)
  simpa only [depthRow, Finset.length_toList, hdn, hdepth] using hb

open Classical in
omit [LinearOrder I] in
private theorem sum_card_incidence_le
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {t L μ : ℕ}
    (offset : Fin S.K → Fin S.m) (σ : Fin S.K → PhysicalPartition (Site Λ))
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
        (physical_row_bound hT S hdepth hrows) side hd) hmult
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
theorem sum_card_state_designatedSplitIncidence_le_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (hn : 2 ≤ S.n) (hm : 2 ≤ S.m)
    (hk : k ≤ S.n * S.m) (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦ S.designatedSplitIncidence (S.state h g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ := by
  apply sum_card_incidence_le hT S hdepth h.1 (S.state h) hn hm hk hr hDpos hmargin hL
    hrows hmult
  intro g side i hs
  have heq := S.designatedSupport_eq_ball_of_state_split h g side i hL hs
  exact state_split_anchor_bounds_domainGraph hT S hgraph hdepth h g side i
    (by omega) hL hrows hclear
    (by simpa only [designatedSplitIncidence, heq] using hs)

open Classical in
/-- The number of actual designated split incidences at all bands and both sides
is at most `10 K n D μ`. Multiplicity counts interaction labels, not anchor sites. -/
theorem sum_card_old_designatedSplitIncidence_le_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (hn : 2 ≤ S.n) (hm : 2 ≤ S.m)
    (hk : k + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) :
    (∑ g : Fin S.K, ∑ side : Bool,
      (Finset.univ.filter fun i ↦
        S.designatedSplitIncidence (S.oldChargeState h g) L i side).card) ≤
      10 * S.K * S.n * S.D * μ := by
  apply sum_card_incidence_le hT S hdepth h.1 (S.oldChargeState h)
    hn hm hk hr hDpos hmargin hL
    hrows hmult
  intro g side i hs
  have heq := S.designatedSupport_eq_ball_of_split h g side i hL hs
  exact old_split_anchor_bounds_domainGraph hT S hgraph hdepth h g side i
    (by omega) hL hrows hclear
    (by simpa only [designatedSplitIncidence, heq] using hs)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
