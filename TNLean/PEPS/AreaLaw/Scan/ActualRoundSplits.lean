/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualScanMeasures
import TNLean.PEPS.AreaLaw.Scan.DesignatedDilution
import TNLean.PEPS.AreaLaw.Scan.SplitCounting
import TNLean.PEPS.AreaLaw.Scan.SupportClassification

/-!
# Split terms of the actual fill and charge rounds

A term splits at a leaf of an actual fill or charge round only when its designated
support meets the receiving side and the middle of some band. Consequently every leaf
has at most `10 K n D μ` split terms, and for every common interpolation parameter the
terminal probabilities on which a fixed term splits sum to at most `10 D / m`. These are
Lemma 9.1(2) and (3) for the rounds of the actual scan.

The designated supports of the energy terms are the truncated radius-`r₀` supports;
the energy operators themselves do not enter.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 9.1(2)–(3) (`scanner:histories`), `08-scanner.tex`, lines 195–221 and 416–440.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators
open Set
open TensorPower TensorPower.ReplicaTransport

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

open Classical in
/-- A filter set is no larger than the sum of the sizes of finitely many filter sets
whose union covers it. -/
theorem card_filter_le_sum_card {ι G B : Type*}
    [Fintype ι] [Fintype G] [Fintype B]
    (P : ι → Prop) (Q : G → B → ι → Prop)
    (hPQ : ∀ i, P i → ∃ g b, Q g b i) :
    (Finset.univ.filter P).card ≤ ∑ g, ∑ b, (Finset.univ.filter (Q g b)).card := by
  calc
    _ ≤ (Finset.univ.biUnion fun g ↦
        Finset.univ.biUnion fun b ↦ Finset.univ.filter (Q g b)).card :=
      Finset.card_le_card fun i hi ↦ by
        obtain ⟨g, b, hQ⟩ := hPQ i (Finset.mem_filter.mp hi).2
        exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩⟩⟩
    _ ≤ ∑ g, (Finset.univ.biUnion fun b ↦ Finset.univ.filter (Q g b)).card :=
      Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun g _ ↦ Finset.card_biUnion_le

namespace CollarScan

variable {I : Type} [Fintype I] [LinearOrder I]
variable {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
  (hm : 0 < S.m) (hM : 0 < S.M) {L : ℕ}
  (n : Site Λ ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (Site Λ ⊕ Bool) n I)
  (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

open Classical in
/-- At an old leaf of an actual charge round, a split term has a designated split
incidence with the old pre-charge partition of some band (`08-scanner.tex`, lines 431–437). -/
theorem actualChargeScanRound_splitOld_incidence
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    {s : ℕ} (hn : 0 < S.n) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {hist : History S.K S.m S.M s} {i : I}
    (hi : (S.actualChargeScanRound hm hM s n E a pre).splitOld i hist) :
    ∃ g side, S.designatedSplitIncidence (S.oldChargeState hist g) L i side := by
  change (⟨hist, none⟩ : Σ _ : History S.K S.m S.M s,
    Option (ChargeChoices S.K S.M)) ∈ (S.actualChargeData hm hM s).splitLeaves E i at hi
  obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hi).2
  change ¬ (augmentedPartition (S.oldChargeState hist g)).Contains (E.support i) at hg
  rw [hsupport] at hg
  rcases S.old_designatedSupport_classification_domainGraph hT hgraph hdepth hist
      hn hs hr hDpos hD hL hrows hclear g i with hc | ⟨side, ht⟩
  · exact (hg (augmentedPartition_contains_of_constant _ _ hc)).elim
  · exact ⟨g, side, ht.2.1, ht.1⟩

open Classical in
/-- At a new leaf of an actual charge round, a split term has a designated split
incidence with the completed partition after the charge (`06-transport.tex`,
lines 336–352). -/
theorem actualChargeScanRound_splitNew_incidence
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    {s : ℕ} (hn : 0 < S.n) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {hist : History S.K S.m S.M s} {c : ChargeChoices S.K S.M} {i : I}
    (hi : (S.actualChargeScanRound hm hM s n E a pre).splitNew i hist c) :
    ∃ g side, S.designatedSplitIncidence (S.state (extendHistory hist c) g) L i side := by
  change (⟨hist, some c⟩ : Σ _ : History S.K S.m S.M s,
    Option (ChargeChoices S.K S.M)) ∈ (S.actualChargeData hm hM s).splitLeaves E i at hi
  obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hi).2
  change ¬ ((S.chargeTransportData (historyMeanTree S.K S.m S.M hm hM s)
    (fun _ ↦ chargeChoiceTree S.K S.M hM)).new hist c g).Contains (E.support i) at hg
  rw [S.chargeTransportData_new, hsupport] at hg
  rcases S.state_designatedSupport_classification_domainGraph hT hgraph hdepth
      (extendHistory hist c) hn hs hr hDpos hD hL hrows hclear g i with hc | ⟨side, ht⟩
  · exact (hg (augmentedPartition_contains_of_constant _ _ hc)).elim
  · exact ⟨g, side, ht.2.1, ht.1⟩

open Classical in
/-- At an old leaf of an actual fill round, a split term has a designated split
incidence with the completed partition of some band. -/
theorem actualFillScanRound_splitOld_incidence
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    {s : ℕ} (hn : 0 < S.n) (hs : s ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {hist : History S.K S.m S.M s} {i : I}
    (hi : (S.actualFillScanRound hm hM s n E a pre).splitOld i hist) :
    ∃ g side, S.designatedSplitIncidence (S.state hist g) L i side := by
  change (⟨hist, none⟩ : Σ _ : History S.K S.m S.M s, Option Unit) ∈
    (S.actualFillData hm hM s).splitLeaves E i at hi
  obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hi).2
  change ¬ (augmentedPartition (S.state hist g)).Contains (E.support i) at hg
  rw [hsupport] at hg
  rcases S.state_designatedSupport_classification_domainGraph hT hgraph hdepth hist
      hn hs hr hDpos hD hL hrows hclear g i with hc | ⟨side, ht⟩
  · exact (hg (augmentedPartition_contains_of_constant _ _ hc)).elim
  · exact ⟨g, side, ht.2.1, ht.1⟩

open Classical in
/-- At a new leaf of an actual fill round, a split term has a designated split
incidence with the next pre-charge partition of some band. -/
theorem actualFillScanRound_splitNew_incidence
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    {s : ℕ} (hn : 0 < S.n) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {hist : History S.K S.m S.M s} {c : Unit} {i : I}
    (hi : (S.actualFillScanRound hm hM s n E a pre).splitNew i hist c) :
    ∃ g side, S.designatedSplitIncidence (S.oldChargeState hist g) L i side := by
  change (⟨hist, some c⟩ : Σ _ : History S.K S.m S.M s, Option Unit) ∈
    (S.actualFillData hm hM s).splitLeaves E i at hi
  obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hi).2
  change ¬ ((S.fillTransportData (historyMeanTree S.K S.m S.M hm hM s)).new hist c g).Contains
    (E.support i) at hg
  rw [S.fillTransportData_new, hsupport] at hg
  rcases S.old_designatedSupport_classification_domainGraph hT hgraph hdepth hist
      hn hs hr hDpos hD hL hrows hclear g i with hc | ⟨side, ht⟩
  · exact (hg (augmentedPartition_contains_of_constant _ _ hc)).elim
  · exact ⟨g, side, ht.2.1, ht.1⟩

open Classical in
/-- At most `10 K n D μ` terms split at an old leaf of an actual charge round, where `μ`
bounds the number of labels sharing an anchor (Lemma 9.1(2), `08-scanner.tex`, line 207). -/
theorem actualChargeScanRound_card_splitOld_le
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    {s μ : ℕ} (hn : 2 ≤ S.n) (hm2 : 2 ≤ S.m) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hist : History S.K S.m S.M s) :
    ((Finset.univ.filter fun i ↦
        (S.actualChargeScanRound hm hM s n E a pre).splitOld i hist).card : ℝ) ≤
      10 * S.K * S.n * S.D * μ := by
  exact_mod_cast (card_filter_le_sum_card _
    (fun g side i ↦ S.designatedSplitIncidence (S.oldChargeState hist g) L i side)
    (fun i hi ↦ S.actualChargeScanRound_splitOld_incidence hT hm hM n E a pre hgraph hdepth
      hsupport (by omega) hs hr hDpos (by omega) hL hrows hclear hi)).trans
    (S.sum_card_old_designatedSplitIncidence_le_domainGraph hT hgraph hdepth
      hist hn hm2 hs hr hDpos hmargin hL hrows hmult hclear)

open Classical in
/-- At most `10 K n D μ` terms split at a new leaf of an actual charge round
(Lemma 9.1(2), `08-scanner.tex`, line 207). -/
theorem actualChargeScanRound_card_splitNew_le
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    {s μ : ℕ} (hn : 2 ≤ S.n) (hm2 : 2 ≤ S.m) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hist : History S.K S.m S.M s) (c : ChargeChoices S.K S.M) :
    ((Finset.univ.filter fun i ↦
        (S.actualChargeScanRound hm hM s n E a pre).splitNew i hist c).card : ℝ) ≤
      10 * S.K * S.n * S.D * μ := by
  exact_mod_cast (card_filter_le_sum_card _
    (fun g side i ↦ S.designatedSplitIncidence (S.state (extendHistory hist c) g) L i side)
    (fun i hi ↦ S.actualChargeScanRound_splitNew_incidence hT hm hM n E a pre hgraph hdepth
      hsupport (by omega) hs hr hDpos (by omega) hL hrows hclear hi)).trans
    (S.sum_card_state_designatedSplitIncidence_le_domainGraph hT hgraph hdepth
      (extendHistory hist c) hn hm2 hs hr hDpos hmargin hL hrows hmult hclear)

open Classical in
/-- At most `10 K n D μ` terms split at an old leaf of an actual fill round
(Lemma 9.1(2), `08-scanner.tex`, line 207). -/
theorem actualFillScanRound_card_splitOld_le
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    {s μ : ℕ} (hn : 2 ≤ S.n) (hm2 : 2 ≤ S.m) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hist : History S.K S.m S.M s) :
    ((Finset.univ.filter fun i ↦
        (S.actualFillScanRound hm hM s n E a pre).splitOld i hist).card : ℝ) ≤
      10 * S.K * S.n * S.D * μ := by
  exact_mod_cast (card_filter_le_sum_card _
    (fun g side i ↦ S.designatedSplitIncidence (S.state hist g) L i side)
    (fun i hi ↦ S.actualFillScanRound_splitOld_incidence hT hm hM n E a pre hgraph hdepth
      hsupport (by omega) (by omega) hr hDpos (by omega) hL hrows hclear hi)).trans
    (S.sum_card_state_designatedSplitIncidence_le_domainGraph hT hgraph hdepth
      hist hn hm2 (by omega) hr hDpos hmargin hL hrows hmult hclear)

open Classical in
/-- At most `10 K n D μ` terms split at a new leaf of an actual fill round
(Lemma 9.1(2), `08-scanner.tex`, line 207). -/
theorem actualFillScanRound_card_splitNew_le
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    {s μ : ℕ} (hn : 2 ≤ S.n) (hm2 : 2 ≤ S.m) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hist : History S.K S.m S.M s) (c : Unit) :
    ((Finset.univ.filter fun i ↦
        (S.actualFillScanRound hm hM s n E a pre).splitNew i hist c).card : ℝ) ≤
      10 * S.K * S.n * S.D * μ := by
  exact_mod_cast (card_filter_le_sum_card _
    (fun g side i ↦ S.designatedSplitIncidence (S.oldChargeState hist g) L i side)
    (fun i hi ↦ S.actualFillScanRound_splitNew_incidence hT hm hM n E a pre hgraph hdepth
      hsupport (by omega) hs hr hDpos (by omega) hL hrows hclear hi)).trans
    (S.sum_card_old_designatedSplitIncidence_le_domainGraph hT hgraph hdepth
      hist hn hm2 hs hr hDpos hmargin hL hrows hmult hclear)

open Classical in
/-- For a common interpolation parameter, the terminal probabilities of an actual charge
round on which a fixed term splits sum to at most `10 D / m` (Lemma 9.1(3),
`08-scanner.tex`, lines 208–210). -/
theorem actualChargeScanRound_splitWeight_le
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    (hC : 0 < S.C₁) {s : ℕ} (hn : 0 < S.n) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (i : I) :
    (S.actualChargeScanRound hm hM s n E a pre).splitWeight p i ≤ 10 * (S.D : ℝ) / S.m := by
  let Rd := S.actualChargeScanRound hm hM s n E a pre
  let oldEvent := fun hist : History S.K S.m S.M s ↦
    ∃ g side, S.designatedSplitIncidence (S.oldChargeState hist g) L i side
  let newEvent := fun hist : History S.K S.m S.M (s + 1) ↦
    ∃ g side, S.designatedSplitIncidence (S.state hist g) L i side
  have hw (hist : Rd.H) : Rd.w hist = historyWeight hist :=
    historyMeanTree_weight S.K S.m S.M hm hM s hist
  have hc (hist : Rd.H) (c : Rd.Ch hist) : Rd.q hist c = chargeWeight c :=
    chargeChoiceTree_weight S.K S.M hM c
  have hold : (∑ hist, if Rd.splitOld i hist then (1 - p) * Rd.w hist else 0) ≤
      (1 - p) * ∑ hist, if oldEvent hist then historyWeight hist else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun hist _ ↦ ?_
    rw [hw]
    by_cases hi : Rd.splitOld i hist
    · simp only [hi, S.actualChargeScanRound_splitOld_incidence hT hm hM n E a pre hgraph
        hdepth hsupport hn hs hr hDpos hD hL hrows hclear hi, oldEvent, ↓reduceIte, le_refl]
    · simp only [hi, ↓reduceIte]
      exact mul_nonneg (sub_nonneg.mpr hp.2) (by
        split_ifs
        · exact historyWeight_nonneg hist
        · exact le_rfl)
  have hnew : (∑ hist, ∑ c,
      if Rd.splitNew i hist c then p * Rd.w hist * Rd.q hist c else 0) ≤
      p * ∑ hist, if newEvent hist then historyWeight hist else 0 := by
    have heq : (∑ hist : History S.K S.m S.M (s + 1),
        if newEvent hist then historyWeight hist else 0) =
        ∑ hist : History S.K S.m S.M s, ∑ c : ChargeChoices S.K S.M,
          if newEvent (extendHistory hist c) then historyWeight hist * chargeWeight c
          else 0 := by
      simpa only [mul_ite, _root_.mul_one, MulZeroClass.mul_zero] using
        sum_historyWeight_mul_eq_sum_extendHistory
          (fun hist ↦ if newEvent hist then (1 : ℝ) else 0)
    rw [heq, Finset.mul_sum]
    refine Finset.sum_le_sum fun hist _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ ↦ ?_
    rw [hw, hc]
    by_cases hi : Rd.splitNew i hist c
    · simp only [hi, S.actualChargeScanRound_splitNew_incidence hT hm hM n E a pre hgraph
        hdepth hsupport hn hs hr hDpos hD hL hrows hclear hi, newEvent, ↓reduceIte]
      exact le_of_eq (_root_.mul_assoc _ _ _)
    · simp only [hi, ↓reduceIte]
      exact mul_nonneg hp.1 (by
        split_ifs
        · exact mul_nonneg (historyWeight_nonneg hist) (chargeWeight_nonneg c)
        · exact le_rfl)
  exact (add_le_add hold hnew).trans
    (S.designated_split_mixture_dilution_domainGraph hT hgraph hdepth i
      hn hm hr hD hDpos hC hL hrows hclear hp.1 hp.2)

open Classical in
/-- For a common interpolation parameter, the terminal probabilities of an actual fill
round on which a fixed term splits sum to at most `10 D / m` (Lemma 9.1(3),
`08-scanner.tex`, lines 208–210). -/
theorem actualFillScanRound_splitWeight_le
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    (hC : 0 < S.C₁) {s : ℕ} (hn : 0 < S.n) (hs : s + 1 ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (i : I) :
    (S.actualFillScanRound hm hM s n E a pre).splitWeight p i ≤ 10 * (S.D : ℝ) / S.m := by
  let Rd := S.actualFillScanRound hm hM s n E a pre
  let oldEvent := fun hist : History S.K S.m S.M s ↦
    ∃ g side, S.designatedSplitIncidence (S.state hist g) L i side
  let newEvent := fun hist : History S.K S.m S.M s ↦
    ∃ g side, S.designatedSplitIncidence (S.oldChargeState hist g) L i side
  have hw (hist : Rd.H) : Rd.w hist = historyWeight hist :=
    historyMeanTree_weight S.K S.m S.M hm hM s hist
  have hold : (∑ hist, if Rd.splitOld i hist then (1 - p) * Rd.w hist else 0) ≤
      (1 - p) * ∑ hist, if oldEvent hist then historyWeight hist else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun hist _ ↦ ?_
    rw [hw]
    by_cases hi : Rd.splitOld i hist
    · simp only [hi, S.actualFillScanRound_splitOld_incidence hT hm hM n E a pre hgraph
        hdepth hsupport hn (by omega) hr hDpos hD hL hrows hclear hi, oldEvent, ↓reduceIte,
        le_refl]
    · simp only [hi, ↓reduceIte]
      exact mul_nonneg (sub_nonneg.mpr hp.2) (by
        split_ifs
        · exact historyWeight_nonneg hist
        · exact le_rfl)
  have hnew : (∑ hist, ∑ c,
      if Rd.splitNew i hist c then p * Rd.w hist * Rd.q hist c else 0) ≤
      p * ∑ hist, if newEvent hist then historyWeight hist else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun hist _ ↦ ?_
    change (∑ c : Unit, if Rd.splitNew i hist c then p * Rd.w hist * Rd.q hist c else 0) ≤ _
    rw [Fintype.sum_unique]
    change (if Rd.splitNew i hist () then p * Rd.w hist * 1 else 0) ≤ _
    rw [hw]
    by_cases hi : Rd.splitNew i hist ()
    · simp only [hi, S.actualFillScanRound_splitNew_incidence hT hm hM n E a pre hgraph
        hdepth hsupport hn hs hr hDpos hD hL hrows hclear hi, newEvent, ↓reduceIte,
        _root_.mul_one, le_refl]
    · simp only [hi, ↓reduceIte]
      exact mul_nonneg hp.1 (by
        split_ifs
        · exact historyWeight_nonneg hist
        · exact le_rfl)
  exact (add_le_add hold hnew).trans
    (S.fill_split_mixture_dilution_domainGraph hT hgraph hdepth i
      hn hm hr hD hDpos hC hL hrows hclear hp.1 hp.2)

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
