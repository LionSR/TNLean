/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualScanMeasures
import TNLean.PEPS.AreaLaw.Scan.ChargeEnergyAccounting
import TNLean.PEPS.AreaLaw.Scan.SplitEntropyBound
import TNLean.PEPS.AreaLaw.Scan.SplitCounting
import TNLean.PEPS.AreaLaw.Scan.TransportDimension

/-!
# Actual charge energy from the literal entropy defect

The actual charge trees and their Fourier–coherent leaf measures satisfy the
energy Hölder estimate. Geometry supplies labelled split counts and unconditional
dilution. Physical-only support dimensions supply the entropy cap independently
of both auxiliary dimensions. The old and new measures each have mass one half,
derived for the same nonzero symmetric supplied vector.

The bound retains the classical bad-old-history probability, the interpolation
factors, and the literal charge defect. No positive band count or split capacity
is imposed, and no capacity is divided out. This is a supplied-vector one-round
estimate; it does not identify the physical prevector or construct the scanner.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 416–440 and 492–511, at `openai/math@adc7f124`.
-/

open scoped BigOperators Matrix
open MeasureTheory Set TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open Classical in
private theorem card_filter_le_sum_card {ι G B : Type*}
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

open Classical in
/-- The literal charge energy is controlled by its actual entropy defect and
classical bad-old mass. The split capacity and replica count may be zero. -/
theorem actualCharge_energyError_le_domainGraph
    {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ} [NeZero q]
    [LinearOrder (AdmissibleSupport Λ R)]
    (hT : T.Nonempty) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
    {s L μ : ℕ} (hn : 2 ≤ S.n) (hs : s + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L) (hC : 0 < S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : (r : ℕ) → Config r
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ)
    (hsym : pre k ∈ symmetricSubspace k
      (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)))
    (hpre : pre k ≠ 0) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let hm : 0 < S.m := by omega
    let hM : 0 < S.M := chargeSlotCount_pos hC (by omega) hDpos
    let n := augmentedDimensions (V := Site Λ) q aux
    let E := S.actualEnergyTerms h Ω Δ L aux
    let A : ℝ := 10 * S.K * S.n * S.D * μ
    let ℓ := transportLogDimBound q S.r₀
    let b := ∑ hist : History S.K S.m S.M s,
      if S.IsGoodOldHistory hist then 0 else historyWeight hist
    (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
      (10 * (S.D : ℝ) / S.m) *
        ((1 - p) * A ^ (7 / 8 : ℝ) *
          (S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) p) ^ (1 / 8 : ℝ) +
          A * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 * ((1 - p) * b + p)) := by
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hC (by omega) hDpos
  let n := augmentedDimensions (V := Site Λ) q aux
  let E := S.actualEnergyTerms h Ω Δ L aux
  let D := S.actualChargeData hm hM s
  let Rd := S.actualChargeScanRound hm hM s n E a pre
  let A : ℝ := 10 * S.K * S.n * S.D * μ
  let ℓ := transportLogDimBound q S.r₀
  have hD : 4 * S.D ≤ S.m := by omega
  have hm2 : 2 ≤ S.m := by omega
  have hq : 1 ≤ q := NeZero.pos q
  have hℓ : 0 ≤ ℓ := (zero_le_one.trans (one_le_transportLogDimBound hq S.r₀))
  have hA : 0 ≤ A := by positivity
  have hp' : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have hcompat : D.SupportCompatible E :=
    S.chargeTransportData_supportCompatible_domainGraph hT hgraph hdepth
      (historyMeanTree S.K S.m S.M hm hM s) (fun _ ↦ chargeChoiceTree S.K S.M hM)
      (by omega) hs hr hDpos hD hL hrows hclear n E (fun _ ↦ rfl)
  have hsupp : ∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ :=
    S.chargeTransportData_logDim_support_le_domainGraph hgraph
      (historyMeanTree S.K S.m S.M hm hM s) (fun _ ↦ chargeChoiceTree S.K S.M hM)
      n hq (fun _ ↦ rfl) hL E (fun _ ↦ rfl)
  have hadm : D.IsAdmissible := S.actualChargeData_isAdmissible hm hM s
  have hOldSplit (hist : History S.K S.m S.M s) (i : AdmissibleSupport Λ R)
      (hi : Rd.splitOld i hist) :
      ∃ g side, S.designatedSplitIncidence (S.oldChargeState hist g) L i side := by
    change (⟨hist, none⟩ : Σ _ : History S.K S.m S.M s,
      Option (ChargeChoices S.K S.M)) ∈ D.splitLeaves E i at hi
    obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hi).2
    change ¬ (augmentedPartition (S.oldChargeState hist g)).Contains
      ((designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩) at hg
    rcases S.old_designatedSupport_classification_domainGraph hT hgraph hdepth hist
      (by omega) hs hr hDpos hD hL hrows hclear g i with hc | ⟨side, ht⟩
    · exact (hg (augmentedPartition_contains_of_constant _ _ hc)).elim
    · exact ⟨g, side, ht.2.1, ht.1⟩
  have hNewSplit (hist : History S.K S.m S.M s) (c : ChargeChoices S.K S.M)
      (i : AdmissibleSupport Λ R) (hi : Rd.splitNew i hist c) :
      ∃ g side, S.designatedSplitIncidence (S.state (extendHistory hist c) g) L i side := by
    change (⟨hist, some c⟩ : Σ _ : History S.K S.m S.M s,
      Option (ChargeChoices S.K S.M)) ∈ D.splitLeaves E i at hi
    obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hi).2
    change ¬ ((S.chargeTransportData (historyMeanTree S.K S.m S.M hm hM s)
      (fun _ ↦ chargeChoiceTree S.K S.M hM)).new hist c g).Contains (E.support i) at hg
    rw [S.chargeTransportData_new] at hg
    rcases S.state_designatedSupport_classification_domainGraph hT hgraph hdepth
      (extendHistory hist c) (by omega) hs hr hDpos hD hL hrows hclear g i with hc | ⟨side, ht⟩
    · exact (hg (augmentedPartition_contains_of_constant _ _ hc)).elim
    · exact ⟨g, side, ht.2.1, ht.1⟩
  have hcardOld (hist : Rd.H) :
      ((Finset.univ.filter fun i ↦ Rd.splitOld i hist).card : ℝ) ≤ A := by
    have hc := (card_filter_le_sum_card (fun i ↦ Rd.splitOld i hist)
      (fun g side i ↦ S.designatedSplitIncidence (S.oldChargeState hist g) L i side)
      (hOldSplit hist)).trans
      (S.sum_card_old_designatedSplitIncidence_le_domainGraph hT hgraph hdepth
        hist hn hm2 hs hr hDpos hmargin hL hrows hmult hclear)
    dsimp only [A]
    exact_mod_cast hc
  have hcardNew (hist : Rd.H) (c : Rd.Ch hist) :
      ((Finset.univ.filter fun i ↦ Rd.splitNew i hist c).card : ℝ) ≤ A := by
    have hc := (card_filter_le_sum_card (fun i ↦ Rd.splitNew i hist c)
      (fun g side i ↦ S.designatedSplitIncidence (S.state (extendHistory hist c) g) L i side)
      (hNewSplit hist c)).trans
      (S.sum_card_state_designatedSplitIncidence_le_domainGraph hT hgraph hdepth
        (extendHistory hist c) hn hm2 hs hr hDpos hmargin hL hrows hmult hclear)
    dsimp only [A]
    exact_mod_cast hc
  have hw (hist : Rd.H) : Rd.w hist = historyWeight hist :=
    historyMeanTree_weight S.K S.m S.M hm hM s hist
  have hc (hist : Rd.H) (c : Rd.Ch hist) : Rd.q hist c = chargeWeight c :=
    chargeChoiceTree_weight S.K S.M hM c
  have hsplit (i : AdmissibleSupport Λ R) : Rd.splitWeight p i ≤ 10 * (S.D : ℝ) / S.m := by
    let oldEvent := fun hist : History S.K S.m S.M s ↦
      ∃ g side, S.designatedSplitIncidence (S.oldChargeState hist g) L i side
    let newEvent := fun hist : History S.K S.m S.M (s + 1) ↦
      ∃ g side, S.designatedSplitIncidence (S.state hist g) L i side
    have hold : (∑ hist, if Rd.splitOld i hist then (1 - p) * Rd.w hist else 0) ≤
        (1 - p) * ∑ hist, if oldEvent hist then historyWeight hist else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro hist _
      rw [hw]
      by_cases hi : Rd.splitOld i hist
      · simp only [hi, hOldSplit hist i hi, oldEvent, ↓reduceIte]
        exact le_rfl
      · simp only [hi, ↓reduceIte]
        exact mul_nonneg (sub_nonneg.mpr hp.2.le) (by
          split_ifs
          · exact historyWeight_nonneg hist
          · exact le_rfl)
    have hnew : (∑ hist, ∑ c,
        if Rd.splitNew i hist c then p * Rd.w hist * Rd.q hist c else 0) ≤
        p * ∑ hist, if newEvent hist then historyWeight hist else 0 := by
      have heq : (∑ hist : History S.K S.m S.M (s + 1),
          if newEvent hist then historyWeight hist else 0) =
          ∑ hist : History S.K S.m S.M s, ∑ c : ChargeChoices S.K S.M,
            if newEvent (extendHistory hist c) then historyWeight hist * chargeWeight c else 0 := by
        simpa only [mul_ite, _root_.mul_one, MulZeroClass.mul_zero] using
          sum_historyWeight_mul_eq_sum_extendHistory
            (fun hist ↦ if newEvent hist then (1 : ℝ) else 0)
      rw [heq, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro hist _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c _
      rw [hw, hc]
      by_cases hi : Rd.splitNew i hist c
      · simp only [hi, hNewSplit hist c i hi, newEvent, ↓reduceIte]
        exact le_of_eq (_root_.mul_assoc _ _ _)
      · simp only [hi, ↓reduceIte]
        exact mul_nonneg hp.1.le (by
          split_ifs
          · exact mul_nonneg (historyWeight_nonneg hist) (chargeWeight_nonneg c)
          · exact le_rfl)
    exact (add_le_add hold hnew).trans
      (S.designated_split_mixture_dilution_domainGraph hT hgraph hdepth i
        (by omega) hm hr hD hDpos hC hL hrows hclear hp.1.le hp.2.le)
  have hη0 (i : AdmissibleSupport Λ R)
      (j : Σ _ : History S.K S.m S.M s, Option (ChargeChoices S.K S.M))
      (θ : CoherentSphere (SiteConfig n)) : 0 ≤ D.splitEta E i j θ.1 :=
    D.splitEta_nonneg n E hadm i j θ.1
  have hηB (i : AdmissibleSupport Λ R)
      (j : Σ _ : History S.K S.m S.M s, Option (ChargeChoices S.K S.M))
      (θ : CoherentSphere (SiteConfig n)) : D.splitEta E i j θ.1 ≤ 2 * ℓ :=
    D.splitEta_le_two_mul_of_logDim_le n E hadm hcompat hℓ hsupp i j θ
  letI : ∀ hist : Rd.H, IsFiniteMeasure (Rd.μOld k p hist) := fun hist ↦
    D.isFiniteMeasure_transportLeafMeasure n (a / 2) k (pre k) p ⟨hist, none⟩
  letI : ∀ (hist : Rd.H) (c : Rd.Ch hist), IsFiniteMeasure (Rd.μNew k p hist c) :=
    fun hist c ↦ D.isFiniteMeasure_transportLeafMeasure n (a / 2) k (pre k) p ⟨hist, some c⟩
  have hmass := S.actualChargeScanRound_mass hm hM s n E a pre ha k hsym hpre hp
  have hbound := Rd.energySum_le_of_leaf_bounds (B := 2 * ℓ) (N := A)
    (d := 10 * (S.D : ℝ) / S.m) k hp'
    (fun hist ↦ by rw [hw]; exact historyWeight_nonneg hist)
    (by simp_rw [hw]; exact sum_historyWeight S.K s hm hM)
    (fun hist c ↦ by rw [hc]; exact chargeWeight_nonneg c)
    (fun hist ↦ by simp_rw [hc]; exact sum_chargeWeight S.K hM)
    (fun hist ↦ (hmass hist).1) (fun hist c ↦ (hmass hist).2 c)
    (fun i hist ↦ D.measurable_splitEta_sphere n E i ⟨hist, none⟩)
    (fun i hist θ ↦ hη0 i ⟨hist, none⟩ θ)
    (fun i hist c θ ↦ hη0 i ⟨hist, some c⟩ θ)
    (mul_nonneg (by norm_num) hℓ) hA (by positivity)
    (fun i hist θ ↦ hηB i ⟨hist, none⟩ θ)
    (fun i hist c θ ↦ hηB i ⟨hist, some c⟩ θ) hcardOld hcardNew hsplit
  have hbad : Rd.badWeight = ∑ hist : History S.K S.m S.M s,
      if S.IsGoodOldHistory hist then 0 else historyWeight hist := by
    change (∑ hist : History S.K S.m S.M s,
      if S.IsGoodOldHistory hist then 0 else
        (historyMeanTree S.K S.m S.M hm hM s).weight hist) = _
    simp only [historyMeanTree_weight]
  rw [S.actualChargeScanRound_energySum hm hM s n E a pre ha k hp',
    S.actualChargeScanRound_chargeDefect hm hM s n E a pre ha k p, hbad] at hbound
  exact hbound

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
