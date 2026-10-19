/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoundSplits
import TNLean.PEPS.AreaLaw.Scan.SplitEntropyBound
import TNLean.PEPS.AreaLaw.Scan.TransportDimension
import TNLean.PEPS.AreaLaw.Scan.ActualEntropySampling
import TNLean.PEPS.AreaLaw.Scan.BadOldHistoryDecay
import TNLean.PEPS.AreaLaw.Scan.FillSupportCompatibility
import TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport
import TNLean.PEPS.AreaLaw.LatticeCounts

/-!
# Lemma 9.1 for the rounds of the actual collar scan

The `2nm` rounds of one physical collar scan, fills at even and charges at odd
positions, are scan rounds on the literal coherent sphere. For this family the
conclusions of Lemma 9.1 used by Proposition 9.2 are derived from the scan geometry:
classical history and choice probabilities, the `10D/m` dilution of split terms, the
`10KnDμ` count of split terms at every leaf, the bad-history tail, sampling of split
terms on good histories at charge rounds, and the bounds on move entropies. At the
source scales they hold for all sufficiently large `n` with constants chosen before
the domain, Hamiltonian, scan, auxiliary dimensions and replica vectors.

Only the classical history tree and the move geometry enter; the replica vector and
the interpolation scale are arbitrary.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.actualScanRound`: the round family.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.historyFacts_actualScanRound`: Lemma 9.1 for
  that family at one scale, under explicit finite scale inequalities.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_historyFacts_actualScanRound`: Lemma 9.1
  for that family at the source scales.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 9.1 (`scanner:histories`), `08-scanner.tex`, lines 195–221, the construction of
  lines 83–154 and the move entropies of lines 431–444. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently formalized from
  the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators
open Filter Set MeasureTheory
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

open TNLean.Lattice

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]

/-- A valid move has entropy at most twice the logarithmic dimension of its moved
subsystem (`06-transport.tex`, lines 315–322; `08-scanner.tex`, lines 434–440). -/
theorem moveEta_le_two_mul_logDim (π : PYF V) (hπ : π.IsPartition) (m : Move V)
    (hm : m.IsValid π) (θ : EuclideanSpace ℂ (SiteConfig n)) (hθ : ‖θ‖ = 1) :
    moveEta n π m θ ≤ 2 * logDim n m.subsystem := by
  cases m with
  | stay => simp [moveEta, Move.subsystem, logDim]
  | toP x =>
    have hxY : x ⊆ π.Y := hm
    exact (FiniteProduct.conditionalMutualInformation_le_two_entropy _ θ hθ x π.F π.P
      (hπ.2.2.1.mono_left hxY) (hπ.1.symm.mono_left hxY)).trans
      (mul_le_mul_of_nonneg_left (entropy_le_logDim_of_subset n θ hθ subset_rfl)
        (by norm_num))
  | toF x =>
    have hxY : x ⊆ π.Y := hm
    exact (FiniteProduct.conditionalMutualInformation_le_two_entropy _ θ hθ x π.P π.F
      (hπ.1.symm.mono_left hxY) (hπ.2.2.1.mono_left hxY)).trans
      (mul_le_mul_of_nonneg_left (entropy_le_logDim_of_subset n θ hθ subset_rfl)
        (by norm_num))

namespace TransportData

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)

omit [Fintype H] in
/-- The choice-averaged move entropy is at most `2Kℓ` when every move has logarithmic
dimension at most `ℓ`: each band contributes one probability average of move entropies
(`08-scanner.tex`, lines 434–440). -/
theorem choiceEntropySymbol_le_of_logDim_move_le (hD : D.IsAdmissible) {ℓ : ℝ}
    (hmove : ∀ h c g, logDim n (D.move h c g).subsystem ≤ ℓ) (h : H)
    (θ : EuclideanSpace ℂ (SiteConfig n)) (hθ : ‖θ‖ = 1) :
    D.choiceEntropySymbol n h (fun x => θ x) ≤ K * (2 * ℓ) := by
  classical
  unfold choiceEntropySymbol
  calc
    _ ≤ ∑ _g : Fin K, ∑ c, (D.choiceTree h).weight c * (2 * ℓ) := by
      refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun c _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ ((D.choiceTree h).weight_nonneg c)
      exact (moveEta_le_two_mul_logDim n _ (hD.old_isPartition h g) _
        (hD.move_isValid h c g) θ hθ).trans
        (mul_le_mul_of_nonneg_left (hmove h c g) (by norm_num))
    _ = K * (2 * ℓ) := by
      simp [← Finset.sum_mul, (D.choiceTree h).sum_weight]

end TransportData

end TensorPower.ReplicaTransport

namespace TNLean.PEPS.AreaLaw.Scan

namespace CollarScan

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
  (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

/-- The rounds of the actual scan: `nm` fills and `nm` charges, interleaved with a fill
first (`08-scanner.tex`, lines 106–107), so round `j` is the fill or charge after `⌊j/2⌋`
completed fill/charge pairs. Every round uses the same supplied replica vectors. -/
def actualScanRound (j : ℕ) : ScanRound I (CoherentSphere (SiteConfig n)) :=
  if IsChargeRound j then S.actualChargeScanRound hm hM (j / 2) n E a pre
  else S.actualFillScanRound hm hM (j / 2) n E a pre

/-- An odd round of the actual scan is its charge round. -/
theorem actualScanRound_of_charge {j : ℕ} (hj : IsChargeRound j) :
    S.actualScanRound hm hM n E a pre j = S.actualChargeScanRound hm hM (j / 2) n E a pre := by
  simp only [actualScanRound, hj, ↓reduceIte]

/-- An even round of the actual scan is its fill round. -/
theorem actualScanRound_of_fill {j : ℕ} (hj : ¬IsChargeRound j) :
    S.actualScanRound hm hM n E a pre j = S.actualFillScanRound hm hM (j / 2) n E a pre := by
  simp only [actualScanRound, hj, ↓reduceIte]

/-- Prove a property of an actual round from the corresponding charge and fill rounds. -/
theorem actualScanRound_cases (P : ScanRound I (CoherentSphere (SiteConfig n)) → Prop) (j : ℕ)
    (hcharge : IsChargeRound j → P (S.actualChargeScanRound hm hM (j / 2) n E a pre))
    (hfill : ¬IsChargeRound j → P (S.actualFillScanRound hm hM (j / 2) n E a pre)) :
    P (S.actualScanRound hm hM n E a pre j) := by
  unfold actualScanRound
  split_ifs with hj
  exacts [hcharge hj, hfill hj]

end CollarScan

namespace CollarScan

variable {I : Type} [Fintype I] [LinearOrder I]

open Classical in
/-- The classical probability, at stage `s`, that the old history is not good
(Lemma 9.1(4), `08-scanner.tex`, lines 212–215). -/
def badOldWeight {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I) (s : ℕ) : ℝ :=
  ∑ h : History S.K S.m S.M s, if S.IsGoodOldHistory h then 0 else historyWeight h

/-- **Lemma 9.1 for the actual scan at one scale.** At scale `N`, with the scanner scales
`n = N`, `m = ⌊N^μ⌋`, `K = ⌊L/(8m)⌋`, `D = ⌈N^κ⌉` and `L = ⌊N^{1-ℓ}⌋`, the actual rounds
satisfy every conclusion of Lemma 9.1 used by Proposition 9.2, together with the move-entropy
bounds of lines 434–440, for constants `C`, `C_l`, `c` dominating the explicit geometric ones:
`10` for dilution, `10μ` for split counts, the support cap `2ℓ` for move entropies, and the
sampling constant `1/(2(C₁+1))`. The finite scale inequalities `2r₀ ≤ D`,
`4(D + 2r₀) ≤ m` and the bad-history tail are hypotheses here; they hold at the source scales
for all large `N` (`exists_historyFacts_actualScanRound`).

Source: `08-scanner.tex`, Lemma 9.1, lines 195–221, and lines 431–444. -/
theorem historyFacts_actualScanRound (X : ScannerExponents) (N : ℕ)
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty) (S : CollarScan (Site Λ) I)
    (hm : 0 < S.m) (hM : 0 < S.M) {q : ℕ} (hq : 1 ≤ q)
    (dims : Site Λ ⊕ Bool → ℕ) [∀ v, NeZero (dims v)] (hphysical : ∀ x, dims (Sum.inl x) = q)
    (E : EnergyTerms (Site Λ ⊕ Bool) dims I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet (X.L N)) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (dims v)) → ℂ)
    (hSn : S.n = N) (hSm : S.m = X.m N) (hSK : S.K = X.K N) (hSD : S.D = X.D N)
    (hgraph : S.graph = domainGraph Λ) (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hN : 2 ≤ N) (hr : 2 * S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D)
    (hmargin : 4 * (S.D + 2 * S.r₀) ≤ S.m)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ X.L N →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * X.L N + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {μ : ℕ} (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hC₁ : 3 * (μ : ℝ) ≤ S.C₁) (hC₁pos : 0 < S.C₁)
    (hbad : ∀ s ≤ S.n * S.m, S.badOldWeight s ≤ (N : ℝ) ^ (-200 : ℝ))
    {C Cl c : ℝ} (hC10 : 10 ≤ C) (hCμ : 10 * (μ : ℝ) ≤ C)
    (hCη : 2 * transportLogDimBound q S.r₀ ≤ C * Real.log N ^ Cl)
    (hc : c ≤ 1 / (2 * (S.C₁ + 1))) :
    HistoryFacts X N C Cl c (fun r ↦ S.actualScanRound hm hM dims E a pre r.val) := by
  -- Every round index is a completed-pair count inside the physical horizon.
  have hstage (r : Fin (X.rounds N)) : r.val / 2 + 1 ≤ S.n * S.m := by
    have hr' : r.val < 2 * (S.n * S.m) := by
      have := r.isLt
      simp only [ScannerExponents.rounds] at this
      rw [hSn, hSm]
      linarith [Nat.mul_assoc 2 N (X.m N)]
    omega
  have hL : 8 * S.K * S.m ≤ X.L N := by
    rw [hSK, hSm]
    exact eight_mul_bandCount_mul_le (X.L N) (X.m N)
  have hn0 : 0 < S.n := by omega
  have hm2 : 2 ≤ S.m := by omega
  have hD : 4 * S.D ≤ S.m := by omega
  have hr1 : S.r₀ ≤ S.D := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hDR : (0 : ℝ) < X.D N := by rw [← hSD]; exact_mod_cast hDpos
  have hmR : (0 : ℝ) < X.m N := by rw [← hSm]; exact_mod_cast hm
  have hℓ : 0 ≤ transportLogDimBound q S.r₀ :=
    zero_le_one.trans (one_le_transportLogDimBound hq S.r₀)
  have hlogC : 0 ≤ C * Real.log N ^ Cl := (mul_nonneg (by norm_num) hℓ).trans hCη
  -- The dilution and counting constants.
  have hsplitC : 10 * (S.D : ℝ) / S.m ≤ C * X.D N / X.m N := by
    rw [hSD, hSm]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC10 hDR.le) hmR.le
  have hcardC : 10 * (S.K : ℝ) * S.n * S.D * μ ≤ C * X.K N * N * X.D N := by
    rw [hSK, hSn, hSD]
    have : (0 : ℝ) ≤ X.K N * N * X.D N := by positivity
    nlinarith
  have hηC : 2 * transportLogDimBound q S.r₀ ≤ C * Real.log N ^ Cl := hCη
  -- Admissibility, compatibility and support caps for both kinds of round.
  have hadmC (s : ℕ) := S.actualChargeData_isAdmissible hm hM s
  have hadmF (s : ℕ) := S.actualFillData_isAdmissible hm hM s
  have hcompatC (s : ℕ) (hs : s + 1 ≤ S.n * S.m) :
      (S.actualChargeData hm hM s).SupportCompatible E :=
    S.chargeTransportData_supportCompatible_domainGraph hT hgraph hdepth
      (historyMeanTree S.K S.m S.M hm hM s) (fun _ ↦ chargeChoiceTree S.K S.M hM)
      hn0 hs hr1 hDpos hD hL hrows hclear dims E hsupport
  have hcompatF (s : ℕ) (hs : s + 1 ≤ S.n * S.m) :
      (S.actualFillData hm hM s).SupportCompatible E :=
    S.fillTransportData_supportCompatible_domainGraph hT hgraph hdepth
      (historyMeanTree S.K S.m S.M hm hM s) hn0 hs hr1 hDpos hD hL hrows hclear dims E hsupport
  have hsuppC (s : ℕ) (i : I) (hi : ((S.actualChargeData hm hM s).splitLeaves E i).Nonempty) :
      logDim dims (E.support i) ≤ transportLogDimBound q S.r₀ :=
    S.chargeTransportData_logDim_support_le_domainGraph hgraph
      (historyMeanTree S.K S.m S.M hm hM s) (fun _ ↦ chargeChoiceTree S.K S.M hM)
      dims hq hphysical hL E hsupport i hi
  have hsuppF (s : ℕ) (i : I) (hi : ((S.actualFillData hm hM s).splitLeaves E i).Nonempty) :
      logDim dims (E.support i) ≤ transportLogDimBound q S.r₀ :=
    S.fillTransportData_logDim_support_le_domainGraph hgraph
      (historyMeanTree S.K S.m S.M hm hM s) dims hq hphysical hL E hsupport i hi
  have hmoveC (s : ℕ) : ∀ h c g, logDim dims ((S.actualChargeData hm hM s).move h c g).subsystem ≤
      transportLogDimBound q S.r₀ :=
    S.chargeTransportData_logDim_move_le_domainGraph hgraph
      (historyMeanTree S.K S.m S.M hm hM s) (fun _ ↦ chargeChoiceTree S.K S.M hM) dims hq
      hphysical
  have hmoveF (s : ℕ) : ∀ h c g, logDim dims ((S.actualFillData hm hM s).move h c g).subsystem ≤
      transportLogDimBound q S.r₀ :=
    S.fillTransportData_logDim_move_le (historyMeanTree S.K S.m S.M hm hM s) dims hq hphysical
  -- The choice-averaged gain is at most `K · 2ℓ`.
  have hgainC : ∀ s h (θ : CoherentSphere (SiteConfig dims)),
      (S.actualChargeData hm hM s).choiceEntropySymbol dims h (fun x => θ.1 x) ≤
        C * X.K N * Real.log N ^ Cl := fun s h θ ↦
    ((S.actualChargeData hm hM s).choiceEntropySymbol_le_of_logDim_move_le dims (hadmC s)
      (hmoveC s) h θ.1 θ.2).trans (by
        rw [hSK]; nlinarith [show (0 : ℝ) ≤ X.K N by positivity])
  have hgainF : ∀ s h (θ : CoherentSphere (SiteConfig dims)),
      (S.actualFillData hm hM s).choiceEntropySymbol dims h (fun x => θ.1 x) ≤
        C * X.K N * Real.log N ^ Cl := fun s h θ ↦
    ((S.actualFillData hm hM s).choiceEntropySymbol_le_of_logDim_move_le dims (hadmF s)
      (hmoveF s) h θ.1 θ.2).trans (by
        rw [hSK]; nlinarith [show (0 : ℝ) ≤ X.K N by positivity])
  refine
    { w_nonneg := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ h, 0 ≤ R.w h) r.val
        (fun _ h ↦ (historyMeanTree S.K S.m S.M hm hM _).weight_nonneg h)
        (fun _ h ↦ (historyMeanTree S.K S.m S.M hm hM _).weight_nonneg h)
      q_nonneg := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ h c, 0 ≤ R.q h c) r.val
        (fun _ h c ↦ (chargeChoiceTree S.K S.M hM).weight_nonneg c)
        (fun _ h c ↦ fillChoiceTree.weight_nonneg c)
      sum_w := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∑ h, R.w h = 1) r.val
        (fun _ ↦ (historyMeanTree S.K S.m S.M hm hM (r.val / 2)).sum_weight)
        (fun _ ↦ (historyMeanTree S.K S.m S.M hm hM (r.val / 2)).sum_weight)
      sum_q := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ h, ∑ c, R.q h c = 1) r.val
        (fun _ h ↦ (chargeChoiceTree S.K S.M hM).sum_weight)
        (fun _ h ↦ fillChoiceTree.sum_weight)
      splitWeight_le := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ i, R.splitWeight p i ≤ C * X.D N / X.m N) r.val
        (fun _ p hp i ↦ (S.actualChargeScanRound_splitWeight_le hT hm hM dims E a pre hgraph
          hdepth hsupport hC₁pos hn0 (hstage r) hr1 hDpos hD hL hrows hclear
          ⟨hp.1.le, hp.2.le⟩ i).trans hsplitC)
        (fun _ p hp i ↦ (S.actualFillScanRound_splitWeight_le hT hm hM dims E a pre hgraph
          hdepth hsupport hC₁pos hn0 (hstage r) hr1 hDpos hD hL hrows hclear
          ⟨hp.1.le, hp.2.le⟩ i).trans hsplitC)
      card_splitOld_le := open Classical in fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ h, ((Finset.univ.filter fun i ↦ R.splitOld i h).card : ℝ) ≤
          C * X.K N * N * X.D N) r.val
        (fun _ h ↦ (S.actualChargeScanRound_card_splitOld_le hT hm hM dims E a pre hgraph
          hdepth hsupport (by omega) hm2 (hstage r) hr1 hDpos hmargin hL hrows hclear hmult
          h).trans hcardC)
        (fun _ h ↦ (S.actualFillScanRound_card_splitOld_le hT hm hM dims E a pre hgraph
          hdepth hsupport (by omega) hm2 (hstage r) hr1 hDpos hmargin hL hrows hclear hmult
          h).trans hcardC)
      card_splitNew_le := open Classical in fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ h c, ((Finset.univ.filter fun i ↦ R.splitNew i h c).card : ℝ) ≤
          C * X.K N * N * X.D N) r.val
        (fun _ h c ↦ (S.actualChargeScanRound_card_splitNew_le hT hm hM dims E a pre hgraph
          hdepth hsupport (by omega) hm2 (hstage r) hr1 hDpos hmargin hL hrows hclear hmult
          h c).trans hcardC)
        (fun _ h c ↦ (S.actualFillScanRound_card_splitNew_le hT hm hM dims E a pre hgraph
          hdepth hsupport (by omega) hm2 (hstage r) hr1 hDpos hmargin hL hrows hclear hmult
          h c).trans hcardC)
      badWeight_le := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ R.badWeight ≤ (N : ℝ) ^ (-200 : ℝ)) r.val
        (fun _ ↦ by
          refine le_of_eq_of_le ?_ (hbad (r.val / 2) (by have := hstage r; omega))
          simp only [ScanRound.badWeight, transportScanRound, actualChargeScanRound,
            actualChargeData, chargeTransportData, historyMeanTree_weight, badOldWeight]
          refine Finset.sum_congr
            (Finset.ext fun _ ↦ iff_of_true (Finset.mem_univ _) (Finset.mem_univ _)) fun h _ ↦ ?_
          by_cases hg : S.IsGoodOldHistory h <;> simp [hg])
        (fun _ ↦ by
          refine le_of_eq_of_le ?_ (hbad (r.val / 2) (by have := hstage r; omega))
          simp only [ScanRound.badWeight, transportScanRound, actualFillScanRound,
            actualFillData, fillTransportData, historyMeanTree_weight, badOldWeight]
          refine Finset.sum_congr
            (Finset.ext fun _ ↦ iff_of_true (Finset.mem_univ _) (Finset.mem_univ _)) fun h _ ↦ ?_
          by_cases hg : S.IsGoodOldHistory h <;> simp [hg])
      sampling := open Classical in fun r hr' ↦ by
        classical
        rw [show S.actualScanRound hm hM dims E a pre r.val =
          S.actualChargeScanRound hm hM (r.val / 2) dims E a pre from
          S.actualScanRound_of_charge hm hM dims E a pre hr']
        intro h hgood θ
        have hsum : (∑ i, if (S.actualChargeScanRound hm hM (r.val / 2) dims E a pre).splitOld
              i h then (S.actualChargeScanRound hm hM (r.val / 2) dims E a pre).etaOld i h θ
              else 0) =
            ∑ i, (S.actualChargeData hm hM (r.val / 2)).splitEta E i ⟨h, none⟩
              ((EuclideanSpace.equiv _ ℂ).symm (fun x => θ.1 x)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          split_ifs with hi
          · rfl
          · exact ((S.actualChargeData hm hM (r.val / 2)).splitEta_eq_zero_of_not_mem_splitLeaves
              E hi _).symm
        have hnonneg : 0 ≤ ∑ i, (S.actualChargeData hm hM (r.val / 2)).splitEta E i ⟨h, none⟩
            ((EuclideanSpace.equiv _ ℂ).symm (fun x => θ.1 x)) :=
          Finset.sum_nonneg fun i _ ↦
            (S.actualChargeData hm hM (r.val / 2)).splitEta_nonneg dims E (hadmC _) i _ _
        rw [hsum]
        refine le_trans ?_ (S.good_sum_splitEta_le_choiceEntropySymbol_domainGraph hT hgraph
          hdepth hm hM h dims E hsupport (by omega) hm2 (hstage r) hr hD hDpos hL hC₁ hrows
          hmult hclear hgood (fun x => θ.1 x))
        refine mul_le_mul_of_nonneg_right ?_ hnonneg
        rw [hSn, hSD]
        exact div_le_div_of_nonneg_right hc (by positivity)
      etaOld_nonneg := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ i h θ, 0 ≤ R.etaOld i h θ) r.val
        (fun _ i h θ ↦ (S.actualChargeData hm hM _).splitEta_nonneg dims E (hadmC _) i _ θ.1)
        (fun _ i h θ ↦ (S.actualFillData hm hM _).splitEta_nonneg dims E (hadmF _) i _ θ.1)
      etaOld_le := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ i h θ, R.etaOld i h θ ≤ C * Real.log N ^ Cl) r.val
        (fun _ i h θ ↦ ((S.actualChargeData hm hM _).splitEta_le_two_mul_of_logDim_le dims E
          (hadmC _) (hcompatC _ (hstage r)) hℓ (hsuppC _) i _ θ).trans hηC)
        (fun _ i h θ ↦ ((S.actualFillData hm hM _).splitEta_le_two_mul_of_logDim_le dims E
          (hadmF _) (hcompatF _ (hstage r)) hℓ (hsuppF _) i _ θ).trans hηC)
      etaNew_nonneg := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ i h c θ, 0 ≤ R.etaNew i h c θ) r.val
        (fun _ i h c θ ↦ (S.actualChargeData hm hM _).splitEta_nonneg dims E (hadmC _) i _ θ.1)
        (fun _ i h c θ ↦ (S.actualFillData hm hM _).splitEta_nonneg dims E (hadmF _) i _ θ.1)
      etaNew_le := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ i h c θ, R.etaNew i h c θ ≤ C * Real.log N ^ Cl) r.val
        (fun _ i h c θ ↦ ((S.actualChargeData hm hM _).splitEta_le_two_mul_of_logDim_le dims E
          (hadmC _) (hcompatC _ (hstage r)) hℓ (hsuppC _) i _ θ).trans hηC)
        (fun _ i h c θ ↦ ((S.actualFillData hm hM _).splitEta_le_two_mul_of_logDim_le dims E
          (hadmF _) (hcompatF _ (hstage r)) hℓ (hsuppF _) i _ θ).trans hηC)
      measurable_etaOld := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ i h, Measurable (R.etaOld i h)) r.val
        (fun _ i h ↦ (S.actualChargeData hm hM _).measurable_splitEta_sphere dims E i _)
        (fun _ i h ↦ (S.actualFillData hm hM _).measurable_splitEta_sphere dims E i _)
      measurable_etaNew := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ i h c, Measurable (R.etaNew i h c)) r.val
        (fun _ i h c ↦ (S.actualChargeData hm hM _).measurable_splitEta_sphere dims E i _)
        (fun _ i h c ↦ (S.actualFillData hm hM _).measurable_splitEta_sphere dims E i _)
      choiceGain_nonneg := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ h θ, 0 ≤ R.choiceGain h θ) r.val
        (fun _ h θ ↦ (S.actualChargeData hm hM _).choiceEntropySymbol_nonneg dims (hadmC _) h _)
        (fun _ h θ ↦ (S.actualFillData hm hM _).choiceEntropySymbol_nonneg dims (hadmF _) h _)
      measurable_choiceGain := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ h, Measurable (R.choiceGain h)) r.val
        (fun _ h ↦ (((S.actualChargeData hm hM _).continuous_choiceEntropySymbol dims h).comp
          continuous_coherentSphere_coe).measurable)
        (fun _ h ↦ (((S.actualFillData hm hM _).continuous_choiceEntropySymbol dims h).comp
          continuous_coherentSphere_coe).measurable)
      choiceGain_le := fun r ↦ S.actualScanRound_cases hm hM dims E a pre
        (fun R ↦ ∀ h θ, R.choiceGain h θ ≤ C * X.K N * Real.log N ^ Cl) r.val
        (fun _ h θ ↦ hgainC _ h θ)
        (fun _ h θ ↦ hgainF _ h θ) }

/-- The support cap `2ℓ = 2(1 + (2r₀ + 1)² log q)` of the source radius
`r₀ = ⌈C_tr log² N⌉` is at most a fixed multiple of `(log N)^4` once `log N ≥ 1`
(`08-scanner.tex`, lines 49 and 434–440). -/
theorem two_mul_transportLogDimBound_le {q : ℕ} (hq : 1 ≤ q) {Ctr : ℝ} (hCtr : 0 ≤ Ctr)
    {N : ℕ} (hN : 3 ≤ N) :
    2 * transportLogDimBound q ⌈Ctr * Real.log N ^ 2⌉₊ ≤
      2 * (1 + (2 * Ctr + 3) ^ 2 * Real.log q) * Real.log N ^ (4 : ℝ) := by
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)).trans
      (by exact_mod_cast hN)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hr : (⌈Ctr * Real.log N ^ 2⌉₊ : ℝ) ≤ Ctr * Real.log N ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hl2 : 1 ≤ Real.log N ^ 2 := one_le_pow₀ hlog
  have hrad : (((2 * ⌈Ctr * Real.log N ^ 2⌉₊ + 1) ^ 2 : ℕ) : ℝ) ≤
      (2 * Ctr + 3) ^ 2 * Real.log N ^ 4 := by
    push_cast
    have h1 : 2 * (⌈Ctr * Real.log N ^ 2⌉₊ : ℝ) + 1 ≤ (2 * Ctr + 3) * Real.log N ^ 2 := by
      nlinarith
    calc (2 * (⌈Ctr * Real.log N ^ 2⌉₊ : ℝ) + 1) ^ 2 ≤ ((2 * Ctr + 3) * Real.log N ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = _ := by ring
  have h4 : (1 : ℝ) ≤ Real.log N ^ 4 := one_le_pow₀ hlog
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold transportLogDimBound
  nlinarith [mul_le_mul_of_nonneg_right hrad hlq]

/-- **Lemma 9.1 for the actual scan at the source scales.** The constants `C`, `C_l = 4`,
`c` and the charge-list constant `C₁` are chosen before the scale, from the interaction
range `R`, the local dimension `q`, the truncation-radius coefficient and the target-size
coefficient. For every sufficiently large `N`, every physical collar scan at the source
scales `scanner:scales` with radius `r₀ = ⌈C_tr log² N⌉`, under the source test geometry
`scanner:test-geometry`, satisfies `HistoryFacts` for its actual rounds, for any energy
terms with the truncated radius-`r₀` designated supports, any auxiliary dimensions, and any
replica vectors.

Source: `08-scanner.tex`, Lemma 9.1, lines 195–221, with the scales and test geometry of
lines 32–58 and the move entropies of lines 431–444. -/
theorem exists_historyFacts_actualScanRound (X : ScannerExponents) (R : ℕ) {q : ℕ}
    (hq : 1 ≤ q) {Ctr CT : ℝ} (hCtr : 0 < Ctr) (hCT : 0 ≤ CT) :
    ∃ C c C₁ : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 < C₁ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hm : 0 < S.m) (hM : 0 < S.M)
        (dims : Site Λ ⊕ Bool → ℕ) [∀ v, NeZero (dims v)]
        (E : EnergyTerms (Site Λ ⊕ Bool) dims (AdmissibleSupport Λ R)) (a : ℝ)
        (pre : (k : ℕ) → Config k (fun v => Fin (dims v)) → ℂ),
        (∀ x, dims (Sum.inl x) = q) →
        (∀ i, E.support i =
          (designatedSupport S.graph (S.truncationSet (X.L N)) S.r₀ (S.anchor i)).map
            ⟨Sum.inl, Sum.inl_injective⟩) →
        S.n = N → S.m = X.m N → S.K = X.K N → S.D = X.D N →
        S.r₀ = ⌈Ctr * Real.log N ^ 2⌉₊ → S.C₁ = C₁ →
        (T.card : ℝ) ≤ CT * (N : ℝ) ^ 2 →
        S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) →
        (∀ d : ℕ, 1 ≤ d → d ≤ X.L N →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * X.L N + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        HistoryFacts X N C 4 c (fun r ↦ S.actualScanRound hm hM dims E a pre r.val) := by
  let μ : ℕ := 2 ^ ((1 + 2 * R * (R + 1)) - 1)
  let C₁ : ℝ := 3 * μ + 1
  have hC₁ : 0 < C₁ := by positivity
  let C : ℝ := max (max 10 (10 * μ)) (2 * (1 + (2 * Ctr + 3) ^ 2 * Real.log q))
  refine ⟨C, 1 / (2 * (C₁ + 1)), C₁, (by norm_num : (0 : ℝ) ≤ 10).trans
    ((le_max_left _ _).trans (le_max_left _ _)), by positivity, hC₁, ?_⟩
  have htail := eventually_bad_history_probability_le X.ell_pos X.kappa_pos X.kappa_lt_mu
    X.mu_lt_one_sub_ell hCtr hC₁ hCT μ 200
  have hscales := eventually_split_counting_scale_separation (ell := X.ell) hCtr.le
    X.kappa_pos X.kappa_lt_mu
  have htwo := eventually_const_mul_roundedLogRadius_le_rpow hCtr.le X.kappa_pos 2
  filter_upwards [htail, hscales, htwo, eventually_ge_atTop 3] with N htail hscales htwo hN3
  intro Λ T _ hT S hm hM dims _ E a pre hphysical hsupport hSn hSm hSK hSD hSr hSC hTcard
    hgraph hdepth hanchor hrows hclear
  dsimp only [roundedLogRadius] at hscales htwo
  obtain ⟨hN2, -, hDpos, hmargin, -⟩ := hscales
  have hmult (x : Site Λ) : (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ :=
    card_anchor_fiber_le S.anchor hanchor x
  have hr2 : 2 * S.r₀ ≤ S.D := by
    have hceil : (N : ℝ) ^ X.kappa ≤ (X.D N : ℝ) := Nat.le_ceil _
    have : (2 * S.r₀ : ℝ) ≤ X.D N := by rw [hSr]; linarith
    rw [hSD]; exact_mod_cast this
  have hbad : ∀ s ≤ S.n * S.m, S.badOldWeight s ≤ (N : ℝ) ^ (-200 : ℝ) := by
    intro s hs
    unfold badOldWeight
    have hM' : S.M = ⌈C₁ * N * S.D⌉₊ := by simp only [CollarScan.M, chargeSlotCount, hSC, hSn]
    refine (S.sum_historyWeight_bad_old_le_bad_through (N := N * S.m) hM
      (by rw [hSn] at hs; exact hs)).trans ?_
    exact htail _ Λ T hT S hSn hSm (by rw [hSK, hSm]; rfl) hSD hSr hM' hTcard hgraph hdepth
        (by simpa only [ScannerExponents.L] using hclear)
        (by simpa only [ScannerExponents.L] using hrows) hmult
  refine historyFacts_actualScanRound X N hT S hm hM hq dims hphysical E hsupport a pre
    hSn hSm hSK hSD hgraph hdepth (by omega) hr2 (by rw [hSD]; exact hDpos)
    (by rw [hSD, hSm, hSr]; exact hmargin) hrows hclear hmult
    (by rw [hSC]; dsimp only [C₁]; linarith) (by rw [hSC]; exact hC₁) hbad
    ((le_max_left 10 _).trans (le_max_left _ _)) ((le_max_right 10 _).trans (le_max_left _ _))
    ?_ (by rw [hSC])
  rw [hSr]
  refine (two_mul_transportLogDimBound_le hq hCtr.le hN3).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
