/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualScanMeasures

/-!
# Literal actual-round measure regressions

Source-only tests, uncompiled pending upstream acceptance. These statements retain
both actual leaf kinds, the supplied vector, arbitrary real parameters for finiteness,
zero copies, inactive and active endpoints, and both energy probability factors.
No analytic outputs are hypotheses. Existing endpoint norm and integrated entropy
tests remain unchanged in `ActualTransportEstimates`.
-/

set_option autoImplicit false

open scoped BigOperators Matrix
open Matrix MeasureTheory Set
open TensorPower TensorPower.ReplicaTransport Entropy
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

noncomputable section

namespace TNLeanTest.ActualScanMeasures

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
  (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

-- Exact canonical measure, with no history or conditional-choice weight inside it.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) :
    (S.actualFillScanRound hm hM s n E a pre).μOld k p h =
      (S.actualFillData hm hM s).transportLeafMeasure n (a / 2) k (pre k) p ⟨h, none⟩ := rfl

-- Finiteness at all real parameters and all natural replica counts.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) :
    IsFiniteMeasure ((S.actualFillScanRound hm hM s n E a pre).μOld k p h) := by
  change IsFiniteMeasure
    ((S.actualFillData hm hM s).transportLeafMeasure n (a / 2) k (pre k) p ⟨h, none⟩)
  infer_instance

-- Exact canonical measure, with no history or conditional-choice weight inside it.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) (c : Unit) :
    (S.actualFillScanRound hm hM s n E a pre).μNew k p h c =
      (S.actualFillData hm hM s).transportLeafMeasure n (a / 2) k (pre k) p ⟨h, some c⟩ := rfl

-- Finiteness at all real parameters and all natural replica counts.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) (c : Unit) :
    IsFiniteMeasure ((S.actualFillScanRound hm hM s n E a pre).μNew k p h c) := by
  change IsFiniteMeasure
    ((S.actualFillData hm hM s).transportLeafMeasure n (a / 2) k (pre k) p ⟨h, some c⟩)
  infer_instance

-- Zero replicas retain the Fourier factor one half for a nonzero symmetric scalar.
example (ha : 0 ≤ a)
    (hsym : pre 0 ∈ symmetricSubspace 0 (fun v => Fin (n v))) (hpre : pre 0 ≠ 0)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (h : History S.K S.m S.M s) :
    ((S.actualFillScanRound hm hM s n E a pre).μOld 0 p h).real univ = 1 / 2 ∧
      ∀ c, ((S.actualFillScanRound hm hM s n E a pre).μNew 0 p h c).real univ = 1 / 2 :=
  S.actualFillScanRound_mass hm hM s n E a pre ha 0 hsym hpre hp h

-- Inactive endpoint measures are literally zero, without prevector assumptions.
example (k : ℕ) (h : History S.K S.m S.M s) :
    (S.actualFillScanRound hm hM s n E a pre).μOld k 1 h = 0 ∧
      ∀ c, (S.actualFillScanRound hm hM s n E a pre).μNew k 0 h c = 0 :=
  transportScanRound_inactive (S.actualFillData hm hM s) n E S.IsGoodOldHistory
    (a / 2) pre k h

-- Complementary active endpoints retain the original measure and Fourier mass.
example (ha : 0 ≤ a) (k : ℕ)
    (hsym : pre k ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre k ≠ 0)
    (h : History S.K S.m S.M s) :
    ((S.actualFillScanRound hm hM s n E a pre).μOld k 0 h).real univ = 1 / 2 ∧
      ∀ c, ((S.actualFillScanRound hm hM s n E a pre).μNew k 1 h c).real univ = 1 / 2 :=
  transportScanRound_active (S.actualFillData hm hM s) n E S.IsGoodOldHistory
    (a / 2) pre (S.actualFillData_isAdmissible hm hM s)
    (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k)
    hsym hpre h

-- The zero vector produces a zero measure, rather than a mass-one convention.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) (c : Unit) :
    (S.actualFillScanRound hm hM s n E a (fun _ => 0)).μNew k p h c = 0 :=
  (S.actualFillData hm hM s).transportLeafMeasure_zero_pre n (a / 2) k p ⟨h, some c⟩

-- Both boundary values satisfy the energy identity, with the closed-interval guard.
example (ha : 0 ≤ a) (k : ℕ) :
    (S.actualFillScanRound hm hM s n E a pre).energySum k 0 =
        (S.actualFillData hm hM s).energyError E (a / 2) k (pre k) 0 ∧
      (S.actualFillScanRound hm hM s n E a pre).energySum k 1 =
        (S.actualFillData hm hM s).energyError E (a / 2) k (pre k) 1 :=
  ⟨S.actualFillScanRound_energySum hm hM s n E a pre ha k (by simp),
    S.actualFillScanRound_energySum hm hM s n E a pre ha k (by simp)⟩

-- The norm uses the same root and supplied vector even at zero copies.
example (p : ℝ) :
    (S.actualFillScanRound hm hM s n E a pre).logNormSq 0 p =
      Real.log (Transport.filteredNormSq
        ((S.actualFillData hm hM s).rootPath n (a / 2) 0 p) (pre 0)) := rfl

-- Exact canonical measure, with no history or conditional-choice weight inside it.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) :
    (S.actualChargeScanRound hm hM s n E a pre).μOld k p h =
      (S.actualChargeData hm hM s).transportLeafMeasure n (a / 2) k (pre k) p ⟨h, none⟩ := rfl

-- Finiteness at all real parameters and all natural replica counts.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) :
    IsFiniteMeasure ((S.actualChargeScanRound hm hM s n E a pre).μOld k p h) := by
  change IsFiniteMeasure
    ((S.actualChargeData hm hM s).transportLeafMeasure n (a / 2) k (pre k) p ⟨h, none⟩)
  infer_instance

-- Exact canonical measure, with no history or conditional-choice weight inside it.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) (c : ChargeChoices S.K S.M) :
    (S.actualChargeScanRound hm hM s n E a pre).μNew k p h c =
      (S.actualChargeData hm hM s).transportLeafMeasure n (a / 2) k (pre k) p ⟨h, some c⟩ := rfl

-- Finiteness at all real parameters and all natural replica counts.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) (c : ChargeChoices S.K S.M) :
    IsFiniteMeasure ((S.actualChargeScanRound hm hM s n E a pre).μNew k p h c) := by
  change IsFiniteMeasure
    ((S.actualChargeData hm hM s).transportLeafMeasure n (a / 2) k (pre k) p ⟨h, some c⟩)
  infer_instance

-- Zero replicas retain the Fourier factor one half for a nonzero symmetric scalar.
example (ha : 0 ≤ a)
    (hsym : pre 0 ∈ symmetricSubspace 0 (fun v => Fin (n v))) (hpre : pre 0 ≠ 0)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (h : History S.K S.m S.M s) :
    ((S.actualChargeScanRound hm hM s n E a pre).μOld 0 p h).real univ = 1 / 2 ∧
      ∀ c, ((S.actualChargeScanRound hm hM s n E a pre).μNew 0 p h c).real univ = 1 / 2 :=
  S.actualChargeScanRound_mass hm hM s n E a pre ha 0 hsym hpre hp h

-- Inactive endpoint measures are literally zero, without prevector assumptions.
example (k : ℕ) (h : History S.K S.m S.M s) :
    (S.actualChargeScanRound hm hM s n E a pre).μOld k 1 h = 0 ∧
      ∀ c, (S.actualChargeScanRound hm hM s n E a pre).μNew k 0 h c = 0 :=
  transportScanRound_inactive (S.actualChargeData hm hM s) n E S.IsGoodOldHistory
    (a / 2) pre k h

-- Complementary active endpoints retain the original measure and Fourier mass.
example (ha : 0 ≤ a) (k : ℕ)
    (hsym : pre k ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre k ≠ 0)
    (h : History S.K S.m S.M s) :
    ((S.actualChargeScanRound hm hM s n E a pre).μOld k 0 h).real univ = 1 / 2 ∧
      ∀ c, ((S.actualChargeScanRound hm hM s n E a pre).μNew k 1 h c).real univ = 1 / 2 :=
  transportScanRound_active (S.actualChargeData hm hM s) n E S.IsGoodOldHistory
    (a / 2) pre (S.actualChargeData_isAdmissible hm hM s)
    (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k)
    hsym hpre h

-- The zero vector produces a zero measure, rather than a mass-one convention.
example (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) (c : ChargeChoices S.K S.M) :
    (S.actualChargeScanRound hm hM s n E a (fun _ => 0)).μNew k p h c = 0 :=
  (S.actualChargeData hm hM s).transportLeafMeasure_zero_pre n (a / 2) k p ⟨h, some c⟩

-- Both boundary values satisfy the energy identity, with the closed-interval guard.
example (ha : 0 ≤ a) (k : ℕ) :
    (S.actualChargeScanRound hm hM s n E a pre).energySum k 0 =
        (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) 0 ∧
      (S.actualChargeScanRound hm hM s n E a pre).energySum k 1 =
        (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) 1 :=
  ⟨S.actualChargeScanRound_energySum hm hM s n E a pre ha k (by simp),
    S.actualChargeScanRound_energySum hm hM s n E a pre ha k (by simp)⟩

-- The norm uses the same root and supplied vector even at zero copies.
example (p : ℝ) :
    (S.actualChargeScanRound hm hM s n E a pre).logNormSq 0 p =
      Real.log (Transport.filteredNormSq
        ((S.actualChargeData hm hM s).rootPath n (a / 2) 0 p) (pre 0)) := rfl

-- The exact old symbol is integrated against the literal sphere state.
example (ha : 0 ≤ a) (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualFillScanRound hm hM s n E a pre).μOld k p h) =
      (S.actualFillData hm hM s).oldFourierCoherentIntegral n (a / 2) k (pre k) p h f :=
  S.integral_actualFillScanRound_old hm hM s n E a pre ha k p h hf

-- The exact new symbol is integrated against the literal sphere state.
example (ha : 0 ≤ a) (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) (c : Unit)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualFillScanRound hm hM s n E a pre).μNew k p h c) =
      ∫ u, Transport.fourierWeight u * realCoherentIntegral k (TransportData.base n)
        ((S.actualFillData hm hM s).state n (a / 2) k (pre k) p ⟨h, some c⟩ u) f :=
  S.integral_actualFillScanRound_new hm hM s n E a pre ha k p h c hf

-- The exact old symbol is integrated against the literal sphere state.
example (ha : 0 ≤ a) (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualChargeScanRound hm hM s n E a pre).μOld k p h) =
      (S.actualChargeData hm hM s).oldFourierCoherentIntegral n (a / 2) k (pre k) p h f :=
  S.integral_actualChargeScanRound_old hm hM s n E a pre ha k p h hf

-- The exact new symbol is integrated against the literal sphere state.
example (ha : 0 ≤ a) (k : ℕ) (p : ℝ) (h : History S.K S.m S.M s) (c : ChargeChoices S.K S.M)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂(S.actualChargeScanRound hm hM s n E a pre).μNew k p h c) =
      ∫ u, Transport.fourierWeight u * realCoherentIntegral k (TransportData.base n)
        ((S.actualChargeData hm hM s).state n (a / 2) k (pre k) p ⟨h, some c⟩ u) f :=
  S.integral_actualChargeScanRound_new hm hM s n E a pre ha k p h c hf

-- The entropy gain retains w_h rather than (1-p)w_h at every real parameter.
example (ha : 0 ≤ a) (k : ℕ) (p : ℝ) :
    (S.actualChargeScanRound hm hM s n E a pre).choiceGainSum k p =
      ∑ h, historyWeight h *
        (S.actualChargeData hm hM s).oldFourierCoherentIntegral n (a / 2) k (pre k) p h
          ((S.actualChargeData hm hM s).choiceEntropySymbol n h) := by
  rw [S.actualChargeScanRound_choiceGainSum hm hM s n E a pre ha k p,
    TransportData.entropyGain_eq_sum_oldFourierCoherentIntegral]
  apply Finset.sum_congr rfl
  intro h _
  rw [show (S.actualChargeData hm hM s).histTree.weight h = historyWeight h from
    historyMeanTree_weight _ _ _ hm hM s h]

-- Charge sampling consumes precisely this scalar defect, without an interior guard.
example (ha : 0 ≤ a) (k : ℕ) (p : ℝ) :
    (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p =
      S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) p :=
  S.actualChargeScanRound_chargeDefect hm hM s n E a pre ha k p

end TNLeanTest.ActualScanMeasures
