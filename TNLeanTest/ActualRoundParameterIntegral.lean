/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoundParameterIntegral

/-!
# Parameter regularity of literal fill and charge rounds

Source-only regressions, uncompiled pending the separately authorized upstream
integration. The generic tests retain the original supplied family and fixed
good-history predicate. Both actual kinds include arbitrary natural replica counts,
the zero supplied vector at every real parameter, an explicitly nonzero constant
vector at zero copies, and the closed interpolation interval. The charge scalar
identity gives an independent route through the existing actual-defect theorems.
The earlier scalar, measure, energy, mass and discontinuity tests are unchanged.
-/

set_option autoImplicit false

open scoped BigOperators
open TensorPower TensorPower.ReplicaTransport MeasureTheory
open Entropy (SiteConfig)
open TNLean.PEPS.AreaLaw.Scan

noncomputable section

namespace TNLeanTest.ActualRoundParameterIntegral

/-- The constant scalar vector is nonzero even when there are no copies. -/
theorem zero_copy_pre_ne_zero {V : Type} (n : V → ℕ) :
    (fun _ : Config 0 (fun v => Fin (n v)) => (1 : ℂ)) ≠ 0 := by
  intro h
  have he := congrFun h (fun i => Fin.elim0 i)
  norm_num at he

section Generic

variable {V H I : Type} [Fintype V] [DecidableEq V] {K : ℕ}
  [Fintype H] [DecidableEq H] {C : H → Type}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] [Fintype I]
  (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]
  (E : EnergyTerms V n I) (good : H → Prop) (t : ℝ)
  (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

/-- Both regularity conclusions concern the same literal round and supplied family. -/
theorem transport_regularity (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k) :
    AEStronglyMeasurable (fun p => (transportScanRound D n E good t pre).chargeDefect k p)
        (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable (fun p => (transportScanRound D n E good t pre).chargeDefect k p)
        volume 0 1 :=
  ⟨aestronglyMeasurable_transportScanRound_chargeDefect D n E good t pre hD ht k hcomm,
    intervalIntegrable_transportScanRound_chargeDefect D n E good t pre hD ht k hcomm⟩

/-- Closed-interval regularity does not replace the values at either endpoint. -/
theorem transport_closed_interval (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k) :
    AEStronglyMeasurable (fun p => (transportScanRound D n E good t pre).chargeDefect k p)
        (volume.restrict (Set.Icc 0 1)) ∧
      IntegrableOn (fun p => (transportScanRound D n E good t pre).chargeDefect k p)
        (Set.Icc 0 1) :=
  ⟨aestronglyMeasurable_Icc_transportScanRound_chargeDefect D n E good t pre hD ht k hcomm,
    integrableOn_Icc_transportScanRound_chargeDefect D n E good t pre hD ht k hcomm⟩

/-- Zero supplied vectors have zero literal defect for every real parameter. -/
theorem transport_zero_pre (k : ℕ) (p : ℝ) :
    (transportScanRound D n E good t (fun _ => 0)).chargeDefect k p = 0 := by
  classical
  simp [ScanRound.chargeDefect, transportScanRound]

/-- The literal old measures vanish at the right endpoint, without normalization. -/
theorem transport_right_endpoint (k : ℕ) :
    (transportScanRound D n E good t pre).chargeDefect k 1 = 0 := by
  classical
  simp [ScanRound.chargeDefect, transportScanRound]

/-- The generic theorem includes zero copies and a nonzero constant supplied vector. -/
theorem transport_zero_copies (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : D.CrossBandCommute n t 0) :
    (fun _ : Config 0 (fun v => Fin (n v)) => (1 : ℂ)) ≠ 0 ∧
      AEStronglyMeasurable
          (fun p => (transportScanRound D n E good t (fun _ _ => 1)).chargeDefect 0 p)
          (volume.restrict (Set.Ioo 0 1)) ∧
        IntervalIntegrable
          (fun p => (transportScanRound D n E good t (fun _ _ => 1)).chargeDefect 0 p)
          volume 0 1 :=
  ⟨zero_copy_pre_ne_zero n,
    transport_regularity D n E good t (fun _ _ => 1) hD ht 0 hcomm⟩

end Generic

section Actual

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
  (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

/-- Actual fill regularity uses the original common family at every natural count. -/
theorem fill_regularity (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable (fun p => (S.actualFillScanRound hm hM s n E a pre).chargeDefect k p)
        (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable (fun p => (S.actualFillScanRound hm hM s n E a pre).chargeDefect k p)
        volume 0 1 :=
  ⟨S.aestronglyMeasurable_actualFillScanRound_chargeDefect hm hM s n E a pre ha k,
    S.intervalIntegrable_actualFillScanRound_chargeDefect hm hM s n E a pre ha k⟩

/-- Actual charge regularity imposes neither symmetry nor a nonzero-vector premise. -/
theorem charge_regularity (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p)
        (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p)
        volume 0 1 :=
  ⟨S.aestronglyMeasurable_actualChargeScanRound_chargeDefect hm hM s n E a pre ha k,
    S.intervalIntegrable_actualChargeScanRound_chargeDefect hm hM s n E a pre ha k⟩

/-- Both closed endpoints are retained for the actual fill defect. -/
theorem fill_closed_interval (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable (fun p => (S.actualFillScanRound hm hM s n E a pre).chargeDefect k p)
        (volume.restrict (Set.Icc 0 1)) ∧
      IntegrableOn (fun p => (S.actualFillScanRound hm hM s n E a pre).chargeDefect k p)
        (Set.Icc 0 1) :=
  ⟨S.aestronglyMeasurable_Icc_actualFillScanRound_chargeDefect hm hM s n E a pre ha k,
    S.integrableOn_Icc_actualFillScanRound_chargeDefect hm hM s n E a pre ha k⟩

/-- Both closed endpoints are retained for the actual charge defect. -/
theorem charge_closed_interval (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p)
        (volume.restrict (Set.Icc 0 1)) ∧
      IntegrableOn (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p)
        (Set.Icc 0 1) :=
  ⟨S.aestronglyMeasurable_Icc_actualChargeScanRound_chargeDefect hm hM s n E a pre ha k,
    S.integrableOn_Icc_actualChargeScanRound_chargeDefect hm hM s n E a pre ha k⟩

/-- A zero family gives zero literal fill defect at every real parameter. -/
theorem fill_zero_pre (k : ℕ) (p : ℝ) :
    (S.actualFillScanRound hm hM s n E a (fun _ => 0)).chargeDefect k p = 0 :=
  transport_zero_pre (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) k p

/-- A zero family gives zero literal charge defect at every real parameter. -/
theorem charge_zero_pre (k : ℕ) (p : ℝ) :
    (S.actualChargeScanRound hm hM s n E a (fun _ => 0)).chargeDefect k p = 0 :=
  transport_zero_pre (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) k p

/-- The fill regularity theorem specializes to the zero family itself. -/
theorem fill_zero_pre_regularity (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable
        (fun p => (S.actualFillScanRound hm hM s n E a (fun _ => 0)).chargeDefect k p)
        (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable
        (fun p => (S.actualFillScanRound hm hM s n E a (fun _ => 0)).chargeDefect k p)
        volume 0 1 :=
  fill_regularity S hm hM s n E a (fun _ => 0) ha k

/-- The charge regularity theorem specializes to the zero family itself. -/
theorem charge_zero_pre_regularity (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable
        (fun p => (S.actualChargeScanRound hm hM s n E a (fun _ => 0)).chargeDefect k p)
        (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable
        (fun p => (S.actualChargeScanRound hm hM s n E a (fun _ => 0)).chargeDefect k p)
        volume 0 1 :=
  charge_regularity S hm hM s n E a (fun _ => 0) ha k

/-- The zero-copy fill test includes proof that its supplied scalar is nonzero. -/
theorem fill_zero_copies (ha : 0 ≤ a) :
    (fun _ : Config 0 (fun v => Fin (n v)) => (1 : ℂ)) ≠ 0 ∧
      AEStronglyMeasurable
          (fun p => (S.actualFillScanRound hm hM s n E a (fun _ _ => 1)).chargeDefect 0 p)
          (volume.restrict (Set.Ioo 0 1)) ∧
        IntervalIntegrable
          (fun p => (S.actualFillScanRound hm hM s n E a (fun _ _ => 1)).chargeDefect 0 p)
          volume 0 1 :=
  ⟨zero_copy_pre_ne_zero n, fill_regularity S hm hM s n E a (fun _ _ => 1) ha 0⟩

/-- The zero-copy charge test includes proof that its supplied scalar is nonzero. -/
theorem charge_zero_copies (ha : 0 ≤ a) :
    (fun _ : Config 0 (fun v => Fin (n v)) => (1 : ℂ)) ≠ 0 ∧
      AEStronglyMeasurable
          (fun p => (S.actualChargeScanRound hm hM s n E a (fun _ _ => 1)).chargeDefect 0 p)
          (volume.restrict (Set.Ioo 0 1)) ∧
        IntervalIntegrable
          (fun p => (S.actualChargeScanRound hm hM s n E a (fun _ _ => 1)).chargeDefect 0 p)
          volume 0 1 :=
  ⟨zero_copy_pre_ne_zero n, charge_regularity S hm hM s n E a (fun _ _ => 1) ha 0⟩

open Classical in
/-- The original fill scalar identity holds at each endpoint with the same family. -/
theorem fill_endpoint_identities (ha : 0 ≤ a) (k : ℕ) :
    let D := S.actualFillData hm hM s
    let Q := fun p => ∑ h, if S.IsGoodOldHistory h then D.histTree.weight h *
      D.oldFourierCoherentIntegral n (a / 2) k (pre k) p h
        (fun θ => ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ))
      else 0
    (S.actualFillScanRound hm hM s n E a pre).chargeDefect k 0 = Q 0 ∧
      (S.actualFillScanRound hm hM s n E a pre).chargeDefect k 1 = Q 1 := by
  exact ⟨transportScanRound_chargeDefect (S.actualFillData hm hM s) n E
      S.IsGoodOldHistory (a / 2) pre (S.actualFillData_isAdmissible hm hM s)
      (div_nonneg ha (by norm_num)) k
      (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k) 0,
    transportScanRound_chargeDefect (S.actualFillData hm hM s) n E
      S.IsGoodOldHistory (a / 2) pre (S.actualFillData_isAdmissible hm hM s)
      (div_nonneg ha (by norm_num)) k
      (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k) 1⟩

/-- The actual charge scalar identity holds at both endpoints for every count. -/
theorem charge_endpoint_identities (ha : 0 ≤ a) (k : ℕ) :
    (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k 0 =
        S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) 0 ∧
      (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k 1 =
        S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) 1 :=
  ⟨S.actualChargeScanRound_chargeDefect hm hM s n E a pre ha k 0,
    S.actualChargeScanRound_chargeDefect hm hM s n E a pre ha k 1⟩

/-- Both actual defects retain the zero value of their inactive old endpoint. -/
theorem actual_right_endpoints (k : ℕ) :
    (S.actualFillScanRound hm hM s n E a pre).chargeDefect k 1 = 0 ∧
      (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k 1 = 0 :=
  ⟨transport_right_endpoint (S.actualFillData hm hM s) n E S.IsGoodOldHistory
      (a / 2) pre k,
    transport_right_endpoint (S.actualChargeData hm hM s) n E S.IsGoodOldHistory
      (a / 2) pre k⟩

/-- Independently transfer both scalar charge results using the literal identity,
without invoking either new actual-round regularity theorem. -/
theorem charge_regularity_via_scalar (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p)
        (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p)
        volume 0 1 := by
  have heq : (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p) =
      S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) := by
    funext p
    exact S.actualChargeScanRound_chargeDefect hm hM s n E a pre ha k p
  rw [heq]
  exact ⟨S.aestronglyMeasurable_actualChargeEntropyDefect hm hM s n E
      (div_nonneg ha (by norm_num)) k (pre k),
    S.intervalIntegrable_actualChargeEntropyDefect hm hM s n E
      (div_nonneg ha (by norm_num)) k (pre k)⟩

end Actual

end TNLeanTest.ActualRoundParameterIntegral
