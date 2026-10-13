/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualScanMeasures
import TNLean.PEPS.AreaLaw.Scan.ActualParameterIntegral
import TNLean.PEPS.AreaLaw.Scan.TransportRoundParameterIntegral

/-!
# Parameter regularity of actual fill and charge rounds

Actual admissibility and cross-band commutation specialize the literal-round
parameter theorems at scale `a / 2`. Both kinds keep the same supplied family,
good-history predicate and history weights. Zero vectors and zero copies are
included. The actual charge identity also gives an independent route through
the scalar charge-defect theorem to closed-interval integrability.

These results supply parameter regularity, without constructing all scanner
fields, comparators, a physical common vector or a ground state.

Source: *A two-dimensional area law from a global spectral gap*, Proposition 7.4,
`06-transport.tex`, lines 364–434, and `08-scanner.tex`, lines 416–451.
-/

open TensorPower TensorPower.ReplicaTransport MeasureTheory Set

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
  (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

/-- The actual fill-round defect is AE strongly measurable on `(0,1)`. -/
theorem aestronglyMeasurable_actualFillScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable
      (fun p => (S.actualFillScanRound hm hM s n E a pre).chargeDefect k p)
      (volume.restrict (Ioo 0 1)) :=
  aestronglyMeasurable_transportScanRound_chargeDefect
    (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualFillData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k)

/-- The actual fill-round defect is interval integrable for every supplied vector
and every replica count, including zero. -/
theorem intervalIntegrable_actualFillScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) :
    IntervalIntegrable
      (fun p => (S.actualFillScanRound hm hM s n E a pre).chargeDefect k p) volume 0 1 :=
  intervalIntegrable_transportScanRound_chargeDefect
    (S.actualFillData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualFillData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.fillTransportData_crossBandCommute _ n (div_nonneg ha (by norm_num)) k)

/-- The actual fill-round defect is integrable with its literal endpoint values. -/
theorem integrableOn_Icc_actualFillScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) :
    IntegrableOn
      (fun p => (S.actualFillScanRound hm hM s n E a pre).chargeDefect k p) (Icc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (S.intervalIntegrable_actualFillScanRound_chargeDefect hm hM s n E a pre ha k)

/-- The actual fill-round defect is AE strongly measurable on `[0,1]`. -/
theorem aestronglyMeasurable_Icc_actualFillScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable
      (fun p => (S.actualFillScanRound hm hM s n E a pre).chargeDefect k p)
      (volume.restrict (Icc 0 1)) :=
  (S.integrableOn_Icc_actualFillScanRound_chargeDefect hm hM s n E a pre
    ha k).aestronglyMeasurable

/-- The actual charge-round defect is AE strongly measurable on `(0,1)`. -/
theorem aestronglyMeasurable_actualChargeScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable
      (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p)
      (volume.restrict (Ioo 0 1)) :=
  aestronglyMeasurable_transportScanRound_chargeDefect
    (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k)

/-- The actual charge-round defect is interval integrable for the unchanged
supplied family, without symmetry or nonzero-vector assumptions. -/
theorem intervalIntegrable_actualChargeScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) :
    IntervalIntegrable
      (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p) volume 0 1 :=
  intervalIntegrable_transportScanRound_chargeDefect
    (S.actualChargeData hm hM s) n E S.IsGoodOldHistory (a / 2) pre
    (S.actualChargeData_isAdmissible hm hM s) (div_nonneg ha (by norm_num)) k
    (S.chargeTransportData_crossBandCommute _ _ n (div_nonneg ha (by norm_num)) k)

/-- The scalar actual charge identity independently gives closed-interval
integrability of the literal round defect, including its original endpoints. -/
theorem integrableOn_Icc_actualChargeScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) :
    IntegrableOn
      (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p) (Icc 0 1) := by
  have heq : (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p) =
      S.actualChargeEntropyDefect hm hM s n E (a / 2) k (pre k) := by
    funext p
    exact S.actualChargeScanRound_chargeDefect hm hM s n E a pre ha k p
  rw [heq]
  exact S.integrableOn_Icc_actualChargeEntropyDefect hm hM s n E
    (div_nonneg ha (by norm_num)) k (pre k)

/-- The actual charge-round defect is AE strongly measurable on `[0,1]`. -/
theorem aestronglyMeasurable_Icc_actualChargeScanRound_chargeDefect (ha : 0 ≤ a) (k : ℕ) :
    AEStronglyMeasurable
      (fun p => (S.actualChargeScanRound hm hM s n E a pre).chargeDefect k p)
      (volume.restrict (Icc 0 1)) :=
  (S.integrableOn_Icc_actualChargeScanRound_chargeDefect hm hM s n E a pre
    ha k).aestronglyMeasurable

end TNLean.PEPS.AreaLaw.Scan.CollarScan
