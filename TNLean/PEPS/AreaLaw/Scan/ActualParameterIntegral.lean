/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEntropySampling
import TNLean.PEPS.AreaLaw.Scan.OldStateParameterIntegral

/-!
# Derived parameter regularity of actual charge defects

The finite split-entropy symbols are continuous in the coherent vector. The
actual admissibility and cross-band commutation theorems therefore give AE
strong measurability and interval integrability of the literal old-state
scalar charge defect, for every supplied pre-vector and replica count.

Only the accepted transport expectation APIs are used. This does not construct
scanner leaf measures, the other scanner fields, or a physical common vector.
-/

open scoped BigOperators
open TensorPower TensorPower.ReplicaTransport MeasureTheory
open Entropy (SiteConfig)

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- The actual scalar charge defect is AE strongly measurable in the scan
parameter, with the original good-history predicate and history weights. -/
theorem aestronglyMeasurable_actualChargeEntropyDefect
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (V ⊕ Bool) n I) {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) :
    AEStronglyMeasurable (S.actualChargeEntropyDefect hm hM k n E t r pre)
      (volume.restrict (Set.Ioo 0 1)) := by
  classical
  let D := S.actualChargeData hm hM k
  let F (h : History S.K S.m S.M k) (θ : SiteConfig n → ℂ) :=
    ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ)
  have hF (h : History S.K S.m S.M k) : Continuous (F h) := by
    unfold F TransportData.splitEta
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun g _ =>
      continuous_splitBandEta _ _
  exact D.aestronglyMeasurable_sum_oldFourierCoherentIntegral n
    (S.actualChargeData_isAdmissible hm hM k) ht
    (S.chargeTransportData_crossBandCommute _ _ n ht r) pre
    S.IsGoodOldHistory historyWeight F hF

/-- The actual scalar charge defect is interval integrable on `[0,1]`.
No nonzero-vector, symmetry or positive-replica-count hypothesis is added. -/
theorem intervalIntegrable_actualChargeEntropyDefect
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (V ⊕ Bool) n I) {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) :
    IntervalIntegrable (S.actualChargeEntropyDefect hm hM k n E t r pre) volume 0 1 := by
  classical
  let D := S.actualChargeData hm hM k
  let F (h : History S.K S.m S.M k) (θ : SiteConfig n → ℂ) :=
    ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ)
  have hF (h : History S.K S.m S.M k) : Continuous (F h) := by
    unfold F TransportData.splitEta
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun g _ =>
      continuous_splitBandEta _ _
  exact D.intervalIntegrable_sum_oldFourierCoherentIntegral n
    (S.actualChargeData_isAdmissible hm hM k) ht
    (S.chargeTransportData_crossBandCommute _ _ n ht r) pre
    S.IsGoodOldHistory historyWeight F hF

/-- The closed interval retains the actual endpoint values of the defect. -/
theorem integrableOn_Icc_actualChargeEntropyDefect
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (V ⊕ Bool) n I) {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) :
    IntegrableOn (S.actualChargeEntropyDefect hm hM k n E t r pre) (Set.Icc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (S.intervalIntegrable_actualChargeEntropyDefect hm hM k n E ht r pre)

/-- On the closed interval, AE strong measurability follows from the derived
integrability and does not assert parameter continuity. -/
theorem aestronglyMeasurable_Icc_actualChargeEntropyDefect
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (V ⊕ Bool) n I) {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) :
    AEStronglyMeasurable (S.actualChargeEntropyDefect hm hM k n E t r pre)
      (volume.restrict (Set.Icc 0 1)) :=
  (S.integrableOn_Icc_actualChargeEntropyDefect hm hM k n E ht r pre).aestronglyMeasurable

/-- A zero supplied vector makes the actual finite charge defect zero. -/
@[simp] theorem actualChargeEntropyDefect_zero_pre
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (V ⊕ Bool) n I) (t : ℝ) (r : ℕ) (p : ℝ) :
    S.actualChargeEntropyDefect hm hM k n E t r 0 p = 0 := by
  classical
  simp [actualChargeEntropyDefect]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
