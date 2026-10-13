/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualParameterIntegral
import TNLean.PEPS.AreaLaw.Scan.FillTransport

/-!
# Actual fill and charge parameter-integrability regressions

These specializations use the actual recursive history trees and physical
commutation proofs. They include the zero supplied vector at every parameter,
zero copies with an explicitly nonzero vector, arbitrary fixed good-history
predicates in deterministic fills, and the actual good-history charge defect.
No symmetry or positive replica count is assumed by the regularity theorems.
-/

set_option autoImplicit false

open scoped BigOperators
open TensorPower TensorPower.ReplicaTransport MeasureTheory
open Entropy (SiteConfig)
open TNLean.PEPS.AreaLaw.Scan

noncomputable section

namespace TNLeanTest.ActualParameterIntegral

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
variable (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
variable (E : EnergyTerms (V ⊕ Bool) n I)

/-- Both forms of actual charge regularity consume the same supplied vector. -/
theorem charge_regularity {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) :
    AEStronglyMeasurable (S.actualChargeEntropyDefect hm hM s n E t r pre)
        (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable (S.actualChargeEntropyDefect hm hM s n E t r pre) volume 0 1 :=
  ⟨S.aestronglyMeasurable_actualChargeEntropyDefect hm hM s n E ht r pre,
    S.intervalIntegrable_actualChargeEntropyDefect hm hM s n E ht r pre⟩

/-- The generic finite-sum bridge applies to the actual deterministic-fill
split symbols and an arbitrary fixed history predicate. -/
theorem fill_regularity {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ)
    (good : History S.K S.m S.M s → Prop) [DecidablePred good] :
    let D := S.actualFillData hm hM s
    let Q := fun p => ∑ h, if good h then
      historyWeight h * D.oldFourierCoherentIntegral n t r pre p h
        (fun θ => ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ))
      else 0
    AEStronglyMeasurable Q (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable Q volume 0 1 := by
  classical
  let D := S.actualFillData hm hM s
  let F (h : History S.K S.m S.M s) (θ : SiteConfig n → ℂ) :=
    ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ)
  have hF (h : History S.K S.m S.M s) : Continuous (F h) := by
    unfold F TransportData.splitEta
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun g _ =>
      continuous_splitBandEta _ _
  have hcomm : D.CrossBandCommute n t r :=
    S.fillTransportData_crossBandCommute _ n ht r
  exact ⟨D.aestronglyMeasurable_sum_oldFourierCoherentIntegral n
      (S.actualFillData_isAdmissible hm hM s) ht hcomm pre good historyWeight F hF,
    D.intervalIntegrable_sum_oldFourierCoherentIntegral n
      (S.actualFillData_isAdmissible hm hM s) ht hcomm pre good historyWeight F hF⟩

/-- Charge defects of zero supplied vectors vanish even at the endpoints. -/
theorem charge_zero_pre (t : ℝ) (r : ℕ) (p : ℝ) :
    S.actualChargeEntropyDefect hm hM s n E t r 0 p = 0 :=
  S.actualChargeEntropyDefect_zero_pre hm hM s n E t r p

/-- The same zero-vector conclusion holds for the actual fill scalar sum,
without nonnegative metric or interior-parameter assumptions. -/
theorem fill_zero_pre (t : ℝ) (r : ℕ) (p : ℝ)
    (good : History S.K S.m S.M s → Prop) [DecidablePred good] :
    let D := S.actualFillData hm hM s
    (∑ h, if good h then
      historyWeight h * D.oldFourierCoherentIntegral n t r 0 p h
        (fun θ => ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ))
      else 0) = 0 := by
  simp

omit [Fintype V] [DecidableEq V] [∀ v, NeZero (n v)] in
/-- There is a nonzero supplied vector even at zero copies. -/
theorem zero_copy_pre_ne_zero :
    (fun _ : Config 0 (fun v => Fin (n v)) => (1 : ℂ)) ≠ 0 := by
  intro h
  have he := congrFun h (fun i => Fin.elim0 i)
  norm_num at he

/-- Zero copies are covered with that explicitly nonzero supplied vector. -/
theorem charge_zero_copies {t : ℝ} (ht : 0 ≤ t) :
    AEStronglyMeasurable (S.actualChargeEntropyDefect hm hM s n E t 0 (fun _ => 1))
        (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable (S.actualChargeEntropyDefect hm hM s n E t 0 (fun _ => 1)) volume 0 1 :=
  charge_regularity S hm hM s n E ht 0 (fun _ => 1)

/-- Zero-copy deterministic fills use the same finite-sum theorem. -/
theorem fill_zero_copies {t : ℝ} (ht : 0 ≤ t)
    (good : History S.K S.m S.M s → Prop) [DecidablePred good] :
    let D := S.actualFillData hm hM s
    let Q := fun p => ∑ h, if good h then
      historyWeight h * D.oldFourierCoherentIntegral n t 0 (fun _ => 1) p h
        (fun θ => ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ))
      else 0
    AEStronglyMeasurable Q (volume.restrict (Set.Ioo 0 1)) ∧
      IntervalIntegrable Q volume 0 1 :=
  fill_regularity S hm hM s n E ht 0 (fun _ => 1) good

/-- Both closed endpoints are retained by the actual charge theorem. -/
example {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (n v)) → ℂ) :
    IntegrableOn (S.actualChargeEntropyDefect hm hM s n E t r pre) (Set.Icc 0 1) :=
  S.integrableOn_Icc_actualChargeEntropyDefect hm hM s n E ht r pre

omit [Fintype I] [LinearOrder I] in
/-- The generic single-leaf theorem does not need finite histories or choices. -/
example {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)]
    (D : TransportData (V ⊕ Bool) S.K H C) (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {r : ℕ} (hcomm : D.CrossBandCommute n t r)
    (pre : Config r (fun v => Fin (n v)) → ℂ) (h : H)
    {F : (SiteConfig n → ℂ) → ℝ} (hF : Continuous F) :
    AEStronglyMeasurable (fun p => D.oldFourierCoherentIntegral n t r pre p h F)
      (volume.restrict (Set.Icc 0 1)) :=
  D.aestronglyMeasurable_Icc_oldFourierCoherentIntegral n hD ht hcomm pre h hF

end TNLeanTest.ActualParameterIntegral
