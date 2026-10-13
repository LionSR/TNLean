/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TransportRound
import TNLean.PEPS.AreaLaw.Scan.OldStateParameterIntegral

/-!
# Parameter regularity of the literal scan-round charge defect

The literal sphere integral equals the finite good-history sum of old-state
Fourier/coherent integrals. Its continuous split-entropy symbols therefore give
AE strong measurability and interval integrability in the scan parameter. The
split indicator is removed by the exact zero entropy of an unsplit leaf.

The supplied family, good-history predicate and history weights are unchanged.
Neither continuity in the scan parameter nor measurability of a measure-valued
kernel is assumed. Zero supplied vectors and zero copies are included.

These results concern the scalar defect of a supplied round; they do not
construct the other scanner fields or a physical vector.

Source: *A two-dimensional area law from a global spectral gap*, Proposition 7.4,
`06-transport.tex`, lines 364–434, and `08-scanner.tex`, lines 416–451.
-/

open scoped BigOperators
open TensorPower TensorPower.ReplicaTransport MeasureTheory Set
open Entropy (SiteConfig)

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

variable {V H ι : Type} [Fintype V] [DecidableEq V] {K : ℕ}
  [Fintype H] [DecidableEq H] {C : H → Type}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] [Fintype ι]
  (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]
  (E : EnergyTerms V n ι) (good : H → Prop) (t : ℝ)
  (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)]
    [∀ h, DecidableEq (C h)] [∀ v, NeZero (n v)] in
/-- The old split-entropy sum is continuous in the coherent vector. -/
private theorem continuous_chargeDefectSymbol (h : H) :
    Continuous (fun θ : SiteConfig n → ℂ =>
      ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ)) := by
  unfold TransportData.splitEta
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun g _ =>
    continuous_splitBandEta _ _

/-- The literal round defect is AE strongly measurable on the open unit interval,
for the original supplied family and every replica count. -/
theorem aestronglyMeasurable_transportScanRound_chargeDefect
    (hD : D.IsAdmissible) (ht : 0 ≤ t) (k : ℕ) (hcomm : D.CrossBandCommute n t k) :
    AEStronglyMeasurable
      (fun p => (transportScanRound D n E good t pre).chargeDefect k p)
      (volume.restrict (Ioo 0 1)) := by
  classical
  let F (h : H) (θ : SiteConfig n → ℂ) :=
    ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ)
  have hF (h : H) : Continuous (F h) := continuous_chargeDefectSymbol D n E h
  refine (D.aestronglyMeasurable_sum_oldFourierCoherentIntegral n hD ht hcomm
    (pre k) good D.histTree.weight F hF).congr ?_
  exact Filter.Eventually.of_forall fun p =>
    (transportScanRound_chargeDefect D n E good t pre hD ht k hcomm p).symm

/-- The same literal round defect is interval integrable on `[0,1]`, without
symmetry, a nonzero supplied vector or a positive replica-count premise. -/
theorem intervalIntegrable_transportScanRound_chargeDefect
    (hD : D.IsAdmissible) (ht : 0 ≤ t) (k : ℕ) (hcomm : D.CrossBandCommute n t k) :
    IntervalIntegrable
      (fun p => (transportScanRound D n E good t pre).chargeDefect k p) volume 0 1 := by
  classical
  let F (h : H) (θ : SiteConfig n → ℂ) :=
    ∑ i, D.splitEta E i ⟨h, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ)
  have hF (h : H) : Continuous (F h) := continuous_chargeDefectSymbol D n E h
  have heq : (fun p => (transportScanRound D n E good t pre).chargeDefect k p) =
      (fun p => ∑ h, if good h then D.histTree.weight h *
        D.oldFourierCoherentIntegral n t k (pre k) p h (F h) else 0) := by
    funext p
    exact transportScanRound_chargeDefect D n E good t pre hD ht k hcomm p
  rw [heq]
  exact D.intervalIntegrable_sum_oldFourierCoherentIntegral n hD ht hcomm
    (pre k) good D.histTree.weight F hF

/-- Closed-interval integrability retains the literal endpoint values. -/
theorem integrableOn_Icc_transportScanRound_chargeDefect
    (hD : D.IsAdmissible) (ht : 0 ≤ t) (k : ℕ) (hcomm : D.CrossBandCommute n t k) :
    IntegrableOn (fun p => (transportScanRound D n E good t pre).chargeDefect k p)
      (Icc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (intervalIntegrable_transportScanRound_chargeDefect D n E good t pre hD ht k hcomm)

/-- The literal defect is also AE strongly measurable on the closed unit interval. -/
theorem aestronglyMeasurable_Icc_transportScanRound_chargeDefect
    (hD : D.IsAdmissible) (ht : 0 ≤ t) (k : ℕ) (hcomm : D.CrossBandCommute n t k) :
    AEStronglyMeasurable
      (fun p => (transportScanRound D n E good t pre).chargeDefect k p)
      (volume.restrict (Icc 0 1)) :=
  (integrableOn_Icc_transportScanRound_chargeDefect D n E good t pre
    hD ht k hcomm).aestronglyMeasurable

end TNLean.PEPS.AreaLaw.Scan
