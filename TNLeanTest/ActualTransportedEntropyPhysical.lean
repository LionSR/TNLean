/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLeanTest.ActualScanPhysicalSamplingData
import TNLean.PEPS.AreaLaw.Scan.ActualEntropySampling

/-!
# Transported entropy on a nonempty physical scan

Both entropy inequalities specialize to the original six-site physical
sampling geometry. Its actual good old history has a designated near-middle
split, a nonempty cut, and jointly discharged physical numerical hypotheses.
The two-dimensional local factors include both auxiliary factors. The energy
terms are zero operators with the actual designated supports; the entropy
assertions depend on the supports and on the actual transported old state.
-/

set_option autoImplicit false

open TensorPower TensorPower.ReplicaTransport
open Entropy (SiteConfig)
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open TNLeanTest.ActualScanPhysicalSampling
open scoped BigOperators

namespace TNLeanTest.ActualTransportedEntropyPhysical

noncomputable section

private def dimensions : Site domain ⊕ Bool → ℕ := fun _ => 2

private instance (v : Site domain ⊕ Bool) : NeZero (dimensions v) := ⟨by decide⟩

private def terms : EnergyTerms (Site domain ⊕ Bool) dimensions (Fin 1) where
  term := fun _ => 0
  support := fun i =>
    (designatedSupport scan.graph (scan.truncationSet 256) scan.r₀ (scan.anchor i)).map
      ⟨Sum.inl, Sum.inl_injective⟩

private theorem capacity_pos : 0 < scan.M :=
  chargeSlotCount_pos (by norm_num) (by norm_num) (by norm_num)

private theorem multiplicity (x : Site domain) :
    (Finset.univ.filter fun i => scan.anchor i = x).card ≤ 1 :=
  (Finset.card_filter_le _ _).trans (by simp)

-- The actual support splits; the entropy margin and actual history are compatible.
example : 2 * scan.r₀ ≤ scan.D ∧ scan.IsGoodOldHistory history ∧
    scan.designatedSplitIncidence (scan.oldChargeState history 0) 256 0 false ∧
    (Geometry.boundaryEndpoints domain scan.A).Nonempty := by
  refine ⟨by norm_num, good_history, ?_, ?_⟩
  · unfold CollarScan.designatedSplitIncidence
    rw [designated_ball]
    exact ball_split
  · rw [boundary_endpoints]
    simp

-- No support-compatibility certificate is supplied for this physical instance.
example (θ : SiteConfig dimensions → ℂ) :
    ((1 / (2 * (scan.C₁ + 1))) / ((scan.n : ℝ) * scan.D)) *
        (∑ i, (scan.actualChargeData (by norm_num) capacity_pos 0).splitEta
          terms i ⟨history, none⟩ ((EuclideanSpace.equiv _ ℂ).symm θ)) ≤
      (scan.actualChargeData (by norm_num) capacity_pos 0).
        choiceEntropySymbol dimensions history θ := by
  exact CollarScan.good_sum_splitEta_le_choiceEntropySymbol_domainGraph
    target_nonempty scan rfl rfl (by norm_num) capacity_pos history dimensions terms
    (fun _ => rfl) (L := 256) (μ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows multiplicity clearance good_history θ

-- The integrated inequality is proved on the same concrete geometry and trees.
example {t : ℝ} (ht : 0 ≤ t) (r : ℕ)
    (pre : Config r (fun v => Fin (dimensions v)) → ℂ) (p : ℝ) :
    ((1 / (2 * (scan.C₁ + 1))) / ((scan.n : ℝ) * scan.D)) *
        scan.actualChargeEntropyDefect (by norm_num) capacity_pos 0 dimensions terms t r pre p ≤
      (scan.actualChargeData (by norm_num) capacity_pos 0).entropyGain dimensions t r pre p := by
  exact CollarScan.actualChargeEntropyDefect_le_entropyGain_domainGraph
    target_nonempty scan rfl rfl (by norm_num) capacity_pos dimensions terms
    (fun _ => rfl) (L := 256) (μ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows multiplicity clearance ht r pre p

end

end TNLeanTest.ActualTransportedEntropyPhysical
