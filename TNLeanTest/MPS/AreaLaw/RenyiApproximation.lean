/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.RenyiApproximation

open TNLean.MPS.AreaLaw

-- Empty and one-site chains need no internal rank hypothesis, even at bond zero.
example {q : ℕ} (ψ : EuclideanSpace ℂ (Fin 0 → Fin q)) (hψ : ‖ψ‖ = 1) :
    IsOpenMPS 0 q 0 (fun x ↦ ψ x) :=
  isOpenMPS_of_regionState_rank_le ψ hψ (by simp)

example {q : ℕ} (ψ : EuclideanSpace ℂ (Fin 1 → Fin q)) (hψ : ‖ψ‖ = 1) :
    IsOpenMPS 1 q 0 (fun x ↦ ψ x) :=
  isOpenMPS_of_regionState_rank_le ψ hψ (by simp)

/-- info: 'TNLean.MPS.AreaLaw.one_sub_kyFanNorm_le_of_renyiEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_sub_kyFanNorm_le_of_renyiEntropy_le

/-- info: 'TNLean.MPS.AreaLaw.exists_normalized_isOpenMPS_of_renyiEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_normalized_isOpenMPS_of_renyiEntropy_le

/-- info: 'TNLean.MPS.AreaLaw.isOpenMPS_of_regionState_rank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isOpenMPS_of_regionState_rank_le

/-- info: 'TNLean.MPS.AreaLaw.isEfficientlyApproximableByMPS_of_renyiEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isEfficientlyApproximableByMPS_of_renyiEntropy_le
