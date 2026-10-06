/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointSpectatorGap

/-!
# Dependent spectator gap regressions

The examples cover unequal active and spectator dimensions, an operator with
purely imaginary scalar action, empty labels, empty spectator fibers, and
replacement by different nonempty multiplicities.
-/

-- These regression files intentionally audit axioms with guarded #print commands.
set_option linter.hashCommand false

open scoped BigOperators InnerProductSpace
open ContinuousLinearMap

namespace DependentSpectatorGapEquivalenceTest

-- The two active dimensions are 1 and 2, while the spectator dimensions are
-- 2 and 3. Multiplication by the imaginary unit needs no positivity assumption.
example :
    ∀ x ∈ (LinearMap.ker
      (dependentRightFiberwiseMap (S := fun q : Fin 2 ↦ Fin (q.val + 2))
        (fun q ↦ Complex.I •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (q.val + 1))))).toLinearMap)ᗮ,
      1 * ‖x‖ ≤ ‖dependentRightFiberwiseMap
        (S := fun q : Fin 2 ↦ Fin (q.val + 2))
        (fun q ↦ Complex.I •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (q.val + 1)))) x‖ := by
  apply norm_gap_dependentRightFiberwiseMap _ zero_le_one
  intro q x _
  simp [norm_smul]

-- No label exists, so the fiber nonemptiness assumption is vacuous even when
-- every displayed spectator type is empty.
example (G : ∀ _ : Fin 0, EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ x ∈ (LinearMap.ker
      (dependentRightFiberwiseMap (S := fun _ : Fin 0 ↦ Fin 0) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap (S := fun _ : Fin 0 ↦ Fin 0) G x‖ := by
  letI : ∀ q : Fin 0, Nonempty (Fin 0) := fun q ↦ Fin.elim0 q
  apply (norm_gap_dependentRightFiberwiseMap_iff (S := fun _ : Fin 0 ↦ Fin 0) G hδ).mpr
  intro q
  exact Fin.elim0 q

-- Forward transport allows empty spectators at present labels.
example (G : ∀ q : Fin 2,
      EuclideanSpace ℂ (Fin (q.val + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (q.val + 1)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ q x ∈ (LinearMap.ker (G q).toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G q x‖) :
    ∀ x ∈ (LinearMap.ker
      (dependentRightFiberwiseMap (S := fun _ ↦ Fin 0) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap (S := fun _ ↦ Fin 0) G x‖ :=
  norm_gap_dependentRightFiberwiseMap G hδ hGap

-- The multiplicities (2, 3) and (3, 5) give exactly the same common gap.
example (G : ∀ q : Fin 2,
      EuclideanSpace ℂ (Fin (q.val + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (q.val + 1)))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker
      (dependentRightFiberwiseMap (S := fun q ↦ Fin (q.val + 2)) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap (S := fun q ↦ Fin (q.val + 2)) G x‖) ↔
      ∀ x ∈ (LinearMap.ker
        (dependentRightFiberwiseMap (S := fun q ↦ Fin (2 * q.val + 3)) G).toLinearMap)ᗮ,
        δ * ‖x‖ ≤
          ‖dependentRightFiberwiseMap (S := fun q ↦ Fin (2 * q.val + 3)) G x‖ :=
  norm_gap_dependentRightFiberwiseMap_iff_dependentRightFiberwiseMap G hδ

-- The actual boundary specialization keeps all four ordered pairs of two
-- labels, including (0, 1) and (1, 0), and allows a zero second-endpoint dimension.
example {d N : ℕ}
    (G : ∀ q : Fin 2 × Fin 2,
      EuclideanSpace ℂ (Fin (q.1.val + 1) × MPSTensor.Cfg d N × Fin (q.2.val + 1)) →L[ℂ]
        EuclideanSpace ℂ
          (Fin (q.1.val + 1) × MPSTensor.Cfg d N × Fin (q.2.val + 1)))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker (dependentRightFiberwiseMap
        (S := fun q : Fin 2 × Fin 2 ↦ Fin (q.1.val + 1) × Fin (q.2.val + 1)) G)
        .toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap
        (S := fun q : Fin 2 × Fin 2 ↦ Fin (q.1.val + 1) × Fin (q.2.val + 1)) G x‖) ↔
      ∀ x ∈ (LinearMap.ker (dependentRightFiberwiseMap
          (S := fun q : Fin 2 × Fin 2 ↦
            Fin (q.1.val + 1 + 2 * q.1.val) × Fin (q.2.val + 1 + 2 * q.2.val)) G)
          .toLinearMap)ᗮ,
        δ * ‖x‖ ≤ ‖dependentRightFiberwiseMap
          (S := fun q : Fin 2 × Fin 2 ↦
            Fin (q.1.val + 1 + 2 * q.1.val) × Fin (q.2.val + 1 + 2 * q.2.val)) G x‖ :=
  MPSTensor.MPOSymmetry.jointMixedEndpoint_spectatorGap_iff
    (fun x ↦ x.val + 1) (fun x ↦ 2 * x.val) (fun _ ↦ Nat.zero_lt_succ _) G hδ

end DependentSpectatorGapEquivalenceTest

/--
info: 'ContinuousLinearMap.norm_gap_dependentRightFiberwiseMap_iff_dependentRightFiberwiseMap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousLinearMap.norm_gap_dependentRightFiberwiseMap_iff_dependentRightFiberwiseMap

/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_spectatorGap_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_spectatorGap_iff
