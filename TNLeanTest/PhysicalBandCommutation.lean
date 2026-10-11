/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalBandCommutation
import Mathlib.Tactic.FinCases

/-!
# Physical cross-band and projection-scope regressions

The complementary swap test is an exact finite permutation statement, not a
numerical evaluation of the replica weights. It rules out removing the
symmetric-subspace restriction from the complementary-subsystem mechanism.
The actual two-band scanner tests use distinct offsets and histories, arbitrary
old/completed statuses, and positive physical and auxiliary dimensions.
-/

set_option autoImplicit false

open TensorPower TensorPower.ReplicaTransport PermutationRepresentation
open TNLean.PEPS.AreaLaw.Scan

namespace TNLeanTest.PhysicalBandCommutation

private def basisConfig : Config 2 (fun _ : Fin 2 => Fin 2) :=
  fun j f => if f = 0 then j else 0

private theorem first_swap_moves :
    subsystemPerm 2 (fun _ : Fin 2 => Fin 2) {0} (Equiv.swap 0 1) basisConfig ≠
      basisConfig := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  norm_num [subsystemPerm_apply, basisConfig] at hh

private theorem second_swap_fixes :
    subsystemPerm 2 (fun _ : Fin 2 => Fin 2) {1} (Equiv.swap 0 1) basisConfig =
      basisConfig := by
  ext j f
  fin_cases j <;> fin_cases f <;> norm_num [subsystemPerm_apply, basisConfig]

-- Complementary subsystem swaps are genuinely unequal off the symmetric space.
example :
    permOp (subsystemPerm 2 (fun _ : Fin 2 => Fin 2) {0}) (Equiv.swap 0 1) ≠
      permOp (subsystemPerm 2 (fun _ : Fin 2 => Fin 2) {1}) (Equiv.swap 0 1) := by
  intro h
  have hh := congrArg (fun M => M basisConfig basisConfig) h
  simp only [permOp_apply_apply, ite_eq_right first_swap_moves,
    ite_eq_left second_swap_fixes] at hh
  exact zero_ne_one hh

-- The corresponding basis vector is outside the symmetric subspace.
example : (Pi.single basisConfig (1 : ℂ)) ∉
    symmetricSubspace 2 (fun _ : Fin 2 => Fin 2) := by
  intro h
  have hm : copyPerm (Fin 2 → Fin 2) 2 (Equiv.swap 0 1) basisConfig ≠ basisConfig := by
    intro he
    have hh := congrFun (congrFun he 0) 0
    norm_num [copyPerm_apply, basisConfig] at hh
  have hh := congrFun (h (Equiv.swap 0 1)) basisConfig
  simp only [permOp_mulVec, Function.comp_apply, ← map_inv, Equiv.swap_inv] at hh
  simp [hm] at hh

-- The exact complementary central-projector identity retains the symmetric projection.
example (l : IrrepLabel (Equiv.Perm (Fin 2))) :
    labelProj (subsystemPerm 2 (fun _ : Fin 2 => Fin 2) {0}) l *
        symProj (copyPerm (Fin 2 → Fin 2) 2) =
      labelProj (subsystemPerm 2 (fun _ : Fin 2 => Fin 2) {1}) l *
        symProj (copyPerm (Fin 2 → Fin 2) 2) := by
  have hc : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  simpa only [hc] using labelProj_mul_symProj_compl
    (fun _ : Fin 2 => Fin 2) 2 ({0} : Finset (Fin 2)) l

private def scanner : CollarScan (Fin 3) (Fin 1) where
  graph := ⊤
  A := Finset.univ
  depth x := if x = 0 then 0 else if x = 1 then 5 else 20
  anchor _ := 1
  n := 3
  m := 2
  K := 2
  D := 1
  r₀ := 1
  C₁ := 1

private def firstHistory : History scanner.K scanner.m scanner.M 0 :=
  (fun _ => ⟨0, by decide⟩, Fin.elim0)

private def secondHistory : History scanner.K scanner.m scanner.M 1 :=
  (fun _ => ⟨1, by decide⟩,
    fun _ _ => (true, ⟨0, by norm_num [scanner, CollarScan.M, chargeSlotCount]⟩))

-- Independent offsets/times and all four statuses use the same actual scanner.
example (before before' : Bool) (replicas : ℕ) :
    Commute
      (symBandMetric (fun _ : Fin 3 ⊕ Bool => 2) (1 / 10) replicas
        (scanner.quantumHistoryPartition firstHistory ⟨0, by decide⟩ before))
      (symBandMetric (fun _ : Fin 3 ⊕ Bool => 2) (1 / 10) replicas
        (scanner.quantumHistoryPartition secondHistory ⟨1, by decide⟩ before')) :=
  scanner.commute_quantumHistoryPartition firstHistory secondHistory
    ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) before before' _ (by norm_num) replicas

-- A nonempty physical move sends only the middle site to the near side, retaining C and R.
example :
    let σ : PhysicalPartition (Fin 2) := fun x => if x = 0 then some false else none
    (augmentedMove σ false {1}).apply (augmentedPartition σ) =
      augmentedPartition (fun _ => some false) := by
  dsimp only
  rw [augmentedMove_apply]
  congr 1
  funext x
  fin_cases x <;> simp [assign]

-- Caller-supplied trees are not assumed to carry physical uniform weights.
example (histTree : Matrix.MeanTree (History scanner.K scanner.m scanner.M 0))
    (choiceTree : History scanner.K scanner.m scanner.M 0 →
      Matrix.MeanTree (ChargeChoices scanner.K scanner.M)) (replicas : ℕ) :
    (scanner.chargeTransportData histTree choiceTree).CrossBandCommute
      (fun _ : Fin 3 ⊕ Bool => 2) (1 / 10) replicas :=
  scanner.chargeTransportData_crossBandCommute histTree choiceTree _ (by norm_num) replicas

end TNLeanTest.PhysicalBandCommutation
