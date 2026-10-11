/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.HistoryMeanTree

/-!
# Branching history-tree regressions

Two offset choices, four charge choices, two rounds, and guarded stock axioms.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw.Scan
open scoped unitInterval

/- Two offset choices, four charge labels, and two charge rounds: this is
not a singleton or zero-band fixture. Both old and new terminal masses are tested. -/
private def h0 : History 1 2 2 0 := (fun _ ↦ 1, Fin.elim0)
private def c0 : ChargeChoices 1 2 := fun _ ↦ (false, 0)
private def c1 : ChargeChoices 1 2 := fun _ ↦ (true, 1)

example : (chargeChoiceTree 1 2 (by decide)).weight c0 = 1 / 4 := by
  rw [chargeChoiceTree_weight]
  norm_num [chargeWeight]

example : (historyMeanTree 1 2 2 (by decide) (by decide) 2).weight
    (extendHistory (extendHistory h0 c0) c1) = 1 / 32 := by
  rw [historyMeanTree_weight]
  norm_num [historyWeight]

example : (Matrix.MeanTree.interpTree (historyMeanTree 1 2 2 (by decide) (by decide) 1)
    (fun _ ↦ chargeChoiceTree 1 2 (by decide))
    (⟨1 / 3, by constructor <;> norm_num⟩ : unitInterval)).weight
      ⟨extendHistory h0 c0, some c1⟩ = 1 / 96 := by
  rw [historyMeanTree_interp_weight_new]
  norm_num [historyWeight, chargeWeight]

example : (Matrix.MeanTree.interpTree (historyMeanTree 1 2 2 (by decide) (by decide) 1)
    (fun _ ↦ chargeChoiceTree 1 2 (by decide))
    (⟨1 / 3, by constructor <;> norm_num⟩ : unitInterval)).weight
      ⟨extendHistory h0 c0, none⟩ = 1 / 12 := by
  rw [historyMeanTree_interp_weight_old]
  norm_num [historyWeight]

example (B : History 1 2 2 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (historyMeanTree 1 2 2 (by decide) (by decide) 2).eval B =
      (historyMeanTree 1 2 2 (by decide) (by decide) 1).eval
        (fun h ↦ (chargeChoiceTree 1 2 (by decide)).eval (fun c ↦ B (extendHistory h c))) :=
  historyMeanTree_eval_succ 1 2 2 (by decide) (by decide) 1 B

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.historyMeanTree_weight'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.historyMeanTree_weight

set_option linter.hashCommand false in
/-- info: 'TNLean.PEPS.AreaLaw.Scan.charge_interpRoot_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.charge_interpRoot_one
