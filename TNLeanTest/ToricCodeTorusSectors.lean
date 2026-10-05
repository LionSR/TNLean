/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.ToricCodeTorusAmplitudes

/-!
# Physical seam-sign tests for the primal toric-code torus

A single horizontal or vertical winding on a 3 × 3 torus distinguishes the
corresponding Pauli-Z closure. The other closure contributes no sign.
-/

open TNLean.PEPS
open scoped BigOperators

private theorem prod_zmod_three (f : ZMod 3 → ℂ) :
    (∏ i, f i) = f 0 * f 1 * f 2 := by
  exact Fin.prod_univ_three f

private def horizontalProbe (v : TorusVertex 3 3) :
    ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup :=
  let z : ToricCodeGroup := if v.2 = 0 then Multiplicative.ofAdd (1 : ZMod 2) else 1
  (1, 1, z, z)

private def verticalProbe (v : TorusVertex 3 3) :
    ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup :=
  let z : ToricCodeGroup := if v.1 = 0 then Multiplicative.ofAdd (1 : ZMod 2) else 1
  (1, z, z, 1)

example : IsToricCodeBondCompatible horizontalProbe := by unfold IsToricCodeBondCompatible; decide
example : IsToricCodeBondCompatible verticalProbe := by unfold IsToricCodeBondCompatible; decide

example : toricCodeTorusState 1 (Multiplicative.ofAdd (1 : ZMod 2)) horizontalProbe = -1 := by
  rw [toricCodeTorusState_apply, ite_eq_left (by unfold IsToricCodeBondCompatible; decide)]
  norm_num [toricCodeSeamPhase, horizontalProbe, quantumDoublePrimalLabels,
    Fintype.prod_prod_type, prod_zmod_three, ZMod.val_one_eq_one_mod,
    show (3 : ZMod 3) = 0 from by decide, show (2 : ZMod 3) ≠ 0 from by decide]
  decide

example : toricCodeTorusState (Multiplicative.ofAdd (1 : ZMod 2)) 1 horizontalProbe = 1 := by
  rw [toricCodeTorusState_apply, ite_eq_left (by unfold IsToricCodeBondCompatible; decide)]
  norm_num [toricCodeSeamPhase, horizontalProbe, quantumDoublePrimalLabels,
    Fintype.prod_prod_type, prod_zmod_three, ZMod.val_one_eq_one_mod,
    show (3 : ZMod 3) = 0 from by decide, show (2 : ZMod 3) ≠ 0 from by decide]

example : toricCodeTorusState (Multiplicative.ofAdd (1 : ZMod 2)) 1 verticalProbe = -1 := by
  rw [toricCodeTorusState_apply, ite_eq_left (by unfold IsToricCodeBondCompatible; decide)]
  norm_num [toricCodeSeamPhase, verticalProbe, quantumDoublePrimalLabels,
    Fintype.prod_prod_type, prod_zmod_three, ZMod.val_one_eq_one_mod,
    show (3 : ZMod 3) = 0 from by decide, show (2 : ZMod 3) ≠ 0 from by decide]
  decide

example : toricCodeTorusState 1 (Multiplicative.ofAdd (1 : ZMod 2)) verticalProbe = 1 := by
  rw [toricCodeTorusState_apply, ite_eq_left (by unfold IsToricCodeBondCompatible; decide)]
  norm_num [toricCodeSeamPhase, verticalProbe, quantumDoublePrimalLabels,
    Fintype.prod_prod_type, prod_zmod_three, ZMod.val_one_eq_one_mod,
    show (3 : ZMod 3) = 0 from by decide, show (2 : ZMod 3) ≠ 0 from by decide]
