/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.GHZSectorParent

/-! Source-tensor regressions for equal parents and incompatible periodic sector weights. -/

open Matrix MPSTensor QuantumCircuit
open scoped InnerProductSpace

-- The nearest-neighbour parent Hamiltonians really are equal at every size.
example (N : ℕ) :
    parentHamiltonian repeatedBlockTensor 2 N = parentHamiltonian ghzTensor 2 N :=
  parentHamiltonian_repeatedBlockTensor_eq_ghzTensor 2 N

-- A much smaller requested error forces linear depth on actual normalized periodic vectors.
example {N T : ℕ} [NeZero N] {U : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hU : IsLocalCircuitOfDepth U T)
    (herr : 1 - ‖⟪Matrix.toEuclideanLin U (normalizedMPVState repeatedBlockTensor N),
      normalizedMPVState ghzTensor N⟫_ℂ‖ ≤ (1 : ℝ) / 10000) : N ≤ 4 * T + 4 :=
  length_le_of_repeatedBlockTensor_infidelity_lt hU (lt_of_le_of_lt herr (by norm_num))

-- Multiplicity is independent of length, including lengths not divisible by a block size.
example : (mpv repeatedBlockTensor : NSiteSpace 2 7) = ghzState (M := 7) ![2, 1] :=
  mpv_repeatedBlockTensor_eq_ghzState 7
