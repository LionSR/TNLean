/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoWindowOperatorForms

/-!
# Adjacent windows with an independent middle operator

All four window terms vanish. The independently supplied middle bulk operator
is the identity on its singleton support. Thus its value cannot be recovered
from a complementary sum of the window terms. The regional theorem is applied
at every local dimension, including zero.
-/

open Matrix QuantumCircuit
open TNLean.MPS.AreaLaw

/-- A middle bulk operator independent of the four zero window terms. -/
private noncomputable def middleOnlyFamily (q : ℕ) :
    ((Fin 2 ⊕ Fin 2) ⊕ Fin 3) → Matrix (Fin 5 → Fin q) (Fin 5 → Fin q) ℂ :=
  fun r ↦ if r = Sum.inr 1 then 1 else 0

-- The two windows touch, and the selected crossing edges are adjacent.
private noncomputable abbrev adjacentWindowsIndependentMiddle (q : ℕ) :=
  exists_threeSplit_two_window_factors (L := 5) (q := q) (ℓ := 1) (a := 0) (b := 2)
    (middleOnlyFamily q)
    (by intro r; simp [middleOnlyFamily])
    (by intro r; simp [middleOnlyFamily])
    (by simp [middleOnlyFamily])
    (by simpa [middleOnlyFamily] using
      one_mem_supportedOperators (d := q) (interval 5 2 3 : Set (Fin 5)))
    (by simp [middleOnlyFamily])
    (by decide) (by decide) (1 : Fin 2) 0

-- For qubits the middle bulk term is nonzero although every window term vanishes.
example : middleOnlyFamily 2 (Sum.inr 1) ≠ 0 := by
  simp [middleOnlyFamily]

-- At local dimension zero the global configuration type is empty.
private noncomputable abbrev zeroDimensionAdjacentWindows :=
  adjacentWindowsIndependentMiddle 0

-- The middle bulk support remains a singleton for the positive-dimensional example.
example : interval 5 2 3 = {(2 : Fin 5)} := by decide
