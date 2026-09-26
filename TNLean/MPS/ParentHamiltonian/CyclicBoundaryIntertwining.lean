/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryOverlap
import Mathlib.GroupTheory.OrderOfElement

/-!
# Cyclic propagation of boundary intertwiners

A boundary matrix which intertwines adjacent cyclic cuts commutes with every
word extending once around the cycle. This is the algebraic propagation step
in the periodic closure argument of PGVWC07, arXiv:quant-ph/0608197,
Theorem 12 (lines 1424--1458).
-/

namespace MPSTensor

/-- Propagating adjacent boundary intertwiners around one full cycle gives
commutation with every matrix word of that length. -/
theorem boundary_commutes_evalWord_of_cyclic_intertwining
    {d D N : ℕ} [NeZero N] (A : MPSTensor d D)
    (Y : Fin N → Matrix (Fin D) (Fin D) ℂ) (s : Fin N)
    (hStep : ∀ i a, Y i * A a = A a * Y (s + i))
    (ω : Fin N → Fin d) (i : Fin N) :
    Y i * Kraus.evalWord A (List.ofFn ω) =
      Kraus.evalWord A (List.ofFn ω) * Y i := by
  have hcycle : N • s = 0 := by simpa using (card_nsmul_eq_zero (x := s))
  have hpath := boundary_witness_product_of_adjacent_overlaps
    (A := A) (fun r : Fin (N + 1) ↦ Y (r.val • s + i)) ω ω
    (fun r : Fin N ↦ by
      simpa [succ_nsmul, add_assoc, add_comm, add_left_comm] using
        hStep (r.val • s + i) (ω r))
  simpa [hcycle] using hpath

end MPSTensor
