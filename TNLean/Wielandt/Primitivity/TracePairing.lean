/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.TracePairing
import QICLean.MPS.Core.TransferChannel

/-!
# Trace-pairing identity for the Wielandt primitivity route

This file contains the trace identity used in the proof that strong
irreducibility implies eventual full Kraus rank.
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder NNReal
open Matrix Filter

namespace MPSTensor

variable {d D : ℕ}

/-- **Trace-pairing identity for transfer-map powers.**

The sum of squared absolute traces `∑_σ |tr(B† A_σ)|²` equals the `.re` of a
bilinear form in `B` built from the iterated transfer map and matrix units.

This is the core algebraic identity used in the proof of
**Proposition 3(c)→(b)** of arXiv:0909.5347 (the "quantum Wielandt" paper). -/
theorem sum_normSq_trace_conjTranspose_mul_evalWord
    [NeZero D]
    (A : MPSTensor d D) (n : ℕ)
    (B : Matrix (Fin D) (Fin D) ℂ) :
    (∑ σ : Fin n → Fin d,
        ‖Matrix.trace (Bᴴ * evalWord A (List.ofFn σ))‖ ^ 2 : ℝ) =
      (∑ i : Fin D, ∑ k : Fin D,
        (Bᴴ * ((transferMap (d := d) (D := D) A) ^ n)
          (Matrix.single i k 1) * B) i k).re := by
  simpa only [Kraus.mapLM_eq_transferMap] using
    Kraus.sum_normSq_trace_conjTranspose_mul_evalWord A n B

end MPSTensor
