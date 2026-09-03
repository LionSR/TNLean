/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ReflectedTransferKernel
import TNLean.MPS.MPU.SourceUCompleteNetwork

/-!
# Retained-interior contractions for the paper source gate u

This module isolates the finite contractions with one blocked interior of
length \(K=JD^2\) and two unblocked one-site endpoint letters.  The direct
fixed pair closes the normalized input tail.  Identifying that closure with
the transpose-oriented fixed pair of the staggered source-$u$ Gram network is
the remaining contraction in CPSV17 Lemma `lemuisometry`.

Source: arXiv:1703.09188, equation `uUnitary` and Lemma `lemuisometry`
(lines 545--557).
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- The normalized retained input tail closes against the untransposed supplied
fixed pair.  Only the length-\(K\) interior is blocked; the endpoint letters
remain the original one-site double-layer letters.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557).
-/
theorem normalized_mpo_input_tail_eq_fixed_pair_trace
    [NeZero d] [NeZero D]
    (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρtrace : Matrix.trace ρ = 1)
    (J : ℕ)
    (hpower :
      transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ J =
        Matrix.vecMulVec ρ.vec
          (1 : Matrix (Fin D) (Fin D) ℂ).vec)
    (p q : Fin d × Fin d) :
    let K := J * (D * D)
    let ρ' : Fin (D * D) → ℂ :=
      fun x ↦ ρ.vec (finProdFinEquiv.symm x)
    let Φ' : Fin (D * D) → ℂ :=
      fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec
        (finProdFinEquiv.symm x)
    ((d : ℂ)⁻¹) ^ K *
        ∑ τ : Fin K → Fin d, ∑ η : Fin (K + 2) → Fin d,
          star (mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))) *
          mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) =
      Matrix.trace
        (doubleLayerTensor U p.2 q.2 *
          Matrix.vecMulVec ρ' Φ' *
          doubleLayerTensor U p.1 q.1) := by
  dsimp only
  let K := J * (D * D)
  let ρ' : Fin (D * D) → ℂ :=
    fun x ↦ ρ.vec (finProdFinEquiv.symm x)
  let Φ' : Fin (D * D) → ℂ :=
    fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec
      (finProdFinEquiv.symm x)
  have htail := normalized_mpo_input_tail_eq_closed_doubleLayer_trace U K p q
  have hfixed := normalizedDiagonal_blockTensor_mul_sq_eq_vecMulVec_of_transfer_power
    U ρ hρtrace J hpower
  have hEK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec ρ' Φ' := by
    dsimp only [K, ρ', Φ'] at hfixed ⊢
    rw [doubleLayerTensor_blockTensor, normalizedDiagonal_blockTensor] at hfixed
    exact hfixed
  rw [htail, hEK]
  exact (Matrix.trace_mul_cycle
    (doubleLayerTensor U p.2 q.2)
    (Matrix.vecMulVec ρ' Φ')
    (doubleLayerTensor U p.1 q.1)).symm

end MPOTensor
