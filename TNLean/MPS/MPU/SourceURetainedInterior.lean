/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ReflectedTransferKernel
import TNLean.MPS.MPU.SourceUCompleteNetwork

/-!
# Retained-interior contraction for the paper source gate u

In the diagonal canonical-form-II coordinates fixed in CPSV17, the right
transfer fixed point satisfies \(\rho^{\mathsf T}=\rho\). This identifies the
transpose-oriented closure of the source-gate Gram matrix with the direct
fixed pair supplied by the transfer power. The normalized input tail then gives
the complete network in Lemma `lemuisometry`.

Source: arXiv:1703.09188, equations `Erightleft`, `X1X2b`, and `uUnitary`,
and Lemma `lemuisometry` (lines 269--280 and 487--557).
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- If the supplied source weight is symmetric, its source-$u$ Gram matrix is
the closed direct double-layer trace for any matching fixed pair. The source
factors remain those constructed from `ρ`.

Source: CPSV17 equations `Erightleft`, `X1X2b`, and `uUnitary`, and Lemma
`lemuisometry` (lines 269--280 and 487--557). -/
theorem sourceU_gram_eq_closed_doubleLayer_trace_of_isSymm
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (hρ : ρ.IsSymm) (K : ℕ)
    (hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec
        (fun x ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec
          (finProdFinEquiv.symm x)))
    (p q : Fin d × Fin d) :
    (∑ lr, sourceU U S lr q * star (sourceU U S lr p)) =
      Matrix.trace
        (doubleLayerTensor U p.1 q.1 * doubleLayerTensor U p.2 q.2 *
          normalizedDiagonal (doubleLayerTensor U) ^ K) := by
  rw [sourceU_gram_eq_transpose_fixed_pair_trace, hρ.eq, ← hK]
  exact Matrix.trace_mul_cycle _ _ _

/-- In diagonal canonical-form-II coordinates, the source-$u$ Gram matrix is
the normalized input-first contraction with one length-\(JD^2\) interior and
two retained one-site endpoints.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557).
-/
theorem sourceU_gram_eq_normalized_mpo_input_tail_of_isDiag
    [NeZero d] [NeZero D]
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (hρdiag : ρ.IsDiag) (hρtrace : Matrix.trace ρ = 1)
    (J : ℕ)
    (hpower :
      transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ J =
        Matrix.vecMulVec ρ.vec
          (1 : Matrix (Fin D) (Fin D) ℂ).vec)
    (p q : Fin d × Fin d) :
    let K := J * (D * D)
    (∑ lr, sourceU U S lr q * star (sourceU U S lr p)) =
      ((d : ℂ)⁻¹) ^ K *
        ∑ τ : Fin K → Fin d, ∑ η : Fin (K + 2) → Fin d,
          star (mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (p, τ))) *
          mpo U (K + 2) η
            ((finAddTwoArrowEquiv (Fin d) K).symm (q, τ)) := by
  dsimp only
  let K := J * (D * D)
  let ρ' : Fin (D * D) → ℂ :=
    fun x ↦ ρ.vec (finProdFinEquiv.symm x)
  let Φ' : Fin (D * D) → ℂ :=
    fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec
      (finProdFinEquiv.symm x)
  have hfixed := normalizedDiagonal_blockTensor_mul_sq_eq_vecMulVec_of_transfer_power
    U ρ hρtrace J hpower
  have hK : normalizedDiagonal (doubleLayerTensor U) ^ K =
      Matrix.vecMulVec ρ' Φ' := by
    dsimp only [K, ρ', Φ'] at hfixed ⊢
    rw [doubleLayerTensor_blockTensor, normalizedDiagonal_blockTensor] at hfixed
    exact hfixed
  calc
    (∑ lr, sourceU U S lr q * star (sourceU U S lr p)) =
        Matrix.trace
          (doubleLayerTensor U p.1 q.1 * doubleLayerTensor U p.2 q.2 *
            normalizedDiagonal (doubleLayerTensor U) ^ K) :=
      sourceU_gram_eq_closed_doubleLayer_trace_of_isSymm U S hρdiag.isSymm K hK p q
    _ = _ := (normalized_mpo_input_tail_eq_closed_doubleLayer_trace U K p q).symm

/-- In the diagonal canonical-form-II coordinates of CPSV17, the paper source
gate \(u=Y_2\mathbin{-}Y_1\) is an isometry.

Source: CPSV17 Lemma `lemuisometry` and equation `uUnitary` (lines 545--557).
-/
theorem sourceU_isIsometry_of_isDiag
    [NeZero d] [NeZero D] (hU : IsMPU U)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (hρdiag : ρ.IsDiag) (hρtrace : Matrix.trace ρ = 1)
    (J : ℕ)
    (hpower :
      transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ J =
        Matrix.vecMulVec ρ.vec
          (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    (sourceU U S).IsIsometry := by
  rw [Matrix.IsIsometry]
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  let K := J * (D * D)
  have hgram := sourceU_gram_eq_normalized_mpo_input_tail_of_isDiag
    U S hρdiag hρtrace J hpower p q
  dsimp only at hgram
  rw [hU.normalized_mpo_tail_isometry K p q] at hgram
  simpa only [mul_comm] using hgram

end SourceFactors

end MPOTensor
