/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceUCompleteNetwork

/-!
# Transfer-power adapter for the paper source gate u

This module converts a supplied normalized transfer-matrix power at length
\(J\) into the direct double-layer fixed pair at length \(JD^2\), then applies
the arbitrary-interior complete-network theorem for the paper gate
\(u=Y_2\mathbin{-}Y_1\).

**Scope restriction (supplied stabilized fixed pair):** the theorem assumes the
raw rank-one transfer identity and the source's diagonal canonical-form-II
coordinates explicitly.  It keeps `SourceFactors U ρ`; no source factor is
recomputed from \(\rho^{\mathsf T}\).  Documented in
`docs/paper-gaps/mpu_canonical_form_full_support.tex` and
`docs/paper-gaps/mpu_source_cut_orientation.tex`.

Source: arXiv:1703.09188, equations `Erightleft`, `X1X2b`, and `uUnitary`,
and Lemma `lemuisometry` (lines 269--280 and 487--557).
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

namespace SourceFactors

/-- A trace-one transfer fixed pair at exponent \(J\) gives the normalized
source-$u$ input-tail identity with one length-\(JD^2\) interior and two
retained one-site endpoints.

Source: CPSV17 equation `uUnitary` and Lemma `lemuisometry` (lines 545--557),
with the fixed point in the diagonal coordinates of lines 269--280. -/
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
  exact sourceU_gram_eq_normalized_input_tail U S hρdiag K hK p q

end SourceFactors

end MPOTensor
