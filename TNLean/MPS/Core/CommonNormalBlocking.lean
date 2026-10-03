/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain

/-!
# Common physical blocking for normal tensors

The quantum Wielandt bound gives an injective blocking length depending only
on a bound for the bond dimension. A trace-preserving gauge permits the bound
to be applied to every normalized normal tensor, and injectivity is preserved
by transport through this gauge.

Source context: arXiv:1606.00608, lines 318–344, and quantum Wielandt theory.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

namespace MPSTensor

/-- A normalized normal tensor is block injective at length D^4. Source:
arXiv:1606.00608, lines 318–344, using the quantum Wielandt bound. -/
theorem IsNormalTensor.isNBlkInjective_pow_four {d D : ℕ} {A : MPSTensor d D}
    (hA : IsNormalTensor A) : Kraus.IsNBlkInjective A (D ^ 4) := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨σ, _, _, hTP, hGauge, _, _⟩ := hA.exists_tpGauge
  have hNormal := isNormal_of_gaugeEquiv hA.isNormal hGauge
  exact isNBlkInjective_of_gaugeEquiv
    (isNBlkInjective_pow_four_of_isNormal_leftCanonical _ hTP hNormal) hGauge.symm

/-- A bound K on the bond dimension gives the common injective block length K^4.
Source: arXiv:1606.00608, lines 318–344, bounded common physical blocking. -/
theorem IsNormalTensor.blockTensor_isInjective_of_bondDim_le
    {d D K : ℕ} {A : MPSTensor d D} (hA : IsNormalTensor A) (hDK : D ≤ K) :
    Kraus.IsInjective (MPSTensor.blockTensor A (K ^ 4)) := by
  have hD : 0 < D := Nat.pos_of_ne_zero hA.bondDim_ne_zero
  exact (isNBlkInjective_iff_blockTensor_isInjective A (K ^ 4)).1
    (isNBlkInjective_of_le (Nat.pow_pos hD) hA.isNBlkInjective_pow_four
      (Nat.pow_le_pow_left hDK 4))

end MPSTensor
