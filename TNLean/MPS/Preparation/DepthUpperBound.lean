/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.BlockStatePreparation

/-!
# Preparing the uniform approximating state

The generic block-isometry circuit construction is re-exported from
`TNLean.MPS.Preparation.BlockStatePreparation`. This module identifies its equal-block,
fixed-point-pair case with `approximatingMPVState` and gives the depth bound `O(q)`.
The statements and the original import surface are preserved.

Source: arXiv:2307.01696, eqs. (10)–(12), Fig. 1 and the paragraph
"The sequential-RG circuit".
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder
open QuantumCircuit

namespace MPSPreparation

variable {d D M N r₁ : ℕ} {ℓ : Fin M → ℕ}

/-- For blocks of equal length `q` and the pair of the fixed point, the state
`(⊗ₖ V_k) ⊗ₖ |ω⟩` is the approximating state `|φ'_N⟩` of eq. (10) of arXiv:2307.01696. -/
theorem approximatingMPVState_eq_blockIsometryState (A : MPSTensor d D) {q : ℕ}
    (hB : Kraus.IsInjective (blockTensor A q)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (M : ℕ) [NeZero M]
    (hN : ∑ _ : Fin M, q = M * q) :
    approximatingMPVState A σ q M = blockIsometryState A (fixedPointPair σ) hN := by
  rw [(inner_approximatingMPVState_mpvState A hB hσ htr M).1]
  ext s
  rw [approximatingMPVStateRaw_apply, blockIsometryState_apply, mpv_approximatingTensor,
    blockedConfigEquiv_symm_eq_blockIndexEquiv q hN]

/-- **The approximating state is prepared in depth `O(q)`.** There is `C`, depending only on
`d` and `D`, such that for every tensor `A`, every `σ ≥ 0` with `Tr σ = 1`, every block length
`q ≥ 3D` for which the `q`-site blocked tensor is injective and every number of blocks `M ≥ 1`,
the approximating state `|φ'_N⟩` on `N = M q` sites is prepared in depth at most `C q` from a
product state.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1; this is
`MPSPreparation.exists_isPreparedInDepth_blockIsometryState` for blocks of equal length. -/
theorem exists_isPreparedInDepth_approximatingMPVState (d D : ℕ) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosSemidef →
      σ.trace = 1 → ∀ q, 3 * D ≤ q → Kraus.IsInjective (blockTensor A q) →
        ∀ (M : ℕ) [NeZero (M * q)],
          IsPreparedInDepth (C * q) fun s => approximatingMPVState A σ q M s := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_blockIsometryState d D
  refine ⟨C, fun A σ hσ htr q hq hinj M _ => ?_⟩
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hN : ∑ _ : Fin M, q = M * q := by simp
  rw [approximatingMPVState_eq_blockIsometryState A hinj hσ htr M hN]
  exact hC A (fixedPointPair σ) (by rw [fixedPointPair_norm_sq hσ, htr]) (fun _ => q) hN q
    (fun _ => hq) (fun _ => le_rfl) (fun _ => hinj)

end MPSPreparation
