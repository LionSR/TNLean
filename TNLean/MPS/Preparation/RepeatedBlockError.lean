/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RepeatedBlockSum

/-!
# The overlap of the corrected approximating state

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1') measure the
error of an approximating state `φ~_N` by `ε = 1 - |⟨φ~_N|φ_N⟩|`. This file defines the overlap
`⟨φ~_N|φ_N⟩` for the corrected approximating state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` of
`TNLean.MPS.Preparation.RepeatedBlockSum` (`copyApproxOverlap`) and writes it as the unnormalized
overlap divided by the two norms (`copyApproxOverlap_eq`). The error bounds are
`MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum` and its corollaries in
`TNLean.MPS.Preparation.BlockSumError`.

**Local fix (corrected fixed-point state):** the approximating state is the corrected state of
`TNLean.MPS.Preparation.RepeatedBlockSum`, not the state of eq. (S7), which fails for `m_j ≥ 2`.
Documented in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

## Main declarations

* `MPSTensor.copyApproxOverlap` — the overlap of the corrected approximating state with `φ_N`.
* `MPSTensor.copyApproxOverlap_eq` — the overlap as the unnormalized overlap divided by the norms.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, Lemma 1'(ii) (`eq:fid_err_gen_non_normal`).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}

/-! ### The overlap -/

/-- The overlap `⟨φ~_N|φ_N⟩` of the normalized corrected approximating state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` with the normalized periodic state `φ_N` of `A` on `N = qM` sites
read as `M` blocks of `q` sites; the error of arXiv:2307.01696, Supplemental Material,
Lemma 1', is `ε = 1 - |⟨φ~_N|φ_N⟩|`. -/
noncomputable def copyApproxOverlap (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) : ℂ :=
  ∑ τ, star (((Real.sqrt (∑ τ', ‖copyApproxVector A q M α L σ τ'‖ ^ 2) : ℂ)⁻¹) *
      copyApproxVector A q M α L σ τ) *
    normalizedMPVState A (M * q) (blockedConfigEquiv d M q τ)

/-- The overlap is the unnormalized overlap divided by the two norms. -/
theorem copyApproxOverlap_eq (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    copyApproxOverlap A q M α L σ =
      ((Real.sqrt (∑ τ, ‖copyApproxVector A q M α L σ τ‖ ^ 2) : ℂ)⁻¹ *
        (‖mpvState A (M * q)‖ : ℂ)⁻¹) *
        ∑ τ, star (copyApproxVector A q M α L σ τ) * mpv A (blockedConfigEquiv d M q τ) := by
  rw [copyApproxOverlap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [normalizedMPVState, star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal,
    PiLp.smul_apply, smul_eq_mul, mpvState_apply]
  ring

end MPSTensor
