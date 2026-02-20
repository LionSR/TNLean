/-
Copyright (c) 2026 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.MPS.FixedPointInvariantProjection
import MPSLean.MPS.InvariantSubspaceDecomp

/-!
# Fixed point → 2-block decomposition

This file packages the canonical-form reduction step

> PSD fixed point → invariant support projection → two-block direct sum.

Concretely, if $\rho \succeq 0$ satisfies $E_A(\rho)=\rho$, then the support
projection $P := \mathrm{supp}(\rho)$ is invariant under the Kraus operators `(A i)`, i.e.
`(1 - P) * A i * P = 0`. Applying `exists_twoBlock_decomp_of_lowerZero`, we obtain an
explicit two-block block-diagonal tensor which is MPV-equivalent to `A`.

References:
* Perez-Garcia et al., quant-ph/0608197, Thm. 3 (support projection argument)
* Cirac et al., arXiv:1606.00608, §2.3
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- If `ρ` is a PSD fixed point of the transfer map, then `A` is MPV-equivalent to a
2-block block-diagonal tensor.

This is just the composition
`lowerZero_of_posSemidef_fixedPoint` + `exists_twoBlock_decomp_of_lowerZero`.
-/
theorem exists_twoBlock_decomp_of_posSemidef_fixedPoint
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ∃ (n m : ℕ) (hnm : n + m = D)
      (A₁ : MPSTensor d n) (A₂ : MPSTensor d m),
      SameMPV₂ A (twoBlockTensor (d := d) (n := n) (m := m) A₁ A₂) := by
  classical
  let P : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ_psd
  have hP : IsOrthogonalProjection P ∧ (∀ i : Fin d, (1 - P) * A i * P = 0) := by
    simpa [P] using
      (lowerZero_of_posSemidef_fixedPoint (d := d) (D := D) A ρ hρ_psd hρ_fix)
  exact exists_twoBlock_decomp_of_lowerZero (d := d) (D := D) A P hP.1 hP.2

end MPSTensor
