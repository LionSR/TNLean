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

/-- **Strict dimension decrease**: If `ρ` is a PSD fixed point of the transfer map,
`ρ ≠ 0`, and `ρ` is not positive definite, then `A` is MPV-equivalent to a
two-block block-diagonal tensor where **both** block bond dimensions are
strictly less than `D`.

This is the key recursion step in the canonical form existence proof:
each iteration strictly reduces the bond dimension.

The proof composes:
1. `lowerZero_of_posSemidef_fixedPoint` — support projection is invariant,
2. `supportProj_ne_zero_of_ne_zero` — `P ≠ 0` from `ρ ≠ 0`,
3. `supportProj_ne_one_of_not_posDef` — `P ≠ 1` from `¬ρ.PosDef`,
4. `exists_twoBlock_decomp_of_lowerZero_strict` — strict dimension bounds.

References:
* Perez-Garcia et al., quant-ph/0608197, Thm. 3
* Cirac et al., arXiv:1606.00608, §2.3
-/
theorem exists_twoBlock_decomp_of_posSemidef_fixedPoint_strict
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (hρ_ne : ρ ≠ 0)
    (hρ_not_pd : ¬ ρ.PosDef) :
    ∃ n m : ℕ, ∃ hnm : n + m = D, n < D ∧ m < D ∧
      ∃ (A₁ : MPSTensor d n) (A₂ : MPSTensor d m),
        SameMPV₂ A (twoBlockTensor (d := d) (n := n) (m := m) A₁ A₂) := by
  -- Step 1: obtain the invariant support projection
  let P : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ_psd
  have hP_inv : IsOrthogonalProjection P ∧ (∀ i : Fin d, (1 - P) * A i * P = 0) := by
    simpa [P] using
      (lowerZero_of_posSemidef_fixedPoint (d := d) (D := D) A ρ hρ_psd hρ_fix)
  -- Step 2: P ≠ 0 from ρ ≠ 0
  have hP0 : P ≠ 0 := supportProj_ne_zero_of_ne_zero ρ hρ_psd hρ_ne
  -- Step 3: P ≠ 1 from ¬ρ.PosDef
  have hP1 : P ≠ 1 := supportProj_ne_one_of_not_posDef ρ hρ_psd hρ_not_pd
  -- Step 4: apply strict decomposition
  exact exists_twoBlock_decomp_of_lowerZero_strict A P hP_inv.1 hP_inv.2 hP0 hP1

end MPSTensor
