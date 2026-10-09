/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Simple

/-!
# Simplicity of tensors with diagonal rank-one double layers

Suppose the double-layer letters of a tensor are diagonal in the physical indices and of rank
one, \(W^{ij}=\delta_{ij}|X_i)(Y_i|\). Then the two simplicity identities of
arXiv:1703.09188, Definition III.2, reduce to scalar identities: with boundary vectors `a`, `b`,
\[
  (a|X_i)(Y_i|b)=1, \qquad (Y_i|X_k)=(Y_i|b)(a|X_k)
\]
for all physical indices `i`, `k`. This is the reduction used for the blocked
next-nearest-neighbour controlled-\(Z\) tensor (chapter Example 4.9) and has the same form as
the simplicity of the shifts.

## Main results

* `MPOTensor.isMPUSimple_of_rankOne_diagonal`: the reduction above.
-/

open scoped Matrix
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- **Simplicity from diagonal rank-one double-layer letters.** If the double-layer letters are
\(W^{ij}=\delta_{ij}|X_i)(Y_i|\) and the boundary vectors `a`, `b` satisfy
\((Y_i|X_k)=(Y_i|b)(a|X_k)\) and \((a|X_i)(Y_i|b)=1\) for all `i`, `k`, then `U` is simple with
witnesses `a`, `b`.

Source: arXiv:1703.09188, Definition III.2, equations `simple1` and `simple2`, lines 363--374;
the reduction is the one used for chapter Example 4.9 (next-nearest-neighbour controlled-\(Z\)). -/
theorem isMPUSimple_of_rankOne_diagonal {U : MPOTensor d D} (X Y : Fin d → Fin (D * D) → ℂ)
    (a b : Fin (D * D) → ℂ)
    (hW : ∀ i j, doubleLayerTensor U i j = if i = j then vecMulVec (X i) (Y i) else 0)
    (hYX : ∀ i k, Y i ⬝ᵥ X k = (Y i ⬝ᵥ b) * (a ⬝ᵥ X k))
    (hab : ∀ i, (a ⬝ᵥ X i) * (Y i ⬝ᵥ b) = 1) :
    IsMPUSimple U := by
  refine ⟨a, b, fun i j ↦ ?_, fun i j k l ↦ ?_⟩
  · rw [hW]
    split_ifs with hij
    · subst hij
      rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, mul_comm, hab]
    · simp
  · rw [hW i j, hW k l]
    split_ifs with hij hkl hkl
    · subst hij hkl
      rw [vecMulVec_mul_vecMulVec, Matrix.mul_assoc, vecMulVec_mul_vecMulVec,
        vecMulVec_mul_vecMulVec, hYX, mul_smul]
    all_goals simp

end MPOTensor
