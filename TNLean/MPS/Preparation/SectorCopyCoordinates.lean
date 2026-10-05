/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.NonNormalCanonicalForm
import TNLean.MPS.Preparation.RepeatedBlockSum

/-!
# Copy coordinates of a sector decomposition

The assembled tensor of a sector decomposition is exactly the repeated block sum on its
canonical copy coordinates. This identifies the direct sum of arXiv:2307.01696,
Supplemental Material, eq. (S2), at the level of tensor entries, so its blocked physical
matrix and polar factors can be studied using the repeated-block formulas.

## Main declarations

* `MPSTensor.SectorDecomposition.copyWeights` packages the sector weights as copy weights.
* `MPSTensor.SectorDecomposition.bntWeight_copyWeights` identifies the power sums with
  the sector coefficients of eq. (S4).
* `MPSTensor.SectorDecomposition.copyCoord_disjoint` proves that distinct copies, including
  copies of the same block, occupy disjoint bond coordinates.
* `MPSTensor.SectorDecomposition.toTensor_eq_repeatedBlockSum` is the exact tensor identity.
-/

open scoped BigOperators Matrix
open Matrix

namespace MPSTensor

variable {d : ℕ}

private theorem toTensorFromBlocks_eq_sum_blockInclusion {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (s : Fin r) → MPSTensor d (dim s)) (i : Fin d) :
    toTensorFromBlocks μ A i =
      ∑ s, μ s • (blockInclusion dim s * A s i * (blockInclusion dim s)ᴴ) := by
  classical
  let dim' := fun s : Fin r => Fin (dim s)
  let e : (Σ s, dim' s) ≃ Fin (∑ s, dim s) := finSigmaFinEquiv
  let E := fun s => Matrix.sigmaBlockInclusion dim' s
  change Matrix.reindexLinearEquiv ℂ ℂ e e
      (Matrix.blockDiagonal' fun s => μ s • A s i) = _
  rw [Matrix.blockDiagonal'_eq_sum_sigmaBlockInclusion, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  change Matrix.reindexLinearEquiv ℂ ℂ e e (E s * (μ s • A s i) * (E s)ᴴ) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) e,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) (Equiv.refl _)]
  change blockInclusion dim s * (μ s • A s i) * (blockInclusion dim s)ᴴ = _
  rw [Matrix.mul_smul, Matrix.smul_mul]

namespace SectorDecomposition

/-- The nonzero weights of the retained copies in arXiv:2307.01696, eq. (S2),
with the positive multiplicities already supplied by the sector decomposition. -/
def copyWeights (P : SectorDecomposition d) : CopyWeights P.basisCount P.copies where
  weight := P.weight
  mult_pos := P.copies_pos
  weight_ne_zero := P.weight_ne_zero

/-- The copy-weight power sum is the sector coefficient
`βⱼ = ∑ₖ μ_{j,k}^N` of arXiv:2307.01696, eq. (S4). -/
@[simp]
theorem bntWeight_copyWeights (P : SectorDecomposition d) (N : ℕ) :
    bntWeight P.copyWeights N = P.coeff N :=
  rfl

/-- Distinct retained copies occupy disjoint bond coordinates in the direct sum of
arXiv:2307.01696, eq. (S2), even when they are copies of the same basis block. -/
theorem copyCoord_disjoint (P : SectorDecomposition d)
    (p p' : (j : Fin P.basisCount) × Fin (P.copies j)) (h : p ≠ p')
    (a : Fin (P.basisDim p.1)) (a' : Fin (P.basisDim p'.1)) :
    P.copyCoord p.1 p.2 a ≠ P.copyCoord p'.1 p'.2 a' := by
  intro heq
  have hflat := (Sigma.mk.inj_iff.1 (finSigmaFinEquiv.injective heq)).1
  exact h (P.flatIndexEquiv.injective hflat)

/-- The assembled sector tensor is exactly the repeated block sum of arXiv:2307.01696,
eq. (S2), on its canonical copy coordinates. This is equality of tensors, so the
identification also preserves the blocked physical matrix and its polar factors. -/
theorem toTensor_eq_repeatedBlockSum (P : SectorDecomposition d) :
    P.toTensor = repeatedBlockSum P.basis P.copyCoord P.copyWeights := by
  classical
  funext i
  rw [toTensor, toTensorFromBlocks_eq_sum_blockInclusion]
  unfold repeatedBlockSum
  rw [← Fintype.sum_sigma', ← Equiv.sum_comp P.flatIndexEquiv.symm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hι :
      coordEmbedding (P.copyCoord (P.flatIndexEquiv.symm s).1
        (P.flatIndexEquiv.symm s).2) = blockInclusion P.flatDim s := by
    ext x a
    have hs : P.flatIndexEquiv
        ⟨(P.flatIndexEquiv.symm s).1, (P.flatIndexEquiv.symm s).2⟩ = s :=
      P.flatIndexEquiv.apply_symm_apply s
    have hc : P.copyCoord (P.flatIndexEquiv.symm s).1
        (P.flatIndexEquiv.symm s).2 a = finSigmaFinEquiv ⟨s, a⟩ := by
      unfold copyCoord
      apply congrArg finSigmaFinEquiv
      exact Sigma.ext hs ((Fin.heq_ext_iff (congrArg P.flatDim hs)).2 rfl)
    rw [blockInclusion_apply P.flatDim s x a]
    simp only [coordEmbedding, Matrix.of_apply, hc]
  rw [hι]
  rfl

end SectorDecomposition

end MPSTensor
