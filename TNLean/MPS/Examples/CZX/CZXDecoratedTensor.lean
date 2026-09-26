/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.CZX.CZXReviewTensor
import TNLean.MPS.MPDO.CZXTensor
import TNLean.MPS.MPU.GroupCocycleMPO.Instances

/-!
# The decorated CZX matrix product unitary: the tensor and its operator

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section III.D, "The simplest example",
`Papers/2405.00439/MPU-DW.tex` lines 1128–1180: the CZX symmetry
`U_{CZX} = ∏_i Z_i CZ_{i,i+1} ∏_i X_i` of Chen, Liu and Wen (arXiv:1106.4752), written with
delta tensors and the unnormalized Hadamard matrix `H = [[1,1],[1,-1]]` as the bond-two tensor
drawn at lines 1164–1180: the input passes through `X`, is copied to the left bond through
`H` and to the right bond, and leaves through `Z`.

**Formalized here.** The printed tensor, its periodic operator
`U |t⟩ = (-1)^{∑_n s_n s_{n+1} + ∑_n s_n} |s⟩` with `s` the spin flip of `t`, the identity
`U = Z^{⊗ N} · D_N X^{⊗ N}` relating it to the CZX operator of the review arXiv:2011.12127,
the order-two relation `U^2 = 1` at every positive length, unitarity, and normality of the
tensor (line 1181: "this tensor becomes injective when blocking two sites").

The same Z-decorated one-site tensor, with its two bonds exchanged, is
`MPOTensor.CZX.decoratedSiteTensor` of `TNLean.MPS.MPDO.CZXTensor` (arXiv:2502.20257); that
tensor is the review's tensor with a Pauli `Z` on the output.

## Main definitions

* `CZXCompression.czxDecoratedIntTensor`, `CZXCompression.czxDecoratedTensor`: the tensor of
  lines 1164–1180, over the integers and over the complexes.
* `CZXCompression.spinParity`, `CZXCompression.globalZ`: the number of ones of a
  configuration and the diagonal operator `Z^{⊗ N}`.

## Main results

* `CZXCompression.mpo_czxDecoratedTensor_apply`: the periodic operator entrywise.
* `CZXCompression.mpo_czxDecoratedTensor_eq`: `U = Z^{⊗ N} O(A)` with `O(A)` the review's
  operator.
* `CZXCompression.mpo_czxDecoratedTensor_mul_self`: `U^2 = 1` at every positive length.
* `CZXCompression.czxDecoratedTensor_isMPUPos`: the tensor is a matrix product unitary.
* `CZXCompression.czxDecoratedMPS_isNormal`: the tensor is normal.
* `CZXCompression.czxDecoratedTensor_eq_transpose`,
  `CZXCompression.decoratedSiteTensor_eq_smul_reviewCZXTensor`: the relations to
  `MPOTensor.CZX.decoratedSiteTensor`.

## References

- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Domain wall excitations for anomalous matrix product unitary symmetries*
- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752) -- X. Chen, Z.-X. Liu, X.-G. Wen,
  *Two-dimensional symmetry-protected topological orders and their protected gapless edge
  excitations*
-/

noncomputable section

open scoped BigOperators Matrix

namespace CZXCompression

open MPSTensor

/-! ### The tensor -/

/-- The integer matrices of the decorated CZX tensor: `T^{01} = [[1,0],[1,0]]`,
`T^{10} = [[0,-1],[0,1]]`, and `T^{00} = T^{11} = 0`, the first physical index being the
output.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1164–1180: at input `j` the
Pauli `X` gives `x = 1 - j`, the left bond `l` contributes `H_{l x} = (-1)^{l x}`, the right
bond carries `x`, and the Pauli `Z` gives the output `x` with the sign `(-1)^x`. -/
def czxDecoratedIntTensor : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0, 1 => !![1, 0; 1, 0]
  | 1, 0 => !![0, -1; 0, 1]
  | _, _ => 0

/-- The decorated CZX tensor as a matrix product operator tensor, the first physical index
being the output.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1164–1180. -/
def czxDecoratedTensor : MPOTensor 2 2 := fun i j => complexOfInt (czxDecoratedIntTensor i j)

/-- The entries of the decorated tensor: the output `i` is the flip of the input `j`, the
outgoing bond carries `i`, and the incoming bond `l` contributes `(-1)^{l i}`, times the sign
`(-1)^i` of the Pauli `Z`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1140–1180. -/
theorem czxDecoratedTensor_apply (i j l r : Fin 2) :
    czxDecoratedTensor i j l r =
      if i = j.rev ∧ r = i then (-1 : ℂ) ^ (l.val * i.val + i.val) else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [czxDecoratedTensor, czxDecoratedIntTensor, complexOfInt, Fin.rev]

/-- Bridge: the decorated tensor is the one-site tensor `MPOTensor.CZX.decoratedSiteTensor`
of arXiv:2502.20257 with every matrix transposed, that is, with its two bonds exchanged. -/
theorem czxDecoratedTensor_eq_transpose (i j : Fin 2) :
    czxDecoratedTensor i j = (MPOTensor.CZX.decoratedSiteTensor i j)ᵀ := by
  ext l r
  rw [Matrix.transpose_apply, czxDecoratedTensor_apply]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [MPOTensor.CZX.decoratedSiteTensor, Fin.rev]

/-- Bridge: `MPOTensor.CZX.decoratedSiteTensor` is the review's CZX tensor with a Pauli `Z` on
the output, `(-1)^i` times the letter at output `i`. -/
theorem decoratedSiteTensor_eq_smul_reviewCZXTensor (i j : Fin 2) :
    MPOTensor.CZX.decoratedSiteTensor i j = ((-1 : ℂ) ^ i.val) • reviewCZXTensor i j := by
  ext l r
  rw [Matrix.smul_apply, reviewCZXTensor_apply]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [MPOTensor.CZX.decoratedSiteTensor, Fin.rev]

/-! ### Normality -/

private theorem czxDecoratedMPS_one :
    czxDecoratedTensor.toMPSTensor 1 = complexOfInt !![1, 0; 1, 0] := rfl

private theorem czxDecoratedMPS_two :
    czxDecoratedTensor.toMPSTensor 2 = complexOfInt !![0, -1; 0, 1] := rfl

/-- Each matrix unit is a half-sum or a half-difference of two length-two words. -/
private theorem czxDecorated_single (i j : Fin 2) :
    ∃ a b c e : Fin 4, ∃ u v : ℂ, Matrix.single i j (1 : ℂ) =
      u • (czxDecoratedTensor.toMPSTensor a * czxDecoratedTensor.toMPSTensor b) +
        v • (czxDecoratedTensor.toMPSTensor c * czxDecoratedTensor.toMPSTensor e) := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, 1, 2, 1, 1 / 2, -1 / 2, ?_⟩
    rw [czxDecoratedMPS_one, czxDecoratedMPS_two, ← complexOfInt_mul, ← complexOfInt_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt, Matrix.mul_apply]
  · refine ⟨1, 2, 2, 2, -1 / 2, -1 / 2, ?_⟩
    rw [czxDecoratedMPS_one, czxDecoratedMPS_two, ← complexOfInt_mul, ← complexOfInt_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt, Matrix.mul_apply]
  · refine ⟨1, 1, 2, 1, 1 / 2, 1 / 2, ?_⟩
    rw [czxDecoratedMPS_one, czxDecoratedMPS_two, ← complexOfInt_mul, ← complexOfInt_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt, Matrix.mul_apply]
  · refine ⟨2, 2, 1, 2, 1 / 2, -1 / 2, ?_⟩
    rw [czxDecoratedMPS_one, czxDecoratedMPS_two, ← complexOfInt_mul, ← complexOfInt_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt, Matrix.mul_apply]

/-- **The decorated CZX tensor is normal**: its length-two words span the full two-by-two
matrix algebra. This is the source's statement that the tensor "becomes injective when blocking
two sites".

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 1181. -/
theorem czxDecoratedMPS_isNormal : Kraus.IsNormal czxDecoratedTensor.toMPSTensor :=
  MPSTensor.isNormal_of_single_eq_two_words _ czxDecorated_single

/-! ### The periodic operator -/

/-- The number of ones of a configuration, the exponent of the sign of `Z^{⊗ N}`. -/
def spinParity {N : ℕ} (t : Fin N → Fin 2) : ℕ := ∑ n, (t n).val

/-- The diagonal operator `Z^{⊗ N}` on a chain of `N` qubits. -/
def globalZ (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.diagonal fun t ↦ (-1 : ℂ) ^ spinParity t

/-- A configuration and its spin flip have `N` ones between them. -/
theorem spinParity_spinFlip_add {N : ℕ} (t : Fin N → Fin 2) :
    spinParity (spinFlip N t) + spinParity t = N := by
  have h : ∀ a : Fin 2, a.rev.val + a.val = 1 := by decide
  simp only [spinParity, spinFlip_apply, ← Finset.sum_add_distrib, h]
  simp

variable {N : ℕ} [NeZero N]

/-- **The periodic operator of the decorated tensor entrywise**: the entry at `(s, t)`
vanishes unless `s` is the spin flip of `t`, and then equals the controlled-`Z` sign of `s`
times the sign `(-1)^{∑_n s_n}` of `Z^{⊗ N}`. The bond configuration is forced to be
`g_n = s_{n-1}`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1128–1129 and 1164–1180. -/
theorem mpo_czxDecoratedTensor_apply (s t : Fin N → Fin 2) :
    MPOTensor.mpo czxDecoratedTensor N s t =
      if s = spinFlip N t then (-1 : ℂ) ^ (czExponent s + spinParity s) else 0 := by
  rw [MPOTensor.mpo_apply_of_forced_right_bond czxDecoratedTensor_apply,
    Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
    Fintype.sum_equiv (Equiv.addRight 1) (fun n ↦ (s (n + 1)).val) (fun n ↦ (s n).val)
      fun _ ↦ rfl]
  rfl

/-- The periodic operator of the decorated tensor is the monomial matrix of the global spin flip
whose phase at the input `t` is the sign `(-1)^{∑_n s_n s_{n+1} + ∑_n s_n}` of the output. -/
theorem mpo_czxDecoratedTensor :
    MPOTensor.mpo czxDecoratedTensor N =
      Matrix.monomial (spinFlip N) fun t ↦
        (-1 : ℂ) ^ (czExponent (spinFlip N t) + spinParity (spinFlip N t)) := by
  ext s t
  rw [mpo_czxDecoratedTensor_apply, Matrix.monomial_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- Bridge: **`U_{CZX} = Z^{⊗ N} · D_N X^{⊗ N}`**, the decorated operator is the review's CZX
operator followed by a Pauli `Z` on every site.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1128–1129; arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex` lines 2585–2587. -/
theorem mpo_czxDecoratedTensor_eq :
    MPOTensor.mpo czxDecoratedTensor N = globalZ N * MPOTensor.mpo reviewCZXTensor N := by
  ext s t
  rw [globalZ, Matrix.diagonal_mul, mpo_czxDecoratedTensor_apply, mpo_reviewCZXTensor_apply]
  split_ifs <;> simp [pow_add, mul_comm]

/-- Bridge: the decorated operator is the operator `∏ CZ_{i,i+1} Z_i ∏ X_i` of
`MPOTensor.GroupCocycle.czxDecorated`, hence the periodic operator of the group-cocycle
construction for the generator of `ℤ₂` and the nontrivial three-cocycle.

Source: arXiv:2203.12563, line 2224. -/
theorem mpo_czxDecoratedTensor_eq_groupCocycle :
    MPOTensor.mpo czxDecoratedTensor N =
      MPOTensor.mpo (MPOTensor.GroupCocycle.tensor MPOTensor.GroupCocycle.bitEquiv
        (TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle 1)
        (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))) N := by
  rw [MPOTensor.GroupCocycle.mpo_tensor_cyclicTwo, mpo_czxDecoratedTensor]
  rfl

/-- **The decorated CZX operator has order two**: `U^2 = 1` at every positive length.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 412–428 (the MPU of order
two) and lines 1128–1136 (the CZX symmetry is a `ℤ_2` symmetry). -/
theorem mpo_czxDecoratedTensor_mul_self :
    MPOTensor.mpo czxDecoratedTensor N * MPOTensor.mpo czxDecoratedTensor N = 1 := by
  rw [mpo_czxDecoratedTensor_eq_groupCocycle, MPOTensor.GroupCocycle.mpo_tensor_mul _
    (TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_isCocycle 1),
    show (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 by
      decide,
    MPOTensor.GroupCocycle.mpo_tensor_one _
      (TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_isNormalized 1)]

/-- The periodic operator of the decorated tensor is unitary at every positive length. -/
theorem mpo_czxDecoratedTensor_mem_unitaryGroup :
    MPOTensor.mpo czxDecoratedTensor N ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  rw [mpo_czxDecoratedTensor_eq_groupCocycle]
  exact MPOTensor.GroupCocycle.mpo_tensor_mem_unitaryGroup _
    (TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_norm 1) _

omit [NeZero N] in
/-- **The decorated CZX tensor is a matrix product unitary** on every periodic chain of
positive length.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1164–1180 ("The MPU tensor of
`U_{CZX}` that we choose"). -/
theorem czxDecoratedTensor_isMPUPos : MPOTensor.IsMPUPos czxDecoratedTensor := by
  intro N hN
  let : NeZero N := ⟨by omega⟩
  exact mpo_czxDecoratedTensor_mem_unitaryGroup

end CZXCompression
