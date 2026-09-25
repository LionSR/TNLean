/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.CZX.CZXUnitary
import TNLean.MPS.Examples.CZX.CZXSquare
import TNLean.MPS.MPU.Examples.CZXNormalizationAudit

/-!
# The CZX matrix product unitary of the review: the tensor and its square

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"The CZX MPU", `Papers/2011.12127/TN-Review-main.tex` lines 2582–2601: the review prints the
bond-two tensor of the CZX symmetry of Chen, Liu and Wen (arXiv:1106.4752) through its two
nonzero matrices `A^{01} = [[1,1],[0,0]]` and `A^{10} = [[0,0],[1,-1]]`, states that the
matrix product operator `O(A)` is injective, displays the bond-four tensor `B` of `O(A)^2`,
and states that `B` is not injective.
Review: arXiv:2011.12127, Appendix A, "The CZX MPU".

**Formalized here.** The tensor with the two printed matrices, its periodic operator
`O(A) |t⟩ = (-1)^{∑_n s_n s_{n+1}} |s⟩` with `s` the spin flip of `t`, its unitarity at every
positive length, the global identity `O(A)^2 = (-1)^N I` of line 2601, normality of the tensor
(the review's "injective"), the two printed matrices of the bond-four square at lines
2593–2595, and the failure of normality of the square.

**Local fix (normalization):** the bra-ket display at line 2585,
`|0⟩⟨1| ⊗ |0)(+| + |1⟩⟨0| ⊗ |1)(-|` with normalized `(±|`, carries a factor `2^{-1/2}` per site
relative to the printed matrices at lines 2588–2591, and its periodic operator is not unitary.
The tensor defined here is the one with the printed matrices, for which every later claim of
the passage holds; documented in `docs/paper-gaps/mpu_czx_tensor_normalization.tex`.

The printed matrices contract to `O(A) = D_N X^{⊗ N}`, with `D_N` the diagonal cyclic
controlled-`Z` phase: the Pauli `X` acts first. The review's words at line 2586, controlled-`Z`
gates "followed by a Pauli `X` on all sites", read in time order as `X^{⊗ N} D_N`, which is also
the order `U_{CZX} = U_X U_{CZ}` of Chen, Liu and Wen (`References/1106.4752/source/dDSPTmodel.tex`
line 287). The two differ by the global sign `(-1)^N` and both square to `(-1)^N I`; the
operators here follow the printed matrices (recorded in the same paper-gap note).

The review's tensor is the transpose, letter by letter and with the two physical indices
exchanged, of the tensor `CZXCompression.czxTensor` of `CZXTensor`, whose operator is
`X^{⊗ N} D_N`.

## Main definitions

* `CZXCompression.reviewCZXIntTensor`, `CZXCompression.reviewCZXTensor`: the tensor with the
  printed matrices, over the integers and over the complexes.
* `CZXCompression.reviewCZXSquareInt`, `CZXCompression.reviewCZXSquare`: the bond-four tensor
  of the square, in the pair-alphabet view.

## Main results

* `CZXCompression.mpo_reviewCZXTensor_apply`: the periodic operator entrywise.
* `CZXCompression.mpo_reviewCZXTensor_mul_self`: `O(A)^2 = (-1)^N I` at every positive length.
* `CZXCompression.reviewCZXTensor_isMPUPos`: the tensor is a matrix product unitary.
* `CZXCompression.reviewCZXMPS_isNormal`: the tensor is normal.
* `CZXCompression.reviewCZXSquare_apply_zero`, `CZXCompression.reviewCZXSquare_apply_three`: the
  printed matrices `B^{00}` and `B^{11}`.
* `CZXCompression.reviewCZXSquare_not_isNormal`: the square is not normal.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
- [arXiv:1106.4752](https://arxiv.org/abs/1106.4752) -- X. Chen, Z.-X. Liu, X.-G. Wen,
  *Two-dimensional symmetry-protected topological orders and their protected gapless edge
  excitations*
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace CZXCompression

open MPSTensor

/-! ### The tensor with the printed matrices -/

/-- The integer matrices of the CZX tensor of the review: `A^{01} = [[1,1],[0,0]]`,
`A^{10} = [[0,0],[1,-1]]`, and `A^{00} = A^{11} = 0`.

Source: arXiv:2011.12127, Appendix A, `Papers/2011.12127/TN-Review-main.tex` lines 2588–2591. -/
def reviewCZXIntTensor : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0, 1 => !![1, 1; 0, 0]
  | 1, 0 => !![0, 0; 1, -1]
  | _, _ => 0

/-- The CZX tensor of the review as a matrix product operator tensor, the first physical index
being the output.

Source: arXiv:2011.12127, Appendix A, `Papers/2011.12127/TN-Review-main.tex` lines 2588–2591.
The bra-ket display at line 2585 differs from these matrices by `2^{-1/2}`
(`docs/paper-gaps/mpu_czx_tensor_normalization.tex`). -/
def reviewCZXTensor : MPOTensor 2 2 := fun i j => complexOfInt (reviewCZXIntTensor i j)

/-- The entries of the review's tensor: output `i` is the flip of input `j`, the incoming bond
carries `i`, and the outgoing bond `r` contributes `(-1)^{i r}`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2585–2591. -/
theorem reviewCZXTensor_apply (i j l r : Fin 2) :
    reviewCZXTensor i j l r = if i = j.rev ∧ l = i then (-1 : ℂ) ^ (i.val * r.val) else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [reviewCZXTensor, reviewCZXIntTensor, complexOfInt, Fin.rev]

/-- Bridge: the review's tensor is the tensor `czxTensor` of `CZXTensor` with its two physical
indices exchanged and every matrix transposed. -/
theorem reviewCZXTensor_eq_transpose (i j : Fin 2) :
    reviewCZXTensor i j = (czxTensor j i)ᵀ := by
  ext l r
  rw [Matrix.transpose_apply, reviewCZXTensor_apply, czxTensor_apply]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;> simp [Fin.rev]

/-- Bridge: the tensor `printed2017Tensor` with the normalized Hadamard matrix of
`CZXNormalizationAudit` is `2^{-1/2}` times the review's tensor; this is the review's bra-ket
display at `Papers/2011.12127/TN-Review-main.tex` line 2585. -/
theorem printed2017Tensor_eq_smul_reviewCZXTensor :
    MPOTensor.CZX.printed2017Tensor = ((↑(Real.sqrt 2) : ℂ)⁻¹) • reviewCZXTensor := by
  funext i j
  ext l r
  change _ = (↑(Real.sqrt 2) : ℂ)⁻¹ * reviewCZXTensor i j l r
  rw [reviewCZXTensor_apply]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [MPOTensor.CZX.printed2017Tensor, MPSTensor.pauliX, Fin.rev]

/-! ### The periodic operator -/

variable {N : ℕ} [NeZero N]

/-- **The periodic operator of the review's tensor entrywise**: the entry at `(s, t)` vanishes
unless `s` is the spin flip of `t`, and then equals the controlled-`Z` sign of `s`. The bond
configuration is forced to be `g_n = s_n`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2588–2591 (the printed
matrices). The operator is `D_N X^{⊗ N}`; the verbal description at lines 2585–2587,
controlled-`Z` gates followed by a Pauli `X`, reads as `X^{⊗ N} D_N`, which differs by
`(-1)^N` (`mpo_reviewCZXTensor_eq_smul`, `docs/paper-gaps/mpu_czx_tensor_normalization.tex`). -/
theorem mpo_reviewCZXTensor_apply (s t : Fin N → Fin 2) :
    MPOTensor.mpo reviewCZXTensor N s t =
      if s = spinFlip N t then (-1 : ℂ) ^ czExponent s else 0 := by
  rw [MPOTensor.mpo_apply_eq_prod_of_forced_bond reviewCZXTensor s t s fun g hg ↦ by
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    refine ⟨n, ?_⟩
    rw [reviewCZXTensor_apply, ite_eq_right]
    exact fun h ↦ hn h.2]
  by_cases hst : s = spinFlip N t
  · have hp : ∀ n, s n = (t n).rev := fun n ↦ congrFun hst n
    rw [ite_eq_left hst, czExponent, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun n _ ↦ ?_
    rw [reviewCZXTensor_apply, ite_eq_left ⟨hp n, rfl⟩]
  · rw [ite_eq_right hst]
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hst
    refine Finset.prod_eq_zero (Finset.mem_univ n) ?_
    rw [reviewCZXTensor_apply, ite_eq_right]
    exact fun h ↦ hn h.1

/-- The periodic operator of the review's tensor is the monomial matrix of the global spin flip
whose phase at the input `t` is the controlled-`Z` sign of the output. -/
theorem mpo_reviewCZXTensor :
    MPOTensor.mpo reviewCZXTensor N =
      Matrix.monomial (spinFlip N) fun t ↦ (-1 : ℂ) ^ czExponent (spinFlip N t) := by
  ext s t
  rw [mpo_reviewCZXTensor_apply, Matrix.monomial_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- Bridge: the review's operator `D_N X^{⊗ N}` is `(-1)^N` times the operator
`X^{⊗ N} D_N` of `czxTensor`. -/
theorem mpo_reviewCZXTensor_eq_smul :
    MPOTensor.mpo reviewCZXTensor N = ((-1 : ℂ) ^ N) • MPOTensor.mpo czxTensor N := by
  rw [mpo_reviewCZXTensor, mpo_czxTensor, Matrix.smul_monomial]
  congr 1
  funext t
  rw [Pi.smul_apply, smul_eq_mul, ← neg_one_pow_czExponent_spinFlip_mul t, mul_assoc,
    ← pow_add, ← two_mul, pow_mul]
  simp

/-- The periodic operator of the review's tensor is unitary at every positive length. -/
theorem mpo_reviewCZXTensor_mem_unitaryGroup :
    MPOTensor.mpo reviewCZXTensor N ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  rw [mpo_reviewCZXTensor]
  refine Matrix.monomial_mem_unitaryGroup _ _ fun t ↦ ?_
  rw [star_pow, star_neg, star_one, ← mul_pow]
  simp

/-- **`O(A)^2 = (-1)^N I`** at every positive length.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2601. -/
theorem mpo_reviewCZXTensor_mul_self :
    MPOTensor.mpo reviewCZXTensor N * MPOTensor.mpo reviewCZXTensor N = ((-1 : ℂ) ^ N) • 1 := by
  rw [mpo_reviewCZXTensor_eq_smul, smul_mul_smul_comm, mpo_czxTensor_mul_self, smul_smul,
    ← pow_add, ← two_mul, pow_mul]
  simp

omit [NeZero N] in
/-- **The review's CZX tensor is a matrix product unitary** on every periodic chain of positive
length.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2582–2587. -/
theorem reviewCZXTensor_isMPUPos : MPOTensor.IsMPUPos reviewCZXTensor := by
  intro N hN
  let : NeZero N := ⟨by omega⟩
  exact mpo_reviewCZXTensor_mem_unitaryGroup

/-! ### Normality -/

private theorem reviewCZXMPS_one :
    reviewCZXTensor.toMPSTensor 1 = complexOfInt !![1, 1; 0, 0] := rfl

private theorem reviewCZXMPS_two :
    reviewCZXTensor.toMPSTensor 2 = complexOfInt !![0, 0; 1, -1] := rfl

/-- Each matrix unit is a half-sum or a half-difference of two length-two words. -/
private theorem reviewCZX_single (i j : Fin 2) :
    ∃ a b c e : Fin 4, ∃ u v : ℂ, Matrix.single i j (1 : ℂ) =
      u • (reviewCZXTensor.toMPSTensor a * reviewCZXTensor.toMPSTensor b) +
        v • (reviewCZXTensor.toMPSTensor c * reviewCZXTensor.toMPSTensor e) := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, 1, 1, 2, 1 / 2, 1 / 2, ?_⟩
    rw [reviewCZXMPS_one, reviewCZXMPS_two, ← complexOfInt_mul, ← complexOfInt_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt, Matrix.mul_apply]
  · refine ⟨1, 1, 1, 2, 1 / 2, -1 / 2, ?_⟩
    rw [reviewCZXMPS_one, reviewCZXMPS_two, ← complexOfInt_mul, ← complexOfInt_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt, Matrix.mul_apply]
  · refine ⟨2, 1, 2, 2, 1 / 2, -1 / 2, ?_⟩
    rw [reviewCZXMPS_one, reviewCZXMPS_two, ← complexOfInt_mul, ← complexOfInt_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt, Matrix.mul_apply]
  · refine ⟨2, 1, 2, 2, 1 / 2, 1 / 2, ?_⟩
    rw [reviewCZXMPS_one, reviewCZXMPS_two, ← complexOfInt_mul, ← complexOfInt_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt, Matrix.mul_apply]

/-- **The review's CZX tensor is normal**: its length-two words span the full two-by-two matrix
algebra. This is the review's statement that `O(A)` is injective, which it reads off the algebra
generated by `A^{01}` and `A^{10}`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2588–2591. -/
theorem reviewCZXMPS_isNormal : Kraus.IsNormal reviewCZXTensor.toMPSTensor :=
  MPSTensor.isNormal_of_single_eq_two_words _ reviewCZX_single

/-! ### The square -/

/-- The integer matrices of the square `B^{ij} = ∑_m A^{im} ⊗ A^{mj}` in the pair alphabet,
with the letters `(0,0), (0,1), (1,0), (1,1)` in this order.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2593–2595. -/
def reviewCZXSquareInt : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, 0, 0; 1, -1, 1, -1; 0, 0, 0, 0; 0, 0, 0, 0]
  | 1 => 0
  | 2 => 0
  | 3 => !![0, 0, 0, 0; 0, 0, 0, 0; 1, 1, -1, -1; 0, 0, 0, 0]

/-- The bond-four tensor of `O(A)^2`, in the pair-alphabet view.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2593–2595. -/
def reviewCZXSquare : MPSTensor 4 4 :=
  (MPOTensor.mulTensor reviewCZXTensor reviewCZXTensor).toMPSTensor

theorem reviewCZXSquare_eq (a : Fin 4) :
    reviewCZXSquare a = complexOfInt (reviewCZXSquareInt a) := by
  have h : reviewCZXSquare a = complexOfInt (mulIntTensor reviewCZXIntTensor reviewCZXIntTensor
      (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfRing _ reviewCZXIntTensor reviewCZXIntTensor _ _
  have hint : ∀ b : Fin 4, mulIntTensor reviewCZXIntTensor reviewCZXIntTensor
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) =
        reviewCZXSquareInt b := by
    decide
  rw [h, hint]

/-- `B^{00} = A^{01} ⊗ A^{10}`, with the bond pair `(α, β)` encoded as `2α + β`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2594. -/
theorem mulTensor_reviewCZX_zero_zero :
    MPOTensor.mulTensor reviewCZXTensor reviewCZXTensor 0 0 =
      (reviewCZXTensor 0 1 ⊗ₖ reviewCZXTensor 1 0).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  have h : reviewCZXTensor 0 0 = 0 := complexOfInt_zero
  rw [MPOTensor.mulTensor_apply, Fin.sum_univ_two, h, Matrix.zero_kronecker, zero_add]

/-- `B^{11} = A^{10} ⊗ A^{01}`, with the bond pair `(α, β)` encoded as `2α + β`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2595. -/
theorem mulTensor_reviewCZX_one_one :
    MPOTensor.mulTensor reviewCZXTensor reviewCZXTensor 1 1 =
      (reviewCZXTensor 1 0 ⊗ₖ reviewCZXTensor 0 1).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  have h : reviewCZXTensor 1 1 = 0 := complexOfInt_zero
  rw [MPOTensor.mulTensor_apply, Fin.sum_univ_two, h, Matrix.kronecker_zero, add_zero]

/-- **The printed matrix `B^{00}`** of the square.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2594. -/
theorem reviewCZXSquare_apply_zero :
    reviewCZXSquare 0 = !![0, 0, 0, 0; 1, -1, 1, -1; 0, 0, 0, 0; 0, 0, 0, 0] := by
  rw [reviewCZXSquare_eq]
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [reviewCZXSquareInt, complexOfInt]

/-- **The printed matrix `B^{11}`** of the square.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2595. -/
theorem reviewCZXSquare_apply_three :
    reviewCZXSquare 3 = !![0, 0, 0, 0; 0, 0, 0, 0; 1, 1, -1, -1; 0, 0, 0, 0] := by
  rw [reviewCZXSquare_eq]
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [reviewCZXSquareInt, complexOfInt]

theorem reviewCZXSquare_apply_one : reviewCZXSquare 1 = 0 := by
  rw [reviewCZXSquare_eq, show reviewCZXSquareInt 1 = 0 from rfl, complexOfInt_zero]

theorem reviewCZXSquare_apply_two : reviewCZXSquare 2 = 0 := by
  rw [reviewCZXSquare_eq, show reviewCZXSquareInt 2 = 0 from rfl, complexOfInt_zero]

/-- Every letter of the square has vanishing first row. -/
theorem reviewCZXSquare_apply_zero_row (a : Fin 4) (q : Fin 4) : reviewCZXSquare a 0 q = 0 := by
  rw [reviewCZXSquare_eq, complexOfInt_apply, Int.cast_eq_zero]
  revert a q
  decide

/-- **The square of the review's CZX tensor is not normal**: every nonempty word has vanishing
first row, so no span of words of a fixed positive length contains the matrix unit `E_{00}`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2596 ("This MPO is
clearly not injective"). -/
theorem reviewCZXSquare_not_isNormal : ¬ Kraus.IsNormal reviewCZXSquare := by
  rintro ⟨n, hn, hinj⟩
  let φ : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => X 0 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Kraus.not_isNBlkInjective_of_linearMap φ (fun σ => ?_) (Matrix.single 0 0 1)
    (by change Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℂ) 0 0 ≠ 0; simp) hinj
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [List.ofFn_succ, Kraus.evalWord_cons]
  change (reviewCZXSquare (σ 0) *
    Kraus.evalWord reviewCZXSquare (List.ofFn fun i => σ i.succ)) 0 0 = 0
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun q _ => by rw [reviewCZXSquare_apply_zero_row, zero_mul]

end CZXCompression
