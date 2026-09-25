/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingTensors
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.FundamentalTheorem.Reduction.ProjectorWeightedSum

/-!
# The weighted Ising bond object, its stacked product, and the gauge

The weighted bond object `Θ_2 = 5 A_1 ⊕ 3 A_ψ` of the Ising twist
(`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1.2–1.3, verified by
`checks/asym_ising_action_verify.py`), the stacked product `Θ_2 ⋆ (√2 A_σ)` of bond dimension
`24`, and the change of bond coordinates under which every letter of the stacked product becomes
block diagonal. The gauge is a signed permutation of the bond coordinates whose rows are the
F-move isometries of the fusions `1 ⊗ σ = σ` and `ψ ⊗ σ = σ`; its single sign is the F-symbol
`[F^{ψσψ}_σ] = -1` of the `ψ` line (data file §1.3).

This file also sets up the sector-by-sector computation of the conjugated letters: for a letter
`(h, h')` with `ρ(h) = ρ(h') = r`, only the middle labels `j` with `ρ(j) = r` contribute to the
stacked product, so the conjugated letter is the sector matrix `conjSector r h h'`, and letters
with `ρ(h) ≠ ρ(h')` vanish. The sector identities themselves are decided in
`IsingLetterSectorOne`, `IsingLetterSectorPsi`, `IsingLetterSectorSigmaAbelian` and
`IsingLetterSectorSigmaSigma`, and assembled into the compression datum in `IsingWeightedTwist`.

## Main definitions

* `MPSTensor.signedPermMatrix`: the signed permutation matrix of a map and a sign vector.
* `MPSTensor.twoTermMatrix`: a matrix with at most two nonzero entries in each row.
* `IsingTwist.thetaTwo`: the weighted bond object `5 A_1 ⊕ 3 A_ψ`.
* `IsingTwist.isingBondObject`: the stacked product `Θ_2 ⋆ (√2 A_σ)` on the pair alphabet.
* `IsingTwist.isingGauge`: the gauge, a signed permutation of the bond coordinates transported
  to the graded block space `IsingTwist.isingTau`.
* `IsingTwist.isingBlockZ`: the prescribed diagonal blocks of a conjugated letter.
* `IsingTwist.conjSector`: the conjugated stacked letter of a sector, in the block coordinates.

## Main results

* `IsingTwist.stack_eq_sector`, `IsingTwist.stack_eq_zero_of_rho_ne`: the sector reduction of
  the stacked product.
-/

open scoped Matrix Kronecker

namespace MPSTensor

/-! ### Signed permutation matrices -/

/-- The signed permutation matrix with the entry `s x` in row `x` and column `π x`. -/
def signedPermMatrix {R : Type*} [Zero R] {n : Type*} [DecidableEq n] (π : n → n) (s : n → R) :
    Matrix n n R :=
  Matrix.of fun x i => if i = π x then s x else 0

/-- Conjugating by a signed permutation matrix and its transpose reads off the entries of the
conjugated matrix at the permuted positions, with the two signs. -/
theorem signedPermMatrix_mul_mul_transpose {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (π : n → n) (s : n → R) (B : Matrix n n R) :
    signedPermMatrix π s * B * (signedPermMatrix π s)ᵀ =
      Matrix.of fun x y => s x * B (π x) (π y) * s y := by
  ext x y
  simp [signedPermMatrix, Matrix.mul_apply, Finset.sum_ite_eq', mul_assoc]

/-- The matrix with at most two nonzero entries in each row: `s x` in the column `π x` and
`s' x` in the column `π' x`. With `s' = 0` it is the signed permutation matrix of `π` and `s`. -/
def twoTermMatrix {R : Type*} [Add R] [Zero R] {n : Type*} [DecidableEq n] (π π' : n → n)
    (s s' : n → R) : Matrix n n R :=
  Matrix.of fun x i => (if i = π x then s x else 0) + (if i = π' x then s' x else 0)

/-- Conjugating by a matrix with at most two nonzero entries per row and its transpose reads
off four entries of the conjugated matrix. -/
theorem twoTermMatrix_mul_mul_transpose {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (π π' : n → n) (s s' : n → R) (B : Matrix n n R) :
    twoTermMatrix π π' s s' * B * (twoTermMatrix π π' s s')ᵀ =
      Matrix.of fun x y => s x * (B (π x) (π y) * s y + B (π x) (π' y) * s' y) +
        s' x * (B (π' x) (π y) * s y + B (π' x) (π' y) * s' y) := by
  ext x y
  simp [twoTermMatrix, Matrix.mul_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_mul,
    mul_ite, Finset.sum_ite_eq', mul_assoc]
  ring

end MPSTensor

namespace IsingTwist

open MPSTensor Zsqrtd

/-! ### The weighted bond object and the stacked tensor -/

/-- The weighted bond object `Θ_2 = 5 A_1 ⊕ 3 A_ψ` over `ℤ√2`, on `ℂ^6 = P_1 ⊕ P_ψ`
(data file §1.2). -/
def thetaTwoZ (h h' : Fin 10) : Matrix (Fin 6) (Fin 6) (ℤ√2) :=
  (Matrix.fromBlocks ((5 : ℤ√2) • isingOneZ h h') 0 0 ((3 : ℤ√2) • isingPsiZ h h')).submatrix
    (finSumFinEquiv (m := 3) (n := 3)).symm (finSumFinEquiv (m := 3) (n := 3)).symm

/-- The weighted bond object `Θ_2 = 5 A_1 ⊕ 3 A_ψ` as a matrix product operator tensor: the
weights are ten times the generic P6 point `(λ_1, λ_ψ) = (1/2, 3/10)` (data file §1.2). -/
noncomputable def thetaTwo : MPOTensor 10 6 := fun h h' => complexOfZsqrt2 (thetaTwoZ h h')

/-- The weighted bond object is the direct sum of the two weighted tensors. -/
theorem thetaTwo_eq_fromBlocks (h h' : Fin 10) :
    thetaTwo h h' =
      (Matrix.fromBlocks ((5 : ℂ) • isingOne h h') 0 0 ((3 : ℂ) • isingPsi h h')).submatrix
        (finSumFinEquiv (m := 3) (n := 3)).symm (finSumFinEquiv (m := 3) (n := 3)).symm := by
  ext i j
  simp only [thetaTwo, thetaTwoZ, complexOfZsqrt2_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv (m := 3) (n := 3)).symm i with a | a <;>
    rcases (finSumFinEquiv (m := 3) (n := 3)).symm j with b | b <;>
    simp [isingOne, isingPsi, map_ofNat]

/-- The stacked product `Θ_2 ⋆ (√2 A_σ)` on the hundred-letter pair alphabet, of bond dimension
`24` in the bond order `4 (Θ_2 index) + (P_σ index)` (data file §1.2). -/
noncomputable def isingBondObject : MPSTensor 100 24 :=
  (MPOTensor.mulTensor thetaTwo isingSigma).toMPSTensor

/-- The stacked product over `ℤ√2`. -/
def isingBondObjectZ (a : Fin 100) : Matrix (Fin 24) (Fin 24) (ℤ√2) :=
  mulZsqrt2Tensor thetaTwoZ isingSigmaZ (Fin.divNat (m := 10) (n := 10) a)
    (Fin.modNat (m := 10) (n := 10) a)

theorem isingBondObject_eq (a : Fin 100) :
    isingBondObject a = complexOfZsqrt2 (isingBondObjectZ a) :=
  mulTensor_complexOfRing _ thetaTwoZ isingSigmaZ _ _

/-! ### The gauge

The change of bond coordinates is a signed permutation: its first four rows are the F-move
isometry `U_{1σ}` of the fusion `1 ⊗ σ = σ`, the next four rows the F-move isometry `U_{ψσ}` of
`ψ ⊗ σ = σ`, carrying the sign `[F^{ψσψ}_σ] = -1` on the coordinate `(ψ,σ)`, and the remaining
sixteen rows the complementary coordinate vectors (data file §1.3).
-/

/-- The permutation underlying the gauge: row `x` of the gauge is `±e_{π x}`. -/
def isingPerm : Fin 24 → Fin 24 :=
  ![8, 9, 2, 7, 20, 21, 19, 14, 0, 1, 3, 4, 5, 6, 10, 11, 12, 13, 15, 16, 17, 18, 22, 23]

/-- The signs of the gauge rows: the single sign is the F-symbol of the `ψ` line. -/
def isingSign : Fin 24 → ℤ√2 :=
  ![1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The gauge over `ℤ√2`, a signed permutation matrix whose inverse is its transpose. -/
def isingGaugeZ : Matrix (Fin 24) (Fin 24) (ℤ√2) := signedPermMatrix isingPerm isingSign

theorem isingGaugeZ_mul_transpose : isingGaugeZ * isingGaugeZᵀ = 1 := by decide +kernel

theorem isingGaugeZ_transpose_mul : isingGaugeZᵀ * isingGaugeZ = 1 := by decide +kernel

theorem isingGaugeComplex_mul_transpose :
    complexOfZsqrt2 isingGaugeZ * complexOfZsqrt2 isingGaugeZᵀ = 1 := by
  rw [← complexOfZsqrt2_mul, isingGaugeZ_mul_transpose, complexOfZsqrt2_one]

theorem isingGaugeComplex_transpose_mul :
    complexOfZsqrt2 isingGaugeZᵀ * complexOfZsqrt2 isingGaugeZ = 1 := by
  rw [← complexOfZsqrt2_mul, isingGaugeZ_transpose_mul, complexOfZsqrt2_one]

/-! ### The slots and the block coordinates -/

/-- The two weighted slots: the channel `σ` reached through the bond object `1` and through the
bond object `ψ`. -/
abbrev isingSlots : Finset (Fin 2) := Finset.univ

/-- Both slots carry the tensor `√2 A_σ`, of bond dimension four. -/
abbrev isingBlockDim : Fin 2 → ℕ := fun _ => 4

/-- The two weights over `ℤ√2`: `5` through the bond object `1` and `3` through `ψ`. -/
def isingWeightsZ : Fin 2 → ℤ√2 := ![5, 3]

/-- The two weights, ten times the generic P6 point `(λ_1, λ_ψ) = (1/2, 3/10)`
(data file §1.2). -/
noncomputable def isingWeights : Fin 2 → ℂ := ![5, 3]

theorem zsqrt2ToComplex_isingWeightsZ (s : Fin 2) :
    zsqrt2ToComplex (isingWeightsZ s) = isingWeights s := by
  fin_cases s <;> simp [isingWeightsZ, isingWeights, map_ofNat]

/-- The two target blocks: the tensor `√2 A_σ` with the weights `5` and `3`. -/
noncomputable def isingTargets : Fin 2 → MPSTensor 100 4 :=
  fun s => isingWeights s • isingSigma.toMPSTensor

/-- The block ordering: the two weighted slots, then the sixteen zero slots. -/
def isingOrd : BlockIndex isingSlots 16 ≃ Fin 18 where
  toFun := Sum.elim (fun s => Fin.castLE (by norm_num) s.1) fun t => ⟨t.val + 2, by omega⟩
  invFun i :=
    if h : i.val < 2 then Sum.inl ⟨⟨i.val, h⟩, Finset.mem_univ _⟩
    else Sum.inr ⟨i.val - 2, by omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The position of the first bond coordinate of each block. -/
def isingOffset : BlockIndex isingSlots 16 → ℕ :=
  Sum.elim (fun s => 4 * s.1.val) fun t => 8 + t.val

/-- The bond coordinate attached to a graded coordinate. -/
def isingCoordNat (x : BlockSpace isingBlockDim isingSlots 16) : ℕ :=
  isingOffset x.1 + (x.2 : ℕ)

theorem isingCoordNat_lt (x : BlockSpace isingBlockDim isingSlots 16) : isingCoordNat x < 24 := by
  revert x
  decide +kernel

/-- The labelling of the twenty-four bond coordinates by the graded block space: the first slot
at the coordinates `0..3`, the second at `4..7`, the zero slots at `8..23`. -/
def isingTau : BlockSpace isingBlockDim isingSlots 16 ≃ Fin 24 where
  toFun x := ⟨isingCoordNat x, isingCoordNat_lt x⟩
  invFun i :=
    if h : i.val < 4 then ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, ⟨i.val, h⟩⟩
    else if h' : i.val < 8 then
      ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, ⟨i.val - 4, by change i.val - 4 < 4; omega⟩⟩
    else ⟨Sum.inr ⟨i.val - 8, by omega⟩, ⟨0, Nat.zero_lt_one⟩⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The gauge of the Ising bond-object compression. -/
noncomputable def isingGauge : (Fin 24 → ℂ) ≃ₗ[ℂ] (BlockSpace isingBlockDim isingSlots 16 → ℂ) :=
  gaugeOfMatrix isingTau (complexOfZsqrt2 isingGaugeZ) (complexOfZsqrt2 isingGaugeZᵀ)
    isingGaugeComplex_mul_transpose isingGaugeComplex_transpose_mul

/-- The prescribed diagonal blocks over `ℤ√2` for a letter `X` of `√2 A_σ`: `5 X` on the first
slot, `3 X` on the second, and the `1 × 1` zero matrix on every zero slot. -/
def isingBlockZ (X : Matrix (Fin 4) (Fin 4) (ℤ√2)) :
    ∀ b : BlockIndex isingSlots 16,
      Matrix (Fin (slotSize isingBlockDim b)) (Fin (slotSize isingBlockDim b)) (ℤ√2) :=
  Sum.rec (motive := fun b =>
      Matrix (Fin (slotSize isingBlockDim b)) (Fin (slotSize isingBlockDim b)) (ℤ√2))
    (fun s => isingWeightsZ s.1 • X) fun _ => 0

theorem isingBlockZ_zero : isingBlockZ 0 = 0 := by
  funext b
  rcases b with s | t <;> simp [isingBlockZ]

/-! ### The sector reduction of the stacked letters

For a letter `(h, h')` with `ρ(h) = ρ(h') = r`, only the middle labels `j` with `ρ(j) = r`
contribute to the stacked product, and letters with `ρ(h) ≠ ρ(h')` vanish.
-/

/-- The stacked product restricted to the middle labels of the sector `r`. -/
def stackSector (r : Fin 3) (h h' : Fin 10) : Matrix (Fin 24) (Fin 24) (ℤ√2) :=
  (∑ j : Fin 10, if isingRho j = r then thetaTwoZ h j ⊗ₖ isingSigmaZ j h' else 0).submatrix
    (finProdFinEquiv (m := 6) (n := 4)).symm (finProdFinEquiv (m := 6) (n := 4)).symm

theorem thetaTwoZ_eq_zero_of_rho_ne {h h' : Fin 10} (hne : isingRho h ≠ isingRho h') :
    thetaTwoZ h h' = 0 := by
  rw [thetaTwoZ, isingOneZ_eq_zero_of_rho_ne h h' hne, isingPsiZ_eq_zero_of_rho_ne h h' hne]
  simp

theorem stack_eq_sector (h h' : Fin 10) :
    mulZsqrt2Tensor thetaTwoZ isingSigmaZ h h' = stackSector (isingRho h) h h' := by
  unfold mulZsqrt2Tensor mulTensorR stackSector
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · rw [thetaTwoZ_eq_zero_of_rho_ne fun e => hj e.symm, Matrix.zero_kronecker]

theorem stack_eq_zero_of_rho_ne {h h' : Fin 10} (hne : isingRho h ≠ isingRho h') :
    mulZsqrt2Tensor thetaTwoZ isingSigmaZ h h' = 0 := by
  unfold mulZsqrt2Tensor mulTensorR
  rw [Finset.sum_eq_zero fun j _ => ?_]
  · simp
  rcases eq_or_ne (isingRho h) (isingRho j) with hj | hj
  · rw [isingSigmaZ_eq_zero_of_rho_ne j h' (hj ▸ hne), Matrix.kronecker_zero]
  · rw [thetaTwoZ_eq_zero_of_rho_ne hj, Matrix.zero_kronecker]

/-- The conjugated stacked letter of the sector `r`, in the block coordinates: the sector matrix
conjugated by the signed permutation and relabelled by `isingTau`. -/
def conjSector (r : Fin 3) (h h' : Fin 10) :
    Matrix (BlockSpace isingBlockDim isingSlots 16) (BlockSpace isingBlockDim isingSlots 16)
      (ℤ√2) :=
  (Matrix.of fun x y =>
    isingSign x * stackSector r h h' (isingPerm x) (isingPerm y) * isingSign y).submatrix
    isingTau isingTau

end IsingTwist
