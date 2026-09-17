/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.Zsqrt2Ring
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.FundamentalTheorem.Reduction.ProjectorWeightedSum

/-!
# The hidden bond objects of the weighted Ising twist

A machine-checked instance of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) for
the sitewise content of the weighted Ising bond-object twist of the P6 work
(`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex`,
`thm:p6-round45-fusion`; exact data in
`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1, verified by
`checks/asym_ising_action_verify.py`).

The three topological-symmetry tensors `A_1`, `A_ψ`, `A_σ` of the Ising anyon chain are matrix
product operators on the ten fusion-tree labels `(x', ρ, x)` with `x ∈ x' ⊗ ρ`; their letters are
the F-symbols `[F^{a x' ρ}_y]_{y' x}` of the Ising category, and a letter vanishes unless its
two labels carry the same `ρ` (data file, "Conventions and the dictionary"). In the twist, each
bond of the boundary fixed point carries the weighted bond object
`Θ = λ_1 A_1 ⊕ λ_ψ A_ψ ⊕ λ_σ A_σ`, and the block of flag `σ` is the strand `A_σ` with `Θ`
inserted before it. This file formalises the two-object part `Θ_2 = λ_1 A_1 ⊕ λ_ψ A_ψ` of that
insertion at the generic point `(λ_1, λ_ψ) = (1/2, 3/10)` of the P6 numerics, scaled to the
integers `5, 3`, with the `σ` strand scaled by `√2` so that every entry lies in `ℤ[√2]`.

The stacked product `Θ_2 ⋆ (√2 A_σ)`, of bond dimension `24`, compresses onto two weighted
copies of the *same* normal tensor `√2 A_σ`, with the weights `5` and `3`, and sixteen zero
slots. The two hidden bond objects `1` and `ψ` both feed the visible channel `σ` through the
fusions `1 ⊗ σ = σ` and `ψ ⊗ σ = σ`, with different weights: on a ring of length `L` the
coefficient of the `σ` strand is the power sum `λ_1^L + λ_ψ^L`, which is the origin of the
non-removable length dependence of the P6 twist (`thm:p6-round45-fusion` (v)–(vi), the fusion
operator `χ_{σσ1} = diag(λ_1, λ_ψ)/ν` with two distinct eigenvalues). The gauge is a signed
permutation of the bond coordinates whose rows are the F-move isometries of the two fusions; its
single sign is the F-symbol `[F^{ψσψ}_σ] = -1` of the `ψ` line (data file §1.3). The
conjugated tensor is block diagonal for every letter, so the remainder vanishes and the extension
splits.

## Main definitions

* `IsingTwist.isingOne`, `IsingTwist.isingPsi`, `IsingTwist.isingSigma`: the three
  topological-symmetry tensors, the last one scaled by `√2`.
* `IsingTwist.thetaTwo`: the weighted bond object `5 A_1 ⊕ 3 A_ψ`.
* `IsingTwist.isingBondObject`: the stacked product `Θ_2 ⋆ (√2 A_σ)` on the pair alphabet.

## Main results

* `IsingTwist.isingCompression`: the multi-block compression datum of Theorem 7.7 with two
  weighted slots and sixteen zero slots.
* `IsingTwist.isingBondObject_trace_evalWord`: the word-trace identity
  `tr(B^w) = (5^{|w|} + 3^{|w|}) tr((√2 A_σ)^w)`.
* `IsingTwist.isingTwist_mpo`: the periodic-operator identity
  `O_L(Θ_2) O_L(√2 A_σ) = (5^L + 3^L) O_L(√2 A_σ)` at every positive length.
* `IsingTwist.isingBondObject_remainder`: the remainder vanishes, so the extension splits.
* `IsingTwist.isingSigma_isNormal`, `IsingTwist.isingOne_isNormal`,
  `IsingTwist.isingPsi_isNormal`: the three tensors are normal at blocking length one.
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

end MPSTensor

namespace IsingTwist

open MPSTensor Zsqrtd

/-! ### The three topological-symmetry tensors -/

/-- The label `ρ` of a fusion-tree label `(x', ρ, x)`, in the order `1, ψ, σ`; the ten labels
are `(1,1,1), (1,ψ,ψ), (1,σ,σ), (ψ,1,ψ), (ψ,ψ,1), (ψ,σ,σ), (σ,1,σ), (σ,ψ,σ), (σ,σ,1), (σ,σ,ψ)`
(data file, "Conventions and the dictionary"). -/
def isingRho : Fin 10 → Fin 3 := ![0, 1, 2, 0, 1, 2, 0, 1, 2, 2]

/-- The tensor `A_1` over `ℤ√2`, on the site space `P_1 = [(1,1), (ψ,ψ), (σ,σ)]`: every letter
is a matrix unit (data file §1.1). -/
def isingOneZ : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) (ℤ√2)
  | 0, 0 => Matrix.single 0 0 1
  | 1, 1 => Matrix.single 0 1 1
  | 2, 2 => Matrix.single 0 2 1
  | 3, 3 => Matrix.single 1 1 1
  | 4, 4 => Matrix.single 1 0 1
  | 5, 5 => Matrix.single 1 2 1
  | 6, 6 => Matrix.single 2 2 1
  | 7, 7 => Matrix.single 2 2 1
  | 8, 8 => Matrix.single 2 0 1
  | 9, 9 => Matrix.single 2 1 1
  | _, _ => 0

/-- The tensor `A_ψ` over `ℤ√2`, on the site space `P_ψ = [(1,ψ), (ψ,1), (σ,σ)]`: every letter
is a signed matrix unit, the sign at the letter `((σ,ψ,σ), (σ,ψ,σ))` being the F-symbol
`[F^{ψσψ}_σ] = -1` (data file §1.1). -/
def isingPsiZ : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) (ℤ√2)
  | 0, 3 => Matrix.single 1 1 1
  | 1, 4 => Matrix.single 1 0 1
  | 2, 5 => Matrix.single 1 2 1
  | 3, 0 => Matrix.single 0 0 1
  | 4, 1 => Matrix.single 0 1 1
  | 5, 2 => Matrix.single 0 2 1
  | 6, 6 => Matrix.single 2 2 1
  | 7, 7 => Matrix.single 2 2 (-1)
  | 8, 9 => Matrix.single 2 1 1
  | 9, 8 => Matrix.single 2 0 1
  | _, _ => 0

/-- The tensor `√2 A_σ` over `ℤ√2`, on the site space
`P_σ = [(1,σ), (ψ,σ), (σ,1), (σ,ψ)]`: every letter is a matrix unit scaled by `±1` or `±√2`,
the entries `±1` being the rescaled F-symbols `±1/√2` of the `σσσ` fusion (data file §1.1). -/
def isingSigmaZ : Fin 10 → Fin 10 → Matrix (Fin 4) (Fin 4) (ℤ√2)
  | 0, 6 => Matrix.single 2 2 sqrtd
  | 1, 7 => Matrix.single 2 3 sqrtd
  | 2, 8 => Matrix.single 2 0 1
  | 2, 9 => Matrix.single 2 1 1
  | 3, 6 => Matrix.single 3 3 sqrtd
  | 4, 7 => Matrix.single 3 2 sqrtd
  | 5, 8 => Matrix.single 3 0 1
  | 5, 9 => Matrix.single 3 1 (-1)
  | 6, 0 => Matrix.single 0 0 sqrtd
  | 6, 3 => Matrix.single 1 1 sqrtd
  | 7, 1 => Matrix.single 0 1 sqrtd
  | 7, 4 => Matrix.single 1 0 sqrtd
  | 8, 2 => Matrix.single 0 2 sqrtd
  | 8, 5 => Matrix.single 1 2 sqrtd
  | 9, 2 => Matrix.single 0 3 sqrtd
  | 9, 5 => Matrix.single 1 3 (-sqrtd)
  | _, _ => 0

/-- The tensor `A_1` as a matrix product operator tensor. -/
noncomputable def isingOne : MPOTensor 10 3 := fun h h' => complexOfZsqrt2 (isingOneZ h h')

/-- The tensor `A_ψ` as a matrix product operator tensor. -/
noncomputable def isingPsi : MPOTensor 10 3 := fun h h' => complexOfZsqrt2 (isingPsiZ h h')

/-- The tensor `√2 A_σ` as a matrix product operator tensor. -/
noncomputable def isingSigma : MPOTensor 10 4 :=
  fun h h' => complexOfZsqrt2 (isingSigmaZ h h')

/-- The letter `((1,1,1), (σ,1,σ))` of `√2 A_σ` is `√2` times the matrix unit at
`((σ,1), (σ,1))` (data file §1.1). -/
theorem isingSigma_apply_zero_six :
    isingSigma 0 6 = (Real.sqrt 2 : ℂ) • Matrix.single 2 2 1 := by
  ext p q
  simp only [isingSigma, isingSigmaZ, complexOfZsqrt2_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp

theorem isingOneZ_eq_zero_of_rho_ne :
    ∀ h h' : Fin 10, isingRho h ≠ isingRho h' → isingOneZ h h' = 0 := by
  decide +kernel

theorem isingPsiZ_eq_zero_of_rho_ne :
    ∀ h h' : Fin 10, isingRho h ≠ isingRho h' → isingPsiZ h h' = 0 := by
  decide +kernel

theorem isingSigmaZ_eq_zero_of_rho_ne :
    ∀ h h' : Fin 10, isingRho h ≠ isingRho h' → isingSigmaZ h h' = 0 := by
  decide +kernel

/-! ### Normality of the three tensors

Each tensor realises every matrix unit of its bond algebra as a nonzero multiple of one of its
letters (data file §1.1, check 1b), so it is normal at blocking length one. The pair-alphabet
letter of the pair `(h, h')` is `10 h + h'`.
-/

/-- The letter of `A_1` realising each matrix unit of the three-by-three bond algebra. -/
def isingOneUnitLetter : Fin 3 → Fin 3 → Fin 100 :=
  ![![0, 11, 22], ![44, 33, 55], ![88, 99, 66]]

/-- The letter of `A_ψ` realising each matrix unit of the three-by-three bond algebra. -/
def isingPsiUnitLetter : Fin 3 → Fin 3 → Fin 100 :=
  ![![30, 41, 52], ![14, 3, 25], ![98, 89, 66]]

/-- The letter of `√2 A_σ` realising each matrix unit of the four-by-four bond algebra. -/
def isingSigmaUnitLetter : Fin 4 → Fin 4 → Fin 100 :=
  ![![60, 71, 82, 92], ![74, 63, 85, 95], ![28, 29, 6, 17], ![58, 59, 47, 36]]

/-- The nonzero factor relating that letter of `√2 A_σ` to its matrix unit. -/
def isingSigmaUnitCoef : Fin 4 → Fin 4 → ℤ√2 :=
  ![![sqrtd, sqrtd, sqrtd, sqrtd], ![sqrtd, sqrtd, sqrtd, -sqrtd], ![1, 1, sqrtd, sqrtd],
    ![1, -1, sqrtd, sqrtd]]

private theorem isingOneZ_unit (x y : Fin 3) :
    isingOneZ (Fin.divNat (m := 10) (n := 10) (isingOneUnitLetter x y))
      (Fin.modNat (m := 10) (n := 10) (isingOneUnitLetter x y)) =
      (1 : ℤ√2) • Matrix.single x y 1 := by
  revert x y
  decide +kernel

private theorem isingPsiZ_unit (x y : Fin 3) :
    isingPsiZ (Fin.divNat (m := 10) (n := 10) (isingPsiUnitLetter x y))
      (Fin.modNat (m := 10) (n := 10) (isingPsiUnitLetter x y)) =
      (1 : ℤ√2) • Matrix.single x y 1 := by
  revert x y
  decide +kernel

private theorem isingSigmaZ_unit (x y : Fin 4) :
    isingSigmaZ (Fin.divNat (m := 10) (n := 10) (isingSigmaUnitLetter x y))
      (Fin.modNat (m := 10) (n := 10) (isingSigmaUnitLetter x y)) =
      isingSigmaUnitCoef x y • Matrix.single x y 1 := by
  revert x y
  decide +kernel

/-- **`A_1` is normal at blocking length one** (data file §1.1, check 1b). -/
theorem isingOne_isNormal : Kraus.IsNormal isingOne.toMPSTensor :=
  isNormal_of_single_eq_smul_zsqrt2 (fun a => isingOneZ (Fin.divNat (m := 10) (n := 10) a)
      (Fin.modNat (m := 10) (n := 10) a)) (fun _ => rfl)
    isingOneUnitLetter (fun _ _ => 1) (fun _ _ => one_ne_zero) isingOneZ_unit

/-- **`A_ψ` is normal at blocking length one** (data file §1.1, check 1b). -/
theorem isingPsi_isNormal : Kraus.IsNormal isingPsi.toMPSTensor :=
  isNormal_of_single_eq_smul_zsqrt2 (fun a => isingPsiZ (Fin.divNat (m := 10) (n := 10) a)
      (Fin.modNat (m := 10) (n := 10) a)) (fun _ => rfl)
    isingPsiUnitLetter (fun _ _ => 1) (fun _ _ => one_ne_zero) isingPsiZ_unit

/-- **`√2 A_σ` is normal at blocking length one**: its sixteen nonzero letters are scaled
matrix units covering every position of the four-by-four matrix algebra (data file §1.1,
check 1b). -/
theorem isingSigma_isNormal : Kraus.IsNormal isingSigma.toMPSTensor :=
  isNormal_of_single_eq_smul_zsqrt2 (fun a => isingSigmaZ (Fin.divNat (m := 10) (n := 10) a)
      (Fin.modNat (m := 10) (n := 10) a)) (fun _ => rfl)
    isingSigmaUnitLetter isingSigmaUnitCoef (by decide) isingSigmaZ_unit

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
  mulTensor_complexOfZsqrt2 thetaTwoZ isingSigmaZ _ _

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

/-! ### The letter identity

The conjugated letter is computed sector by sector: for a letter `(h, h')` with
`ρ(h) = ρ(h') = r`, only the middle labels `j` with `ρ(j) = r` contribute to the stacked product,
and the identity is decided on the resulting matrix; letters with `ρ(h) ≠ ρ(h')` vanish on both
sides.
-/

/-- The stacked product restricted to the middle labels of the sector `r`. -/
private def stackSector (r : Fin 3) (h h' : Fin 10) : Matrix (Fin 24) (Fin 24) (ℤ√2) :=
  (∑ j : Fin 10, if isingRho j = r then thetaTwoZ h j ⊗ₖ isingSigmaZ j h' else 0).submatrix
    (finProdFinEquiv (m := 6) (n := 4)).symm (finProdFinEquiv (m := 6) (n := 4)).symm

private theorem thetaTwoZ_eq_zero_of_rho_ne {h h' : Fin 10} (hne : isingRho h ≠ isingRho h') :
    thetaTwoZ h h' = 0 := by
  rw [thetaTwoZ, isingOneZ_eq_zero_of_rho_ne h h' hne, isingPsiZ_eq_zero_of_rho_ne h h' hne]
  simp

private theorem stack_eq_sector (h h' : Fin 10) :
    mulZsqrt2Tensor thetaTwoZ isingSigmaZ h h' = stackSector (isingRho h) h h' := by
  unfold mulZsqrt2Tensor stackSector
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · rw [thetaTwoZ_eq_zero_of_rho_ne fun e => hj e.symm, Matrix.zero_kronecker]

private theorem stack_eq_zero_of_rho_ne {h h' : Fin 10} (hne : isingRho h ≠ isingRho h') :
    mulZsqrt2Tensor thetaTwoZ isingSigmaZ h h' = 0 := by
  unfold mulZsqrt2Tensor
  rw [Finset.sum_eq_zero fun j _ => ?_]
  · simp
  rcases eq_or_ne (isingRho h) (isingRho j) with hj | hj
  · rw [isingSigmaZ_eq_zero_of_rho_ne j h' (hj ▸ hne), Matrix.kronecker_zero]
  · rw [thetaTwoZ_eq_zero_of_rho_ne hj, Matrix.zero_kronecker]

/-- The conjugated stacked letter, in the block coordinates. -/
private def conjSector (r : Fin 3) (h h' : Fin 10) :
    Matrix (BlockSpace isingBlockDim isingSlots 16) (BlockSpace isingBlockDim isingSlots 16)
      (ℤ√2) :=
  (Matrix.of fun x y =>
    isingSign x * stackSector r h h' (isingPerm x) (isingPerm y) * isingSign y).submatrix
    isingTau isingTau

private theorem letter_sector_zero : ∀ h h' : Fin 10, isingRho h = 0 → isingRho h' = 0 →
    conjSector 0 h h' = Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h')) := by
  decide +kernel

private theorem letter_sector_one : ∀ h h' : Fin 10, isingRho h = 1 → isingRho h' = 1 →
    conjSector 1 h h' = Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h')) := by
  decide +kernel

private theorem letter_sector_two : ∀ h h' : Fin 10, isingRho h = 2 → isingRho h' = 2 →
    conjSector 2 h h' = Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h')) := by
  decide +kernel

private theorem isingBlockZ_zero : isingBlockZ 0 = 0 := by
  funext b
  rcases b with s | t <;> simp [isingBlockZ]

/-- **The letter identity over `ℤ√2`** (data file §1.3, check T2-G3): in the block coordinates,
every letter of the stacked product is block diagonal with the blocks `5 (√2 A_σ)`, `3 (√2 A_σ)`
and sixteen zeros. -/
theorem isingGaugeZ_conj (h h' : Fin 10) :
    (isingGaugeZ * mulZsqrt2Tensor thetaTwoZ isingSigmaZ h h' * isingGaugeZᵀ).submatrix
        isingTau isingTau =
      Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ h h')) := by
  rw [isingGaugeZ, signedPermMatrix_mul_mul_transpose]
  rcases eq_or_ne (isingRho h) (isingRho h') with hρ | hρ
  · rw [stack_eq_sector]
    have h3 : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
    rcases h3 (isingRho h) with hr | hr | hr
    · rw [hr]; exact letter_sector_zero h h' hr (hρ.symm.trans hr)
    · rw [hr]; exact letter_sector_one h h' hr (hρ.symm.trans hr)
    · rw [hr]; exact letter_sector_two h h' hr (hρ.symm.trans hr)
  · rw [stack_eq_zero_of_rho_ne hρ, isingSigmaZ_eq_zero_of_rho_ne h h' hρ, isingBlockZ_zero,
      Matrix.blockDiagonal'_zero]
    refine Matrix.ext fun x y => ?_
    simp

theorem isingBondObject_conjMatrix (a : Fin 100) :
    conjMatrix isingGauge (isingBondObject a) =
      complexOfZsqrt2 (Matrix.blockDiagonal' (isingBlockZ (isingSigmaZ
        (Fin.divNat (m := 10) (n := 10) a) (Fin.modNat (m := 10) (n := 10) a)))) := by
  rw [isingGauge, conjMatrix_gaugeOfMatrix, isingBondObject_eq, ← complexOfZsqrt2_mul,
    ← complexOfZsqrt2_mul, ← complexOfZsqrt2_submatrix, isingBondObjectZ, isingGaugeZ_conj]

/-! ### The compression datum -/

/-- **The multi-block asymmetric compression datum of the Ising bond-object twist** (P5 note,
Theorem 7.7(i)–(iii); data file §1.2–1.3): two weighted copies of the normal tensor `√2 A_σ`,
with the weights `5` and `3`, and sixteen zero slots. -/
noncomputable def isingCompression :
    MultiBlockCompression isingBondObject isingSlots isingTargets where
  z := 16
  ord := isingOrd
  gauge := isingGauge
  triangular a x y h := by
    have h' : isingOrd y.1 < isingOrd x.1 := h
    have hxy : x.1 ≠ y.1 := fun e => by rw [e] at h'; exact lt_irrefl _ h'
    rw [isingBondObject_conjMatrix, complexOfZsqrt2_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hxy,
      map_zero]
  matched a s := by
    rw [isingBondObject_conjMatrix, complexOfZsqrt2, Matrix.blockDiag'_map,
      Matrix.blockDiag'_blockDiagonal']
    ext p q
    simp [isingBlockZ, isingTargets, isingSigma, MPOTensor.toMPSTensor,
      zsqrt2ToComplex_isingWeightsZ]
  unmatched a t := by
    rw [isingBondObject_conjMatrix, complexOfZsqrt2, Matrix.blockDiag'_map,
      Matrix.blockDiag'_blockDiagonal']
    ext p q
    simp [isingBlockZ]

/-- **The remainder of the Ising bond-object compression vanishes** (P5 note, Theorem 7.7(vi);
data file §1.3, check T2-G6): the conjugated letters are block diagonal, so the extension
splits. -/
theorem isingBondObject_remainder : isingCompression.remainder = 0 := by
  funext a
  have h : conjMatrix isingGauge (isingCompression.remainder a) =
      conjMatrix isingGauge (isingBondObject a) -
        Matrix.blockDiagonal' (conjMatrix isingGauge (isingBondObject a)).blockDiag' :=
    isingCompression.conjMatrix_remainder a
  refine conjMatrix_injective isingGauge ?_
  rw [h, Pi.zero_apply, conjMatrix_zero, sub_eq_zero, isingBondObject_conjMatrix, complexOfZsqrt2,
    Matrix.blockDiagonal'_map _ _ (map_zero _), Matrix.blockDiag'_blockDiagonal']

/-! ### Consequences -/

/-- **The word-trace identity of the Ising bond-object twist** (data file §1.2, check T2-G5):
the periodic coefficient of the `σ` strand is the power sum `5^L + 3^L` of the two weights, the
sitewise origin of the length-dependent coefficient `λ_1^L + λ_ψ^L` of the P6 twist
(`thm:p6-round45-fusion` (v)–(vi)). -/
theorem isingBondObject_trace_evalWord (w : List (Fin 100)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord isingBondObject w) =
      ((5 : ℂ) ^ w.length + 3 ^ w.length) *
        Matrix.trace (Kraus.evalWord isingSigma.toMPSTensor w) := by
  have h := isingCompression.trace_evalWord_eq_sum w hw
  have hs : ∀ s : Fin 2,
      Matrix.trace (Kraus.evalWord (isingTargets s) w) =
        isingWeights s ^ w.length * Matrix.trace (Kraus.evalWord isingSigma.toMPSTensor w) := by
    intro s
    rw [isingTargets, show isingWeights s • isingSigma.toMPSTensor =
        fun i => isingWeights s • isingSigma.toMPSTensor i from rfl,
      Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
  rw [h, show isingSlots = Finset.univ from rfl, Fin.sum_univ_two, hs 0, hs 1]
  simp only [isingWeights, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **The weighted bond object acting on the `σ` strand** (data file §1.2 and §1.5): at every
positive length, the periodic operator of `Θ_2 = 5 A_1 ⊕ 3 A_ψ` composed with the periodic
operator of `√2 A_σ` is `5^L + 3^L` times the latter. The two hidden bond objects feed the same
visible channel with different weights, and their power sum is the length-dependent coefficient
of the P6 twist (`thm:p6-round45-fusion` (v)–(vi)). -/
theorem isingTwist_mpo (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo thetaTwo L * MPOTensor.mpo isingSigma L =
      ((5 : ℂ) ^ L + 3 ^ L) • MPOTensor.mpo isingSigma L := by
  rw [← MPOTensor.mpo_mulTensor]
  ext σ τ
  have hw : (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) ≠ [] := by
    simp only [ne_eq, List.ofFn_eq_nil_iff]
    omega
  have h := isingBondObject_trace_evalWord (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) hw
  unfold isingBondObject at h
  rw [MPOTensor.evalWord_toMPSTensor_pairConfig, MPOTensor.evalWord_toMPSTensor_pairConfig] at h
  simpa [MPOTensor.mpoMatrixEntry] using h

/-- **Biorthogonal compression onto each weighted slot** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem isingBondObject_isReduction (s : {s // s ∈ isingSlots}) :
    IsReduction isingBondObject (isingTargets s.1) (isingCompression.left s)
      (isingCompression.right s) :=
  isingCompression.isReduction s

/-- The two weighted slots are biorthogonal (P5 note, Theorem 7.7(iv)). -/
theorem isingBondObject_left_mul_right_of_ne {s t : {s // s ∈ isingSlots}} (h : s ≠ t) :
    isingCompression.left s * isingCompression.right t = 0 :=
  isingCompression.left_mul_right_of_ne h

/-- **The sitewise right intertwiner of each slot**: `B^a V_s = V_s (μ_s (√2 A_σ)^a)`
(data file §1.3, check T2-G4). -/
theorem isingBondObject_mul_right_eq_right_mul (a : Fin 100) (s : {s // s ∈ isingSlots}) :
    isingBondObject a * isingCompression.right s =
      isingCompression.right s * isingTargets s.1 a :=
  isingCompression.mul_right_eq_right_mul isingBondObject_remainder a s

/-- **The sitewise left intertwiner of each slot**: `W_s B^a = (μ_s (√2 A_σ)^a) W_s`
(data file §1.3, check T2-G4). -/
theorem isingBondObject_left_mul_eq_mul_left (a : Fin 100) (s : {s // s ∈ isingSlots}) :
    isingCompression.left s * isingBondObject a =
      isingTargets s.1 a * isingCompression.left s :=
  isingCompression.left_mul_eq_mul_left isingBondObject_remainder a s

/-- The Ising bond-object compression has sixteen zero slots. -/
theorem isingBondObject_z_eq : isingCompression.z = 16 := rfl

/-- **The dimension count** `24 = 4 + 4 + 16` (P5 note, Theorem 7.7(vii)). -/
theorem isingBondObject_dim_eq : (24 : ℕ) = ∑ _s ∈ isingSlots, 4 + 16 :=
  isingCompression.dim_eq

end IsingTwist
