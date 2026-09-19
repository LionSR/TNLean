/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Matrix.Basis
import QICLean.Kraus.Injectivity
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.ExplicitGauge
import TNLean.MPS.MPDO.OperatorProduct

/-!
# The undecorated CZX matrix product operator

On a periodic chain of `L > 0` qubits, let
`D_L |t⟩ = (-1)^{∑_j t_j t_{j+1}} |t⟩`, with indices modulo `L`.
The tensor below generates `U_L = X^{⊗ L} D_L`, so
`U_L |t⟩ = (-1)^{∑_j t_j t_{j+1}} |1-t⟩` in the computational basis.
Its bond dimension is two, with `M^{ij} = δ_{i,1 ⊕ j} T_j`,
`T_0 = [[1,0],[1,0]]` and `T_1 = [[0,1],[0,-1]]`.
The cyclic convention includes the self-loop `D_1 = Z` and counts the two-site edge twice,
giving `D_2 = I`. The operator is unitary and satisfies `U_L² = (-1)^L I` at every
positive length, as proved in `CZXUnitary`; no even-length restriction is imposed.

The review arXiv:2011.12127 displays the reverse gate order `D_L X^{⊗ L}`, which differs
from this tensor's operator by `(-1)^L`. The decorated, two-qubit-blocked convention of
arXiv:2502.20257 in `TNLean.MPS.MPDO.CZXTensor` is a different tensor whose square is the
identity. Here the stacked square has the word traces of the bond-one target `-δ`.
The explicit construction is recorded in
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`,
`ex:p5ft-czx` and `ex:p5ft-oscillating`.

The entries are integers. The length-two words span `M_2(ℂ)`, proving normality, and the
stacked product has an explicit bond-four integer tensor.

## Main definitions

* `CZXCompression.czxIntTensor`, `CZXCompression.czxTensor`, `CZXCompression.czxMPS`: the
  bond-two tensor of the note, over the integers, over the complexes, and in the
  pair-alphabet view.
* `CZXCompression.identityMPS`: the bond-one identity tensor `δ` in the pair-alphabet view.
* `CZXCompression.negIdentityIntMPS`: the integer matrices of `-δ`.
* `CZXCompression.czxSquareInt`, `CZXCompression.czxSquare`: the stacked product tensor
  `B^{ij} = ∑_m M^{im} ⊗ M^{mj}` of bond dimension four.

## Main results

* `CZXCompression.czxMPS_isNormal`: the bond-two tensor is normal, its length-two words
  spanning the full two-by-two matrix algebra.
* `CZXCompression.czxSquare_eq`: the stacked product tensor is the coercion of an explicit
  integer tensor.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace CZXCompression

open MPSTensor

/-! ### The bond-two tensor of the note -/

/-- The integer tensor `M^{ij} = δ_{i,1 ⊕ j} T_j` of the CZX symmetry
(construction note, `ex:p5ft-czx`). -/
def czxIntTensor : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0, 1 => !![0, 1; 0, -1]
  | 1, 0 => !![1, 0; 1, 0]
  | _, _ => 0

/-- The CZX tensor of the note as a matrix product operator tensor. -/
def czxTensor : MPOTensor 2 2 := fun i j => complexOfInt (czxIntTensor i j)

/-- The integer tensor of the identity operator, of bond dimension one. -/
def identityIntTensor : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℤ :=
  fun i j => if i = j then 1 else 0

/-- The identity operator as a matrix product operator tensor of bond dimension one. -/
def identityTensor : MPOTensor 2 1 := fun i j => complexOfInt (identityIntTensor i j)

/-- The CZX tensor read as a tensor over the pair alphabet `Fin 4`. -/
def czxMPS : MPSTensor 4 2 := czxTensor.toMPSTensor

/-- The bond-one identity tensor `δ` read as a tensor over the pair alphabet `Fin 4`. -/
def identityMPS : MPSTensor 4 1 := identityTensor.toMPSTensor

/-- The integer matrices of the pair-alphabet CZX tensor, in the letter order
`(0,0), (0,1), (1,0), (1,1)`. -/
def czxIntMPS : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 0
  | 1 => !![0, 1; 0, -1]
  | 2 => !![1, 0; 1, 0]
  | 3 => 0

/-- The integer matrices of the pair-alphabet identity tensor. -/
def identityIntMPS : Fin 4 → Matrix (Fin 1) (Fin 1) ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 1

theorem czxMPS_eq (a : Fin 4) : czxMPS a = complexOfInt (czxIntMPS a) := by
  fin_cases a <;> rfl

theorem identityMPS_eq (a : Fin 4) : identityMPS a = complexOfInt (identityIntMPS a) := by
  fin_cases a <;> rfl

/-- The integer matrices of the identity tensor carried with the weight `-1`. -/
def negIdentityIntMPS (a : Fin 4) : Matrix (Fin 1) (Fin 1) ℤ := -identityIntMPS a

theorem negIdentityMPS_eq (a : Fin 4) :
    ((-1 : ℂ) • identityMPS) a = complexOfInt (negIdentityIntMPS a) := by
  rw [negIdentityIntMPS, complexOfInt_neg, ← identityMPS_eq]
  simp

/-! ### Normality of the bond-two tensor -/

private theorem czxIntMPS_mul_two_two : czxIntMPS 2 * czxIntMPS 2 = !![1, 0; 1, 0] := by decide

private theorem czxIntMPS_mul_one_two : czxIntMPS 1 * czxIntMPS 2 = !![1, 0; -1, 0] := by decide

private theorem czxIntMPS_mul_two_one : czxIntMPS 2 * czxIntMPS 1 = !![0, 1; 0, 1] := by decide

private theorem czxIntMPS_mul_one_one : czxIntMPS 1 * czxIntMPS 1 = !![0, -1; 0, 1] := by decide

private theorem czxMPS_mul_two_two : czxMPS 2 * czxMPS 2 = complexOfInt !![1, 0; 1, 0] := by
  simp only [czxMPS_eq]
  rw [← complexOfInt_mul, czxIntMPS_mul_two_two]

private theorem czxMPS_mul_one_two : czxMPS 1 * czxMPS 2 = complexOfInt !![1, 0; -1, 0] := by
  simp only [czxMPS_eq]
  rw [← complexOfInt_mul, czxIntMPS_mul_one_two]

private theorem czxMPS_mul_two_one : czxMPS 2 * czxMPS 1 = complexOfInt !![0, 1; 0, 1] := by
  simp only [czxMPS_eq]
  rw [← complexOfInt_mul, czxIntMPS_mul_two_one]

private theorem czxMPS_mul_one_one : czxMPS 1 * czxMPS 1 = complexOfInt !![0, -1; 0, 1] := by
  simp only [czxMPS_eq]
  rw [← complexOfInt_mul, czxIntMPS_mul_one_one]

/-- Each matrix unit is a half-sum or a half-difference of two length-two words. -/
private theorem single_zero_zero : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) =
    (1 / 2 : ℂ) • (czxMPS 2 * czxMPS 2) + (1 / 2 : ℂ) • (czxMPS 1 * czxMPS 2) := by
  rw [czxMPS_mul_two_two, czxMPS_mul_one_two]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt]

private theorem single_one_zero : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) =
    (1 / 2 : ℂ) • (czxMPS 2 * czxMPS 2) + (-1 / 2 : ℂ) • (czxMPS 1 * czxMPS 2) := by
  rw [czxMPS_mul_two_two, czxMPS_mul_one_two]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt]

private theorem single_zero_one : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) =
    (1 / 2 : ℂ) • (czxMPS 2 * czxMPS 1) + (-1 / 2 : ℂ) • (czxMPS 1 * czxMPS 1) := by
  rw [czxMPS_mul_two_one, czxMPS_mul_one_one]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt]

private theorem single_one_one : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) =
    (1 / 2 : ℂ) • (czxMPS 2 * czxMPS 1) + (1 / 2 : ℂ) • (czxMPS 1 * czxMPS 1) := by
  rw [czxMPS_mul_two_one, czxMPS_mul_one_one]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.single_apply, complexOfInt]

/-- **The bond-two tensor of the note is normal.** Its length-two words span the full
two-by-two matrix algebra (construction note, `ex:p5ft-czx`). -/
theorem czxMPS_isNormal : Kraus.IsNormal czxMPS := by
  refine ⟨2, two_pos, ?_⟩
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan]
  set T := Submodule.span ℂ
    (Set.range fun σ : Fin 2 → Fin 4 => Kraus.evalWord czxMPS (List.ofFn σ)) with hT
  have hword : ∀ a b : Fin 4, czxMPS a * czxMPS b ∈ T := by
    intro a b
    refine Submodule.subset_span ⟨![a, b], ?_⟩
    simp [Kraus.evalWord, List.ofFn_succ]
  have hcomb : ∀ X Y : Matrix (Fin 2) (Fin 2) ℂ, ∀ a b c e : Fin 4, ∀ u v : ℂ,
      X = u • (czxMPS a * czxMPS b) + v • (czxMPS c * czxMPS e) → X ∈ T := by
    intro X Y a b c e u v hX
    rw [hX]
    exact T.add_mem (T.smul_mem _ (hword a b)) (T.smul_mem _ (hword c e))
  have m00 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ T :=
    hcomb _ 0 2 2 1 2 _ _ single_zero_zero
  have m10 : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ T :=
    hcomb _ 0 2 2 1 2 _ _ single_one_zero
  have m01 : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ T :=
    hcomb _ 0 2 1 1 1 _ _ single_zero_one
  have m11 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ T :=
    hcomb _ 0 2 1 1 1 _ _ single_one_one
  have hunit : ∀ i j : Fin 2, Matrix.single i j (1 : ℂ) ∈ T := by
    intro i j
    fin_cases i <;> fin_cases j
    exacts [m00, m01, m10, m11]
  exact T.eq_top_of_forall_single_mem hunit

/-! ### The stacked product tensor of Example D -/

/-- The integer matrices of the stacked product tensor
`B^{ij} = ∑_m M^{im} ⊗ M^{mj}` of bond dimension four (construction note, `ex:p5ft-czx`). -/
def czxSquareInt : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, 1, 0; 0, 0, 1, 0; 0, 0, -1, 0; 0, 0, -1, 0]
  | 1 => 0
  | 2 => 0
  | 3 => !![0, 1, 0, 0; 0, -1, 0, 0; 0, 1, 0, 0; 0, -1, 0, 0]

/-- The stacked product tensor of Example D, in the pair-alphabet view. -/
def czxSquare : MPSTensor 4 4 := (MPOTensor.mulTensor czxTensor czxTensor).toMPSTensor

theorem czxSquare_eq (a : Fin 4) : czxSquare a = complexOfInt (czxSquareInt a) := by
  have h : czxSquare a = complexOfInt (mulIntTensor czxIntTensor czxIntTensor
      (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfInt czxIntTensor czxIntTensor _ _
  have hint : ∀ b : Fin 4, mulIntTensor czxIntTensor czxIntTensor
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) = czxSquareInt b := by
    decide
  rw [h, hint]

end CZXCompression
