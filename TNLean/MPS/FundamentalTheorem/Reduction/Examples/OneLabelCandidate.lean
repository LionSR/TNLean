/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.StackedPairGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# The one-label renormalization fixed point at `λ = 7/25`

A machine-checked instance of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) for
the one-label candidate of the P6 work
(`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex`; exact data in
`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, §4, verified by
`checks/p6_onelabel_candidate_verify.py`).

The one-site matrices of the candidate are the four scaled matrix units
`A⁰ = (4/5) E₀₀`, `A¹ = (4/5) E₁₁`, `A² = (3/5) E₀₁`, `A³ = (3/5) E₁₀`, a Pythagorean point at
which `c₊² = (1 + λ)/2` and `c₋² = (1 - λ)/2` for `λ = 7/25`. The vertical tensor is the
doubled family `M₀^{(i,j)} = A^i ⊗ A^j` on the sixteen-letter pair alphabet, and its stacked
product has the bond dimension sixteen. That stacked product factorises as
`B^{(i,k)} = A^i ⊗ T ⊗ A^k` with the inner-bond matrix `T = ∑_j A^j ⊗ A^j`, whose spectrum is
`{1, 7/25, 0, 0}`: the whole compression is the spectral decomposition of one four-by-four
matrix, its blocks are the eigenspaces of that matrix and its weights the eigenvalues.

This is the answer, at this example, to the question of what produces a length-dependent
structure constant: not two inequivalent sectors, but two *weighted copies of one sector*, the
same normal tensor carried with the weights `1` and `7/25`. The periodic coefficient
`c^{(L)} = 1 + (7/25)^L` is the length-`L` power sum of that weight multiset.

## Main definitions

* `P6Compression.oneLabelTarget`: the vertical tensor of the candidate on the pair alphabet.
* `P6Compression.oneLabelStacked`: its stacked product, of bond dimension sixteen.

## Main results

* `P6Compression.oneLabelCompression`: the multi-block compression datum of Theorem 7.7, with
  two weighted slots and eight zero slots.
* `P6Compression.oneLabel_trace_evalWord`: the word-trace identity
  `tr(B^w) = (1 + (7/25)^{|w|}) tr(M₀^w)`.
* `P6Compression.oneLabel_remainder`: the remainder vanishes, so the extension splits.
* `P6Compression.oneLabel_isReduction`, `P6Compression.oneLabel_mul_right_eq_right_mul`,
  `P6Compression.oneLabel_left_mul_eq_mul_left`: the compression pair and the sitewise
  intertwiners of each slot.
* `P6Compression.oneLabel_dim_eq`: the dimension count `16 = 4 + 4 + 8`.
* `P6Compression.oneLabelTarget_isNormal`: the target is normal at blocking length one.
-/

open scoped Matrix Kronecker

namespace P6Compression

open MPSTensor

/-! ### The tensor -/

/-- Five times the four one-site matrices of the one-label candidate:
`A⁰ = (4/5) E₀₀`, `A¹ = (4/5) E₁₁`, `A² = (3/5) E₀₁`, `A³ = (3/5) E₁₀`
(`p6_examples_compression_data.md`, §4.1). -/
def oneLabelAInt : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![4, 0; 0, 0]
  | 1 => !![0, 0; 0, 4]
  | 2 => !![0, 3; 0, 0]
  | 3 => !![0, 0; 3, 0]

/-- Twenty-five times the vertical tensor `M₀^{(i,j)} = A^i ⊗ A^j` of the one-label candidate. -/
def oneLabelMInt (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  (oneLabelAInt i ⊗ₖ oneLabelAInt j).submatrix
    (finProdFinEquiv (m := 2) (n := 2)).symm (finProdFinEquiv (m := 2) (n := 2)).symm

/-- The vertical tensor of the one-label candidate, as a matrix product operator tensor. -/
noncomputable def oneLabelM : MPOTensor 4 4 :=
  fun i j => (25 : ℂ)⁻¹ • complexOfInt (oneLabelMInt i j)

/-- The vertical tensor of the one-label candidate on the sixteen-letter pair alphabet. -/
noncomputable def oneLabelTarget : MPSTensor 16 4 := oneLabelM.toMPSTensor

/-- The stacked product of the vertical tensor with itself, of bond dimension sixteen
(`p6_examples_compression_data.md`, §4.2). -/
noncomputable def oneLabelStacked : MPSTensor 16 16 :=
  (MPOTensor.mulTensor oneLabelM oneLabelM).toMPSTensor

/-- Twenty-five times the pair-alphabet vertical tensor. -/
def oneLabelTargetInt (a : Fin 16) : Matrix (Fin 4) (Fin 4) ℤ :=
  oneLabelMInt (Fin.divNat (m := 4) (n := 4) a) (Fin.modNat (m := 4) (n := 4) a)

/-- Six hundred and twenty-five times the stacked product. -/
def oneLabelStackedInt (a : Fin 16) : Matrix (Fin 16) (Fin 16) ℤ :=
  mulIntTensor oneLabelMInt oneLabelMInt (Fin.divNat (m := 4) (n := 4) a)
    (Fin.modNat (m := 4) (n := 4) a)

theorem oneLabelTarget_eq (a : Fin 16) :
    oneLabelTarget a = (25 : ℂ)⁻¹ • complexOfInt (oneLabelTargetInt a) := rfl

theorem oneLabelStacked_eq (a : Fin 16) :
    oneLabelStacked a = ((25 : ℂ)⁻¹ * (25 : ℂ)⁻¹) • complexOfInt (oneLabelStackedInt a) :=
  mulTensor_smul_complexOfInt (25 : ℂ)⁻¹ oneLabelMInt oneLabelMInt _ _

/-! ### The two weighted slots -/

/-- The two target blocks of the one-label candidate: the same vertical tensor twice
(`p6_examples_compression_data.md`, §4.2). -/
noncomputable def oneLabelBlocks : Fin 2 → MPSTensor 16 4 := fun _ => oneLabelTarget

/-- The two weights of the one-label candidate, the eigenvalues `1` and `λ = 7/25` of the
inner-bond matrix. -/
noncomputable def oneLabelWeights : Fin 2 → ℂ := ![1, 7 / 25]

/-- Twenty-five times the two weights, the integer coefficients of the letter identity. -/
def oneLabelCoefInt : Fin 2 → ℤ := ![25, 7]

private theorem oneLabel_letter_int (a : Fin 16) :
    (2 : ℤ) • oneLabelStackedInt a =
      ∑ s, oneLabelCoefInt s • pairBlockInt (fun _ => oneLabelTargetInt) s a := by
  revert a
  decide +kernel

private theorem oneLabel_scalar (s : Fin 2) :
    (((2 : ℤ) : ℂ)) * (oneLabelWeights s * ((2 : ℂ)⁻¹ * (25 : ℂ)⁻¹)) =
      ((oneLabelCoefInt s : ℤ) : ℂ) * ((25 : ℂ)⁻¹ * (25 : ℂ)⁻¹) := by
  fin_cases s <;> norm_num [oneLabelWeights, oneLabelCoefInt]

private theorem oneLabel_hB (a : Fin 16) :
    oneLabelStacked a = (∑ s ∈ pairSlots, oneLabelWeights s •
      (basisProj pairU pairUinv (pairJ s) ⊗ₖ oneLabelBlocks s a)).submatrix
        pairReorder.symm pairReorder.symm :=
  stackedPair_letter_identity (by norm_num) oneLabelStacked_eq
    (fun _ a => oneLabelTarget_eq a) oneLabel_scalar oneLabel_letter_int a

/-! ### The compression datum -/

/-- **The multi-block asymmetric compression datum of the one-label candidate** (P5 note,
Theorem 7.7(i)–(iii)): two weighted copies of one normal block and eight zero slots. -/
noncomputable def oneLabelCompression :
    MultiBlockCompression (D := fun _ : Fin 2 => 4) oneLabelStacked pairSlots
      fun s => oneLabelWeights s • oneLabelBlocks s :=
  MultiBlockCompression.ofProjectorSum (zz := 2) pairU_mul_pairUinv pairUinv_mul_pairU
    pairRho pairReorder pairRho_inl oneLabel_hB

/-- **The remainder of the one-label compression vanishes** (P5 note, Theorem 7.7(vi)): the
conjugated tensor is block diagonal, so the extension splits. -/
theorem oneLabel_remainder : oneLabelCompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofProjectorSum (zz := 2) pairU_mul_pairUinv pairUinv_mul_pairU
    pairRho pairReorder pairRho_inl oneLabel_hB

/-! ### Consequences -/

/-- **The word-trace identity of the one-label candidate**: the periodic coefficient
`c^{(L)} = 1 + λ^L` at `λ = 7/25` (`p6_examples_compression_data.md`, §4.3). -/
theorem oneLabel_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord oneLabelStacked w) =
      (1 + (7 / 25 : ℂ) ^ w.length) * Matrix.trace (Kraus.evalWord oneLabelTarget w) := by
  have h := oneLabelCompression.trace_evalWord_eq_sum w hw
  have hs : ∀ s : Fin 2,
      Matrix.trace (Kraus.evalWord (oneLabelWeights s • oneLabelBlocks s) w) =
        oneLabelWeights s ^ w.length * Matrix.trace (Kraus.evalWord oneLabelTarget w) := by
    intro s
    rw [show oneLabelWeights s • oneLabelBlocks s =
        fun i => oneLabelWeights s • oneLabelBlocks s i from rfl,
      Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  rw [h, show pairSlots = Finset.univ from rfl, Fin.sum_univ_two, hs 0, hs 1]
  simp only [oneLabelWeights, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow]
  ring

/-- **Biorthogonal compression onto each weighted slot** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem oneLabel_isReduction (s : {s // s ∈ pairSlots}) :
    IsReduction oneLabelStacked (oneLabelWeights s.1 • oneLabelBlocks s.1)
      (oneLabelCompression.left s) (oneLabelCompression.right s) :=
  oneLabelCompression.isReduction s

/-- Two distinct slots of the one-label candidate are biorthogonal (P5 note,
Theorem 7.7(iv)). -/
theorem oneLabel_left_mul_right_of_ne {s t : {s // s ∈ pairSlots}} (h : s ≠ t) :
    oneLabelCompression.left s * oneLabelCompression.right t = 0 :=
  oneLabelCompression.left_mul_right_of_ne h

/-- **The sitewise right intertwiner of each slot**: `B^a V_s = V_s (μ_s M₀^a)`
(`p6_examples_compression_data.md`, §1.3, for the shared gauge). -/
theorem oneLabel_mul_right_eq_right_mul (a : Fin 16) (s : {s // s ∈ pairSlots}) :
    oneLabelStacked a * oneLabelCompression.right s =
      oneLabelCompression.right s * (oneLabelWeights s.1 • oneLabelBlocks s.1) a :=
  oneLabelCompression.mul_right_eq_right_mul oneLabel_remainder a s

/-- **The sitewise left intertwiner of each slot**: `W_s B^a = (μ_s M₀^a) W_s`. -/
theorem oneLabel_left_mul_eq_mul_left (a : Fin 16) (s : {s // s ∈ pairSlots}) :
    oneLabelCompression.left s * oneLabelStacked a =
      (oneLabelWeights s.1 • oneLabelBlocks s.1) a * oneLabelCompression.left s :=
  oneLabelCompression.left_mul_eq_mul_left oneLabel_remainder a s

/-- The one-label candidate has eight zero slots. -/
theorem oneLabel_z_eq : oneLabelCompression.z = 8 := rfl

/-- **The dimension count of the one-label candidate**: `16 = 4 + 4 + 8` (P5 note,
Theorem 7.7(vii)). -/
theorem oneLabel_dim_eq : (16 : ℕ) = ∑ _s ∈ pairSlots, 4 + 8 :=
  oneLabelCompression.dim_eq

/-! ### Normality of the target -/

/-- The letter realising each matrix unit of the bond algebra of the target. -/
def oneLabelUnitLetter : Fin 4 → Fin 4 → Fin 16 :=
  ![![0, 2, 8, 10], ![3, 1, 11, 9], ![12, 14, 4, 6], ![15, 13, 7, 5]]

/-- The nonzero integer factor relating that letter to its matrix unit. -/
def oneLabelUnitCoef : Fin 4 → Fin 4 → ℤ :=
  ![![16, 12, 12, 9], ![12, 16, 9, 12], ![12, 9, 16, 12], ![9, 12, 12, 16]]

private theorem oneLabelTargetInt_unit (x y : Fin 4) :
    oneLabelTargetInt (oneLabelUnitLetter x y) = oneLabelUnitCoef x y • Matrix.single x y 1 := by
  revert x y
  decide +kernel

/-- **The target of the one-label candidate is normal at blocking length one**: its sixteen
letters are scaled matrix units covering every position, so they span the four-by-four matrix
algebra (`p6_examples_compression_data.md`, §4.3). -/
theorem oneLabelTarget_isNormal : Kraus.IsNormal oneLabelTarget :=
  isNormal_of_single_eq_smul oneLabelTargetInt (by norm_num) oneLabelTarget_eq
    oneLabelUnitLetter oneLabelUnitCoef (by decide) oneLabelTargetInt_unit

end P6Compression
