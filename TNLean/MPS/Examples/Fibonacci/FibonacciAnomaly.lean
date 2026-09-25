/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.NatSquarePlusOne
import TNLean.MPS.Examples.Fibonacci.FibonacciAction
import TNLean.MPS.Examples.Fibonacci.FibonacciUnit
import TNLean.MPS.Symmetry.MPOSymmetry.Character

/-!
# Fibonacci anomaly: no single normal state carries the Fibonacci symmetry

**Source.** Garre-Rubio, Lootens and Molnár 2023 (arXiv:2203.12563), Section `nonuniqueGS`,
`Papers/2203.12563/REsubmission.tex` lines 607–634: an injective matrix product state without
multiplicity, `M_{a,x}^x = 1`, is invariant only under a matrix product operator algebra with
trivial F-symbols; lines 564–568: the nonnegative integer multiplicities `M_{a,x}^y` of the action
on blocks satisfy `∑_c N_{ab}^c M_{c,x}^y = ∑_z M_{a,z}^y M_{b,x}^z`; Section `sec:examples`, lines
1991–1993: for the Fibonacci matrix product operator the only invariant family of normal states
consists of two blocks `x_1, x_τ` with `τ · x_1 = x_τ` and `τ · x_τ = x_1 + x_τ`. The operator
tensor is that of Bultinck et al. (arXiv:1511.08090), Appendix D.1.1,
`References/1511.08090/AnyonsPEPS.tex` lines 1240–1269, whose fusion rules `N_{ττ}^1 = N_{ττ}^τ = 1`
are printed at lines 1241–1243.

**Formalized here.** The Fibonacci periodic operators form a matrix product operator fusion
algebra (`MPOTensor.IsMPOFusionAlgebra`) with unit `1`; the source's two-block action is a
symmetric family (`MPOTensor.IsMPOSymmetricFamily`) whose multiplicities are the regular
representation `N_τ = [[0, 1], [1, 1]]` on the pair of normal states of
`Examples/FibonacciAction.lean`; and the one-block statement implicit in lines 1991–1993 holds: a
length-independent eigenvalue `c` of `O_τ` on the periodic vectors of a normal tensor is zero.
The last is an instance of the general fusion-character obstruction
`MPOTensor.exists_isFusionCharacter_of_isMPOSymmetric`: an eigenvalue `c ≠ 0` forces `O_1 ψ = ψ`
through the unit law `O_1 O_τ = O_τ`, so `ψ` is symmetric under the whole algebra and its
eigenvalues form a fusion character in `ℕ`, which the Fibonacci ring does not have, since
`m² = 1 + m` has no natural solution. This covers every multiplicity `c`, not only the case
`c = 1` of lines 607–634.

**Local fix (provenance):** the operator blocks `O_1`, `O_τ` are those of
`Examples/Fibonacci.lean`, whose entries the source does not print; documented in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

## Main definitions

* `FibonacciCompression.fibFusionMatrix`, `FibonacciCompression.fibNim`: the Fibonacci fusion
  matrix and the structure constants of the fusion ring.
* `FibonacciCompression.fibBlock`: the two blocks of the algebra as a family indexed by the label.

## Main results

* `FibonacciCompression.fibFusionMatrix_sq`: `N_τ² = N_τ + 1`.
* `FibonacciCompression.isMPOFusionAlgebra_fibBlock`: the full multiplication table of the
  fusion ring on the periodic operators.
* `FibonacciCompression.isFusionUnit_fibNim`, `FibonacciCompression.isNIMRep_fibNim`,
  `FibonacciCompression.not_isFusionCharacter_fibNim`: the unit, the regular representation as a
  nonnegative integer representation, and the absence of a fusion character in `ℕ`.
* `FibonacciCompression.mpo_fibOne_mulVec_chain`: the unit fixes the second normal state.
* `FibonacciCompression.isMPOSymmetricFamily_fibNimTargets`: the regular representation of the
  fusion rules on the pair of normal states.
* `FibonacciCompression.fibTau_eigenvalue_eq_zero`: a length-independent eigenvalue of `O_τ` on
  the periodic vectors of a normal tensor of positive bond dimension is zero.
* `FibonacciCompression.not_exists_normal_fibonacci_symmetric`: no normal tensor is symmetric
  under the Fibonacci algebra.

## References

- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*

## Provenance

The fusion-ring argument (the two irrational characters `φ` and `-1/φ` of `ℤ[τ]/(τ² - τ - 1)`
and the absence of a rank-one representation by nonnegative integer matrices) was first recorded
in `Notes/OpenProblemsTN/checks/asym_fibonacci_categorical_data.md`, §0, §5 and §6.5. This is a
verification record, not the source.
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open MPSTensor MPOTensor

/-! ### The fusion ring and its regular representation -/

/-- The Fibonacci fusion matrix `N_τ = [[0, 1], [1, 1]]`, the matrix of multiplication by `τ` in
the basis `1, τ` of the fusion ring `ℤ[τ]/(τ² - τ - 1)` (data file §5). -/
def fibFusionMatrix : Matrix (Fin 2) (Fin 2) ℕ := !![0, 1; 1, 1]

/-- The structure constants `N_{ab}^c` of the Fibonacci fusion ring, as the two matrices of its
regular representation: `N_1 = 1` and `N_τ = fibFusionMatrix` (data file §5). -/
def fibNim : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ
  | 0 => 1
  | 1 => fibFusionMatrix

/-- The fusion matrix satisfies the Fibonacci relation `N_τ² = N_τ + 1` (data file §5). -/
theorem fibFusionMatrix_sq : fibFusionMatrix * fibFusionMatrix = fibFusionMatrix + 1 := by
  decide +kernel

/-- The two blocks of the Fibonacci algebra as a family indexed by the label: the admissibility
projector at the trivial label and the `τ` family at `τ`. -/
def fibBlock : (a : Fin 2) → MPOTensor 2 (fibBlockDim a)
  | 0 => fibOne
  | 1 => fibTau


/-! ### The fusion algebra of the periodic operators -/

/-- **The Fibonacci fusion ring on the periodic operators** (arXiv:1511.08090, App. D.1;
arXiv:2203.12563, line 1993; data file §2, §3): at every positive system size the product of the
periodic operators of two blocks is the combination of the periodic operators of the blocks
prescribed by the structure constants, `O_1 O_1 = O_1`, `O_1 O_τ = O_τ O_1 = O_τ` and
`O_τ O_τ = O_1 + O_τ`, so the two blocks form a matrix product operator fusion algebra. -/
theorem isMPOFusionAlgebra_fibBlock : IsMPOFusionAlgebra fibBlock fibNim := by
  intro a b L hL
  match a, b with
  | 0, 0 =>
    simp only [fibBlock, fibNim, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, Nat.cast_zero, one_smul,
      zero_smul, add_zero]
    exact fibOne_mul_fibOne L hL
  | 0, 1 =>
    simp only [fibBlock, fibNim, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, Nat.cast_zero, one_smul,
      zero_smul, zero_add]
    exact fibOne_mul_fibTau L hL
  | 1, 0 =>
    simp only [fibBlock, fibNim, fibFusionMatrix, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_one, Nat.cast_zero, one_smul, zero_smul, zero_add]
    exact fibTau_mul_fibOne L hL
  | 1, 1 =>
    simp only [fibBlock, fibNim, fibFusionMatrix, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_one, one_smul]
    exact fibonacci_fusion_rule L hL

/-- The trivial label `1` is the unit of the Fibonacci fusion ring `{1, τ; τ × τ = 1 + τ}`
(arXiv:2203.12563, line 1993). -/
theorem isFusionUnit_fibNim : IsFusionUnit fibNim 0 := by
  intro b c
  fin_cases b <;> fin_cases c <;> simp [fibNim, fibFusionMatrix, Matrix.one_apply]

/-- The action `τ · x_1 = x_τ`, `τ · x_τ = x_1 + x_τ` of arXiv:2203.12563, line 1993, the
regular representation of the Fibonacci fusion ring, is a nonnegative integer representation. -/
theorem isNIMRep_fibNim : IsNIMRep fibNim fibNim := by
  intro a b x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    simp [fibNim, fibFusionMatrix, Matrix.one_apply, Fin.sum_univ_two]

/-- Project result: the Fibonacci fusion ring has no fusion character in `ℕ`, since
`m_τ² = 1 + m_τ` has no natural solution (data file §0, §6.5). -/
theorem not_isFusionCharacter_fibNim (m : Fin 2 → ℕ) : ¬ IsFusionCharacter fibNim 0 m := by
  rintro ⟨h0, hmul⟩
  have h := hmul 1 1
  simp [fibNim, fibFusionMatrix, Fin.sum_univ_two, h0] at h
  exact Nat.mul_self_ne_add_one (m 1) (by omega)

/-! ### The regular representation on the pair of normal states -/

/-- **The unit fixes the state of `C`**, `O_1 ψ_C = ψ_C`: the image `ψ_C = O_τ ψ_A` of the
all-`τ` state is admissible (data file §4.1), by the unit law `O_1 O_τ = O_τ`. -/
theorem mpo_fibOne_mulVec_chain (L : ℕ) (hL : 0 < L) :
    mpo fibOne L *ᵥ (fun τ : Fin L → Fin 2 => mpv fibChain τ) =
      fun σ : Fin L → Fin 2 => mpv fibChain σ := by
  rw [← mpo_fibTau_mulVec_allTau L hL, Matrix.mulVec_mulVec, fibOne_mul_fibTau L hL]

/-- **The regular representation of the Fibonacci fusion rules on two normal states**
(arXiv:2203.12563, lines 1991-1993; data file §4): at every positive system size the periodic
operator of the block `a` carries the periodic state of the normal tensor `s` of the pair
`(A, C)` to the combination of the two periodic states with the nonnegative integer
coefficients `N_{a s}^t`, so `O_τ ψ_A = ψ_C` and `O_τ ψ_C = ψ_A + ψ_C`: the pair is a symmetric
family whose multiplicities are the rows of the Fibonacci fusion matrices. -/
theorem isMPOSymmetricFamily_fibNimTargets :
    IsMPOSymmetricFamily fibBlock fibNimTargets fun a s t => (fibNim a s t : ℂ) := by
  intro a s L hL
  match a, s with
  | 0, 0 =>
    simp only [fibBlock, fibNim, fibNimTargets, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, Nat.cast_zero, one_mul,
      zero_mul, add_zero]
    exact mpo_fibOne_mulVec_allTau L hL
  | 0, 1 =>
    simp only [fibBlock, fibNim, fibNimTargets, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, Nat.cast_zero, one_mul,
      zero_mul, zero_add]
    exact mpo_fibOne_mulVec_chain L hL
  | 1, 0 =>
    simp only [fibBlock, fibNim, fibNimTargets, fibFusionMatrix, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_add]
    exact mpo_fibTau_mulVec_allTau L hL
  | 1, 1 =>
    simp only [fibBlock, fibNim, fibNimTargets, fibFusionMatrix, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_one, one_mul]
    exact mpo_fibTau_mulVec_chain L hL

/-! ### The no-go theorems -/

/-- **A length-independent eigenvalue of the `τ` family on a normal state vanishes** (data file
§0, §6.5). If the periodic operators of the `τ` family act on the periodic vectors of a normal
tensor `A` of positive bond dimension by one scalar `c` at every positive length, then `c = 0`.
A nonzero `c` forces `O_1 ψ_A = ψ_A` through the unit law `O_1 O_τ = O_τ`, so `A` is symmetric
under the whole Fibonacci algebra with eigenvalues `1, c`; by
`MPOTensor.exists_isFusionCharacter_of_isMPOSymmetric` these form a fusion character in `ℕ`,
which the Fibonacci ring does not have. -/
theorem fibTau_eigenvalue_eq_zero {D : ℕ} [NeZero D] (A : MPSTensor 2 D) (hA : Kraus.IsNormal A)
    (c : ℂ) (h : ∀ L : ℕ, 0 < L →
      mpo fibTau L *ᵥ (fun τ : Fin L → Fin 2 => mpv A τ) = c • fun σ : Fin L → Fin 2 => mpv A σ) :
    c = 0 := by
  by_contra hc
  have hone : ∀ L : ℕ, 0 < L → mpo fibOne L *ᵥ (fun τ : Fin L → Fin 2 => mpv A τ) =
      (1 : ℂ) • fun σ : Fin L → Fin 2 => mpv A σ := by
    intro L hL
    have h1 : mpo fibOne L *ᵥ (mpo fibTau L *ᵥ fun τ : Fin L → Fin 2 => mpv A τ) =
        mpo fibOne L *ᵥ (c • fun σ : Fin L → Fin 2 => mpv A σ) := by
      rw [h L hL]
    rw [Matrix.mulVec_mulVec, fibOne_mul_fibTau L hL, h L hL, Matrix.mulVec_smul] at h1
    rw [one_smul]
    exact (smul_right_injective _ hc h1).symm
  obtain ⟨m, -, hm⟩ := exists_isFusionCharacter_of_isMPOSymmetric (c := ![1, c])
    (e := 0) isMPOFusionAlgebra_fibBlock hA (fun a L hL => match a with
      | 0 => hone L hL
      | 1 => h L hL) rfl
  exact not_isFusionCharacter_fibNim m hm

/-- **No normal matrix product state is symmetric under the Fibonacci algebra.**

Project result, the single-block counterpart of arXiv:2203.12563, line 1993 (the only invariant
family has two blocks): there is no normal tensor of positive bond dimension whose periodic
vectors are fixed by the admissibility projector `O_1` and are eigenvectors of the `τ` family
with one length-independent eigenvalue. It is the instance of the general obstruction
`MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter` for the Fibonacci ring, which has
no fusion character in `ℕ`. -/
theorem not_exists_normal_fibonacci_symmetric :
    ¬ ∃ (D : ℕ) (A : MPSTensor 2 D) (c : ℂ), 0 < D ∧ Kraus.IsNormal A ∧
      (∀ L : ℕ, 0 < L →
        mpo fibOne L *ᵥ (fun τ : Fin L → Fin 2 => mpv A τ) = fun σ : Fin L → Fin 2 => mpv A σ) ∧
      (∀ L : ℕ, 0 < L →
        mpo fibTau L *ᵥ (fun τ : Fin L → Fin 2 => mpv A τ) =
          c • fun σ : Fin L → Fin 2 => mpv A σ) := by
  rintro ⟨D, A, c, hD, hA, hone, hτ⟩
  have : NeZero D := ⟨hD.ne'⟩
  refine not_isMPOSymmetric_of_forall_not_isFusionCharacter (c := ![1, c])
    isMPOFusionAlgebra_fibBlock not_isFusionCharacter_fibNim hA rfl fun a L hL => ?_
  match a with
  | 0 => exact (hone L hL).trans (one_smul ℂ _).symm
  | 1 => exact hτ L hL

end FibonacciCompression
