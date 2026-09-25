/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.NatSquarePlusOne
import TNLean.MPS.Examples.Fibonacci.FibonacciAction
import TNLean.MPS.Examples.Fibonacci.FibonacciUnit
import TNLean.MPS.FundamentalTheorem.Reduction.IntegralRankOneAction
import TNLean.MPS.ParentHamiltonian.Nonvanishing

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

**Formalized here.** The full multiplication table of the Fibonacci fusion ring on the periodic
operators, the source's two-block action as the regular representation `N_τ = [[0, 1], [1, 1]]`
on the pair of normal states of `Examples/FibonacciAction.lean`, and the one-block statement
implicit in lines 1991–1993: a length-independent eigenvalue `c` of `O_τ` on the periodic vectors
of a normal tensor is zero. The proof, a construction of this development, combines the
integrality theorem `MPOTensor.exists_nat_eq_of_mpo_mulVec_mpv_eq_smul` (such an eigenvalue is a
nonnegative integer) with the fusion rule `O_τ² = O_1 + O_τ` of `Examples/Fibonacci.lean` and the
unit law `O_1 O_τ = O_τ` of `Examples/FibonacciUnit.lean`: an eigenvalue `c ≠ 0` forces
`O_1 ψ = ψ` and then `c² = 1 + c`, which no natural number satisfies. This covers every
multiplicity `c`, not only the case `c = 1` of lines 607–634.

**Local fix (provenance):** the operator blocks `O_1`, `O_τ` are those of
`Examples/Fibonacci.lean`, whose entries the source does not print; documented in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

## Main definitions

* `FibonacciCompression.fibFusionMatrix`, `FibonacciCompression.fibNim`: the Fibonacci fusion
  matrix and the structure constants of the fusion ring.
* `FibonacciCompression.fibBlock`: the two blocks of the algebra as a family indexed by the label.

## Main results

* `FibonacciCompression.fibFusionMatrix_sq`: `N_τ² = N_τ + 1`.
* `FibonacciCompression.fibonacci_fusion_algebra`: the full multiplication table of the fusion
  ring on the periodic operators.
* `FibonacciCompression.mpo_fibOne_mulVec_chain`: the unit fixes the second normal state.
* `FibonacciCompression.fibonacci_nim_rep`: the regular representation of the fusion rules on
  the pair of normal states.
* `FibonacciCompression.fibTau_eigenvalue_eq_zero`: a length-independent eigenvalue of `O_τ` on
  the periodic vectors of a normal tensor of positive bond dimension is zero.

The single-block no-go `FibonacciCompression.not_exists_normal_fibonacci_symmetric` is derived
from the general fusion-ring obstruction in `TNLean/MPS/Symmetry/MPOSymmetry/Examples.lean`.

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

/-- **The Fibonacci fusion ring on the periodic operators** (arXiv:1511.08090, App. D.1; data
file §2, §3): at every positive system size the product of the periodic operators of two blocks
is the combination of the periodic operators of the blocks prescribed by the structure constants,
`O_1 O_1 = O_1`, `O_1 O_τ = O_τ O_1 = O_τ` and `O_τ O_τ = O_1 + O_τ`. -/
theorem fibonacci_fusion_algebra (a b : Fin 2) (L : ℕ) (hL : 0 < L) :
    mpo (fibBlock a) L * mpo (fibBlock b) L = ∑ c, (fibNim a b c : ℂ) • mpo (fibBlock c) L := by
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
coefficients `N_{a s}^t`, so `O_τ ψ_A = ψ_C` and `O_τ ψ_C = ψ_A + ψ_C`. The multiplicities are
the rows of the Fibonacci fusion matrix. -/
theorem fibonacci_nim_rep (a s : Fin 2) (L : ℕ) (hL : 0 < L) :
    mpo (fibBlock a) L *ᵥ (fun τ : Fin L → Fin 2 => mpv (fibNimTargets s) τ) =
      fun σ : Fin L → Fin 2 => ∑ t, (fibNim a s t : ℂ) * mpv (fibNimTargets t) σ := by
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

/-! ### The no-go theorem -/

/-- **A length-independent eigenvalue of the `τ` family on a normal state vanishes** (data file
§0, §6.5). If the periodic operators of the `τ` family act on the periodic vectors of a normal
tensor `A` of positive bond dimension by one scalar `c` at every positive length, then `c = 0`:
by `MPOTensor.exists_nat_eq_of_mpo_mulVec_mpv_eq_smul` the scalar is a nonnegative integer, a
nonzero one forces `O_1 ψ_A = ψ_A` through the unit law `O_1 O_τ = O_τ`, and the fusion rule
`O_τ² = O_1 + O_τ` then gives `c² = 1 + c`, impossible for a natural number. -/
theorem fibTau_eigenvalue_eq_zero {D : ℕ} [NeZero D] (A : MPSTensor 2 D) (hA : Kraus.IsNormal A)
    (c : ℂ) (h : ∀ L : ℕ, 0 < L →
      mpo fibTau L *ᵥ (fun τ : Fin L → Fin 2 => mpv A τ) = c • fun σ : Fin L → Fin 2 => mpv A σ) :
    c = 0 := by
  obtain ⟨m, rfl⟩ := exists_nat_eq_of_mpo_mulVec_mpv_eq_smul fibTau A hA c h
  by_contra hc
  obtain ⟨ℓ, hℓ, hinj⟩ := hA
  have hLpos : 0 < ℓ + 1 := Nat.succ_pos ℓ
  have hv0 : (fun σ : Fin (ℓ + 1) → Fin 2 => mpv A σ) ≠ 0 :=
    mpv_ne_zero_of_isNBlkInjective hinj hℓ le_rfl
  have hτ := h (ℓ + 1) hLpos
  have hone : mpo fibOne (ℓ + 1) *ᵥ (fun τ : Fin (ℓ + 1) → Fin 2 => mpv A τ) =
      fun σ : Fin (ℓ + 1) → Fin 2 => mpv A σ := by
    have h1 : mpo fibOne (ℓ + 1) *ᵥ (mpo fibTau (ℓ + 1) *ᵥ fun τ : Fin (ℓ + 1) → Fin 2 => mpv A τ) =
        mpo fibOne (ℓ + 1) *ᵥ ((m : ℂ) • fun σ : Fin (ℓ + 1) → Fin 2 => mpv A σ) := by
      rw [hτ]
    rw [Matrix.mulVec_mulVec, fibOne_mul_fibTau (ℓ + 1) hLpos, hτ, Matrix.mulVec_smul] at h1
    exact (smul_right_injective _ hc h1).symm
  have hfus : (mpo fibTau (ℓ + 1) * mpo fibTau (ℓ + 1)) *ᵥ
        (fun τ : Fin (ℓ + 1) → Fin 2 => mpv A τ) =
      (mpo fibOne (ℓ + 1) + mpo fibTau (ℓ + 1)) *ᵥ fun τ : Fin (ℓ + 1) → Fin 2 => mpv A τ := by
    rw [fibonacci_fusion_rule (ℓ + 1) hLpos]
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, hτ, Matrix.mulVec_smul, hτ, hone,
    smul_smul] at hfus
  have hfus' : ((m : ℂ) * m) • (fun σ : Fin (ℓ + 1) → Fin 2 => mpv A σ) =
      ((m : ℂ) + 1) • fun σ : Fin (ℓ + 1) → Fin 2 => mpv A σ := by
    rw [add_smul, one_smul]
    exact hfus.trans (add_comm _ _)
  have hmm : (m : ℂ) * m = m + 1 := smul_left_injective ℂ hv0 hfus'
  exact Nat.mul_self_ne_add_one m (by exact_mod_cast hmm)

end FibonacciCompression
