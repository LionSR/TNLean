/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFP

/-!
# Closed-operator factorization and local diagonalization for `R`

**Scope: partial formalization.** This file continues
`TNLean.MPS.MPDO.RescalingStableLengthDependentRFP`, rewriting the closed
operator of the rescaling-stable example's tensor `R` through a boundary
partial isometry and diagonalizing its local factor by the hand-defined
matrix `oneLabelChi`.

## Main results

* `mpo_R_eq_B_mul_wN_mul_transpose` — the closed operator factors literally
  as `mpo R N = (25/32)^N • (B N * wN N * (B N)ᵀ)`, with `B N` a boundary
  partial isometry (`B_transpose_mul_B`: `(B N)ᵀ * B N = 1`) built from a
  two-sided inverse of `φ N` on chain-OK strings (`chainEmbed`);
* `wMat_eq_conj_diagonal_oneLabelChi` — the Walsh–Hadamard change of basis
  diagonalizes `wMat` exactly to `Matrix.diagonal (oneLabelChi.entry 0 0 0)`.
  This is a local matrix identity, not an identification with the coefficients
  of a tensor-attached BNT clause.

`mpo_R_entry_formula` is rewritten as a literal matrix product
(`mpo_R_eq_B_mul_wN_mul_transpose`):
```
mpo R N = (25/32)^N • (B N * wN N * (B N)ᵀ)
```
where `B N` is the boundary partial isometry (`B_transpose_mul_B`:
`(B N)ᵀ * B N = 1`) sending a chain of first bits `a : Fin N → Fin 2` to the
unique chain-OK physical-index string `chainEmbed N a` reading `a` back
under `φ N`.  The local factor `wMat` of this factorization is diagonalized
exactly by the Walsh–Hadamard change of basis `hadamard2 = !![1, 1; 1, -1]`
(`hadamard2_mul_diagonal_oneLabelChi_mul_hadamard2`,
`wMat_eq_conj_diagonal_oneLabelChi`):
```
hadamard2 * χ * hadamard2 = 2 • wMat,     χ = Matrix.diagonal (oneLabelChi.entry 0 0 0)
```
so the hand-defined matrix `oneLabelChi` diagonalizes the local factor of the
closed-operator formula. This strengthens the earlier eigenvector-only
spectral link (`wMat_eigenvalue_eq_oneLabelChi_entry`) to an exact matrix
identity. It does not identify `oneLabelChi` with the diagonal data of the
existential tensor-attached BNT clause for `R`; that comparison remains open
in `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 995--1010
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-! ### The boundary partial isometry and the `B W_N Bᵀ` factorization

`chainIndicator N ⊙ (wN N).submatrix (φ N) (φ N)` in `mpo_R_entry_formula` is
rewritten here as a literal `B N * wN N * (B N)ᵀ` matrix product, where
`B N` is a boundary partial isometry (`B_transpose_mul_B`) built from the
two-sided inverse `chainEmbed N` of `φ N` on chain-OK strings.  This is the
`B`, `W_N` of arXiv:1606.00608, lines 995--1010 (project example).

Project example; not from CPSV16. -/

/-- A bond label is `bondEquiv` applied to its own pair of bits. -/
lemma bondEquiv_bit1_bit2 (k : Fin 4) : bondEquiv (bit1 k, bit2 k) = k := by
  fin_cases k <;> rfl

/-- The boundary embedding reconstructing a physical-index string from a
chain of first bits: `chainEmbed N a n = bondEquiv (a n, a (n + 1))`, indices
taken cyclically via `finRotate N`.  This is a two-sided inverse of `φ N` on
chain-OK strings (`φ_chainEmbed`, `chainEmbed_φ_of_chainOK`); it builds the
boundary partial isometry `B` of `mpo_R_eq_B_mul_wN_mul_transpose`.

Project example; not from CPSV16. -/
def chainEmbed (N : ℕ) (a : Fin N → Fin 2) : Fin N → Fin 4 :=
  fun n => bondEquiv (a n, a (finRotate N n))

/-- `φ N` recovers the bit string `a` from its embedding `chainEmbed N a`. -/
@[simp] lemma φ_chainEmbed (N : ℕ) (a : Fin N → Fin 2) : φ N (chainEmbed N a) = a := by
  ext n
  simp [φ, chainEmbed]

/-- The embedding of every bit string satisfies the cyclic bond-matching
condition. -/
lemma chainOK_chainEmbed (N : ℕ) (a : Fin N → Fin 2) : ChainOK N (chainEmbed N a) := by
  intro n
  simp [chainEmbed]

/-- `chainEmbed N` recovers a chain-OK string from its own first-bit
reading. -/
lemma chainEmbed_φ_of_chainOK {N : ℕ} {p : Fin N → Fin 4} (hp : ChainOK N p) :
    chainEmbed N (φ N p) = p := by
  funext n
  simp only [chainEmbed, φ]
  rw [← hp n]
  exact bondEquiv_bit1_bit2 (p n)

/-- `chainEmbed N` is injective: it has `φ N` as a left inverse. -/
lemma chainEmbed_injective (N : ℕ) : Function.Injective (chainEmbed N) := by
  intro a a' h
  simpa using congrArg (φ N) h

/-- `p = chainEmbed N a` is equivalent, for chain-OK `p`, to `a` being the
first-bit reading of `p`. -/
lemma chainEmbed_eq_iff_of_chainOK {N : ℕ} {p : Fin N → Fin 4} (hp : ChainOK N p)
    (a : Fin N → Fin 2) : p = chainEmbed N a ↔ a = φ N p := by
  constructor
  · intro h; rw [h, φ_chainEmbed]
  · intro h; rw [h, chainEmbed_φ_of_chainOK hp]

/-- Collapsing a sum indexed by bit strings against the chain-OK embedding
condition: when `p` is chain-OK, only the term at the first-bit reading of
`p` survives. -/
lemma sum_ite_chainEmbed_mul_of_chainOK {N : ℕ} {p : Fin N → Fin 4} (hp : ChainOK N p)
    (g : (Fin N → Fin 2) → ℂ) :
    (∑ a : Fin N → Fin 2,
      (if p = chainEmbed N a then (1 : ℂ) else 0) * g a) = g (φ N p) := by
  simp only [chainEmbed_eq_iff_of_chainOK hp]
  simp [Finset.sum_ite_eq' (Finset.univ : Finset (Fin N → Fin 2)) (φ N p) g]

/-- Collapsing a sum indexed by bit strings against the chain-OK embedding
condition: when `p` is not chain-OK, no term survives (`chainEmbed N a` is
always chain-OK). -/
lemma sum_ite_chainEmbed_mul_of_not_chainOK {N : ℕ} {p : Fin N → Fin 4} (hp : ¬ ChainOK N p)
    (g : (Fin N → Fin 2) → ℂ) :
    (∑ a : Fin N → Fin 2, (if p = chainEmbed N a then (1 : ℂ) else 0) * g a) = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have hpa : p ≠ chainEmbed N a := fun h => hp (h ▸ chainOK_chainEmbed N a)
  rw [if_neg hpa, zero_mul]

/-- Mirrored form of `sum_ite_chainEmbed_mul_of_chainOK` with the indicator
on the right of the product. -/
lemma sum_mul_ite_chainEmbed_of_chainOK {N : ℕ} {p : Fin N → Fin 4} (hp : ChainOK N p)
    (g : (Fin N → Fin 2) → ℂ) :
    (∑ a : Fin N → Fin 2, g a * if p = chainEmbed N a then (1 : ℂ) else 0) = g (φ N p) := by
  rw [← sum_ite_chainEmbed_mul_of_chainOK hp g]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The boundary partial isometry of the closed-operator factorization:
`B N p a = 1` when `p` is the chain-OK physical-index string reconstructed
from the bit string `a` (`p = chainEmbed N a`), and `0` otherwise.  It
satisfies `(B N)ᵀ * B N = 1` (`B_transpose_mul_B`), because `chainEmbed N`
is injective.

Project example; not from CPSV16. -/
def B (N : ℕ) : Matrix (Fin N → Fin 4) (Fin N → Fin 2) ℂ :=
  Matrix.of fun p a => if p = chainEmbed N a then 1 else 0

/-- **`B` is a boundary partial isometry.** -/
theorem B_transpose_mul_B (N : ℕ) :
    (B N)ᵀ * B N = (1 : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) := by
  ext a a'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply, Matrix.one_apply]
  have hcollapse : ∀ p : Fin N → Fin 4,
      (if p = chainEmbed N a then (1 : ℂ) else 0) * (if p = chainEmbed N a' then 1 else 0) =
        if p = chainEmbed N a then (if p = chainEmbed N a' then (1 : ℂ) else 0) else 0 := by
    intro p; split_ifs <;> ring
  simp only [hcollapse]
  rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin N → Fin 4)) (chainEmbed N a)
    (fun p => if p = chainEmbed N a' then (1 : ℂ) else 0)]
  simp only [Finset.mem_univ, if_true]
  by_cases h : a = a'
  · simp [h]
  · have hc : chainEmbed N a ≠ chainEmbed N a' := fun hh => h ((chainEmbed_injective N) hh)
    simp [h, hc]

/-- **Entrywise agreement of `B N * wN N * (B N)ᵀ` with the
`mpo_R_entry_formula` factor.** -/
lemma B_mul_wN_mul_transpose_apply (N : ℕ) (p q : Fin N → Fin 4) :
    (B N * wN N * (B N)ᵀ) p q = chainIndicator N p q * wN N (φ N p) (φ N q) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply, chainIndicator]
  by_cases hp : ChainOK N p <;> by_cases hq : ChainOK N q
  · simp only [hp, hq, and_self, if_true]
    have step1 : ∀ x : Fin N → Fin 2,
        (∑ x_1, (if p = chainEmbed N x_1 then (1 : ℂ) else 0) * wN N x_1 x) = wN N (φ N p) x :=
      fun x => sum_ite_chainEmbed_mul_of_chainOK hp (fun x_1 => wN N x_1 x)
    simp only [step1]
    rw [one_mul]
    exact sum_mul_ite_chainEmbed_of_chainOK hq (fun x => wN N (φ N p) x)
  · simp only [hp, hq, and_false, if_false]
    rw [zero_mul]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hqx : q ≠ chainEmbed N x := fun h => hq (h ▸ chainOK_chainEmbed N x)
    rw [if_neg hqx, mul_zero]
  · simp only [hp, false_and, if_false]
    rw [zero_mul]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [sum_ite_chainEmbed_mul_of_not_chainOK hp (fun x_1 => wN N x_1 x), zero_mul]
  · simp only [hp, false_and, if_false]
    rw [zero_mul]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [sum_ite_chainEmbed_mul_of_not_chainOK hp (fun x_1 => wN N x_1 x), zero_mul]

/-- **The closed operator of `R` factors through the boundary partial
isometry.** For every positive chain length `N`,
`mpo R N = (25/32)^N • (B N * wN N * (B N)ᵀ)`, with `B N` the boundary
partial isometry satisfying `(B N)ᵀ * B N = 1` (`B_transpose_mul_B`) and
`wN N` the `N`-fold Kronecker power of `wMat`. This is the literal
`B`, `W_N` factorization of arXiv:1606.00608, lines 995--1010 (project
example).

Source: arXiv:1606.00608, lines 995--1010 (project example). -/
theorem mpo_R_eq_B_mul_wN_mul_transpose {N : ℕ} (hN : 0 < N) :
    mpo R N = (25/32 : ℂ) ^ N • (B N * wN N * (B N)ᵀ) := by
  ext p q
  rw [Matrix.smul_apply, smul_eq_mul, B_mul_wN_mul_transpose_apply, ← mul_assoc]
  exact mpo_R_entry_formula hN p q

/-! ### The local factor of `R` is diagonalized by `oneLabelChi`

`wMat`, the local factor of the `B W_N Bᵀ` factorization, is diagonalized
exactly by the (unnormalized) Walsh–Hadamard change of basis: the resulting
diagonal matrix is `Matrix.diagonal (oneLabelChi.entry 0 0 0)`. This is an
explicit matrix identity for the closed-operator factorization. It does not
identify `oneLabelChi` with the diagonal family of the existential
tensor-attached BNT clause.

Project example; not from CPSV16. -/

/-- The Walsh–Hadamard change of basis diagonalizing `wMat` (its columns are
the eigenvectors of `wMat_mulVec_ones` and `wMat_mulVec_alt`). -/
def hadamard2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

/-- `hadamard2` is (twice) its own inverse:
`hadamard2 * hadamard2 = 2 • 1`. -/
lemma hadamard2_mul_self :
    hadamard2 * hadamard2 = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, hadamard2,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
    norm_num

/-- **The local factor `wMat` is diagonalized by `oneLabelChi`.** Conjugating
`wMat` by the Walsh–Hadamard basis `hadamard2` gives
`hadamard2 * χ * hadamard2 = 2 • wMat`, with
`χ = Matrix.diagonal (oneLabelChi.entry 0 0 0) = diag(1, 7/25)`. Here `wMat`
is the local factor of the closed-operator formula
`mpo R N = (25/32)^N • (B N * wN N * (B N)ᵀ)`. No identification with the
coefficient or diagonal data of a tensor-attached BNT clause is asserted.

Source: arXiv:1606.00608, lines 995--1010 (project example). -/
theorem hadamard2_mul_diagonal_oneLabelChi_mul_hadamard2 :
    hadamard2 * Matrix.diagonal (fun k : Fin 2 => oneLabelChi.entry 0 0 0 k) * hadamard2 =
      (2 : ℂ) • wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, hadamard2,
      wMat, oneLabelChi, lambda, Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
    norm_num

/-- Equivalent form of `hadamard2_mul_diagonal_oneLabelChi_mul_hadamard2`
solved for `wMat`, using `hadamard2 * hadamard2 = 2 • 1`. -/
theorem wMat_eq_conj_diagonal_oneLabelChi :
    wMat = (1/2 : ℂ) •
      (hadamard2 * Matrix.diagonal (fun k : Fin 2 => oneLabelChi.entry 0 0 0 k) * hadamard2) := by
  rw [hadamard2_mul_diagonal_oneLabelChi_mul_hadamard2]
  module

end MPOTensor.RescalingStableLengthDependentRFP
