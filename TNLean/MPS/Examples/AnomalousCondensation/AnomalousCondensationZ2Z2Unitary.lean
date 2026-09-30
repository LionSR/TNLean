/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.MonomialMatrix
import TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2Defect
import TNLean.MPS.MPDO.OperatorCyclicSum
import TNLean.MPS.MPU.GroupRepresentation

/-!
# Anomalous `ℤ/2 × ℤ/2` symmetry: physical unitarity of the two-qubit group tensors

**Source.** Construction of this development; no source prints these tensors.
Garre-Rubio, Lootens and Molnár (arXiv:2203.12563), Section "Examples of explicit MPSs and
MPO representations", subsubsection "Periodic boundary condition case",
`Papers/2203.12563/REsubmission.tex` lines 2202–2224, build periodic matrix product operator
representations of a finite group from a three-cocycle and print only the `ℤ/2` example
`U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`; Garre-Rubio and Schuch (arXiv:2405.00439), Section "The simplest
example", `Papers/2405.00439/MPU-DW.tex` lines 1123–1134, print only the CZX matrix product
unitary of `ℤ/2`. The `ℤ/2 × ℤ/2` tensors used here are built from the CZX letters and carry
the mixed (type-II) class `(-1)^{a_1 b_2 c_2}` of `H^3(ℤ/2 × ℤ/2, U(1))`.
The term *condensation defect* for the sum of the operators of a finite symmetry follows
Roumpedakis, Seifnashri and Shao (arXiv:2204.02407), Section "Higher gauging and condensation
defects", `References/2204.02407/source/condensation_draft.tex` lines 145–148, where it is the
sum over insertions of the symmetry defects; lines 1415–1417 of the same file note that for a
`ℤ/2` operator `U` the sum `P_+ = 1 + U` obeys `P_+ × P_+ = 2 P_+`.

**Formalized here.** For every positive length, the tensor `symTensor g` sends a computational
basis configuration `t` to `g ⊕ t`, with input phase
`(-1) ^ ((g.val / 2) * ∑ n, (t n).val % 2 * ((t (n + 1)).val % 2))`.
The ordinary trace includes a self-loop at length one and both cyclic edges at
length two. There is no even-length restriction. The kernel follows by fixing
the unique surviving bond configuration in the cyclic trace expansion.
Unitarity follows from the monomial kernel; the inverse uses the existing periodic
fusion rule. No associator or anomaly invariant is inferred from these physical identities.

## Main definitions

* `Z2Z2Condensation.physicalShift`: bitwise translation of every site by `g`.
* `Z2Z2Condensation.physicalBond`: the bond label fixed by an input letter.
* `Z2Z2Condensation.secondCZExponent`: the exponent of the controlled-`Z` phase on the second
  qubits.

## Main results

* `Z2Z2Condensation.mpo_symTensor_apply`, `Z2Z2Condensation.mpo_symTensor`,
  `Z2Z2Condensation.mpo_symTensor_mulVec_single`: the monomial kernel of the periodic operators.
* `Z2Z2Condensation.mpo_symTensor_mem_unitaryGroup`, `Z2Z2Condensation.symTensor_isMPUPos`:
  the periodic operators are unitary at every positive length.
* `Z2Z2Condensation.mpo_symTensor_zero`, `Z2Z2Condensation.mpo_symTensor_mul_self`,
  `Z2Z2Condensation.mpo_symTensor_inv`, `Z2Z2Condensation.mpo_symTensor_conjTranspose`:
  the identity element and the inverses.

## References

- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:2204.02407](https://arxiv.org/abs/2204.02407) -- K. Roumpedakis, S. Seifnashri,
  S.-H. Shao, *Higher Gauging and Non-invertible Condensation Defects*

## Provenance

The physical action was first recorded in
`Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/group_operator_properties.tex`,
subsection "The two-qubit group tensors" (lines 243–407); it is a verification record, not the
source.
-/

noncomputable section
open scoped BigOperators Matrix
namespace Z2Z2Condensation
open MPSTensor MPOTensor

/-- Bitwise translation of every site by the group label `g`. -/
def physicalShift (g : Fin 4) (N : ℕ) : Equiv.Perm (Fin N → Fin 4) where
  toFun t n := gmul g (t n)
  invFun t n := gmul g (t n)
  left_inv t := by
    funext n
    change gmul g (gmul g (t n)) = t n
    generalize t n = a
    fin_cases g <;> fin_cases a <;> rfl
  right_inv t := by
    funext n
    change gmul g (gmul g (t n)) = t n
    generalize t n = a
    fin_cases g <;> fin_cases a <;> rfl

/-- The outgoing bond records the second input bit for bond-two tensors. -/
def physicalBond : (g : Fin 4) → Fin 4 → Fin (bondDim g)
  | 0, _ => (0 : Fin 1)
  | 1, _ => (0 : Fin 1)
  | 2, i => (Fin.modNat (m := 2) (n := 2) i)
  | 3, i => (Fin.modNat (m := 2) (n := 2) i)

private theorem physicalBond_val (g i : Fin 4) :
    (physicalBond g i).val = (g.val / 2) * (i.val % 2) := by
  fin_cases g <;> fin_cases i <;> rfl

/-- Canonical entries, with the first physical index the output row. -/
theorem symTensor_apply (g o i : Fin 4) (l r : Fin (bondDim g)) :
    symTensor g o i l r =
      if o = gmul g i ∧ r = physicalBond g i then
        (-1 : ℂ) ^ (l.val * (i.val % 2)) else 0 := by
  fin_cases g <;> simp only [bondDim] at l r ⊢ <;>
    fin_cases o <;> fin_cases i <;> fin_cases l <;> fin_cases r <;>
    simp [symTensor, eTensor, yTensor, xTensor, xyTensor, eIntTensor,
      yIntTensor, xIntTensor, xyIntTensor, complexOfInt, gmul, physicalBond,
      Fin.modNat]


variable {N : ℕ} [NeZero N]

/-- The cyclic nearest-neighbor exponent on the second qubits. -/
def secondCZExponent (t : Fin N → Fin 4) : ℕ :=
  ∑ n, (t n).val % 2 * ((t (n + 1)).val % 2)

/-- The computational-basis kernel, with the sign evaluated before the bit flips. -/
theorem mpo_symTensor_apply (g : Fin 4) (s t : Fin N → Fin 4) :
    mpo (symTensor g) N s t =
      if s = physicalShift g N t then
        (-1 : ℂ) ^ ((g.val / 2) * secondCZExponent t) else 0 := by
  rw [mpo_apply_of_forced_right_bond (symTensor_apply g), secondCZExponent, Finset.mul_sum,
    ← Finset.prod_pow_eq_pow_sum]
  simp only [physicalBond_val, Nat.mul_assoc]
  rfl

/-- The periodic operator is a signed permutation matrix. -/
theorem mpo_symTensor (g : Fin 4) :
    mpo (symTensor g) N = Matrix.monomial (physicalShift g N)
      (fun t ↦ (-1 : ℂ) ^ ((g.val / 2) * secondCZExponent t)) := by
  ext s t
  rw [mpo_symTensor_apply, Matrix.monomial_apply]

/-- Action on a computational basis vector. -/
theorem mpo_symTensor_mulVec_single (g : Fin 4) (t : Fin N → Fin 4) :
    mpo (symTensor g) N *ᵥ Pi.single t 1 =
      (-1 : ℂ) ^ ((g.val / 2) * secondCZExponent t) •
        Pi.single (physicalShift g N t) 1 := by
  rw [mpo_symTensor, Matrix.monomial_mulVec_single]

/-- Every group operator is unitary on every positive ring. -/
theorem mpo_symTensor_mem_unitaryGroup (g : Fin 4) :
    mpo (symTensor g) N ∈ Matrix.unitaryGroup (Fin N → Fin 4) ℂ := by
  rw [mpo_symTensor]
  refine Matrix.monomial_mem_unitaryGroup _ _ fun t ↦ ?_
  rw [star_pow, star_neg, star_one, ← mul_pow]
  simp

/-- Every symmetry tensor is a positive-length matrix product unitary. -/
theorem symTensor_isMPUPos (g : Fin 4) : IsMPUPos (symTensor g) := by
  intro N hN
  let : NeZero N := ⟨by omega⟩
  exact mpo_symTensor_mem_unitaryGroup g

/-- The identity tensor contracts to the physical identity. -/
theorem mpo_symTensor_zero : mpo (symTensor 0) N = 1 := by
  rw [mpo_symTensor]
  have hs : physicalShift 0 N = 1 := by ext t n; rfl
  simp only [hs, Fin.val_zero, Nat.zero_div, Nat.zero_mul, pow_zero]
  exact Matrix.monomial_one

/-- The square follows from the established periodic fusion table. -/
theorem mpo_symTensor_mul_self (g : Fin 4) :
    mpo (symTensor g) N * mpo (symTensor g) N =
      fusionSign g g ^ N • (1 : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) := by
  rw [mpo_symTensor_mul g g N (NeZero.pos N)]
  have hg : gmul g g = 0 := by fin_cases g <;> rfl
  rw [hg, mpo_symTensor_zero]

/-- The inverse sign in bit coordinates. -/
theorem fusionSign_self_eq (g : Fin 4) :
    fusionSign g g = (-1 : ℂ) ^ ((g.val / 2) * (g.val % 2)) := by
  fin_cases g <;> simp [fusionSign]

private theorem signed_mpo_symTensor_mul (g : Fin 4) :
    (fusionSign g g ^ N • mpo (symTensor g) N) * mpo (symTensor g) N = 1 := by
  rw [Matrix.smul_mul, mpo_symTensor_mul_self, smul_smul, ← mul_pow]
  have h : fusionSign g g * fusionSign g g = 1 := by
    fin_cases g <;> simp [fusionSign]
  rw [h, one_pow, one_smul]

/-- The physical inverse, including the odd-ring sign of the diagonal element. -/
theorem mpo_symTensor_inv (g : Fin 4) :
    (mpo (symTensor g) N)⁻¹ = fusionSign g g ^ N • mpo (symTensor g) N :=
  Matrix.inv_eq_left_inv (signed_mpo_symTensor_mul g)

/-- The physical adjoint equals the signed original operator. -/
theorem mpo_symTensor_conjTranspose (g : Fin 4) :
    (mpo (symTensor g) N)ᴴ = fusionSign g g ^ N • mpo (symTensor g) N := by
  apply Matrix.left_inv_eq_left_inv _ (signed_mpo_symTensor_mul g)
  exact Matrix.mem_unitaryGroup_iff'.mp (mpo_symTensor_mem_unitaryGroup g)

end Z2Z2Condensation
