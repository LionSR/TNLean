/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.MonomialMatrix
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.Z3AnomalousInverseFusion
import TNLean.MPS.MPDO.OperatorCyclicSum
import TNLean.MPS.MPU.GroupRepresentation

/-!
# Anomalous `ℤ/3` example: the physical operators `U` and `U†` are unitary

**Source.** Construction of this development: no source prints the `ℤ/3` tensors of
`Z3AnomalousTensor.lean` or the operators below. Garre-Rubio and Schuch
(arXiv:2405.00439), subsection "Example: `G = ℤ_n` with fully symmetry breaking",
`Papers/2405.00439/MPU-DW.tex` lines 2038–2040, print the cyclic `3`-cocycles
`ω_j(a, b, c) = exp(2πi j a (b + c - [b + c]) / n²)` of `ℤ/n`; the representative used here has
class `j = 1` for `n = 3`, a fact checked only in the verification script and not formalized.
Garre-Rubio, Lootens and Molnár (arXiv:2203.12563), subsubsection "Periodic boundary condition
case", `Papers/2203.12563/REsubmission.tex` lines 2202–2224, construct periodic matrix product
operator representations of a finite group with a `3`-cocycle and print the `ℤ/2` instance
`∏ CZ_{i,i+1} Z_i ∏ X_i` (line 2222); the phase-decorated shift used here is a `ℤ/3` operator of
the same kind, not the operator of that construction.
No anomaly invariant is asserted here.

**Formalized here.** For a positive periodic length `L`, put
`F(s) = ∑ k, [s k ≠ 0] * (s (k + 1)).val`. The bond-two tensors of `Z3AnomalousTensor.lean`
give `U |s⟩ = ω ^ F(s) |s + 1⟩` and `V |s⟩ = ω ^ (-F(s - 1)) |s - 1⟩`, where `V` is the operator
of the tensor of `U†`. Both physical operators are unitary and `V = Uᴴ`, so both tensors are
matrix product unitaries. The first physical index is the output row. Physical adjunction does
not assert a virtual gauge or a sitewise intertwiner.

Positive length is essential: the empty word has virtual trace two, so both bond-two tensors
give the scalar two at length zero, not a unitary operator.

## Main results

* `Z3Anomalous.mpo_uTensor`, `Z3Anomalous.mpo_uDagTensor`: the physical operators as
  phase-decorated shifts.
* `Z3Anomalous.mpo_uTensor_mem_unitaryGroup`, `Z3Anomalous.mpo_uDagTensor_mem_unitaryGroup`:
  unitarity at every positive length.
* `Z3Anomalous.mpo_uDagTensor_eq_conjTranspose`: the operator of `U†` is the adjoint of `U`.
* `Z3Anomalous.uTensor_isMPU`, `Z3Anomalous.uDagTensor_isMPU`: both tensors are matrix product
  unitaries.
* `Z3Anomalous.mpo_uTensor_zero`, `Z3Anomalous.mpo_uDagTensor_zero`: the length-zero operator is
  the scalar two.

## References

- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*

## Provenance

The tensors were first recorded in `Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`,
§1–§2; that file is a verification record, not the source.
-/

noncomputable section

open scoped BigOperators Matrix

namespace Z3Anomalous

open MPSTensor

/-- The bond index recording whether a qutrit label is nonzero. -/
def occupied (s : Fin 3) : Fin 2 := if s = 0 then 0 else 1

/-- Simultaneous cyclic increment of every physical label. -/
def qutritShift (L : ℕ) : Equiv.Perm (Fin L → Fin 3) :=
  Equiv.piCongrRight fun _ ↦ Equiv.addRight 1

@[simp] theorem qutritShift_apply {L : ℕ} (s : Fin L → Fin 3) (k : Fin L) :
    qutritShift L s k = s k + 1 := rfl

@[simp] theorem qutritShift_symm_apply {L : ℕ} (s : Fin L → Fin 3) (k : Fin L) :
    (qutritShift L).symm s k = s k - 1 := by
  change s k + -1 = s k - 1
  exact (sub_eq_add_neg _ _).symm

/-- The local entries, with the outgoing bond fixed by the input label. -/
theorem uTensor_apply (i j : Fin 3) (l r : Fin 2) :
    uTensor i j l r =
      if i = j + 1 ∧ r = occupied j then eisensteinOmega ^ (l.val * j.val) else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [uTensor, uEis, occupied, complexOfEisenstein]

/-- Complex conjugation of the chosen cubic root is its square. -/
theorem star_eisensteinOmega : star eisensteinOmega = eisensteinOmega ^ 2 := by
  have h : star eisensteinOmega = -eisensteinOmega - 1 := by
    apply Complex.ext <;> simp [eisensteinOmega_re, eisensteinOmega_im]
    ring
  rw [h]
  linear_combination -eisensteinOmega_quadratic

/-- The cubic root used in the tensor has modulus one. -/
theorem star_eisensteinOmega_mul : star eisensteinOmega * eisensteinOmega = 1 := by
  rw [star_eisensteinOmega, ← pow_succ]
  simpa using congrArg eisensteinToComplex EisensteinInt.omega_pow_three

variable {L : ℕ} [NeZero L]

/-- The periodic phase exponent, including the closing edge. -/
def phaseExponent (s : Fin L → Fin 3) : ℕ :=
  ∑ k, (occupied (s k)).val * (s (k + 1)).val

/-- The physical kernel of the forward shift at every positive length. -/
theorem mpo_uTensor_apply (s t : Fin L → Fin 3) :
    MPOTensor.mpo uTensor L s t =
      if s = qutritShift L t then eisensteinOmega ^ phaseExponent t else 0 := by
  let g0 : Fin L → Fin 2 := fun k ↦ occupied (t (k - 1))
  rw [MPOTensor.mpo_apply_eq_prod_of_forced_bond uTensor s t g0 fun g hg ↦ by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hg
    refine ⟨k - 1, ?_⟩
    rw [uTensor_apply, ite_eq_right]
    intro h
    apply hk
    simpa [g0] using h.2]
  by_cases hst : s = qutritShift L t
  · have hp : ∀ k, s k = t k + 1 := fun k ↦ congrFun hst k
    rw [ite_eq_left hst]
    calc
      _ = ∏ k, eisensteinOmega ^ ((occupied (t (k - 1))).val * (t k).val) := by
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        rw [uTensor_apply, ite_eq_left ⟨hp k, by simp [g0]⟩]
      _ = eisensteinOmega ^ ∑ k, (occupied (t (k - 1))).val * (t k).val :=
        Finset.prod_pow_eq_pow_sum _ _ _
      _ = _ := by
        congr 1
        exact Fintype.sum_equiv (Equiv.subRight 1) _ _ fun k ↦ by simp
  · rw [ite_eq_right hst]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hst
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    rw [uTensor_apply, ite_eq_right]
    exact fun h ↦ hk h.1

/-- The forward operator is a phase-decorated permutation matrix. -/
theorem mpo_uTensor :
    MPOTensor.mpo uTensor L =
      Matrix.monomial (qutritShift L) fun t ↦ eisensteinOmega ^ phaseExponent t := by
  ext s t
  rw [mpo_uTensor_apply, Matrix.monomial_apply]

/-- The forward action on a computational basis vector. -/
theorem mpo_uTensor_mulVec_single (t : Fin L → Fin 3) :
    MPOTensor.mpo uTensor L *ᵥ Pi.single t 1 =
      eisensteinOmega ^ phaseExponent t • Pi.single (qutritShift L t) 1 := by
  rw [mpo_uTensor, Matrix.monomial_mulVec_single]

/-- The periodic forward operator is unitary at positive length. -/
theorem mpo_uTensor_mem_unitaryGroup :
    MPOTensor.mpo uTensor L ∈ Matrix.unitaryGroup (Fin L → Fin 3) ℂ := by
  rw [mpo_uTensor]
  refine Matrix.monomial_mem_unitaryGroup _ _ fun t ↦ ?_
  rw [star_pow, ← mul_pow, star_eisensteinOmega_mul, one_pow]

/-- The previously established group inverse is the physical adjoint. -/
theorem mpo_uDagTensor_eq_conjTranspose :
    MPOTensor.mpo uDagTensor L = (MPOTensor.mpo uTensor L)ᴴ := by
  have hu : (MPOTensor.mpo uTensor L)ᴴ * MPOTensor.mpo uTensor L = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp mpo_uTensor_mem_unitaryGroup
  calc
    MPOTensor.mpo uDagTensor L =
        ((MPOTensor.mpo uTensor L)ᴴ * MPOTensor.mpo uTensor L) *
          MPOTensor.mpo uDagTensor L := by rw [hu, one_mul]
    _ = (MPOTensor.mpo uTensor L)ᴴ := by
      rw [Matrix.mul_assoc, mpo_u_mul_uDag L (NeZero.pos L), mul_one]

/-- The inverse operator is the inverse permutation with conjugated input phases. -/
theorem mpo_uDagTensor :
    MPOTensor.mpo uDagTensor L =
      Matrix.monomial (qutritShift L).symm
        fun t ↦ star (eisensteinOmega ^ phaseExponent ((qutritShift L).symm t)) := by
  rw [mpo_uDagTensor_eq_conjTranspose, mpo_uTensor, Matrix.conjTranspose_monomial]

/-- The physical inverse kernel, with the phase evaluated after decrementing. -/
theorem mpo_uDagTensor_apply (s t : Fin L → Fin 3) :
    MPOTensor.mpo uDagTensor L s t =
      if s = (qutritShift L).symm t then
        star (eisensteinOmega ^ phaseExponent ((qutritShift L).symm t)) else 0 := by
  rw [mpo_uDagTensor, Matrix.monomial_apply]

/-- The conjugated phase is the negative integer power in the inverse action. -/
theorem star_eisensteinOmega_pow (n : ℕ) :
    star (eisensteinOmega ^ n) = eisensteinOmega ^ (-(n : ℤ)) := by
  have h : star eisensteinOmega = eisensteinOmega⁻¹ :=
    eq_inv_of_mul_eq_one_left star_eisensteinOmega_mul
  rw [star_pow, h, zpow_neg, zpow_natCast, inv_pow]

/-- The inverse kernel written as `ω ^ (-F(t - 1))`. -/
theorem mpo_uDagTensor_apply_zpow (s t : Fin L → Fin 3) :
    MPOTensor.mpo uDagTensor L s t =
      if s = (qutritShift L).symm t then
        eisensteinOmega ^ (-(phaseExponent ((qutritShift L).symm t) : ℤ)) else 0 := by
  rw [mpo_uDagTensor_apply, star_eisensteinOmega_pow]

/-- The inverse action on a computational basis vector. -/
theorem mpo_uDagTensor_mulVec_single (t : Fin L → Fin 3) :
    MPOTensor.mpo uDagTensor L *ᵥ Pi.single t 1 =
      eisensteinOmega ^ (-(phaseExponent ((qutritShift L).symm t) : ℤ)) •
        Pi.single ((qutritShift L).symm t) 1 := by
  rw [mpo_uDagTensor, Matrix.monomial_mulVec_single, star_eisensteinOmega_pow]

/-- The periodic inverse operator is unitary at positive length. -/
theorem mpo_uDagTensor_mem_unitaryGroup :
    MPOTensor.mpo uDagTensor L ∈ Matrix.unitaryGroup (Fin L → Fin 3) ℂ := by
  rw [mpo_uDagTensor_eq_conjTranspose]
  exact Unitary.star_mem mpo_uTensor_mem_unitaryGroup

/-- The forward tensor is an MPU at every positive length. -/
theorem uTensor_isMPUPos : MPOTensor.IsMPUPos uTensor := by
  intro L hL
  let : NeZero L := ⟨by omega⟩
  exact mpo_uTensor_mem_unitaryGroup

/-- The inverse tensor is an MPU at every positive length. -/
theorem uDagTensor_isMPUPos : MPOTensor.IsMPUPos uDagTensor := by
  intro L hL
  let : NeZero L := ⟨by omega⟩
  exact mpo_uDagTensor_mem_unitaryGroup

/-- The forward tensor also satisfies the all-lengths-greater-than-one MPU predicate. -/
theorem uTensor_isMPU : MPOTensor.IsMPU uTensor := uTensor_isMPUPos.isMPU

/-- The inverse tensor also satisfies the all-lengths-greater-than-one MPU predicate. -/
theorem uDagTensor_isMPU : MPOTensor.IsMPU uDagTensor := uDagTensor_isMPUPos.isMPU

/-- At length zero the forward operator is the scalar virtual dimension two. -/
theorem mpo_uTensor_zero : MPOTensor.mpo uTensor 0 = (2 : ℂ) • 1 := by
  ext s t
  have h : s = t := Subsingleton.elim _ _
  subst t
  simp [MPOTensor.mpo, MPOTensor.mpoMatrixEntry, Matrix.trace]

/-- At length zero the inverse tensor also has virtual trace two. -/
theorem mpo_uDagTensor_zero : MPOTensor.mpo uDagTensor 0 = (2 : ℂ) • 1 := by
  ext s t
  have h : s = t := Subsingleton.elim _ _
  subst t
  simp [MPOTensor.mpo, MPOTensor.mpoMatrixEntry, Matrix.trace]

end Z3Anomalous
