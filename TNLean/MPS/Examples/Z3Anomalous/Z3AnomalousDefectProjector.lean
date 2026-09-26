/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Algebra.PosSemidefSupport
import TNLean.Algebra.FiniteGroupUnitaryAverage
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousDefect
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousRepresentation

/-!
# Anomalous `ℤ/3` example: the normalized condensation defect is a projector

**Source.** Construction of this development, as for `Z3AnomalousDefect.lean`: no source prints
the `ℤ/3` tensors or the defect `A = 1 ⊕ U ⊕ U†`. The name *condensation defect* follows
Roumpedakis, Seifnashri and Shao (arXiv:2204.02407), subsection "Higher gauging and condensation
defects", `References/2204.02407/source/condensation_draft.tex` lines 145–150.

**Formalized here.** At every positive length `L`, the operator `P_L = O_L(A)/3` equals
`(1 + U_L + U_L²)/3` and is the normalized average of the unitary representation
`{1, U_L, U_L†}` of `ℤ/3`, so it is an orthogonal projector (`IsStarProjection`). A vector is
fixed by `P_L` exactly when it is fixed by `U_L`, so the range of `P_L` is the space of
`U_L`-invariant vectors. On a basis vector,
`P_L |t⟩ = (|t⟩ + ω^{F(t)} |Xt⟩ + ω^{-F(X⁻¹t)} |X⁻¹t⟩)/3`. Neither the shift `X` nor its
inverse fixes a configuration, so `tr U_L = tr U_L² = 0` and `rank P_L = tr P_L = 3^{L-1}`.

## Main definitions

* `Z3Anomalous.operatorRepresentation`: the operators `{1, U_L, U_L†}` at a positive length, as
  a unitary matrix representation of `ℤ/3`.
* `Z3Anomalous.defectProjector`: the normalized defect `P_L = O_L(A)/3`.

## Main results

* `Z3Anomalous.mpo_uDagTensor_eq_sq`: `U_L† = U_L²` at positive length.
* `Z3Anomalous.defectProjector_eq`: `P_L = (1 + U_L + U_L²)/3`.
* `Z3Anomalous.isStarProjection_defectProjector`: `P_L` is an orthogonal projector.
* `Z3Anomalous.defectProjector_mulVec_eq_self_iff`,
  `Z3Anomalous.range_defectProjector_mulVecLin`: the range of `P_L` is the space of
  `U_L`-invariant vectors.
* `Z3Anomalous.defectProjector_mulVec_single`: the action on a basis vector.
* `Z3Anomalous.trace_mpo_uTensor`, `Z3Anomalous.trace_mpo_uDagTensor`: both nontrivial group
  operators are traceless.
* `Z3Anomalous.rank_defectProjector`: `rank P_L = 3^{L-1}`.

## References

- [arXiv:2204.02407](https://arxiv.org/abs/2204.02407) -- K. Roumpedakis, S. Seifnashri,
  S.-H. Shao, *Higher gauging and non-invertible condensation defects*
-/

noncomputable section

open scoped Matrix

namespace Z3Anomalous

open MPOTensor TNLean.Algebra

variable {L : ℕ} [NeZero L]

/-! ### The group operators -/

/-- Project result: `U_L† = U_L²` at every positive length (`lem:asymex_z3_physical_cube`). -/
theorem mpo_uDagTensor_eq_sq : mpo uDagTensor L = mpo uTensor L ^ 2 := by
  rw [pow_two, mpo_uu L (NeZero.pos L)]

/-- The shift of every qutrit label fixes no configuration of a nonempty chain. -/
theorem qutritShift_apply_ne (t : Fin L → Fin 3) : qutritShift L t ≠ t := fun h ↦ by
  simpa using congr_fun h 0

/-- The inverse shift of every qutrit label fixes no configuration of a nonempty chain. -/
theorem qutritShift_symm_apply_ne (t : Fin L → Fin 3) : (qutritShift L).symm t ≠ t := fun h ↦ by
  simpa using congr_fun h 0

/-- The forward operator is traceless at positive length. -/
theorem trace_mpo_uTensor : (mpo uTensor L).trace = 0 := by
  rw [mpo_uTensor]
  exact Matrix.trace_monomial_eq_zero _ _ qutritShift_apply_ne

/-- The inverse operator is traceless at positive length. -/
theorem trace_mpo_uDagTensor : (mpo uDagTensor L).trace = 0 := by
  rw [mpo_uDagTensor]
  exact Matrix.trace_monomial_eq_zero _ _ qutritShift_symm_apply_ne

/-- The operators `{1, U_L, U_L†}` at a positive length, as a unitary matrix representation of
`ℤ/3`, from the operator laws `family_operator_laws`. -/
def operatorRepresentation (L : ℕ) [NeZero L] :
    Multiplicative (ZMod 3) →* Matrix.unitaryGroup (Fin L → Fin 3) ℂ :=
  family.operatorRepresentation family_operator_laws.1 family_operator_laws.2.1
    family_operator_laws.2.2.1 L (NeZero.pos L)

/-! ### The normalized defect -/

/-- The normalized condensation defect `P_L = O_L(A)/3`. -/
def defectProjector (L : ℕ) : Matrix (Fin L → Fin 3) (Fin L → Fin 3) ℂ :=
  (3 : ℂ)⁻¹ • mpo defectTensor L

/-- Project result: `P_L = (1 + U_L + U_L²)/3` at every positive length
(`lem:asymex_z3_defect_projector`). -/
theorem defectProjector_eq :
    defectProjector L = (3 : ℂ)⁻¹ • (1 + mpo uTensor L + mpo uTensor L ^ 2) := by
  rw [defectProjector, mpo_defectTensor, mpo_identityTensor, mpo_uDagTensor_eq_sq]

/-- Bridge: the normalized defect is the normalized average of the representation
`{1, U_L, U_L†}` of `ℤ/3`. -/
theorem defectProjector_eq_finiteGroupUnitaryAverage :
    defectProjector L = finiteGroupUnitaryAverage (operatorRepresentation L) := by
  have hsum : ∑ g : Multiplicative (ZMod 3), (operatorRepresentation L g : Matrix _ _ ℂ) =
      ∑ a : Fin 3, mpo (repTensor a) L :=
    Fintype.sum_equiv Multiplicative.toAdd _ _ fun _ ↦ rfl
  rw [finiteGroupUnitaryAverage, hsum, Fin.sum_univ_three, defectProjector, mpo_defectTensor]
  rfl

/-- Project result: the normalized defect is an orthogonal projector: self-adjoint and
idempotent (`lem:asymex_z3_defect_projector`). -/
theorem isStarProjection_defectProjector : IsStarProjection (defectProjector L) := by
  rw [defectProjector_eq_finiteGroupUnitaryAverage]
  exact isStarProjection_finiteGroupUnitaryAverage _

/-- `U_L P_L = P_L`: the normalized defect absorbs the forward operator. -/
theorem mpo_uTensor_mul_defectProjector :
    mpo uTensor L * defectProjector L = defectProjector L := by
  have h3 := mpo_u_pow_three L (NeZero.pos L)
  rw [defectProjector_eq, Matrix.mul_smul, mul_add, mul_add, mul_one, ← pow_two,
    ← pow_succ', h3]
  abel_nf

/-- Project result: a vector is fixed by `P_L` exactly when it is fixed by `U_L`
(`lem:asymex_z3_defect_projector`). -/
theorem defectProjector_mulVec_eq_self_iff (ψ : (Fin L → Fin 3) → ℂ) :
    defectProjector L *ᵥ ψ = ψ ↔ mpo uTensor L *ᵥ ψ = ψ := by
  constructor
  · intro h
    rw [← h, Matrix.mulVec_mulVec, mpo_uTensor_mul_defectProjector]
  · intro h
    have h2 : mpo uTensor L ^ 2 *ᵥ ψ = ψ := by
      rw [pow_two, ← Matrix.mulVec_mulVec, h, h]
    rw [defectProjector_eq, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, h, h2]
    module

/-- Project result: the range of `P_L` is the space of `U_L`-invariant vectors
(`lem:asymex_z3_defect_projector`). -/
theorem range_defectProjector_mulVecLin :
    LinearMap.range (defectProjector L).mulVecLin =
      LinearMap.ker (mpo uTensor L - 1).mulVecLin := by
  ext ψ
  rw [LinearMap.mem_range, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_zero, ← defectProjector_mulVec_eq_self_iff]
  constructor
  · rintro ⟨φ, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      isStarProjection_defectProjector.isIdempotentElem.eq]
  · exact fun h ↦ ⟨ψ, h⟩

/-- Project result: the basis action
`P_L |t⟩ = (|t⟩ + ω^{F(t)} |Xt⟩ + ω^{-F(X⁻¹t)} |X⁻¹t⟩)/3` (`lem:asymex_z3_defect_projector`). -/
theorem defectProjector_mulVec_single (t : Fin L → Fin 3) :
    defectProjector L *ᵥ Pi.single t 1 =
      (3 : ℂ)⁻¹ • (Pi.single t 1 +
        eisensteinOmega ^ phaseExponent t • Pi.single (qutritShift L t) 1 +
        eisensteinOmega ^ (-(phaseExponent ((qutritShift L).symm t) : ℤ)) •
          Pi.single ((qutritShift L).symm t) 1) := by
  rw [defectProjector, mpo_defectTensor, mpo_identityTensor, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, mpo_uTensor_mulVec_single,
    mpo_uDagTensor_mulVec_single]

/-- Project result: `rank P_L = tr P_L = 3^{L-1}` at every positive length
(`lem:asymex_z3_defect_projector`). -/
theorem rank_defectProjector : (defectProjector L).rank = 3 ^ (L - 1) := by
  have hP := isStarProjection_defectProjector (L := L)
  have hrank := Matrix.IsHermitian.rank_eq_trace_re_of_idem hP.isSelfAdjoint
    hP.isIdempotentElem.eq
  have htrace : (defectProjector L).trace = ((3 ^ (L - 1) : ℕ) : ℂ) := by
    rw [defectProjector, mpo_defectTensor, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_add, mpo_identityTensor, trace_mpo_uTensor, trace_mpo_uDagTensor,
      Matrix.trace_one, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
    simp only [Nat.succ_sub_one, pow_succ, add_zero, smul_eq_mul]
    push_cast
    field_simp
  rw [htrace, Complex.natCast_re] at hrank
  exact_mod_cast hrank

end Z3Anomalous
