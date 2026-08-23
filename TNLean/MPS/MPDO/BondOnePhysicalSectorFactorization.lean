/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.NeighboringPreparation
import TNLean.MPS.MPDO.SALTraceTransfer

/-!
# Physical-sector factorization at virtual bond dimension one

A bond-dimension-one MPO tensor has a canonical one-sector physical
factorization: the full physical space is the left factor and the right factor
is one-dimensional.  Saturation of the area law supplies positivity of the
neighboring operator.  Literal physical-trace idempotence and the nonvanishing
consequence of saturation normalize its trace to one.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9 and Appendix C.2, lines 1381--1403, 1441--1450, and 1647--1782
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d : ℕ} [NeZero d]

namespace BondOnePhysicalSectorFactorization

/-- The physical space as one sector with left dimension `d` and right
dimension one. -/
noncomputable def sectorEquiv :
    Fin d ≃ Σ _k : Fin 1, Fin d × Fin 1 where
  toFun i := ⟨0, (i, 0)⟩
  invFun q := q.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨k, i, j⟩
    fin_cases k
    fin_cases j
    rfl

/-- The direct one-sector physical factorization of a bond-dimension-one MPO
tensor.

**Scope restriction (virtual bond dimension one):** This is a boundary
specialization of the physical-sector assertion in CPSV16 Theorem 4.9.  It
does not establish the unrestricted all-sector statement documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388, and equation `etarl`, lines 1441--1450. -/
noncomputable abbrev factorization (K : MPOTensor d 1) :
    PhysicalSectorFactorization K where
  sectorCount := 1
  leftDim := fun _ ↦ d
  rightDim := fun _ ↦ 1
  leftDim_pos := fun _ ↦ NeZero.pos d
  rightDim_pos := fun _ ↦ zero_lt_one
  sectorEquiv := sectorEquiv
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun _ beta ↦ physicalSlice K beta beta
  rightTensor := fun _ _ ↦ 1
  factorization := by
    intro beta alpha
    fin_cases beta
    fin_cases alpha
    ext q r
    obtain ⟨k, i, x⟩ := q
    obtain ⟨h, j, y⟩ := r
    fin_cases k
    fin_cases h
    fin_cases x
    fin_cases y
    simp [Matrix.reindex_apply, sectorEquiv, physicalSlice,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]

omit [NeZero d] in
/-- The physical-trace transfer of a bond-dimension-one SAL tensor with
literal physical-trace idempotence is the scalar identity. -/
lemma physTraceTransfer_eq_one (K : MPOTensor d 1) (hSAL : IsSAL K)
    (hZCL : IsPhysicalTraceIdempotent K) :
    physTraceTransfer K = 1 := by
  have hne : physTraceTransfer K ≠ 0 := hSAL.physTraceTransfer_ne_zero
  have hentry : physTraceTransfer K 0 0 ≠ 0 := by
    intro hz
    apply hne
    ext i j
    fin_cases i
    fin_cases j
    exact hz
  have hidem := congrFun (congrFun ((isPhysicalTraceIdempotent_iff K).mp hZCL) 0) 0
  have hscalar : physTraceTransfer K 0 0 * physTraceTransfer K 0 0 =
      physTraceTransfer K 0 0 := by
    simpa [Matrix.mul_apply] using hidem
  ext i j
  fin_cases i
  fin_cases j
  apply mul_left_cancel₀ hentry
  simp [hscalar]

/-- The sole neighboring operator is the one-site periodic operator, after
reindexing its physical index by the canonical singleton-sector coordinates. -/
lemma neighboringOperator_eq_submatrix (K : MPOTensor d 1)
    (k h : Fin (factorization K).sectorCount) :
    (factorization K).neighboringOperator k h =
      (mpo K 1).submatrix
        (fun x _ ↦ x.2) (fun x _ ↦ x.2) := by
  change Fin 1 at k h
  fin_cases k
  fin_cases h
  ext x y
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  fin_cases x₁
  fin_cases y₁
  simp only [PhysicalSectorFactorization.neighboringOperator_apply,
    factorization, Matrix.submatrix_apply, Finset.univ_unique, Finset.sum_singleton]
  simp only [Matrix.one_apply, physicalSlice]
  simp [mpo_apply, mpoMatrixEntry, Matrix.trace_fin_one]

/-- The direct one-sector factorization has positive neighboring operator. -/
lemma neighboringOperator_pos (K : MPOTensor d 1) (hSAL : IsSAL K) :
    ∀ k h, ((factorization K).neighboringOperator k h).PosSemidef := by
  intro k h
  rw [neighboringOperator_eq_submatrix K k h]
  let e : Fin 1 × Fin d → (Fin 1 → Fin d) := fun x _ ↦ x.2
  change ((mpo K 1).submatrix e e).PosSemidef
  exact ((Classical.choose hSAL) 1 zero_lt_one).submatrix e

/-- The neighboring operator of the direct one-sector factorization has trace
one under literal physical-trace idempotence. -/
lemma neighboringOperator_trace (K : MPOTensor d 1) (hSAL : IsSAL K)
    (hZCL : IsPhysicalTraceIdempotent K) (k h : Fin 1) :
    ((factorization K).neighboringOperator k h).trace = 1 := by
  fin_cases k
  fin_cases h
  have htransfer := congrFun (congrFun (physTraceTransfer_eq_one K hSAL hZCL) 0) 0
  simp only [physTraceTransfer, Matrix.sum_apply, Matrix.one_apply_eq] at htransfer
  change (∑ x : Fin 1 × Fin d, ∑ a : Fin 1,
    (1 : Matrix (Fin 1) (Fin 1) ℂ) x.1 x.1 *
      physicalSlice K a a x.2 x.2) = 1
  simpa [Fintype.sum_prod_type, physicalSlice] using htransfer

/-- The one-sector neighboring operator has the normalized trace
factorization $1=1\cdot1$.

**Scope restriction (virtual bond dimension one):** This is a conditional
boundary specialization of CPSV16 Theorem 4.9 and Appendix C.2.  It does not
prove the unrestricted absorbed-BNT representative assertion tracked in issue
#6775 and documented in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Theorem 4.9 and Appendix C.2, lines 1381--1403,
1441--1450, and 1647--1782. -/
noncomputable def neighboringTraceFactorization (K : MPOTensor d 1)
    (hSAL : IsSAL K) (hZCL : IsPhysicalTraceIdempotent K) :
    PhysicalSectorFactorization.NeighboringTraceFactorization
      (factorization K) where
  neighboringOperator_pos := neighboringOperator_pos K hSAL
  a := fun _ ↦ 1
  b := fun _ ↦ 1
  trace_neighboringOperator := by
    intro k h
    rw [neighboringOperator_trace K hSAL hZCL k h]
    norm_num
  sum_mul := by
    change ∑ _ : Fin 1, (1 : ℝ) * 1 = 1
    simp

end BondOnePhysicalSectorFactorization

/-- SAL and literal physical-trace idempotence imply the complete normalized
physical-sector conclusion at virtual bond dimension one.

**Scope restriction (virtual bond dimension one):** This theorem is a
conditional boundary specialization of CPSV16 Theorem 4.9.  The unrestricted
all-sector assertion remains open in issue #6775 and is documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Theorem 4.9 and Appendix C.2, lines 1381--1403,
1441--1450, and 1647--1782. -/
theorem exists_physicalSectorFactorization_of_bondDim_one
    (K : MPOTensor d 1) (hSAL : IsSAL K)
    (hZCL : IsPhysicalTraceIdempotent K) :
    ∃ F : PhysicalSectorFactorization K,
      Nonempty F.NeighboringTraceFactorization :=
  ⟨BondOnePhysicalSectorFactorization.factorization K,
    ⟨BondOnePhysicalSectorFactorization.neighboringTraceFactorization K hSAL hZCL⟩⟩

end MPOTensor
