/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.Controlled
import QICLean.Algebra.MatrixAux
import TNLean.Algebra.ToEuclideanLinApply
import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Actual hard-core qubit lowering and particle number

The lowering matrix is `|0⟩⟨1|`, lifted to each physical site with `siteOp`. Its squared
modulus is the local occupation projection. Their sum is exactly the diagonal matrix
counting occupied qubits, and its eigenspaces satisfy the sum-of-squared-lowering-norm
identity. These facts do not assume a gap or any bosonic commutation relations.

They are ingredients of the tree example discussed in
`docs/paper-gaps/hastings05_tree_basis_counterexample.tex`, concerning equation `oibu`
of Hastings, arXiv:cond-mat/0508554v3, lines 1690–1694.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace MatrixOrder ComplexOrder

namespace TNLean.Lattice.TreeBasisCounterexample

/-- The actual qubit lowering matrix in the occupation basis `0,1`. -/
noncomputable def qubitLowering : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

theorem qubitLowering_number : qubitLoweringᴴ * qubitLowering =
    diagonal (fun j : Fin 2 ↦ ((j : ℕ) : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitLowering, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lower a qubit at one physical site. -/
noncomputable def lowering (v : ι) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  siteOp v qubitLowering

/-- The physical total particle number. -/
noncomputable def numberOperator : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  ∑ v : ι, (lowering v)ᴴ * lowering v

/-- Number of occupied qubits in a configuration. -/
def occupation (σ : ι → Fin 2) : ℕ := ∑ v, (σ v : ℕ)

theorem lowering_number (v : ι) : (lowering v)ᴴ * lowering v =
    diagonal (fun σ : ι → Fin 2 ↦ ((σ v : ℕ) : ℂ)) := by
  unfold lowering
  rw [siteOp_conjTranspose, siteOp_mul, qubitLowering_number, siteOp_diagonal]

theorem numberOperator_eq_diagonal : (numberOperator : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) =
    diagonal (fun σ ↦ (occupation σ : ℂ)) := by
  ext σ τ
  by_cases h : σ = τ
  · subst τ
    simp [numberOperator, lowering_number, Matrix.sum_apply,
      occupation, Nat.cast_sum]
  · simp [numberOperator, lowering_number, Matrix.sum_apply, h]

theorem isStarProjection_lowering_number (v : ι) :
    IsStarProjection ((lowering v)ᴴ * lowering v) := by
  rw [lowering_number]
  apply isStarProjection_iff'.mpr
  constructor
  · rw [diagonal_mul_diagonal]
    congr 1
    funext σ
    have hv : (σ v : ℕ) = 0 ∨ (σ v : ℕ) = 1 := by omega
    rcases hv with hv | hv <;> simp [hv]
  · simp only [star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext σ
    simp

theorem norm_lowering_le_one (v : ι) : ‖lowering v‖ ≤ 1 := by
  have hp := IsStarProjection.norm_le _ (isStarProjection_lowering_number v)
  have he := CStarRing.norm_star_mul_self (x := lowering v)
  change ‖(lowering v)ᴴ * lowering v‖ = ‖lowering v‖ * ‖lowering v‖ at he
  nlinarith [norm_nonneg (lowering v)]

/-- Every physical qubit lowering is a contraction on state vectors. -/
theorem norm_lowering_apply_le (v : ι) (φ : EuclideanSpace ℂ (ι → Fin 2)) :
    ‖toEuclideanLin (lowering v) φ‖ ≤ ‖φ‖ := by
  have haction : ‖toEuclideanLin (lowering v) φ‖ ≤ ‖lowering v‖ * ‖φ‖ := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin, ← l2_opNorm_toEuclideanCLM]
    exact ContinuousLinearMap.le_opNorm _ _
  exact haction.trans ((mul_le_mul_of_nonneg_right (norm_lowering_le_one v)
    (norm_nonneg φ)).trans_eq (one_mul _))

/-- A physical particle sector is the corresponding eigenspace of the actual number operator. -/
def IsParticleSector (m : ℕ) (φ : EuclideanSpace ℂ (ι → Fin 2)) : Prop :=
  toEuclideanLin numberOperator φ = (m : ℂ) • φ

theorem re_inner_numberOperator (φ : EuclideanSpace ℂ (ι → Fin 2)) :
    (⟪φ, toEuclideanLin numberOperator φ⟫_ℂ).re =
      ∑ v : ι, ‖toEuclideanLin (lowering v) φ‖ ^ 2 := by
  simp only [numberOperator, map_sum, LinearMap.sum_apply, inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

theorem sum_norm_lowering_sq_of_sector {m : ℕ} {φ : EuclideanSpace ℂ (ι → Fin 2)}
    (hφ : IsParticleSector m φ) :
    ∑ v : ι, ‖toEuclideanLin (lowering v) φ‖ ^ 2 = (m : ℝ) * ‖φ‖ ^ 2 := by
  rw [← re_inner_numberOperator, hφ, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

end TNLean.Lattice.TreeBasisCounterexample
