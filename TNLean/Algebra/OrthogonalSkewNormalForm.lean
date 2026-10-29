/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalComplexStructureBasis
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Orthogonal congruence of real skew-orthogonal matrices

The paired orthonormal basis of an orthogonal complex structure gives the
source's interleaved normal form, with the exact orientation `Oᵀ * Σ * O = A`.
The construction includes dimension zero and assumes no preselected invariant
planes or paired basis.

## References

* Cirac, Pérez-García, Schuch and Verstraete, arXiv:1703.09188, proof of
  `corconj`, lines 1129–1140.
-/

open scoped InnerProductSpace Matrix Kronecker

namespace Matrix

/-- In an orthonormal paired basis, an orthogonal complex structure has the
source's interleaved `Y` matrix. This is the coordinate computation underlying
arXiv:1703.09188, proof of `corconj`, lines 1129–1140. -/
theorem toMatrix_paired_orthonormalBasis
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J : E →ₗᵢ[ℝ] E) (B : OrthonormalBasis (Fin m × Fin 2) ℝ E)
    (hB : ∀ i, J (B (i, 0)) = -B (i, 1) ∧ J (B (i, 1)) = B (i, 0)) :
    LinearMap.toMatrix (B.reindex (interleavedSkewFinEquiv m)).toBasis
        (B.reindex (interleavedSkewFinEquiv m)).toBasis J.toLinearMap =
      interleavedSkewFormFin m := by
  classical
  ext i j
  obtain ⟨⟨k, a⟩, rfl⟩ := (interleavedSkewFinEquiv m).surjective i
  obtain ⟨⟨l, b⟩, rfl⟩ := (interleavedSkewFinEquiv m).surjective j
  rw [interleavedSkewFormFin_apply]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]
  fin_cases a <;> fin_cases b <;>
    simp [hB, B.inner_eq_ite, interleavedSkewForm, Matrix.one_apply, eq_comm]

/-- A real skew-symmetric orthogonal matrix is orthogonally congruent to the
interleaved sum of `!![0, 1; -1, 0]` blocks, with the source's orientation.
This is the real normal form asserted in arXiv:1703.09188, proof of `corconj`,
lines 1129–1140. No paired basis is added as a hypothesis. -/
theorem exists_orthogonal_congruence_interleavedSkewForm
    (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hA : A ∈ orthogonalGroup (Fin (2 * m)) ℝ) (hskew : Aᵀ = -A) :
    ∃ O : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ,
      O ∈ orthogonalGroup (Fin (2 * m)) ℝ ∧
        Oᵀ * interleavedSkewFormFin m * O = A := by
  classical
  let J := orthogonalLinearIsometry A hA
  obtain ⟨B, hB⟩ := LinearIsometry.exists_paired_orthonormalBasis m
    (EuclideanSpace ℝ (Fin (2 * m))) J
    (orthogonalLinearIsometry_sq hA hskew) (by simp)
  let b := B.reindex (interleavedSkewFinEquiv m)
  let e := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  let O := b.toBasis.toMatrix e.toBasis
  have hO : O ∈ orthogonalGroup (Fin (2 * m)) ℝ :=
    b.toMatrix_orthonormalBasis_mem_orthogonal e
  have hCO : e.toBasis.toMatrix b.toBasis * O = 1 :=
    e.toBasis.toMatrix_mul_toMatrix_flip b.toBasis
  have hCOt : e.toBasis.toMatrix b.toBasis = Oᵀ := by
    calc
      e.toBasis.toMatrix b.toBasis =
          e.toBasis.toMatrix b.toBasis * (O * Oᵀ) := by
            rw [(mem_orthogonalGroup_iff _ _).mp hO, mul_one]
      _ = (e.toBasis.toMatrix b.toBasis * O) * Oᵀ := (mul_assoc _ _ _).symm
      _ = Oᵀ := by rw [hCO, one_mul]
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis J.toLinearMap =
      interleavedSkewFormFin m := toMatrix_paired_orthonormalBasis J B hB
  have hchange : e.toBasis.toMatrix b.toBasis *
        LinearMap.toMatrix b.toBasis b.toBasis J.toLinearMap * O =
      LinearMap.toMatrix e.toBasis e.toBasis J.toLinearMap :=
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      (b := e.toBasis) (b' := b.toBasis) (c := e.toBasis) (c' := b.toBasis)
      (f := J.toLinearMap)
  refine ⟨O, hO, ?_⟩
  rw [hCOt, hmat] at hchange
  exact hchange.trans (by
    change LinearMap.toMatrix e.toBasis e.toBasis (Matrix.toEuclideanLin A) = A
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact LinearMap.toMatrix_toLin e.toBasis e.toBasis A)

end Matrix
