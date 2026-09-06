/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleTruncation
import TNLean.MPS.MPU.InverseCompatibleWordAdjoint
import TNLean.Algebra.UnitaryEntrywiseConjugation

/-!
# Unitarity and phase cancellation of the raw inverse-compatible words

The raw endpoint matrix $A_N$ is the packaged inverse-compatible truncated
symmetry with only its right source index transported back along the source-rank
equivalence. Thus it is unitary between its raw coordinate spaces. The existing
word identity $A_N=\sigma B_N^\dagger$, together with
$\sigma\overline\sigma=1$, gives $B_N=\sigma A_N^\dagger$. Consequently both
products are $\sigma$ times the identity on their respective coordinate spaces.

Source: arXiv:2502.20257, the local comparison and unitarity transport at
lines 5432–5487, the word contraction extending lines 5444–5487, and
`eq:intro_sigma` (lines 1559–1562). The bulk count is $N$; total source length
is $N+2\geq2$. No spatial reversal or additional permutation is introduced.
This is local endpoint unitarity and cancellation, not periodic sewing or the
final `eq:UUU` identity.
-/

open scoped ComplexOrder Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
  (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
    (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1)

/-- The raw word matrix is the packaged endpoint contraction with its right
source index transported back. Source: FBC25, the rank-transported candidates
at lines 5390–5432 and the local contraction at lines 5444–5487. -/
theorem inverseCompatibleWordA_eq_reindex_truncatedSymmetry (N : ℕ) :
    let e := inverseCompatibleRankEquiv U T hT
    let E := Equiv.prodCongr (Equiv.refl (Fin ℓ[U]))
      (Equiv.prodCongr (Equiv.refl (Fin N → Fin d)) e)
    inverseCompatibleWordA U T N = Matrix.reindex E.symm (Equiv.refl _)
      ((inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).truncatedSymmetry N) := by
  dsimp only
  ext ⟨l, p, s⟩ ⟨a, q, b⟩
  simp [inverseCompatibleWordA, SourceFactors.truncatedSymmetry,
    truncatedSymmetryOfEndpoints, inverseCompatibleSourceFactors_Y₁,
    inverseCompatibleSourceFactors_Y₂, Matrix.reindex_apply, Matrix.submatrix_apply]

include hU hsimple hT σ hσ in
/-- Raw endpoint-coordinate unitarity at every bulk length, by transport of the
packaged all-length result. Source: FBC25, pleasant-property transport at
lines 5486–5487, applied to `eq:truncsym` (lines 2062–2099). -/
theorem inverseCompatibleWordA_isUnitaryBetween (N : ℕ) :
    (inverseCompatibleWordA U T N).IsUnitaryBetween := by
  classical
  rw [inverseCompatibleWordA_eq_reindex_truncatedSymmetry U T hU hsimple hT σ hσ]
  exact (inverseCompatibleSourceFactors_truncatedSymmetry_isUnitaryBetween
    U T hU hsimple hT σ hσ N).reindex _ _ _

include hU hsimple hT hσ in
/-- The two raw endpoint matrices cancel with exactly one factor of $\sigma$
in either order. The first identity is on the raw source space, the second
on the physical input space. Source: FBC25, local word contraction extending
lines 5444–5487 and `eq:intro_sigma` (lines 1559–1562). This is not the
subsequent chain-sewing identity `eq:UUU`. -/
theorem inverseCompatibleWord_mul_eq_smul_one (N : ℕ) :
    inverseCompatibleWordA U T N * inverseCompatibleWordB U T N = σ • 1 ∧
      inverseCompatibleWordB U T N * inverseCompatibleWordA U T N = σ • 1 := by
  have := hU.neZero_bond
  have hσunit : σ * star σ = 1 :=
    Matrix.scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one T T σ hσ
  have hA := inverseCompatibleWordA_isUnitaryBetween U T hU hsimple hT σ hσ N
  have hAB := inverseCompatibleWordA_eq_smul_wordB_adjoint U T hT σ hσ N
  have hBA : inverseCompatibleWordB U T N = σ • (inverseCompatibleWordA U T N)ᴴ := by
    rw [hAB, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, smul_smul]
    rw [hσunit, one_smul]
  constructor
  · rw [hBA, Matrix.mul_smul, hA.2]
  · rw [hBA, Matrix.smul_mul, hA.1]

end MPOTensor
