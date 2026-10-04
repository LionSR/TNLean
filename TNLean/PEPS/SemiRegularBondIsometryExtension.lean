/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondSupport
import QICLean.Algebra.MatrixGramUnitary
/-!
# Full physical isometries extending multiplicity restoration

Multiplicity restoration initially acts isometrically on matching-sector bond
vectors. It extends to an isometry on the entire physical endpoint-pair space.
Choose one multiplicity copy in each block to embed that full input space into
the full output space. On the matching-sector subspace, this embedding and the
multiplicity-restoring map have equal Gram matrices. A unitary on the output
space identifies them, giving the required extension.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2992–3019. The extension agrees
with the actual multiplicity-restoring map on every supported vector, including
the weighted block coefficients. No dimensional inequality, chosen unitary,
or equality of PEPS states is supplied as a hypothesis.
-/

noncomputable section
open scoped Matrix Kronecker

namespace TNLean.PEPS
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ν μ : I → Type*) [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
variable [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)] [∀ i, Nonempty (μ i)]

private def virtualCopyEmbedding : (Σ i, ν i) ↪ (Σ i, ν i × μ i) where
  toFun r := ⟨r.1, r.2, Classical.arbitrary (μ r.1)⟩
  inj' := by
    intro r s h
    exact congrArg (fun t : Σ i, ν i × μ i => (⟨t.1, t.2.1⟩ : Σ i, ν i)) h

private noncomputable def pairCopyInclusion :
    Matrix ((Σ i, ν i × μ i) × (Σ i, ν i × μ i))
      ((Σ i, ν i) × (Σ i, ν i)) ℂ :=
  endpointEmbeddingMatrix ((virtualCopyEmbedding ν μ).prodMap (virtualCopyEmbedding ν μ))
/-- The matching-sector multiplicity-restoring map has a genuine full-domain
physical isometry extension, with unchanged action on all supported vectors
and on the actual weighted block matrices. Source: SCP10, Section 7,
lines 2992–3019. -/
theorem exists_isIsometry_fullMultiplicityBondMap_extension :
    ∃ T : Matrix ((Σ i, ν i × μ i) × (Σ i, ν i × μ i))
        ((Σ i, ν i) × (Σ i, ν i)) ℂ,
      Matrix.IsIsometry T ∧
      T * blockBondInclusion ν = fullMultiplicityBondMap ν μ * blockBondInclusion ν ∧
      (∀ ψ, ψ ∈ LinearMap.range (Matrix.mulVecLin (blockBondInclusion ν)) →
        T *ᵥ ψ = fullMultiplicityBondMap ν μ *ᵥ ψ) ∧
      (∀ X : ∀ i, Matrix (ν i) (ν i) ℂ,
        T *ᵥ (fun r => Matrix.blockDiagonal'
          (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) • X i) r.1 r.2) =
        fun r => Matrix.blockDiagonal'
          (fun i => X i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) r.1 r.2) := by
  let E := blockBondInclusion ν
  let F := fullMultiplicityBondMap ν μ
  let R := pairCopyInclusion ν μ
  have hE : E.conjTranspose * E = 1 := blockBondInclusion_isIsometry ν
  have hR : R.conjTranspose * R = 1 :=
    endpointEmbeddingMatrix_isIsometry
      ((virtualCopyEmbedding ν μ).prodMap (virtualCopyEmbedding ν μ))
  have hFE : (F * E).conjTranspose * (F * E) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = E.conjTranspose * (F.conjTranspose * F) * E := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [fullMultiplicityBondMap_initialProjection]
        change E.conjTranspose * (E * E.conjTranspose) * E = 1
        simp only [← Matrix.mul_assoc, hE, Matrix.one_mul]
  have hRE : (R * E).conjTranspose * (R * E) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = E.conjTranspose * (R.conjTranspose * R) * E := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hR, Matrix.mul_one, hE]
  obtain ⟨U, hUFE⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (F * E) (R * E) (hFE.trans hRE.symm)
  let u : Matrix ((Σ i, ν i × μ i) × (Σ i, ν i × μ i))
      ((Σ i, ν i × μ i) × (Σ i, ν i × μ i)) ℂ := U
  let T := u * R
  have hU : u.conjTranspose * u = 1 := by
    simpa only [u, Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp U.property
  have hT : Matrix.IsIsometry T := by
    change (u * R).conjTranspose * (u * R) = 1
    rw [Matrix.conjTranspose_mul]
    calc
      _ = R.conjTranspose * (u.conjTranspose * u) * R := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hR]
  have hTE : T * E = F * E := by
    rw [show T = u * R from rfl, Matrix.mul_assoc]
    exact hUFE.symm
  have hact : ∀ ψ, ψ ∈ LinearMap.range (Matrix.mulVecLin E) → T *ᵥ ψ = F *ᵥ ψ := by
    rintro ψ ⟨χ, rfl⟩
    change T *ᵥ (E *ᵥ χ) = F *ᵥ (E *ᵥ χ)
    rw [Matrix.mulVec_mulVec χ, hTE, ← Matrix.mulVec_mulVec χ]
  refine ⟨T, hT, hTE, hact, ?_⟩
  intro X
  apply (hact _ ⟨fun c =>
    (Real.sqrt (Fintype.card (μ c.1) : ℝ) : ℂ) * X c.1 c.2.1 c.2.2,
    blockBondInclusion_mulVec ν
      (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) • X i)⟩).trans
  exact fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal ν μ X
end TNLean.PEPS
