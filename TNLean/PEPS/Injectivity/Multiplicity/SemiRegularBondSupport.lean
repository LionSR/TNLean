/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EndpointEmbeddingMatrix
import TNLean.PEPS.Injectivity.Multiplicity.SemiRegularBondState
import Mathlib.LinearAlgebra.Matrix.Block
import QICLean.Algebra.Unitary.MatrixGramUnitary

/-!
# Bond isometries on the actual endpoint spaces

The bond map in Section 7 acts on matching irreducible sectors of the two
physical endpoints. Their canonical inclusion into the full endpoint-pair
space is an isometry. Composing its adjoint with multiplicity restoration
gives an operator on the full physical bond space whose initial projection
is precisely the matching-sector support.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2992–3019.

It also contains the following results.

* `TNLean.PEPS.exists_isIsometry_fullMultiplicityBondMap_extension`: full physical isometries
  extending multiplicity restoration.
-/

section SemiRegularBondSupport

open scoped Matrix BigOperators Kronecker
namespace TNLean.PEPS

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ν : I → Type*) [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]

/-- Regard two coordinates in the same block as a pair of full endpoint coordinates. -/
def matchingEndpointEmbedding :
    (Σ i, ν i × ν i) ↪ ((Σ i, ν i) × (Σ i, ν i)) where
  toFun c := (⟨c.1, c.2.1⟩, ⟨c.1, c.2.2⟩)
  inj' := by
    rintro ⟨i, a, b⟩ ⟨j, c, d⟩ h
    have hi : i = j := congrArg (fun r => r.1.1) h
    subst j
    have ha : a = c := by simpa using congrArg Prod.fst h
    have hb : b = d := by simpa using congrArg Prod.snd h
    subst c
    subst d
    rfl

/-- The matching-sector bond space embeds into the two full physical endpoints.
Source: SCP10, Section 7, lines 2992–3019. -/
noncomputable def blockBondInclusion :
    Matrix ((Σ i, ν i) × (Σ i, ν i)) (Σ i, ν i × ν i) ℂ :=
  endpointEmbeddingMatrix (matchingEndpointEmbedding ν)

/-- Inclusion of the matching irreducible sectors preserves the bond inner product.
Source: SCP10, Section 7, lines 2992–3019. -/
theorem blockBondInclusion_isIsometry : Matrix.IsIsometry (blockBondInclusion ν) :=
  endpointEmbeddingMatrix_isIsometry (matchingEndpointEmbedding ν)

/-- The matching-sector inclusion reconstructs the actual block-diagonal bond matrix.
Source: SCP10, Section 7, lines 2992–3007. -/
theorem blockBondInclusion_mulVec (X : ∀ i, Matrix (ν i) (ν i) ℂ) :
    blockBondInclusion ν *ᵥ (fun c => X c.1 c.2.1 c.2.2) =
      fun r => Matrix.blockDiagonal' X r.1 r.2 := by
  ext r
  rcases r with ⟨⟨i, a⟩, ⟨j, b⟩⟩
  by_cases h : i = j
  · subst j
    exact (endpointEmbeddingMatrix_mulVec_image (matchingEndpointEmbedding ν)
      (fun c => X c.1 c.2.1 c.2.2) ⟨i, (a, b)⟩).trans
        (Matrix.blockDiagonal'_apply_eq X i a b).symm
  · rw [Matrix.blockDiagonal'_apply_ne X _ _ h]
    change (∑ c, (if (⟨i, a⟩, ⟨j, b⟩) =
      ((matchingEndpointEmbedding ν) c) then (1 : ℂ) else 0) * X c.1 c.2.1 c.2.2) = 0
    apply Finset.sum_eq_zero
    intro c _
    have hc : (⟨i, a⟩, ⟨j, b⟩) ≠ matchingEndpointEmbedding ν c := by
      intro he
      have hi : i = c.1 := congrArg (fun r => r.1.1) he
      have hj : j = c.1 := congrArg (fun r => r.2.1) he
      exact h (hi.trans hj.symm)
    simp only [hc, ↓reduceIte, zero_mul]

variable (μ : I → Type*) [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]

private def multiplicityEndpointEquiv :
    (Σ c : (Σ i, ν i × ν i), μ c.1 × μ c.1) ≃
      (Σ i, (ν i × μ i) × (ν i × μ i)) where
  toFun c := ⟨c.1.1, (c.1.2.1, c.2.1), (c.1.2.2, c.2.2)⟩
  invFun r := ⟨⟨r.1, r.2.1.1, r.2.2.1⟩, r.2.1.2, r.2.2.2⟩
  left_inv := by rintro ⟨⟨i, a, b⟩, c, d⟩; rfl
  right_inv := by rintro ⟨i, ⟨a, c⟩, b, d⟩; rfl

/-- The multiplicity-restoring isometry in the paired endpoint coordinates of each block.
Source: SCP10, Section 7, lines 3008–3019. -/
noncomputable def multiplicityBlockBondMatrix :
    Matrix (Σ i, (ν i × μ i) × (ν i × μ i)) (Σ i, ν i × ν i) ℂ :=
  fun r c => multiplicityBondCoefficientMatrix (fun j : (Σ i, ν i × ν i) => μ j.1)
    ((multiplicityEndpointEquiv ν μ).symm r) c

/-- Reordering the endpoint labels preserves the multiplicity-restoring isometry.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem multiplicityBlockBondMatrix_isIsometry [∀ i, Nonempty (μ i)] :
    Matrix.IsIsometry (multiplicityBlockBondMatrix ν μ) := by
  have hJ := multiplicityBondCoefficientMatrix_isIsometry
    (fun j : (Σ i, ν i × ν i) => μ j.1)
  ext i j
  calc
    _ = ∑ r : (Σ c : (Σ i, ν i × ν i), μ c.1 × μ c.1),
        star (multiplicityBondCoefficientMatrix (fun c : (Σ i, ν i × ν i) => μ c.1) r i) *
          multiplicityBondCoefficientMatrix (fun c : (Σ i, ν i × ν i) => μ c.1) r j :=
      Fintype.sum_equiv (multiplicityEndpointEquiv ν μ).symm _ _ (fun _ => rfl)
    _ = _ := congr_fun (congr_fun hJ i) j

/-- In actual endpoint coordinates, the weighted block vector becomes its repeated block.
Source: SCP10, Section 7, lines 2992–3019. -/
theorem multiplicityBlockBondMatrix_mulVec_sqrt [∀ i, Nonempty (μ i)]
    (X : ∀ i, Matrix (ν i) (ν i) ℂ) :
    multiplicityBlockBondMatrix ν μ *ᵥ
      (fun c => (Real.sqrt (Fintype.card (μ c.1) : ℝ) : ℂ) * X c.1 c.2.1 c.2.2) =
        fun r => (X r.1 ⊗ₖ (1 : Matrix (μ r.1) (μ r.1) ℂ)) r.2.1 r.2.2 := by
  ext r
  rcases r with ⟨i, ⟨a, c⟩, b, d⟩
  have h := congr_fun (multiplicityBondCoefficientMatrix_mulVec_sqrt
    (fun j : (Σ i, ν i × ν i) => μ j.1) (fun j => X j.1 j.2.1 j.2.2))
      ⟨⟨i, a, b⟩, c, d⟩
  change (multiplicityBondCoefficientMatrix (fun j : (Σ i, ν i × ν i) => μ j.1) *ᵥ
    (fun j => (Real.sqrt (Fintype.card (μ j.1) : ℝ) : ℂ) * X j.1 j.2.1 j.2.2))
      ⟨⟨i, a, b⟩, c, d⟩ = _
  simpa only [Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero] using h

/-- Multiplicity restoration on the full physical endpoint-pair space, with its
initial matching-sector support. Source: SCP10, Section 7, lines 2992–3019. -/
noncomputable def fullMultiplicityBondMap :
    Matrix ((Σ i, ν i × μ i) × (Σ i, ν i × μ i))
      ((Σ i, ν i) × (Σ i, ν i)) ℂ :=
  blockBondInclusion (fun i => ν i × μ i) * multiplicityBlockBondMatrix ν μ *
    (blockBondInclusion ν).conjTranspose

/-- The full bond map has the matching-sector projector as its initial Gram operator.
Source: SCP10, Section 7, lines 2992–3019. -/
theorem fullMultiplicityBondMap_initialProjection [∀ i, Nonempty (μ i)] :
    (fullMultiplicityBondMap ν μ).conjTranspose * fullMultiplicityBondMap ν μ =
      blockBondInclusion ν * (blockBondInclusion ν).conjTranspose := by
  have hE := blockBondInclusion_isIsometry (fun i => ν i × μ i)
  have hJ := multiplicityBlockBondMatrix_isIsometry ν μ
  simp only [fullMultiplicityBondMap, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    _ = blockBondInclusion ν *
        ((multiplicityBlockBondMatrix ν μ).conjTranspose *
          ((blockBondInclusion (fun i => ν i × μ i)).conjTranspose *
            blockBondInclusion (fun i => ν i × μ i)) * multiplicityBlockBondMatrix ν μ) *
          (blockBondInclusion ν).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hE, Matrix.mul_one, hJ, Matrix.mul_one]

/-- The actual full-endpoint weighted block vector is carried to the regular repeated vector.
Source: SCP10, Section 7, lines 2992–3019. -/
theorem fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal [∀ i, Nonempty (μ i)]
    (X : ∀ i, Matrix (ν i) (ν i) ℂ) :
    fullMultiplicityBondMap ν μ *ᵥ
      (fun r => Matrix.blockDiagonal'
        (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) • X i) r.1 r.2) =
      fun r => Matrix.blockDiagonal'
        (fun i => X i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) r.1 r.2 := by
  have hE := blockBondInclusion_isIsometry ν
  have hFE : fullMultiplicityBondMap ν μ * blockBondInclusion ν =
      blockBondInclusion (fun i => ν i × μ i) * multiplicityBlockBondMatrix ν μ := by
    rw [fullMultiplicityBondMap, Matrix.mul_assoc, hE, Matrix.mul_one]
  rw [← blockBondInclusion_mulVec ν
    (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) • X i)]
  let x : (Σ i, ν i × ν i) → ℂ :=
    fun c => (Real.sqrt (Fintype.card (μ c.1) : ℝ) : ℂ) * X c.1 c.2.1 c.2.2
  change fullMultiplicityBondMap ν μ *ᵥ (blockBondInclusion ν *ᵥ x) = _
  rw [Matrix.mulVec_mulVec x, hFE, ← Matrix.mulVec_mulVec x]
  change blockBondInclusion (fun i => ν i × μ i) *ᵥ
    (multiplicityBlockBondMatrix ν μ *ᵥ
      (fun c => (Real.sqrt (Fintype.card (μ c.1) : ℝ) : ℂ) * X c.1 c.2.1 c.2.2)) = _
  rw [multiplicityBlockBondMatrix_mulVec_sqrt]
  exact blockBondInclusion_mulVec (fun i => ν i × μ i)
    (fun i => X i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ))

/-- The full endpoint map preserves overlaps against vectors in its initial support.
Source: SCP10, the isometric physical bond transformation in Section 7, lines 3008–3019. -/
theorem fullMultiplicityBondMap_dotProduct [∀ i, Nonempty (μ i)]
    (ψ φ : ((Σ i, ν i) × (Σ i, ν i)) → ℂ)
    (hφ : (blockBondInclusion ν * (blockBondInclusion ν).conjTranspose) *ᵥ φ = φ) :
    star (fullMultiplicityBondMap ν μ *ᵥ ψ) ⬝ᵥ
      (fullMultiplicityBondMap ν μ *ᵥ φ) = star ψ ⬝ᵥ φ := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    fullMultiplicityBondMap_initialProjection, ← Matrix.dotProduct_mulVec, hφ]

end TNLean.PEPS

end SemiRegularBondSupport

section SemiRegularBondIsometryExtension

/-!
## Full physical isometries extending multiplicity restoration

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

end

end SemiRegularBondIsometryExtension
