/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondState
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Bond isometries on the actual endpoint spaces

The bond map in Section 7 acts on matching irreducible sectors of the two
physical endpoints. Their canonical inclusion into the full endpoint-pair
space is an isometry. Composing its adjoint with multiplicity restoration
gives an operator on the full physical bond space whose initial projection
is precisely the matching-sector support.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
`Papers/1001.3807/paper_v3.tex`, lines 2992–3019.
-/

open scoped Matrix BigOperators Kronecker
namespace TNLean.PEPS

/-- Include a finite family of orthonormal endpoint coordinates into a larger coordinate space.
Source: SCP10, Section 7, the physical bond isometries, lines 3008–3019. -/
noncomputable def endpointEmbeddingMatrix {α β : Type*} [DecidableEq α]
    (e : β ↪ α) : Matrix α β ℂ := fun r c => if r = e c then 1 else 0

/-- An injective relabelling of endpoint coordinates defines an isometry.
Source: SCP10, Section 7, the physical bond isometries, lines 3008–3019. -/
theorem endpointEmbeddingMatrix_isIsometry {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β] (e : β ↪ α) :
    Matrix.IsIsometry (endpointEmbeddingMatrix e) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, endpointEmbeddingMatrix]
  rw [Finset.sum_eq_single (e i)]
  · simp [Matrix.one_apply, e.injective.eq_iff]
  · intro r _ hri
    simp [hri]
  · simp

/-- An endpoint inclusion recovers each original coordinate at its image. -/
theorem endpointEmbeddingMatrix_mulVec_image {α β : Type*}
    [Fintype β] [DecidableEq α] (e : β ↪ α) (x : β → ℂ) (i : β) :
    (endpointEmbeddingMatrix e *ᵥ x) (e i) = x i := by
  classical
  simp [Matrix.mulVec, dotProduct, endpointEmbeddingMatrix, e.injective.eq_iff]

/-- An endpoint inclusion vanishes outside the embedded coordinate set. -/
theorem endpointEmbeddingMatrix_mulVec_eq_zero_of_notMem_range {α β : Type*}
    [Fintype β] [DecidableEq α] (e : β ↪ α) (x : β → ℂ) (a : α)
    (ha : a ∉ Set.range e) : (endpointEmbeddingMatrix e *ᵥ x) a = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  have hne : a ≠ e b := fun h => ha ⟨b, h.symm⟩
  simp only [endpointEmbeddingMatrix, hne, ↓reduceIte, zero_mul]

/-- The range of a coordinate inclusion consists precisely of vectors
vanishing off the included coordinates. -/
theorem mem_range_endpointEmbeddingMatrix_iff {α β : Type*}
    [Fintype β] [DecidableEq α] (e : β ↪ α) (ψ : α → ℂ) :
    ψ ∈ (Matrix.mulVecLin (endpointEmbeddingMatrix e)).range ↔
      ∀ a, a ∉ Set.range e → ψ a = 0 := by
  constructor
  · rintro ⟨χ, rfl⟩ a ha
    exact endpointEmbeddingMatrix_mulVec_eq_zero_of_notMem_range e χ a ha
  · intro hψ
    refine ⟨fun b => ψ (e b), ?_⟩
    funext a
    by_cases ha : a ∈ Set.range e
    · obtain ⟨b, rfl⟩ := ha
      exact endpointEmbeddingMatrix_mulVec_image e _ b
    · exact (endpointEmbeddingMatrix_mulVec_eq_zero_of_notMem_range e _ a ha).trans
        (hψ a ha).symm

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
