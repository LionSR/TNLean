/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondSparseAction
import TNLean.PEPS.TorusBlockMultiplicityState

/-!
# Crossing-boundary factors of multiplicity restoration

Fix the repeated physical endpoint outside a region. The normalized bond map
then gives a rectangular map from the original virtual boundary coefficient to
a repeated virtual boundary coefficient. Contracting that map with a repeated
representation factor gives exactly the original weighted factor multiplied by
the crossing-bond amplitude. Both edge orientations are treated explicitly.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019, applied to
arbitrary virtual boundary conditions in the regional parent construction.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ν μ : I → Type*) [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
variable [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]

/-- The virtual boundary map obtained by fixing the exterior repeated endpoint.
The original boundary weight is absorbed into its coefficient. -/
def multiplicityBoundaryMap (c : I → ℂ) (z : Σ i, ν i × μ i) :
    Matrix (Σ i, ν i × μ i) (Σ i, ν i) ℂ := fun y x =>
  if multiplicityEndpointBase ν μ y = x ∧
      multiplicityEndpointCopy ν μ y = multiplicityEndpointCopy ν μ z then
    c y.1 * (Real.sqrt (Fintype.card (μ y.1) : ℝ) : ℂ)⁻¹ else 0

/-- The tail crossing factor is an actual repeated-representation boundary
contraction after the rectangular virtual boundary map. No positivity or
irreducibility hypothesis is needed for this coefficient identity. -/
theorem multiplicityBoundaryMap_tail
    (c : I → ℂ) (M : ∀ i, Matrix (ν i) (ν i) ℂ)
    (z y : Σ i, ν i × μ i) (x : Σ i, ν i) :
    (∑ a : Σ i, ν i × μ i, multiplicityBoundaryMap ν μ c z a x *
      Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) a y) =
      multiplicityBondAmplitude ν μ y z *
        Matrix.blockDiagonal' (fun i => c i • M i) x (multiplicityEndpointBase ν μ y) := by
  classical
  rcases y with ⟨i, k, m⟩
  rcases x with ⟨j, l⟩
  rcases z with ⟨h, t, n⟩
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · rw [Fintype.sum_prod_type]
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply]
    by_cases hji : j = i
    · subst j
      by_cases hhi : h = i
      · subst h
        simp [multiplicityBoundaryMap, multiplicityEndpointBase, multiplicityEndpointCopy,
          multiplicityBondAmplitude, Matrix.blockDiagonal'_apply_eq, mul_assoc, mul_comm,
          mul_left_comm, ite_and, eq_comm]
      · simp [multiplicityBoundaryMap, multiplicityEndpointBase, multiplicityEndpointCopy,
          multiplicityBondAmplitude, Ne.symm hhi]
    · have hij : i ≠ j := Ne.symm hji
      simp [multiplicityBoundaryMap, multiplicityEndpointBase, multiplicityEndpointCopy,
        Matrix.blockDiagonal'_apply_ne, hji, hij]
  · intro a _ hai
    apply Finset.sum_eq_zero
    intro b _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hai, mul_zero]
  · simp

/-- The head crossing factor obeys the corresponding boundary contraction
identity, with the repeated matrix on the other side of the boundary map. -/
theorem multiplicityBoundaryMap_head
    (c : I → ℂ) (M : ∀ i, Matrix (ν i) (ν i) ℂ)
    (z y : Σ i, ν i × μ i) (x : Σ i, ν i) :
    (∑ a : Σ i, ν i × μ i,
      Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) y a *
        multiplicityBoundaryMap ν μ c z a x) =
      multiplicityBondAmplitude ν μ y z *
        Matrix.blockDiagonal' (fun i => c i • M i) (multiplicityEndpointBase ν μ y) x := by
  have h := multiplicityBoundaryMap_tail ν μ c (fun i => (M i).transpose) z y x
  have hk (i : I) : (M i).transpose ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ) =
      (M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)).transpose := by
    simpa only [Matrix.transpose_one] using
      Matrix.kroneckerMap_transpose (fun a b : ℂ => a * b) (M i)
        (1 : Matrix (μ i) (μ i) ℂ)
  simpa only [hk, ← Matrix.transpose_smul, ← Matrix.blockDiagonal'_transpose,
    Matrix.transpose_apply, mul_comm] using h

/-- Fixing the exterior endpoint leaves a weighted pullback on the inside endpoint. -/
theorem multiplicityBoundaryMap_mulVec (c : I → ℂ) (z : Σ i, ν i × μ i)
    (ψ : (Σ i, ν i) → ℂ) (y : Σ i, ν i × μ i) :
    (multiplicityBoundaryMap ν μ c z *ᵥ ψ) y =
      c y.1 * multiplicityBondAmplitude ν μ y z * ψ (multiplicityEndpointBase ν μ y) := by
  simp [Matrix.mulVec, dotProduct, multiplicityBoundaryMap, multiplicityBondAmplitude,
    ite_and, ite_mul, mul_ite, mul_assoc]

omit [Fintype I] [∀ i, Fintype (ν i)] in
/-- The normalized boundary filter has real coefficients. -/
theorem multiplicityBoundaryMap_one_conjTranspose (z : Σ i, ν i × μ i) :
    (multiplicityBoundaryMap ν μ (fun _ => 1) z).conjTranspose =
      (multiplicityBoundaryMap ν μ (fun _ => 1) z).transpose := by
  ext x y
  change star (multiplicityBoundaryMap ν μ (fun _ => 1) z y x) =
    multiplicityBoundaryMap ν μ (fun _ => 1) z y x
  unfold multiplicityBoundaryMap
  split_ifs <;> simp

omit [Fintype I] [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)] in
/-- A block scalar can be read from the column sector, including zero off-block entries. -/
theorem blockDiagonal_weight_column
    (c : I → ℂ) (M : ∀ i, Matrix (ν i) (ν i) ℂ) (x y : Σ i, ν i) :
    Matrix.blockDiagonal' (fun i => c i • M i) x y =
      c y.1 * Matrix.blockDiagonal' M x y := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply, smul_eq_mul]
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hij, mul_zero]

omit [Fintype I] [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)] in
/-- A block scalar can be read from the row sector, including zero off-block entries. -/
theorem blockDiagonal_weight_row
    (c : I → ℂ) (M : ∀ i, Matrix (ν i) (ν i) ℂ) (x y : Σ i, ν i) :
    Matrix.blockDiagonal' (fun i => c i • M i) x y =
      c x.1 * Matrix.blockDiagonal' M x y := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply, smul_eq_mul]
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hij, mul_zero]

/-- The adjoint boundary filter carries a repeated head factor back to the
original weighted factor. Its remaining scalar depends only on the virtual
boundary label and the fixed exterior endpoint. -/
theorem multiplicityBoundaryMap_adjoint_head
    (c : I → ℂ) (hc : ∀ i, c i ≠ 0) (M : ∀ i, Matrix (ν i) (ν i) ℂ)
    (z y : Σ i, ν i × μ i) (x : Σ i, ν i) :
    ((multiplicityBoundaryMap ν μ (fun _ => 1) z).conjTranspose *ᵥ
      (fun a => Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) a y)) x =
      ((c y.1)⁻¹ * multiplicityBondAmplitude ν μ y z) *
        Matrix.blockDiagonal' (fun i => c i • M i) x (multiplicityEndpointBase ν μ y) := by
  rw [multiplicityBoundaryMap_one_conjTranspose]
  change (∑ a, multiplicityBoundaryMap ν μ (fun _ => 1) z a x *
    Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) a y) = _
  rw [multiplicityBoundaryMap_tail]
  simp only [one_smul]
  rw [blockDiagonal_weight_column]
  change _ = ((c y.1)⁻¹ * multiplicityBondAmplitude ν μ y z) *
    (c y.1 * Matrix.blockDiagonal' M x (multiplicityEndpointBase ν μ y))
  rw [mul_assoc, mul_left_comm ((c y.1)⁻¹), ← mul_assoc ((c y.1)⁻¹),
    inv_mul_cancel₀ (hc y.1), one_mul]

/-- The adjoint boundary filter also carries a repeated tail factor back to
the original weighted factor, with the same virtual-boundary scalar. -/
theorem multiplicityBoundaryMap_adjoint_tail
    (c : I → ℂ) (hc : ∀ i, c i ≠ 0) (M : ∀ i, Matrix (ν i) (ν i) ℂ)
    (z y : Σ i, ν i × μ i) (x : Σ i, ν i) :
    ((multiplicityBoundaryMap ν μ (fun _ => 1) z).conjTranspose *ᵥ
      (fun a => Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) y a)) x =
      ((c y.1)⁻¹ * multiplicityBondAmplitude ν μ y z) *
        Matrix.blockDiagonal' (fun i => c i • M i) (multiplicityEndpointBase ν μ y) x := by
  rw [multiplicityBoundaryMap_one_conjTranspose]
  change (∑ a, multiplicityBoundaryMap ν μ (fun _ => 1) z a x *
    Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) y a) = _
  simp_rw [mul_comm (multiplicityBoundaryMap ν μ (fun _ => 1) z _ x)]
  rw [multiplicityBoundaryMap_head]
  simp only [one_smul]
  rw [blockDiagonal_weight_row]
  change _ = ((c y.1)⁻¹ * multiplicityBondAmplitude ν μ y z) *
    (c y.1 * Matrix.blockDiagonal' M (multiplicityEndpointBase ν μ y) x)
  rw [mul_assoc, mul_left_comm ((c y.1)⁻¹), ← mul_assoc ((c y.1)⁻¹),
    inv_mul_cancel₀ (hc y.1), one_mul]

/-- On the actual repeated internal-bond vector, the adjoint of multiplicity
restoration returns precisely the original square-root-weighted block vector. -/
theorem fullMultiplicityBondMap_adjoint_mulVec_repeated [∀ i, Nonempty (μ i)]
    (M : ∀ i, Matrix (ν i) (ν i) ℂ) :
    (fullMultiplicityBondMap ν μ).conjTranspose *ᵥ
      (fun r => Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ))
        r.1 r.2) =
      fun r => Matrix.blockDiagonal'
        (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) • M i) r.1 r.2 := by
  rw [← fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal ν μ M,
    Matrix.mulVec_mulVec, fullMultiplicityBondMap_initialProjection]
  rw [← blockBondInclusion_mulVec ν
    (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) • M i)]
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, blockBondInclusion_isIsometry,
    Matrix.mul_one]

variable {G : Type*} [Group G]

/-- A single fourth-root weight is the scalar fourth-root multiple in each
matrix block. This retains the one-ended factors at a region boundary. -/
theorem blockFourthRootWeight_mul_blockMatrixRepresentation
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    blockFourthRootWeight d * blockMatrixRepresentation d D g =
      Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ) • D i g) := by
  change Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ) •
    (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) * Matrix.blockDiagonal' (fun i => D i g) = _
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  rw [Matrix.smul_mul, Matrix.one_mul]

/-- The corresponding head endpoint has the same weighted block factors,
because the fourth-root weights commute with the representation. -/
theorem blockMatrixRepresentation_mul_blockFourthRootWeight
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    blockMatrixRepresentation d D g * blockFourthRootWeight d =
      Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ) • D i g) := by
  rw [← (blockFourthRootWeight_commute d D g).eq]
  exact blockFourthRootWeight_mul_blockMatrixRepresentation d D g

end TNLean.PEPS
