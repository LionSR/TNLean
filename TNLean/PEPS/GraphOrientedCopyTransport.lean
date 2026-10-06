/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOrientedAveragingBondState
import TNLean.PEPS.GraphOpenCopyTransport
import TNLean.PEPS.SemiRegularBoundaryTransport
import TNLean.PEPS.MixedPhysicalProductMap
import TNLean.PEPS.BlockMultiplicityRepresentation

/-!
# Arbitrary-copy transport for arbitrarily oriented open regions

The copy counts mᵢ are independent of the matrix block dimensions dᵢ.
Fourth-root mᵢ weights on the single-copy source give exactly the normalized
mᵢ-copy restoration. The actual crossing factors and their adjoints transport
arbitrary virtual boundary data in both directions.

Source: SCP10, arXiv:1001.3807, Section 4.1 and Section 7,
lines 2977–3019, extended to arbitrary positive copy multiplicities.
-/

noncomputable section
open scoped Matrix BigOperators Kronecker
namespace TNLean.PEPS

section Transpose
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ν μ : I → Type*) [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
variable [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
omit [Fintype I] [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
    [∀ i, Fintype (μ i)] in
private theorem repeatedBlock_transpose
    (M : ∀ i, Matrix (ν i) (ν i) ℂ) :
    Matrix.blockDiagonal' (fun i => (M i).transpose ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) =
      (Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ))).transpose := by
  rw [Matrix.blockDiagonal'_transpose]
  congr 1
  funext i
  simpa only [Matrix.transpose_one] using
    Matrix.kroneckerMap_transpose (fun a b : ℂ => a * b) (M i)
      (1 : Matrix (μ i) (μ i) ℂ)

/-- The same copy map restores blocks whose two physical endpoints are reversed. -/
theorem fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal_transpose [∀ i, Nonempty (μ i)]
    (M : ∀ i, Matrix (ν i) (ν i) ℂ) :
    fullMultiplicityBondMap ν μ *ᵥ
      (fun r => Matrix.blockDiagonal'
        (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) • M i) r.2 r.1) =
      fun r => Matrix.blockDiagonal'
        (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ)) r.2 r.1 := by
  have h := fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal ν μ (fun i => (M i).transpose)
  simpa only [repeatedBlock_transpose, ← Matrix.transpose_smul,
    ← Matrix.blockDiagonal'_transpose, Matrix.transpose_apply] using h

/-- Its adjoint recovers the weighted block from a reversed repeated factor. -/
theorem fullMultiplicityBondMap_adjoint_mulVec_repeated_transpose [∀ i, Nonempty (μ i)]
    (M : ∀ i, Matrix (ν i) (ν i) ℂ) :
    (fullMultiplicityBondMap ν μ).conjTranspose *ᵥ
      (fun r => Matrix.blockDiagonal' (fun i => M i ⊗ₖ (1 : Matrix (μ i) (μ i) ℂ))
        r.2 r.1) =
      fun r => Matrix.blockDiagonal'
        (fun i => (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ) • M i) r.2 r.1 := by
  have h := fullMultiplicityBondMap_adjoint_mulVec_repeated ν μ (fun i => (M i).transpose)
  simpa only [repeatedBlock_transpose, ← Matrix.transpose_smul,
    ← Matrix.blockDiagonal'_transpose, Matrix.transpose_apply] using h
end Transpose

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {G : Type*} [Group G] [Fintype G]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- An internal repeated factor is pulled back to the original weighted one. -/
theorem graphOrientedOpenInternalFactor_copy_adjoint
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R) :
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))).conjTranspose *ᵥ
        graphOrientedOpenInternalFactor (blockMultiplicityRepresentation d m D) 1 o R q e =
      graphOrientedOpenInternalFactor (blockMatrixRepresentation d D)
        (blockMultiplicityRootWeight d m) o R q e := by
  let : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, hm i⟩⟩
  unfold graphOrientedOpenInternalFactor
  cases o e.1
  · simp only [Bool.false_eq_true, ↓reduceIte, one_pow, Matrix.one_mul,
      blockMultiplicityRootWeight_sq_mul]
    simpa [blockMultiplicityRepresentation] using fullMultiplicityBondMap_adjoint_mulVec_repeated
      (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun i => D i (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹))
  · simp only [↓reduceIte, one_pow, Matrix.one_mul,
      blockMultiplicityRootWeight_sq_mul]
    simpa [blockMultiplicityRepresentation] using
      fullMultiplicityBondMap_adjoint_mulVec_repeated_transpose
      (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun i => D i (q ⟨e.1.1.1, e.2.1⟩ * (q ⟨e.1.1.2, e.2.2⟩)⁻¹))

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- The adjoint of a crossing filter preserves the actual weighted boundary
factor, with a scalar depending only on the virtual and exterior labels. -/
theorem graphOrientedOpenBoundaryFactor_copy_adjoint
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R)
    (γ θ : Σ i, Fin (d i) × Fin (m i)) :
    (multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun _ => 1) γ).conjTranspose *ᵥ
        graphOrientedOpenBoundaryFactor (blockMultiplicityRepresentation d m D) 1 o R q e θ =
      (((Real.sqrt (Real.sqrt (m θ.1 : ℝ)) : ℂ)⁻¹ *
        multiplicityBondAmplitude (fun i => Fin (d i)) (fun i => Fin (m i)) θ γ) •
        graphOrientedOpenBoundaryFactor (blockMatrixRepresentation d D)
          (blockMultiplicityRootWeight d m) o R q e
            (multiplicityEndpointBase (fun i => Fin (d i)) (fun i => Fin (m i)) θ)) := by
  have hc (i : I) : (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hm i))).ne'
  funext x
  unfold graphOrientedOpenBoundaryFactor
  by_cases ht : e.1.1.1 ∈ R
  · cases o e.1
    · simp only [dite_eq_left ht, Bool.false_eq_true, ↓reduceIte, Matrix.one_mul,
      Pi.smul_apply, smul_eq_mul, blockMultiplicityRootWeight_mul]
      exact multiplicityBoundaryMap_adjoint_tail (fun i => Fin (d i)) (fun i => Fin (m i))
        (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) hc
        (fun i => D i (q ⟨e.1.1.1, ht⟩)⁻¹) γ θ x
    · simp only [dite_eq_left ht, ↓reduceIte, Matrix.mul_one, Pi.smul_apply, smul_eq_mul,
      mul_blockMultiplicityRootWeight]
      exact multiplicityBoundaryMap_adjoint_head (fun i => Fin (d i)) (fun i => Fin (m i))
        (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) hc
        (fun i => D i (q ⟨e.1.1.1, ht⟩)) γ θ x
  · cases o e.1
    · simp only [dite_eq_right ht, Bool.false_eq_true, ↓reduceIte, Matrix.mul_one,
      Pi.smul_apply, smul_eq_mul, mul_blockMultiplicityRootWeight]
      exact multiplicityBoundaryMap_adjoint_head (fun i => Fin (d i)) (fun i => Fin (m i))
        (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) hc
        (fun i => D i (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => ht h'.1)).2⟩)) γ θ x
    · simp only [dite_eq_right ht, ↓reduceIte, Matrix.one_mul, Pi.smul_apply, smul_eq_mul,
      blockMultiplicityRootWeight_mul]
      exact multiplicityBoundaryMap_adjoint_tail (fun i => Fin (d i)) (fun i => Fin (m i))
        (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) hc
        (fun i => D i (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => ht h'.1)).2⟩)⁻¹) γ θ x

/-- The adjoint regional bond transformation sends every actual repeated
open-region generator to a scalar multiple of an actual weighted generator.
The scalar is absorbed in the arbitrary virtual boundary coefficient. -/
theorem graphRegionCopyMatrix_adjoint_oriented_open
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V)
    (γ θ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (graphRegionCopyMatrix d m R γ).conjTranspose *ᵥ
        graphOrientedOpenBondCoordinates (blockMultiplicityRepresentation d m D) 1 o R θ =
      (∏ e : RB (Γ := Γ) R, (Real.sqrt (Real.sqrt (m (θ e).1 : ℝ)) : ℂ)⁻¹ *
        multiplicityBondAmplitude (fun i => Fin (d i)) (fun i => Fin (m i)) (θ e) (γ e)) •
      graphOrientedOpenBondCoordinates (blockMatrixRepresentation d D)
        (blockMultiplicityRootWeight d m) o R
        (fun e => multiplicityEndpointBase (fun i => Fin (d i)) (fun i => Fin (m i)) (θ e)) := by
  rw [graphOrientedOpenBondCoordinates_eq_sum_prod, graphRegionCopyMatrix,
    mixedPhysicalProductMatrix_conjTranspose]
  change mixedPhysicalProductMap
    (fun e => (multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun _ => 1) (γ e)).conjTranspose)
    (fun _ : RI (Γ := Γ) R =>
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))).conjTranspose) _ = _
  rw [mixedPhysicalProductMap_sum_prod]
  simp only [graphOrientedOpenBoundaryFactor_copy_adjoint o d m D hm,
    graphOrientedOpenInternalFactor_copy_adjoint o d m D hm]
  rw [graphOrientedOpenBondCoordinates_eq_sum_prod]
  funext β
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Multiplicity restoration carries the actual weighted internal factor to
the actual repeated representation factor. -/
theorem graphOrientedOpenInternalFactor_copy
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R) :
    fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)) *ᵥ
        graphOrientedOpenInternalFactor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o R q e =
      graphOrientedOpenInternalFactor (blockMultiplicityRepresentation d m D) 1 o R q e := by
  let : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, hm i⟩⟩
  unfold graphOrientedOpenInternalFactor
  cases o e.1
  · simp only [Bool.false_eq_true, ↓reduceIte, one_pow, Matrix.one_mul,
      blockMultiplicityRootWeight_sq_mul]
    simpa [blockMultiplicityRepresentation] using fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal
      (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun i => D i (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹))
  · simp only [↓reduceIte, one_pow, Matrix.one_mul,
      blockMultiplicityRootWeight_sq_mul]
    simpa [blockMultiplicityRepresentation] using
      fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal_transpose
      (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun i => D i (q ⟨e.1.1.1, e.2.1⟩ * (q ⟨e.1.1.2, e.2.2⟩)⁻¹))

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Each crossing filter sends the weighted one-ended physical factor to
an explicit linear combination of repeated virtual boundary factors. -/
theorem graphOrientedOpenBoundaryFactor_copy
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R)
    (γ : Σ i, Fin (d i) × Fin (m i)) (θ : Σ i, Fin (d i)) :
    multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i)) (fun _ => 1) γ *ᵥ
        graphOrientedOpenBoundaryFactor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o R q e θ =
      fun y => ∑ a : Σ i, Fin (d i) × Fin (m i),
        multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
          (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) γ a θ *
        graphOrientedOpenBoundaryFactor (blockMultiplicityRepresentation d m D) 1 o R q e a y := by
  funext y
  rw [multiplicityBoundaryMap_mulVec, one_mul]
  unfold graphOrientedOpenBoundaryFactor
  by_cases ht : e.1.1.1 ∈ R
  · cases o e.1
    · simp only [dite_eq_left ht, Bool.false_eq_true, ↓reduceIte, Matrix.one_mul,
      blockMultiplicityRootWeight_mul]
      exact (multiplicityBoundaryMap_tail (fun i => Fin (d i)) (fun i => Fin (m i))
        (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ))
        (fun i => D i (q ⟨e.1.1.1, ht⟩)⁻¹) γ y θ).symm
    · simp only [dite_eq_left ht, ↓reduceIte, Matrix.mul_one, mul_blockMultiplicityRootWeight]
      simpa [blockMultiplicityRepresentation, mul_comm] using
        (multiplicityBoundaryMap_head (fun i => Fin (d i)) (fun i => Fin (m i))
          (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ))
          (fun i => D i (q ⟨e.1.1.1, ht⟩)) γ y θ).symm
  · cases o e.1
    · simp only [dite_eq_right ht, Bool.false_eq_true, ↓reduceIte, Matrix.mul_one,
      mul_blockMultiplicityRootWeight]
      simpa [blockMultiplicityRepresentation, mul_comm] using
        (multiplicityBoundaryMap_head (fun i => Fin (d i)) (fun i => Fin (m i))
          (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ))
          (fun i => D i (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => ht h'.1)).2⟩)) γ y θ).symm
    · simp only [dite_eq_right ht, ↓reduceIte, Matrix.one_mul, blockMultiplicityRootWeight_mul]
      exact (multiplicityBoundaryMap_tail (fun i => Fin (d i)) (fun i => Fin (m i))
        (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ))
        (fun i => D i (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => ht h'.1)).2⟩)⁻¹) γ y θ).symm

/-- The actual regional bond map sends a weighted open-region generator to
an explicit superposition of actual repeated open-region generators. All
crossing weights are retained in the transformed virtual boundary coefficients. -/
theorem graphRegionCopyMatrix_oriented_open
    (o : Edge Γ → Bool) (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i))
    (θ : RB (Γ := Γ) R → Σ i, Fin (d i)) :
    graphRegionCopyMatrix d m R γ *ᵥ
        graphOrientedOpenBondCoordinates (blockMatrixRepresentation d D)
          (blockMultiplicityRootWeight d m) o R θ =
      ∑ a : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i),
        (∏ e : RB (Γ := Γ) R,
          multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
            (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) (γ e) (a e) (θ e)) •
        graphOrientedOpenBondCoordinates (blockMultiplicityRepresentation d m D) 1 o R a := by
  rw [graphOrientedOpenBondCoordinates_eq_sum_prod]
  change mixedPhysicalProductMap
    (fun e => multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun _ => 1) (γ e))
    (fun _ : RI (Γ := Γ) R =>
      fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))) _ = _
  rw [mixedPhysicalProductMap_sum_prod]
  simp only [graphOrientedOpenBoundaryFactor_copy o,
    graphOrientedOpenInternalFactor_copy o d m D hm]
  simp_rw [graphOrientedOpenBondCoordinates_eq_sum_prod]
  funext β
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

end TNLean.PEPS
