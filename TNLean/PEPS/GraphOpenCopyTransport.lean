/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenBondFactors
import TNLean.PEPS.SemiRegularBoundaryTransport
import TNLean.PEPS.MixedPhysicalProductMap
import TNLean.PEPS.BlockMultiplicityRepresentation

/-!
# Arbitrary-copy transport of actual open-region contractions

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
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {G : Type*} [Group G] [Fintype G]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual regional multiplicity matrix: full maps on internal bonds and
one-ended filters on crossing bonds, with their exterior coordinates fixed. -/
def graphRegionCopyMatrix (d m : I → ℕ) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    Matrix ((RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) ×
        (RI (Γ := Γ) R → (Σ i, Fin (d i) × Fin (m i)) × (Σ i, Fin (d i) × Fin (m i))))
      ((RB (Γ := Γ) R → Σ i, Fin (d i)) ×
        (RI (Γ := Γ) R → (Σ i, Fin (d i)) × (Σ i, Fin (d i)))) ℂ :=
  mixedPhysicalProductMatrix
    (fun e => multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun _ => 1) (γ e))
    (fun _ => fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)))

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- An internal repeated factor is pulled back to the original weighted one. -/
theorem graphOpenInternalFactor_copy_adjoint
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R) :
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))).conjTranspose *ᵥ
        graphOpenInternalFactor (blockMultiplicityRepresentation d m D) 1 R q e =
      graphOpenInternalFactor (blockMatrixRepresentation d D)
        (blockMultiplicityRootWeight d m) R q e := by
  let : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, hm i⟩⟩
  unfold graphOpenInternalFactor
  simp only [one_pow, Matrix.one_mul, blockMultiplicityRootWeight_sq_mul]
  simpa [blockMultiplicityRepresentation] using fullMultiplicityBondMap_adjoint_mulVec_repeated
    (fun i => Fin (d i)) (fun i => Fin (m i))
    (fun i => D i (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹))

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- The adjoint of a crossing filter preserves the actual weighted boundary
factor, with a scalar depending only on the virtual and exterior labels. -/
theorem graphOpenBoundaryFactor_copy_adjoint
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R)
    (γ θ : Σ i, Fin (d i) × Fin (m i)) :
    (multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun _ => 1) γ).conjTranspose *ᵥ
        graphOpenBoundaryFactor (blockMultiplicityRepresentation d m D) 1 R q e θ =
      (((Real.sqrt (Real.sqrt (m θ.1 : ℝ)) : ℂ)⁻¹ *
        multiplicityBondAmplitude (fun i => Fin (d i)) (fun i => Fin (m i)) θ γ) •
        graphOpenBoundaryFactor (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m)
          R q e (multiplicityEndpointBase (fun i => Fin (d i)) (fun i => Fin (m i)) θ)) := by
  have hc (i : I) : (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hm i))).ne'
  funext x
  unfold graphOpenBoundaryFactor
  by_cases ht : e.1.1.1 ∈ R
  · simp only [dite_eq_left ht, Matrix.one_mul, Pi.smul_apply, smul_eq_mul,
      blockMultiplicityRootWeight_mul]
    exact multiplicityBoundaryMap_adjoint_tail (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) hc
      (fun i => D i (q ⟨e.1.1.1, ht⟩)⁻¹) γ θ x
  · simp only [dite_eq_right ht, Matrix.mul_one, Pi.smul_apply, smul_eq_mul,
      mul_blockMultiplicityRootWeight]
    exact multiplicityBoundaryMap_adjoint_head (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) hc
      (fun i => D i (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => ht h'.1)).2⟩)) γ θ x

/-- The adjoint regional bond transformation sends every actual repeated
open-region generator to a scalar multiple of an actual weighted generator.
The scalar is absorbed in the arbitrary virtual boundary coefficient. -/
theorem graphRegionCopyMatrix_adjoint_open
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V)
    (γ θ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i)) :
    (graphRegionCopyMatrix d m R γ).conjTranspose *ᵥ
        graphOpenBondCoordinates (blockMultiplicityRepresentation d m D) 1 R θ =
      (∏ e : RB (Γ := Γ) R, (Real.sqrt (Real.sqrt (m (θ e).1 : ℝ)) : ℂ)⁻¹ *
        multiplicityBondAmplitude (fun i => Fin (d i)) (fun i => Fin (m i)) (θ e) (γ e)) •
      graphOpenBondCoordinates (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) R
        (fun e => multiplicityEndpointBase (fun i => Fin (d i)) (fun i => Fin (m i)) (θ e)) := by
  rw [graphOpenBondCoordinates_eq_sum_prod, graphRegionCopyMatrix,
    mixedPhysicalProductMatrix_conjTranspose]
  change mixedPhysicalProductMap
    (fun e => (multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun _ => 1) (γ e)).conjTranspose)
    (fun _ : RI (Γ := Γ) R =>
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))).conjTranspose) _ = _
  rw [mixedPhysicalProductMap_sum_prod]
  simp only [graphOpenBoundaryFactor_copy_adjoint d m D hm,
    graphOpenInternalFactor_copy_adjoint d m D hm]
  rw [graphOpenBondCoordinates_eq_sum_prod]
  funext β
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Multiplicity restoration carries the actual weighted internal factor to
the actual repeated representation factor. -/
theorem graphOpenInternalFactor_copy
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R) :
    fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i)) *ᵥ
        graphOpenInternalFactor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) R q e =
      graphOpenInternalFactor (blockMultiplicityRepresentation d m D) 1 R q e := by
  let : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, hm i⟩⟩
  unfold graphOpenInternalFactor
  simp only [one_pow, Matrix.one_mul, blockMultiplicityRootWeight_sq_mul]
  simpa [blockMultiplicityRepresentation] using
    fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal
      (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun i => D i (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹))

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Each crossing filter sends the weighted one-ended physical factor to
an explicit linear combination of repeated virtual boundary factors. -/
theorem graphOpenBoundaryFactor_copy
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R)
    (γ : Σ i, Fin (d i) × Fin (m i)) (θ : Σ i, Fin (d i)) :
    multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i)) (fun _ => 1) γ *ᵥ
        graphOpenBoundaryFactor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) R q e θ =
      fun y => ∑ a : Σ i, Fin (d i) × Fin (m i),
        multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
          (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) γ a θ *
        graphOpenBoundaryFactor (blockMultiplicityRepresentation d m D) 1 R q e a y := by
  funext y
  rw [multiplicityBoundaryMap_mulVec, one_mul]
  unfold graphOpenBoundaryFactor
  by_cases ht : e.1.1.1 ∈ R
  · simp only [dite_eq_left ht, Matrix.one_mul,
      blockMultiplicityRootWeight_mul]
    exact (multiplicityBoundaryMap_tail (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ))
      (fun i => D i (q ⟨e.1.1.1, ht⟩)⁻¹) γ y θ).symm
  · simp only [dite_eq_right ht, Matrix.mul_one,
      mul_blockMultiplicityRootWeight]
    simpa [blockMultiplicityRepresentation, mul_comm] using
      (multiplicityBoundaryMap_head (fun i => Fin (d i)) (fun i => Fin (m i))
        (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ))
        (fun i => D i (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => ht h'.1)).2⟩)) γ y θ).symm

/-- The actual regional bond map sends a weighted open-region generator to
an explicit superposition of actual repeated open-region generators. All
crossing weights are retained in the transformed virtual boundary coefficients. -/
theorem graphRegionCopyMatrix_open
    (d m : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (R : Finset V)
    (γ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i))
    (θ : RB (Γ := Γ) R → Σ i, Fin (d i)) :
    graphRegionCopyMatrix d m R γ *ᵥ
        graphOpenBondCoordinates (blockMatrixRepresentation d D)
          (blockMultiplicityRootWeight d m) R θ =
      ∑ a : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (m i),
        (∏ e : RB (Γ := Γ) R,
          multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
            (fun i => (Real.sqrt (Real.sqrt (m i : ℝ)) : ℂ)) (γ e) (a e) (θ e)) •
        graphOpenBondCoordinates (blockMultiplicityRepresentation d m D) 1 R a := by
  rw [graphOpenBondCoordinates_eq_sum_prod]
  change mixedPhysicalProductMap
    (fun e => multiplicityBoundaryMap (fun i => Fin (d i)) (fun i => Fin (m i))
      (fun _ => 1) (γ e))
    (fun _ : RI (Γ := Γ) R =>
      fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (m i))) _ = _
  rw [mixedPhysicalProductMap_sum_prod]
  simp only [graphOpenBoundaryFactor_copy, graphOpenInternalFactor_copy d m D hm]
  simp_rw [graphOpenBondCoordinates_eq_sum_prod]
  exact sum_prod_sum_mul_eq_sum_prod_smul _ _ _ _

end TNLean.PEPS
