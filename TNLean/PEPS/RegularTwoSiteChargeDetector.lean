/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoSiteChargeCoordinates
import TNLean.PEPS.RegularPhysicalUnitaryTransport

/-!
# The charge projector on shared virtual legs

The actual group-pair charge projector is extended by the identity on all
remaining incident labels. Its positive projection properties and its action
on selected and inequivalent charge columns follow from the literal local
averaging contraction, without a supplied coefficient identity.

Source: SCP10, arXiv:1001.3807, charge detection, lines 2464–2486.
**Scope restriction (finite-leg detector):** The orthogonality statement uses
explicit finite-dimensional irreducible characters and the selected unitary
adjoint identity. Choosing these witnesses from the finite group, original
physical transport, and any lattice geometry are separate steps. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Extend the shared-pair charge detector by the identity on all remaining labels.
Source: SCP10, two-site charge detection, lines 2464–2486. -/
def regularTwoSiteChargeDetector (i : ι) (j : κ) (χ : G → ℂ) :
    Matrix ((ι → G) × (κ → G)) ((ι → G) × (κ → G)) ℂ :=
  ((regularChargeDetectorMatrix χ).kronecker 1).submatrix
    (regularSharedLegEquiv i j) (regularSharedLegEquiv i j)

omit [Group G] in
private theorem shared_detector_mulVec (i : ι) (j : κ) (D : Matrix (G × G) (G × G) ℂ)
    (f : G × G → ℂ)
    (b : (({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) → ℂ)
    (α : (ι → G) × (κ → G)) :
    (((D.kronecker 1).submatrix (regularSharedLegEquiv i j)
        (regularSharedLegEquiv i j)) *ᵥ
      (fun β => f (regularSharedLegEquiv i j β).1 * b (regularSharedLegEquiv i j β).2)) α =
      (D *ᵥ f) (regularSharedLegEquiv i j α).1 * b (regularSharedLegEquiv i j α).2 := by
  rw [Matrix.mulVec, dotProduct, ← (regularSharedLegEquiv (G := G) i j).symm.sum_comp]
  simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply]
  simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/-- The lifted detector is a positive Hermitian projection.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularTwoSiteChargeDetector_properties (i : ι) (j : κ) (χ : G → ℂ) :
    (regularTwoSiteChargeDetector i j χ).IsHermitian ∧
      (regularTwoSiteChargeDetector i j χ).PosSemidef ∧
      regularTwoSiteChargeDetector i j χ * regularTwoSiteChargeDetector i j χ =
        regularTwoSiteChargeDetector i j χ := by
  obtain ⟨hh, _, hi⟩ := regularChargeDetectorMatrix_properties χ
  have hD : (regularTwoSiteChargeDetector i j χ).IsHermitian := by
    change (((regularChargeDetectorMatrix χ).kronecker 1).submatrix _ _).conjTranspose = _
    rw [Matrix.conjTranspose_submatrix, Matrix.kronecker, Matrix.conjTranspose_kronecker, hh.eq,
      Matrix.conjTranspose_one]
    rfl
  have hI : regularTwoSiteChargeDetector i j χ * regularTwoSiteChargeDetector i j χ =
      regularTwoSiteChargeDetector i j χ := by
    rw [regularTwoSiteChargeDetector, Matrix.submatrix_mul_equiv, Matrix.kronecker,
      ← Matrix.mul_kronecker_mul, hi, Matrix.one_mul]
  refine ⟨hD, ?_, hI⟩
  simpa only [hD.eq, hI] using
    Matrix.posSemidef_self_mul_conjTranspose (regularTwoSiteChargeDetector i j χ)

private theorem detector_column_of_action (i : ι) (j : κ) (χ ψ : G → ℂ) (z : ℂ)
    (hact : ∀ p x y, regularChargeDetectorMatrix χ *ᵥ
      (fun rs => regularChargeMatrix ψ p x y rs.1 rs.2) =
        z • (fun rs => regularChargeMatrix ψ p x y rs.1 rs.2)) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    regularTwoSiteChargeDetector i j χ *ᵥ regularTwoSiteChargeColumn i j ψ p θ =
      z • regularTwoSiteChargeColumn i j ψ p θ := by
  classical
  have hcol : regularTwoSiteChargeColumn i j ψ p θ =
      (Fintype.card G : ℂ)⁻¹ ^ 2 • ∑ x : G, ∑ y : G,
        (fun α : (ι → G) × (κ → G) =>
          regularChargeMatrix ψ p x y (regularSharedLegEquiv i j α).1.1
            (regularSharedLegEquiv i j α).1.2 *
          ((if (regularSharedLegEquiv i j α).2.1 = x • θ.1 then 1 else 0) *
            (if (regularSharedLegEquiv i j α).2.2 = y • θ.2 then 1 else 0))) := by
    funext α
    simpa [regularSharedLegEquiv, Equiv.prodProdProdComm, mul_assoc] using
      regularTwoSiteChargeColumn_apply i j ψ p θ α
  rw [hcol, Matrix.mulVec_smul, smul_comm z, Finset.smul_sum, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  funext α
  change _ = z * _
  calc
    _ = (regularChargeDetectorMatrix χ *ᵥ (fun rs => regularChargeMatrix ψ p x y rs.1 rs.2))
      (regularSharedLegEquiv i j α).1 *
        ((if (regularSharedLegEquiv i j α).2.1 = x • θ.1 then 1 else 0) *
          (if (regularSharedLegEquiv i j α).2.2 = y • θ.2 then 1 else 0)) :=
      shared_detector_mulVec i j (regularChargeDetectorMatrix χ)
        (fun rs => regularChargeMatrix ψ p x y rs.1 rs.2)
        (fun γ => (if γ.1 = x • θ.1 then 1 else 0) *
          (if γ.2 = y • θ.2 then 1 else 0)) α
    _ = _ := by
      rw [hact]
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The detector retains every selected-charge column, uniformly in the boundary labels.
Source: SCP10, charge detection, lines 2470–2486. -/
theorem regularTwoSiteChargeDetector_column (i : ι) (j : κ) (χ : G → ℂ) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    regularTwoSiteChargeDetector i j χ *ᵥ regularTwoSiteChargeColumn i j χ p θ =
      regularTwoSiteChargeColumn i j χ p θ := by
  simpa only [one_smul] using detector_column_of_action i j χ χ 1
    (by intro p x y; simpa only [one_smul] using
      regularChargeDetectorMatrix_chargeVector χ p x y) p θ

/-- Every inequivalent irreducible charge has zero detector eigenvalue, including
all unknown endpoint and boundary labels. Source: SCP10, lines 2474–2486. -/
theorem regularTwoSiteChargeDetector_other_column
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (σ : Representation ℂ G E) (τ : Representation ℂ G F)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (hne : σ.character ≠ τ.character)
    (i : ι) (j : κ) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    regularTwoSiteChargeDetector i j σ.character *ᵥ
      regularTwoSiteChargeColumn i j τ.character p θ = 0 := by
  simpa only [zero_smul] using detector_column_of_action i j σ.character τ.character 0
    (by intro p x y; simpa only [zero_smul] using
      regularChargeDetectorMatrix_other_chargeVector σ τ hσ hne p x y) p θ

/-- The two-site canonical column is the actual product-projector contraction
of the character-weighted shared bond. Source: SCP10, lines 2464–2486. -/
theorem regularTwoSiteChargeColumn_eq_projector (i : ι) (j : κ) (χ : G → ℂ) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    regularTwoSiteChargeColumn i j χ p θ =
      ((regularLegProjector (G := G) ι).kronecker (regularLegProjector κ)) *ᵥ
        ∑ k : G, χ (p * k) • Pi.single
          ((Equiv.funSplitAt i G).symm (k, θ.1),
            (Equiv.funSplitAt j G).symm (k, θ.2)) 1 := by
  classical
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
  funext α
  simp [regularTwoSiteChargeColumn, Matrix.kronecker, Matrix.kroneckerMap, mul_assoc]

end TNLean.PEPS
