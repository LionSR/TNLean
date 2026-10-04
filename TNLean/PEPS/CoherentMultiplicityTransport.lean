/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.PhysicalCoherentTransport
import TNLean.PEPS.BondCoordinateTransport
import TNLean.PEPS.SemiRegularBondIsometryExtension

/-!
# Multiplicity restoration for coherent weighted block families

A matrix family consisting of square-root weighted diagonal blocks has
matching-sector support. One fixed product of full-domain bond isometries
restores the multiplicities in every coherent finite sum of this family.
A further isometric coordinate change transports the repeated blocks.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019. The hypotheses
concern ordinary matrix families. These auxiliary results do not assume
an identity between contracted tensor-network states; actual contraction
formulas must be derived before applying them.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {E Q A I : Type*} [Fintype E] [DecidableEq E] [Fintype Q]
variable [Fintype I] [DecidableEq I]

/-- Square-root weighted block families have matching-sector support, and
multiplicity restoration acts term by term on every coherent finite sum.
Source: SCP10, Section 7, lines 2997–3019. -/
theorem coherentWeightedBlocks_support_restore
    (d : I → ℕ) (D : ∀ i, A → Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (M : A → Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) ℂ)
    (hM : ∀ a, M a = Matrix.blockDiagonal'
      (fun i => (Real.sqrt (d i : ℝ) : ℂ) • D i a))
    (hd : ∀ i, 0 < d i) (c : Q → ℂ) (r : Q → E → A) :
    let Ψ := fun σ : E → ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) =>
      ∑ q, c q * ∏ e, M (r q e) (σ e).1 (σ e).2
    Ψ ∈ LinearMap.range
      (physicalProductMap E (blockBondInclusion (fun i => Fin (d i)))) ∧
    physicalProductMap E
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))) Ψ =
      fun τ => ∑ q, c q * ∏ e,
        Matrix.blockDiagonal' (fun i =>
          D i (r q e) ⊗ₖ (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) (τ e).1 (τ e).2 := by
  let : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
  dsimp only
  constructor
  · refine ⟨fun σ => ∑ q, c q * ∏ e,
      (Real.sqrt (d (σ e).1 : ℝ) : ℂ) *
        D (σ e).1 (r q e) (σ e).2.1 (σ e).2.2, ?_⟩
    apply physicalProductMap_sum_prod_eq
      (blockBondInclusion (fun i => Fin (d i))) c
      (fun e q a => (Real.sqrt (d a.1 : ℝ) : ℂ) * D a.1 (r q e) a.2.1 a.2.2)
      (fun e q a => M (r q e) a.1 a.2)
    intro e q
    rw [hM]
    exact blockBondInclusion_mulVec (fun i => Fin (d i))
      (fun i => (Real.sqrt (d i : ℝ) : ℂ) • D i (r q e))
  · apply physicalProductMap_sum_prod_eq
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))) c
      (fun e q a => M (r q e) a.1 a.2)
      (fun e q a => Matrix.blockDiagonal' (fun i =>
        D i (r q e) ⊗ₖ (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) a.1 a.2)
    intro e q
    rw [hM]
    change _ = fun a : (Σ i, Fin (d i) × Fin (d i)) ×
        (Σ i, Fin (d i) × Fin (d i)) => Matrix.blockDiagonal' (fun i =>
      D i (r q e) ⊗ₖ (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) a.1 a.2
    simpa only [Fintype.card_fin] using fullMultiplicityBondMap_mulVec_sqrt_blockDiagonal
      (fun i => Fin (d i)) (fun i => Fin (d i)) (fun i => D i (r q e))

variable {Out : Type*} [Fintype Out]

/-- One full-domain product isometry transports all coherent sums of the
weighted block family, before the summation weights and labels are chosen.
Source: SCP10, Section 7, lines 2988–3019. -/
theorem exists_isometric_coherentWeightedBlocks
    (d : I → ℕ) (D : ∀ i, A → Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (M : A → Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) ℂ)
    (hM : ∀ a, M a = Matrix.blockDiagonal'
      (fun i => (Real.sqrt (d i : ℝ) : ℂ) • D i a))
    (hd : ∀ i, 0 < d i)
    (B : Matrix Out (Σ i, Fin (d i) × Fin (d i)) ℂ) (hB : B.IsIsometry)
    (L : A → Matrix Out Out ℂ)
    (hreg : ∀ a, L a = B * Matrix.blockDiagonal'
      (fun i => D i a ⊗ₖ (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) * B.conjTranspose) :
    ∃ T : Matrix
        ((Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)))
        ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) ℂ,
      T.IsIsometry ∧
      let 𝒯 := physicalProductMap E (bondCoordinateMatrix B) ∘ₗ physicalProductMap E T
      (∀ (c : Q → ℂ) (r : Q → E → A),
        𝒯 (fun σ => ∑ q, c q * ∏ e, M (r q e) (σ e).1 (σ e).2) =
          fun τ => ∑ q, c q * ∏ e, L (r q e) (τ e).1 (τ e).2) ∧
      ∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ := by
  classical
  let : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
  obtain ⟨T, hT, hTE, _, _⟩ := exists_isIsometry_fullMultiplicityBondMap_extension
    (fun i => Fin (d i)) (fun i => Fin (d i))
  refine ⟨T, hT, ?_, ?_⟩
  · intro c r
    obtain ⟨hsupport, hrestore⟩ := coherentWeightedBlocks_support_restore d D M hM hd c r
    simp only [LinearMap.comp_apply]
    rw [physicalProductMap_eq_on_inclusion_range T
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))
      (blockBondInclusion (fun i => Fin (d i))) hTE _ hsupport, hrestore]
    apply physicalProductMap_sum_prod_eq (bondCoordinateMatrix B) c
      (fun e q a => Matrix.blockDiagonal' (fun i =>
        D i (r q e) ⊗ₖ (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) a.1 a.2)
      (fun e q a => L (r q e) a.1 a.2)
    intro e q
    rw [bondCoordinateMatrix_mulVec, ← hreg]
  · intro ψ φ
    simp only [LinearMap.comp_apply]
    rw [physicalProductMap_dotProduct_of_isIsometry _
      (bondCoordinateMatrix_isIsometry B hB), physicalProductMap_dotProduct_of_isIsometry _ hT]

end TNLean.PEPS
