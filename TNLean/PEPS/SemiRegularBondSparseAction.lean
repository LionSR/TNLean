/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondSupport
import TNLean.PEPS.TorusPhysicalMap

/-!
# Sparse coefficients of the supported multiplicity-restoring bond map

The full endpoint-pair map has only one possible input coordinate at each
output coordinate. Its coefficient is the reciprocal square root of the
multiplicity when the two multiplicity-sector labels agree, and zero otherwise.
The product map therefore acts by a weighted pullback on all configurations.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
local source lines 2992–3019.
-/

open scoped Matrix BigOperators
namespace TNLean.PEPS

/-- The adjoint of a coordinate inclusion restricts to the included coordinates. -/
theorem endpointEmbeddingMatrix_conjTranspose_mulVec {α β : Type*}
    [Fintype α] [DecidableEq α] (e : β ↪ α) (x : α → ℂ) (i : β) :
    ((endpointEmbeddingMatrix e).conjTranspose *ᵥ x) i = x (e i) := by
  classical
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, endpointEmbeddingMatrix]

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ν μ : I → Type*) [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
variable [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]

/-- Forget the multiplicity coordinate of a physical endpoint.
Source: SCP10, Section 7, lines 2992–3019. -/
def multiplicityEndpointBase (r : Σ i, ν i × μ i) : Σ i, ν i :=
  ⟨r.1, r.2.1⟩

/-- Retain the sector and multiplicity coordinate of a physical endpoint.
Source: SCP10, Section 7, lines 2992–3019. -/
def multiplicityEndpointCopy (r : Σ i, ν i × μ i) : Σ i, μ i :=
  ⟨r.1, r.2.2⟩

/-- The normalized equal-multiplicity coefficient on a pair of full endpoints.
Source: SCP10, Section 7, lines 3008–3019. -/
noncomputable def multiplicityBondAmplitude (r s : Σ i, ν i × μ i) : ℂ :=
  if multiplicityEndpointCopy ν μ r = multiplicityEndpointCopy ν μ s then
    (Real.sqrt (Fintype.card (μ r.1) : ℝ) : ℂ)⁻¹ else 0

omit [Fintype I] [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)] in
/-- Reversing a bond preserves its equal-multiplicity amplitude.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem multiplicityBondAmplitude_comm (r s : Σ i, ν i × μ i) :
    multiplicityBondAmplitude ν μ r s = multiplicityBondAmplitude ν μ s r := by
  by_cases h : multiplicityEndpointCopy ν μ r = multiplicityEndpointCopy ν μ s
  · have hi : r.1 = s.1 := congrArg (fun z : Σ i, μ i => z.1) h
    unfold multiplicityBondAmplitude
    rw [ite_eq_left h, ite_eq_left h.symm, hi]
  · simp [multiplicityBondAmplitude, h, Ne.symm h]

/-- The actual supported bond map acts by a weighted pullback to the original
endpoint coordinates. No nonempty-multiplicity assumption is needed for this
coefficient formula. Source: SCP10, Section 7, lines 3008–3019. -/
theorem fullMultiplicityBondMap_mulVec
    (ψ : ((Σ i, ν i) × (Σ i, ν i)) → ℂ)
    (r : (Σ i, ν i × μ i) × (Σ i, ν i × μ i)) :
    (fullMultiplicityBondMap ν μ *ᵥ ψ) r =
      multiplicityBondAmplitude ν μ r.1 r.2 *
        ψ (multiplicityEndpointBase ν μ r.1, multiplicityEndpointBase ν μ r.2) := by
  rcases r with ⟨⟨i, a, m⟩, ⟨j, b, n⟩⟩
  rw [fullMultiplicityBondMap, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  by_cases hij : i = j
  · subst j
    rw [show (⟨i, (a, m)⟩, ⟨i, (b, n)⟩) =
      matchingEndpointEmbedding (fun i => ν i × μ i) ⟨i, ((a, m), (b, n))⟩ from rfl]
    rw [blockBondInclusion, endpointEmbeddingMatrix_mulVec_image]
    change (multiplicityBondCoefficientMatrix (fun c : Σ i, ν i × ν i => μ c.1) *ᵥ
      ((blockBondInclusion ν).conjTranspose *ᵥ ψ)) ⟨⟨i, (a, b)⟩, (m, n)⟩ = _
    rw [multiplicityBondCoefficientMatrix_mulVec, blockBondInclusion,
      endpointEmbeddingMatrix_conjTranspose_mulVec]
    change (if m = n then
      (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ)⁻¹ * ψ (⟨i, a⟩, ⟨i, b⟩) else 0) =
      (if (⟨i, m⟩ : Σ i, μ i) = ⟨i, n⟩ then
        (Real.sqrt (Fintype.card (μ i) : ℝ) : ℂ)⁻¹ else 0) * ψ (⟨i, a⟩, ⟨i, b⟩)
    simp [ite_mul]
  · have hnot : (⟨i, (a, m)⟩, ⟨j, (b, n)⟩) ∉
        Set.range (matchingEndpointEmbedding (fun i => ν i × μ i)) := by
      rintro ⟨c, hc⟩
      have hi := congrArg (fun r => r.1.1) hc
      have hj := congrArg (fun r => r.2.1) hc
      exact hij (hi.symm.trans hj)
    rw [blockBondInclusion, endpointEmbeddingMatrix_mulVec_eq_zero_of_notMem_range
      _ _ _ hnot]
    have hcopy : multiplicityEndpointCopy ν μ ⟨i, (a, m)⟩ ≠
        multiplicityEndpointCopy ν μ ⟨j, (b, n)⟩ := by
      intro h
      exact hij (congrArg Sigma.fst h)
    simp [multiplicityBondAmplitude, hcopy]

/-- A row of the actual supported bond map has at most one nonzero coefficient.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem fullMultiplicityBondMap_apply
    (r : (Σ i, ν i × μ i) × (Σ i, ν i × μ i))
    (c : (Σ i, ν i) × (Σ i, ν i)) :
    fullMultiplicityBondMap ν μ r c = multiplicityBondAmplitude ν μ r.1 r.2 *
      (if (multiplicityEndpointBase ν μ r.1, multiplicityEndpointBase ν μ r.2) = c
        then 1 else 0) := by
  have h := fullMultiplicityBondMap_mulVec ν μ (Pi.single c 1) r
  simpa [Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using h

/-- The physical product of the actual supported bond maps is a weighted
pullback on arbitrary coherent states. No positivity or support assumption is
needed. Source: SCP10, Section 7, lines 3008–3019. -/
theorem physicalProductMap_fullMultiplicityBondMap_apply
    (Edge : Type*) [Fintype Edge] [DecidableEq Edge]
    (ψ : (Edge → ((Σ i, ν i) × (Σ i, ν i))) → ℂ)
    (β : Edge → ((Σ i, ν i × μ i) × (Σ i, ν i × μ i))) :
    physicalProductMap Edge (fullMultiplicityBondMap ν μ) ψ β =
      (∏ e, multiplicityBondAmplitude ν μ (β e).1 (β e).2) *
        ψ (fun e =>
          (multiplicityEndpointBase ν μ (β e).1, multiplicityEndpointBase ν μ (β e).2)) := by
  rw [physicalProductMap_apply]
  simp_rw [fullMultiplicityBondMap_apply, Finset.prod_mul_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp [Fintype.prod_boole, ← funext_iff]

end TNLean.PEPS
