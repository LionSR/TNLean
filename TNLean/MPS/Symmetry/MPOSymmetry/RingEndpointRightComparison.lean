/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.RingEndpointComparison
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointRightComparison

/-!
# Periodic comparison at the second mixed endpoint

At parameter one, the first-sector outer row and column selectors are the
penalties supplied by the preceding and following extended interactions.
The actual second-endpoint Hamiltonian therefore satisfies the same factor-three
comparison with the canonical parent of its embedded endpoint. It has the
embedded MPS as its unique ground state and a strictly positive gap uniform
over all periodic lengths at least two.

Source: arXiv:2203.12563, Section 5, lines 1690–1692. This proves both endpoint
gap claims together with the first-endpoint module; it does not infer a
uniform gap over the intervening path from continuity.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ N : ℕ}

/-- At the second endpoint, the outer first-row first-sector penalty is
controlled by the previous actual extended term, including across the periodic
seam. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem periodicLocalInteractionES_outerRowPenalty_one_le_previous
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    periodicLocalInteractionES (mixedEndpointRowSector D₀ D₁ 0) i ≤
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap
        ((finRotate N).symm i) := by
  rw [periodicLocalInteractionES_mixedEndpointRowSector_previous hN i]
  exact periodicLocalInteractionES_mono
    (mixedEndpoint_rowSector_one_le_parentInteraction_one A₀ A₁) _

/-- At the second endpoint, the outer second-column first-sector penalty is
controlled by the next actual extended term, including across the periodic
seam. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem periodicLocalInteractionES_outerColumnPenalty_one_le_next
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    periodicLocalInteractionES (mixedEndpointColumnSector D₀ D₁ 1) i ≤
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap
        (finRotate N i) := by
  rw [periodicLocalInteractionES_mixedEndpointColumnSector_next hN i]
  exact periodicLocalInteractionES_mono
    (mixedEndpoint_columnSector_zero_le_parentInteraction_one A₀ A₁) _

/-- One canonical endpoint term is controlled by three adjacent actual
extended terms. No ring inequality is assumed. Source: arXiv:2203.12563,
Section 5, lines 1690–1692. -/
theorem localTermES_mixedEndpointRightTensor_le_three_extended
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    localTermES (mixedEndpointRightTensor A₁ D₀) 2 i ≤
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap i +
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap
        ((finRotate N).symm i) +
      periodicLocalInteractionES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap
        (finRotate N i) := by
  have hlocal := periodicLocalInteractionES_mono
    (parentInteractionES_mixedEndpointRightTensor_le A₀ A₁) i
  rw [periodicLocalInteractionES_parentInteractionES _ (by decide),
    periodicLocalInteractionES_add, periodicLocalInteractionES_add] at hlocal
  exact hlocal.trans (add_le_add
    (add_le_add_left (periodicLocalInteractionES_outerRowPenalty_one_le_previous A₀ A₁ hN i) _)
    (periodicLocalInteractionES_outerColumnPenalty_one_le_next A₀ A₁ hN i))

/-- The actual extended endpoint Hamiltonian and the canonical parent of the
embedded endpoint satisfy `H′ ≤ K ≤ 3 H′` on every ring of at least two sites.
The factor three comes from counting each bond and its two neighbors.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_one_comparison
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    periodicInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N ≤
        parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N ∧
      parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N ≤
        (3 : ℂ) • periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N := by
  constructor
  · simpa only [periodicInteractionHamiltonianES_parentInteractionES _ (by decide)] using
      periodicInteractionHamiltonianES_mono
        (mixedEndpointParentInteraction_one_le_parentInteractionES A₀ A₁) N
  · have h := Finset.sum_le_sum fun (i : Fin N) (_ : i ∈ Finset.univ) =>
      localTermES_mixedEndpointRightTensor_le_three_extended A₀ A₁ hN i
    rw [← parentHamiltonianES_eq_sum_localTermES] at h
    simp only [Finset.sum_add_distrib, Equiv.sum_comp] at h
    convert h using 1
    simp only [periodicInteractionHamiltonianES]
    module

/-- The ring kernel of the actual extended endpoint equals the canonical
endpoint kernel. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_one_ker_eq
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N) =
      LinearMap.ker (parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N) := by
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_periodic_one_comparison A₀ A₁ hN
  exact (periodicInteractionHamiltonianES_isPositive
    (mixedEndpointParentInteraction_isPositive A₀ A₁ 1) N).ker_eq_of_smul_le_of_le_smul
      (parentHamiltonianES_isPositive _ 2 N)
      (a := 1) (b := 1) (c := 3) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Complex.ofReal_one, one_smul] using hLower)
      (by simpa only [Complex.ofReal_one, one_smul] using hUpper)

/-- A canonical endpoint gap `δ` transfers to the actual extended endpoint
with gap `δ / 3`. The comparison and common kernel are derived from the
mixed tensor, rather than supplied as hypotheses.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_one_norm_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ v ∈ (LinearMap.ker
      (parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N v‖) :
    ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N))ᗮ,
      (δ / 3) * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N v‖ := by
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_periodic_one_comparison A₀ A₁ hN
  have hScaled := smul_le_smul_of_nonneg_left hLower (by norm_num : 0 ≤ (3 : ℂ))
  simpa only [one_mul] using
    (parentHamiltonianES_isPositive (mixedEndpointRightTensor A₁ D₀) 2 N).
      norm_gap_of_smul_le_of_le_smul
        (periodicInteractionHamiltonianES_isPositive
          (mixedEndpointParentInteraction_isPositive A₀ A₁ 1) N)
        (a := 1) (b := 3) (c := 3) (by norm_num) (by norm_num) (by norm_num) hδ
        (by simpa only [Complex.ofReal_one, one_smul] using hUpper) hScaled hGap

/-- At an injective second endpoint, the actual extended periodic Hamiltonian
has precisely the embedded MPS ground line, for every ring of at least two
sites. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_one_groundSpace_eq [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N) =
      Submodule.span ℂ {WithLp.toLp 2
        (mpv (mixedEndpointRightTensor A₁ D₀) :
          NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) N)} := by
  rw [mixedEndpoint_periodic_one_ker_eq A₀ A₁ hN,
    ← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hN,
    chainGroundSpace_eq_mpvSubmodule
      (isInjective_mixedEndpointRightTensor A₁ hA₁ D₀) hN (by decide) hN,
    mpvSubmodule, Submodule.map_span, Set.image_singleton]
  rfl

/-- The actual extended second endpoint has a unique periodic ground state
on every ring of at least two sites. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem mixedEndpoint_periodic_one_groundSpace_finrank [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N)) = 1 := by
  rw [mixedEndpoint_periodic_one_ker_eq A₀ A₁ hN,
    ← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hN,
    LinearEquiv.finrank_map_eq]
  exact groundSpace_unique_periodic
    (isInjective_mixedEndpointRightTensor A₁ hA₁ D₀) hN (by decide) hN

/-- The extended second endpoint of the actual arbitrary mixed tensor has a
strictly positive gap uniform over every periodic length at least two.
Injectivity of the second endpoint supplies its canonical gap; the concrete
three-term comparison transfers it. No gap assumption and no continuity
argument at a rank-changing endpoint is used.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_mixedEndpoint_periodic_one_gap [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N v‖ := by
  obtain ⟨δ, hδ, hGap⟩ :=
    exists_uniform_parentHamiltonianES_gap_of_compact_isInjective_all_lengths
      (fun _ : Unit => mixedEndpointRightTensor A₁ D₀) continuous_const
      (fun _ => isInjective_mixedEndpointRightTensor A₁ hA₁ D₀)
      (S := Set.univ) isCompact_univ
  refine ⟨δ / 3, div_pos hδ (by norm_num), fun N hN => ?_⟩
  exact mixedEndpoint_periodic_one_norm_gap A₀ A₁ hN hδ (hGap () (Set.mem_univ ()) N hN)

/-- One strictly positive gap bound works for both actual extended endpoints
and every periodic chain of length at least two. Only the two endpoint
parameters are quantified here. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem exists_uniform_mixedEndpoint_periodic_endpoints_gap [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ, p = 0 ∨ p = 1 → ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ p).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ p).toLinearMap N v‖ := by
  obtain ⟨δ₀, hδ₀, hGap₀⟩ := exists_uniform_mixedEndpoint_periodic_gap A₀ A₁ hA₀
  obtain ⟨δ₁, hδ₁, hGap₁⟩ := exists_uniform_mixedEndpoint_periodic_one_gap A₀ A₁ hA₁
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  rintro p (rfl | rfl) N hN v hv
  · exact (mul_le_mul_of_nonneg_right (min_le_left δ₀ δ₁) (norm_nonneg v)).trans
      (hGap₀ N hN v hv)
  · exact (mul_le_mul_of_nonneg_right (min_le_right δ₀ δ₁) (norm_nonneg v)).trans
      (hGap₁ N hN v hv)

end MPOSymmetry
end MPSTensor
