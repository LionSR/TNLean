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

**Transitional (#10948).** The last section states the comparison, the common kernel and the
gap for the Hamiltonian of the translates on the ring of the matrix of the extended interaction
(`ManyBody.Interaction.translationInvariant`), with the gap as `ManyBody.IsGapped`. The
declarations before it are stated for the Euclidean-space operators
`periodicLocalInteractionES`, `periodicInteractionHamiltonianES`, `parentHamiltonianES` and
`localTermES`; they are kept for `MixedEndpointPeriodicStateContinuity` and
`MixedEndpointUniformPathGap` and are deleted when those are converted.
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
      periodicLocalInteractionES (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1))
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
      periodicLocalInteractionES (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1))
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
      periodicLocalInteractionES
        (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) i +
      periodicLocalInteractionES (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1))
        ((finRotate N).symm i) +
      periodicLocalInteractionES (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1))
        (finRotate N i) := by
  let E := EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) N)
  let K : E →ₗ[ℂ] E := localTermES (mixedEndpointRightTensor A₁ D₀) 2 i
  let H : E →ₗ[ℂ] E :=
    periodicLocalInteractionES (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) i
  let R : E →ₗ[ℂ] E := periodicLocalInteractionES (mixedEndpointRowSector D₀ D₁ 0) i
  let C : E →ₗ[ℂ] E := periodicLocalInteractionES (mixedEndpointColumnSector D₀ D₁ 1) i
  let P : E →ₗ[ℂ] E := periodicLocalInteractionES
    (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) ((finRotate N).symm i)
  let Q : E →ₗ[ℂ] E := periodicLocalInteractionES
    (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) (finRotate N i)
  have hE : Matrix.toEuclideanLin (LinearMap.toMatrix'
      (parentInteraction (mixedEndpointRightTensor A₁ D₀) 2)) =
      parentInteractionES (mixedEndpointRightTensor A₁ D₀) 2 :=
    toEuclideanLin_toMatrix'_parentInteraction _ _
  have hlocal : K ≤ H + R + C := by
    simpa only [hE, periodicLocalInteractionES_parentInteractionES
      (mixedEndpointRightTensor A₁ D₀) (by decide : 0 < 2),
      periodicLocalInteractionES_add] using
      periodicLocalInteractionES_mono
        (parentInteraction_mixedEndpointRightTensor_le A₀ A₁) i
  have hR : R ≤ P :=
    periodicLocalInteractionES_outerRowPenalty_one_le_previous A₀ A₁ hN i
  have hC : C ≤ Q :=
    periodicLocalInteractionES_outerColumnPenalty_one_le_next A₀ A₁ hN i
  change (H + R + C - K).IsPositive at hlocal
  change (P - R).IsPositive at hR
  change (Q - C).IsPositive at hC
  change (H + P + Q - K).IsPositive
  convert (hlocal.add hR).add hC using 1
  abel

/-- The actual extended endpoint Hamiltonian and the canonical parent of the
embedded endpoint satisfy `H′ ≤ K ≤ 3 H′` on every ring of at least two sites.
The factor three comes from counting each bond and its two neighbors.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_one_comparison
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    periodicInteractionHamiltonianES
      (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N ≤
        parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N ∧
      parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N ≤
        (3 : ℂ) • periodicInteractionHamiltonianES
          (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N := by
  have hE : Matrix.toEuclideanLin (LinearMap.toMatrix'
      (parentInteraction (mixedEndpointRightTensor A₁ D₀) 2)) =
      parentInteractionES (mixedEndpointRightTensor A₁ D₀) 2 :=
    toEuclideanLin_toMatrix'_parentInteraction _ _
  constructor
  · simpa only [hE, periodicInteractionHamiltonianES_parentInteractionES
      (mixedEndpointRightTensor A₁ D₀) (by decide : 0 < 2)] using
      periodicInteractionHamiltonianES_mono
        (mixedEndpointParentInteraction_one_le_parentInteraction A₀ A₁) N
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
      (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N) =
      LinearMap.ker (parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N) := by
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_periodic_one_comparison A₀ A₁ hN
  exact (periodicInteractionHamiltonianES_isPositive
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 1)) N).ker_eq_of_smul_le_of_le_smul
      (parentHamiltonianES_isPositive _ 2 N)
      (a := 1) (b := 1) (c := 3) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Complex.ofReal_one, one_smul] using hLower)
      (by simpa only [Complex.ofReal_one, Complex.ofReal_ofNat, one_smul] using hUpper)

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
      (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N))ᗮ,
      (δ / 3) * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
        (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N v‖ := by
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_periodic_one_comparison A₀ A₁ hN
  have hScaled := smul_le_smul_of_nonneg_left hLower (by norm_num : 0 ≤ (3 : ℂ))
  simpa only [one_mul] using
    LinearMap.IsPositive.norm_gap_of_smul_le_of_le_smul
      (parentHamiltonianES_isPositive (mixedEndpointRightTensor A₁ D₀) 2 N)
        (periodicInteractionHamiltonianES_isPositive
          (Matrix.isPositive_toEuclideanLin_iff.mpr
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 1)) N)
        (a := 1) (b := 3) (c := 3) (by norm_num) (by norm_num) (by norm_num) hδ
        (by simpa only [Complex.ofReal_one, Complex.ofReal_ofNat, one_smul] using hUpper)
        (by simpa only [Complex.ofReal_ofNat] using hScaled) hGap

/-- At an injective second endpoint, the actual extended periodic Hamiltonian
has precisely the embedded MPS ground line, for every ring of at least two
sites. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_periodic_one_groundSpace_eq [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N) =
      Submodule.span ℂ {(WithLp.toLp 2
        (mpv (mixedEndpointRightTensor A₁ D₀) :
          NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) N))} := by
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
      (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N)) = 1 := by
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
        (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ 1)) N v‖ := by
  obtain ⟨δ, hδ, hGap⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isInjective_all_lengths
      (fun _ : Unit => mixedEndpointRightTensor A₁ D₀) continuous_const
      (fun _ => isInjective_mixedEndpointRightTensor A₁ hA₁ D₀)
      (S := Set.univ) isCompact_univ
  refine ⟨δ / 3, div_pos hδ (by norm_num), fun N hN => ?_⟩
  have : NeZero N := ⟨by omega⟩
  exact mixedEndpoint_periodic_one_norm_gap A₀ A₁ hN hδ (by
    rw [parentHamiltonianES, parentHamiltonian_eq_toLin'_hamiltonian]
    exact ((ManyBody.isGapped_zero_iff_norm (posSemidef_hamiltonian_parentRingInteraction _ 2
      N)).mp (hGap () (Set.mem_univ ()) N hN)).2)

/-- One strictly positive gap bound works for both actual extended endpoints
and every periodic chain of length at least two. Only the two endpoint
parameters are quantified here. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem exists_uniform_mixedEndpoint_periodic_endpoints_gap [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ, p = 0 ∨ p = 1 → ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ p)) N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (Matrix.toEuclideanLin (mixedEndpointParentInteraction A₀ A₁ p)) N v‖ := by
  obtain ⟨δ₀, hδ₀, hGap₀⟩ := exists_uniform_mixedEndpoint_periodic_gap A₀ A₁ hA₀
  obtain ⟨δ₁, hδ₁, hGap₁⟩ :=
    exists_uniform_mixedEndpoint_periodic_one_gap A₀ A₁ hA₁
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  rintro p (rfl | rfl) N hN v hv
  · exact (mul_le_mul_of_nonneg_right (min_le_left δ₀ δ₁) (norm_nonneg v)).trans
      (hGap₀ N hN v hv)
  · exact (mul_le_mul_of_nonneg_right (min_le_right δ₀ δ₁) (norm_nonneg v)).trans
      (hGap₁ N hN v hv)

end MPOSymmetry
end MPSTensor

/-! ### Translates of the matrix of the extended interaction on the ring -/

namespace MPSTensor
namespace MPOSymmetry

open scoped MatrixOrder
open ManyBody.Interaction (translationInvariant)

variable {N D₀ D₁ : ℕ}

/-- One term of the parent interaction of the embedded second endpoint on the ring is at most
the sum of three adjacent terms of the translates of the extended interaction. No ring
inequality is assumed. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem parentRingInteraction_mixedEndpointRightTensor_term_le_three_extended
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    (parentRingInteraction (mixedEndpointRightTensor A₁ D₀) 2 N).term i ≤
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).term i +
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).term
        ((finRotate N).symm i) +
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).term (finRotate N i) := by
  have : NeZero N := ⟨by omega⟩
  let Rm (s : Fin 2) : Matrix (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
      (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) ℂ :=
    Matrix.diagonal fun σ => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ s)).1
  let Cm (s : Fin 2) : Matrix (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
      (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) ℂ :=
    Matrix.diagonal fun σ => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ s)).2
  have hR (s : Fin 2) : Matrix.toEuclideanLin (Rm s) = mixedEndpointRowSector D₀ D₁ s := rfl
  have hC (s : Fin 2) : Matrix.toEuclideanLin (Cm s) = mixedEndpointColumnSector D₀ D₁ s := rfl
  have hlocal : LinearMap.toMatrix' (parentInteraction (mixedEndpointRightTensor A₁ D₀) 2) ≤
      mixedEndpointParentInteraction A₀ A₁ 1 + Rm 0 + Cm 1 := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    simpa only [map_add, hR, hC] using parentInteraction_mixedEndpointRightTensor_le A₀ A₁
  have hrow : Rm 1 ≤ mixedEndpointParentInteraction A₀ A₁ 1 := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff, hR]
    exact mixedEndpoint_rowSector_one_le_parentInteraction_one A₀ A₁
  have hcol : Cm 0 ≤ mixedEndpointParentInteraction A₀ A₁ 1 := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff, hC]
    exact mixedEndpoint_columnSector_zero_le_parentInteraction_one A₀ A₁
  have h0 (j : Fin N) : j + Fin.castLE hN (0 : Fin 2) = j := by
    apply Fin.ext
    simp [Fin.add_def, Nat.mod_eq_of_lt j.isLt]
  have h1 (j : Fin N) : j + Fin.castLE hN (1 : Fin 2) = finRotate N j := by
    apply Fin.ext
    simp [finRotate_apply, Fin.add_def]
  have hprev : (translationInvariant N (Rm 0)).term i =
      (translationInvariant N (Rm 1)).term ((finRotate N).symm i) := by
    rw [ManyBody.Interaction.translationInvariant_term_diagonal hN,
      ManyBody.Interaction.translationInvariant_term_diagonal hN]
    simp only [h0, h1, Equiv.apply_symm_apply]
  have hnext : (translationInvariant N (Cm 1)).term i =
      (translationInvariant N (Cm 0)).term (finRotate N i) := by
    rw [ManyBody.Interaction.translationInvariant_term_diagonal hN,
      ManyBody.Interaction.translationInvariant_term_diagonal hN]
    simp only [h0, h1]
  have hK := ManyBody.Interaction.translationInvariant_term_mono (N := N) hlocal i
  have hP := ManyBody.Interaction.translationInvariant_term_mono (N := N) hrow
    ((finRotate N).symm i)
  have hQ := ManyBody.Interaction.translationInvariant_term_mono (N := N) hcol (finRotate N i)
  simp only [ManyBody.Interaction.translationInvariant_term_add] at hK
  rw [← hprev] at hP
  rw [← hnext] at hQ
  exact hK.trans (add_le_add (add_le_add le_rfl hP) hQ)

/-- The Hamiltonian `H′` of the translates of the extended second-endpoint interaction and the
Hamiltonian `K` of the parent interaction of the embedded second endpoint satisfy
`H′ ≤ K ≤ 3 H′` on every ring of at least two sites. The factor three comes from counting each
bond and its two neighbors. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_hamiltonian_translationInvariant_one_comparison
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian ≤
        (parentRingInteraction (mixedEndpointRightTensor A₁ D₀) 2 N).hamiltonian ∧
      (parentRingInteraction (mixedEndpointRightTensor A₁ D₀) 2 N).hamiltonian ≤
        (3 : ℂ) •
          (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian := by
  have : NeZero N := ⟨by omega⟩
  constructor
  · exact ManyBody.Interaction.hamiltonian_translationInvariant_mono
      (Matrix.toEuclideanLin_le_toEuclideanLin_iff.mp
        (mixedEndpointParentInteraction_one_le_parentInteraction A₀ A₁))
  · have h := Finset.sum_le_sum fun (i : Fin N) (_ : i ∈ Finset.univ) =>
      parentRingInteraction_mixedEndpointRightTensor_term_le_three_extended A₀ A₁ hN i
    simp only [Finset.sum_add_distrib, Equiv.sum_comp] at h
    change ∑ i, (parentRingInteraction (mixedEndpointRightTensor A₁ D₀) 2 N).term i ≤ (3 : ℂ) •
      ∑ i, (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).term i
    refine h.trans_eq ?_
    module

/-- On a ring of at least two sites, the Hamiltonian of the translates of the extended
first-endpoint interaction has the kernel of the parent Hamiltonian of the embedded first
endpoint. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_ker_hamiltonian_translationInvariant_one_eq
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian) =
      LinearMap.ker (Matrix.toEuclideanLin
        (parentRingInteraction (mixedEndpointRightTensor A₁ D₀) 2 N).hamiltonian) := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_hamiltonian_translationInvariant_one_comparison A₀ A₁ hN
  have h1 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hLower
  have h2 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hUpper
  rw [map_smul] at h2
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr
    (ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 1))).ker_eq_of_smul_le_of_le_smul
      (Matrix.isPositive_toEuclideanLin_iff.mpr
        (posSemidef_hamiltonian_parentRingInteraction _ 2 N))
      (a := 1) (b := 1) (c := 3) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Complex.ofReal_one, one_smul] using h1)
      (by simpa only [Complex.ofReal_one, Complex.ofReal_ofNat, one_smul] using h2)

/-- If every nonzero eigenvalue of the parent Hamiltonian of the embedded second endpoint is at
least `δ`, every nonzero eigenvalue of the Hamiltonian of the translates of the extended
first-endpoint interaction is at least `δ / 3`. The comparison and common kernel are derived
from the mixed tensor, rather than supplied as hypotheses.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_hamiltonian_translationInvariant_one_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) {δ : ℝ} (hδ : 0 < δ)
    (hGap : haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (parentRingInteraction (mixedEndpointRightTensor A₁ D₀) 2 N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ) :
    haveI : NeZero N := ⟨by omega⟩;
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian) μ →
      μ = 0 ∨ ((δ / 3 : ℝ) : ℂ) ≤ μ := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_hamiltonian_translationInvariant_one_comparison A₀ A₁ hN
  have hκ : ((1 / 3 : ℝ) : ℂ) •
      (parentRingInteraction (mixedEndpointRightTensor A₁ D₀) 2 N).hamiltonian ≤
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff, map_smul]
    have h2 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hUpper
    rw [map_smul] at h2
    have h3 := smul_le_smul_of_nonneg_left h2
      (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 3))
    rwa [smul_smul, show ((1 / 3 : ℝ) : ℂ) * 3 = 1 by norm_num, one_smul] at h3
  have h := ManyBody.forall_hasEigenvalue_of_smul_le_of_le_smul
    (posSemidef_hamiltonian_parentRingInteraction (mixedEndpointRightTensor A₁ D₀) 2 N)
    (ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 1))
    (κ := 1 / 3) (C := 1) (by norm_num) one_pos hδ hκ
    (by simpa only [Complex.ofReal_one, one_smul] using hLower) hGap
  intro μ hμ
  have hμ' := h μ hμ
  rwa [show (1 / 3 * δ : ℝ) = δ / 3 by ring] at hμ'

/-- At an injective second endpoint, the Hamiltonian of the translates of the extended
interaction has precisely the embedded MPS ground line, for every ring of at least two
sites. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_ker_hamiltonian_translationInvariant_one_eq_span [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian) =
      Submodule.span ℂ {(WithLp.toLp 2
        (mpv (mixedEndpointRightTensor A₁ D₀) :
          NSiteSpace ((D₀ + D₁) * (D₀ + D₁)) N))} := by
  have : NeZero N := ⟨by omega⟩
  rw [mixedEndpoint_ker_hamiltonian_translationInvariant_one_eq A₀ A₁ hN,
    ← parentHamiltonianGroundSpaceES_eq_ker_hamiltonian_parentRingInteraction,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hN,
    chainGroundSpace_eq_mpvSubmodule
      (isInjective_mixedEndpointRightTensor A₁ hA₁ D₀) hN (by decide) hN,
    mpvSubmodule, Submodule.map_span, Set.image_singleton]
  rfl

/-- The Hamiltonian of the translates of the extended second-endpoint interaction has a
one-dimensional kernel on every ring of at least two sites. Source: arXiv:2203.12563,
Section 5, lines 1690–1692. -/
theorem mixedEndpoint_finrank_ker_hamiltonian_translationInvariant_one [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian)) = 1 := by
  have : NeZero N := ⟨by omega⟩
  rw [mixedEndpoint_ker_hamiltonian_translationInvariant_one_eq A₀ A₁ hN,
    ← parentHamiltonianGroundSpaceES_eq_ker_hamiltonian_parentRingInteraction,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hN,
    LinearEquiv.finrank_map_eq]
  exact groundSpace_unique_periodic
    (isInjective_mixedEndpointRightTensor A₁ hA₁ D₀) hN (by decide) hN

/-- The Hamiltonian of the translates of the extended second-endpoint interaction of the
arbitrary mixed tensor is gapped at zero with one strictly positive gap for every ring of at
least two sites. Injectivity of the second endpoint supplies the gap of its parent Hamiltonian;
the three-term comparison transfers it. No gap assumption and no continuity argument at a
rank-changing endpoint is used. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_isGapped_mixedEndpoint_hamiltonian_translationInvariant_one [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (hN : 2 ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped
        (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian 0 δ := by
  obtain ⟨δ, hδ, hGap⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isInjective_all_lengths
      (fun _ : Unit => mixedEndpointRightTensor A₁ D₀) continuous_const
      (fun _ => isInjective_mixedEndpointRightTensor A₁ hA₁ D₀)
      (S := Set.univ) isCompact_univ
  refine ⟨δ / 3, div_pos hδ (by norm_num), fun N hN => ?_⟩
  have : NeZero N := ⟨by omega⟩
  have hK := ManyBody.isGapped_zero_iff.mp (hGap () (Set.mem_univ ()) N hN)
  refine ManyBody.isGapped_zero_iff.mpr ⟨?_, ?_⟩
  · rw [ManyBody.groundSpace_zero,
      mixedEndpoint_ker_hamiltonian_translationInvariant_one_eq A₀ A₁ hN,
      ← ManyBody.groundSpace_zero]
    exact hK.1
  · exact mixedEndpoint_hamiltonian_translationInvariant_one_gap A₀ A₁ hN hδ hK.2

/-- One strictly positive gap works for the Hamiltonians of the translates of both extended
endpoint interactions and every ring of at least two sites. Only the two endpoint parameters
are quantified here. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_isGapped_mixedEndpoint_hamiltonian_translationInvariant_endpoints
    [NeZero D₀] [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ, p = 0 ∨ p = 1 → ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped
        (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ p)).hamiltonian 0 δ := by
  obtain ⟨δ₀, hδ₀, hGap₀⟩ :=
    exists_uniform_isGapped_mixedEndpoint_hamiltonian_translationInvariant A₀ A₁ hA₀
  obtain ⟨δ₁, hδ₁, hGap₁⟩ :=
    exists_uniform_isGapped_mixedEndpoint_hamiltonian_translationInvariant_one A₀ A₁ hA₁
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  rintro p (rfl | rfl) N hN
  · exact (hGap₀ N hN).mono (min_le_left δ₀ δ₁)
  · exact (hGap₁ N hN).mono (min_le_right δ₀ δ₁)

end MPOSymmetry
end MPSTensor
