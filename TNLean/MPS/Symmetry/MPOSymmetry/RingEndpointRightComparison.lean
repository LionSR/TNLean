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

/-- At an injective second endpoint, the embedded periodic MPS is nonzero and the ground
space at energy \(0\) of the Hamiltonian of the translates of the extended interaction is the
line through it, for every ring of at least two sites. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem mixedEndpoint_groundSpace_hamiltonian_translationInvariant_one_eq_span [NeZero D₁]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.groundSpace
        (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 1)).hamiltonian 0 =
        ℂ ∙ mpvState (mixedEndpointRightTensor A₁ D₀) N ∧
      mpvState (mixedEndpointRightTensor A₁ D₀) N ≠ 0 := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.groundSpace_zero, mixedEndpoint_ker_hamiltonian_translationInvariant_one_eq A₀ A₁ hN,
    ← ManyBody.groundSpace_zero]
  exact groundSpace_unique_periodic (isInjective_mixedEndpointRightTensor A₁ hA₁ D₀) (by decide) hN

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
