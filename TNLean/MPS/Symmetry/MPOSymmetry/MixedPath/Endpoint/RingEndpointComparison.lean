/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Endpoint.MixedEndpointProjectorComparison
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import QICLean.Spectral.Gap.PositiveComparisonGap
import TNLean.MPS.ParentHamiltonian.Continuity.CompactParentGap
import TNLean.MPS.Tensor.GroundSpace.UniqueGroundState
import TNLean.MPS.ParentHamiltonian.ParentInteraction.KernelChainGroundSpace

/-!
# Periodic comparison at the first mixed endpoint

The missing outer row and column sectors of one extended endpoint interaction
are the inner sectors of its preceding and following interactions. Translating
the actual local comparisons and summing them therefore gives
`H′ ≤ K ≤ 3 H′`, where `K` is the canonical parent of the embedded first
endpoint. The kernels agree, and a gap for `K` gives one third of that gap for
`H′`.

Source: arXiv:2203.12563, Section 5, lines 1690–1692. These comparisons hold on
periodic chains of length at least two. They do not infer a uniform gap along
the interpolation from finite-volume continuity.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace MPSTensor
namespace MPOSymmetry

open scoped MatrixOrder
open ManyBody.Interaction (translationInvariant)

variable {N D₀ D₁ : ℕ}

/-- One term of the parent interaction of the embedded first endpoint on the ring is at most
the sum of three adjacent terms of the translates of the extended interaction. No ring
inequality is assumed. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem parentRingInteraction_mixedEndpointLeftTensor_term_le_three_extended
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) (i : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    (parentRingInteraction (mixedEndpointLeftTensor A₀ D₁) 2 N).term i ≤
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).term i +
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).term
        ((finRotate N).symm i) +
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).term (finRotate N i) := by
  have : NeZero N := ⟨by omega⟩
  let Rm (s : Fin 2) : Matrix (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
      (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) ℂ :=
    Matrix.diagonal fun σ => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ s)).1
  let Cm (s : Fin 2) : Matrix (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
      (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) ℂ :=
    Matrix.diagonal fun σ => bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ s)).2
  have hR (s : Fin 2) : Matrix.toEuclideanLin (Rm s) = mixedEndpointRowSector D₀ D₁ s := rfl
  have hC (s : Fin 2) : Matrix.toEuclideanLin (Cm s) = mixedEndpointColumnSector D₀ D₁ s := rfl
  have hone : Matrix.toEuclideanLin (1 : Matrix (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
      (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) ℂ) = 1 :=
    LinearMap.ext fun v => Matrix.toEuclideanLin_one_apply v
  have hlocal : LinearMap.toMatrix' (parentInteraction (mixedEndpointLeftTensor A₀ D₁) 2) ≤
      mixedEndpointParentInteraction A₀ A₁ 0 + (1 - Rm 0) + (1 - Cm 1) := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    simpa only [map_add, map_sub, hone, hR, hC] using
      parentInteraction_mixedEndpointLeftTensor_le A₀ A₁
  have hrow : 1 - Rm 1 ≤ mixedEndpointParentInteraction A₀ A₁ 0 := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    simpa only [map_sub, hone, hR] using
      mixedEndpoint_one_sub_rowSector_one_le_parentInteraction A₀ A₁
  have hcol : 1 - Cm 0 ≤ mixedEndpointParentInteraction A₀ A₁ 0 := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    simpa only [map_sub, hone, hC] using
      mixedEndpoint_one_sub_columnSector_zero_le_parentInteraction A₀ A₁
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
  simp only [ManyBody.Interaction.translationInvariant_term_add,
    ManyBody.Interaction.translationInvariant_term_sub,
    ManyBody.Interaction.translationInvariant_term_one hN] at hK hP hQ
  rw [← hprev] at hP
  rw [← hnext] at hQ
  exact hK.trans (add_le_add (add_le_add le_rfl hP) hQ)

/-- The Hamiltonian `H′` of the translates of the extended first-endpoint interaction and the
Hamiltonian `K` of the parent interaction of the embedded first endpoint satisfy
`H′ ≤ K ≤ 3 H′` on every ring of at least two sites. The factor three comes from counting each
bond and its two neighbors. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_hamiltonian_translationInvariant_comparison
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian ≤
        (parentRingInteraction (mixedEndpointLeftTensor A₀ D₁) 2 N).hamiltonian ∧
      (parentRingInteraction (mixedEndpointLeftTensor A₀ D₁) 2 N).hamiltonian ≤
        (3 : ℂ) •
          (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian := by
  have : NeZero N := ⟨by omega⟩
  constructor
  · exact ManyBody.Interaction.hamiltonian_translationInvariant_mono
      (Matrix.toEuclideanLin_le_toEuclideanLin_iff.mp
        (mixedEndpointParentInteraction_zero_le_parentInteraction A₀ A₁))
  · have h := Finset.sum_le_sum fun (i : Fin N) (_ : i ∈ Finset.univ) =>
      parentRingInteraction_mixedEndpointLeftTensor_term_le_three_extended A₀ A₁ hN i
    simp only [Finset.sum_add_distrib, Equiv.sum_comp] at h
    change ∑ i, (parentRingInteraction (mixedEndpointLeftTensor A₀ D₁) 2 N).term i ≤ (3 : ℂ) •
      ∑ i, (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).term i
    refine h.trans_eq ?_
    module

/-- On a ring of at least two sites, the Hamiltonian of the translates of the extended
first-endpoint interaction has the kernel of the parent Hamiltonian of the embedded first
endpoint. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_ker_hamiltonian_translationInvariant_eq
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) =
      LinearMap.ker (Matrix.toEuclideanLin
        (parentRingInteraction (mixedEndpointLeftTensor A₀ D₁) 2 N).hamiltonian) := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_hamiltonian_translationInvariant_comparison A₀ A₁ hN
  have h1 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hLower
  have h2 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hUpper
  rw [map_smul] at h2
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr
    (ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 0))).ker_eq_of_smul_le_of_le_smul
      (Matrix.isPositive_toEuclideanLin_iff.mpr
        (posSemidef_hamiltonian_parentRingInteraction _ 2 N))
      (a := 1) (b := 1) (c := 3) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Complex.ofReal_one, one_smul] using h1)
      (by simpa only [Complex.ofReal_one, Complex.ofReal_ofNat, one_smul] using h2)

/-- If every nonzero eigenvalue of the parent Hamiltonian of the embedded first endpoint is at
least `δ`, every nonzero eigenvalue of the Hamiltonian of the translates of the extended
first-endpoint interaction is at least `δ / 3`. The comparison and common kernel are derived
from the mixed tensor, rather than supplied as hypotheses.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_hamiltonian_translationInvariant_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hN : 2 ≤ N) {δ : ℝ} (hδ : 0 < δ)
    (hGap : haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (parentRingInteraction (mixedEndpointLeftTensor A₀ D₁) 2 N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ) :
    haveI : NeZero N := ⟨by omega⟩;
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) μ →
      μ = 0 ∨ ((δ / 3 : ℝ) : ℂ) ≤ μ := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hLower, hUpper⟩ := mixedEndpoint_hamiltonian_translationInvariant_comparison A₀ A₁ hN
  have hκ : ((1 / 3 : ℝ) : ℂ) •
      (parentRingInteraction (mixedEndpointLeftTensor A₀ D₁) 2 N).hamiltonian ≤
      (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff, map_smul]
    have h2 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hUpper
    rw [map_smul] at h2
    have h3 := smul_le_smul_of_nonneg_left h2
      (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 3))
    rwa [smul_smul, show ((1 / 3 : ℝ) : ℂ) * 3 = 1 by norm_num, one_smul] at h3
  have h := ManyBody.forall_hasEigenvalue_of_smul_le_of_le_smul
    (posSemidef_hamiltonian_parentRingInteraction (mixedEndpointLeftTensor A₀ D₁) 2 N)
    (ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant
      (posSemidef_mixedEndpointParentInteraction A₀ A₁ 0))
    (κ := 1 / 3) (C := 1) (by norm_num) one_pos hδ hκ
    (by simpa only [Complex.ofReal_one, one_smul] using hLower) hGap
  intro μ hμ
  have hμ' := h μ hμ
  rwa [show (1 / 3 * δ : ℝ) = δ / 3 by ring] at hμ'

/-- At an injective first endpoint, the embedded periodic MPS is nonzero and the ground
space at energy \(0\) of the Hamiltonian of the translates of the extended interaction is the
line through it, for every ring of at least two sites. Source: arXiv:2203.12563, Section 5,
lines 1690–1692. -/
theorem mixedEndpoint_groundSpace_hamiltonian_translationInvariant_eq_span [NeZero D₀]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.groundSpace
        (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian 0 =
        ℂ ∙ mpvState (mixedEndpointLeftTensor A₀ D₁) N ∧
      mpvState (mixedEndpointLeftTensor A₀ D₁) N ≠ 0 := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.groundSpace_zero, mixedEndpoint_ker_hamiltonian_translationInvariant_eq A₀ A₁ hN,
    ← ManyBody.groundSpace_zero]
  exact groundSpace_unique_periodic (isInjective_mixedEndpointLeftTensor A₀ hA₀ D₁) (by decide) hN

/-- The Hamiltonian of the translates of the extended first-endpoint interaction of the
arbitrary mixed tensor is gapped at zero with one strictly positive gap for every ring of at
least two sites. Injectivity of the first endpoint supplies the gap of its parent Hamiltonian;
the three-term comparison transfers it. No gap assumption and no continuity argument at a
rank-changing endpoint is used. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_uniform_isGapped_mixedEndpoint_hamiltonian_translationInvariant [NeZero D₀]
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (hN : 2 ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped
        (translationInvariant N (mixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian 0 δ := by
  obtain ⟨δ, hδ, hGap⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isInjective_all_lengths
      (fun _ : Unit => mixedEndpointLeftTensor A₀ D₁) continuous_const
      (fun _ => isInjective_mixedEndpointLeftTensor A₀ hA₀ D₁)
      (S := Set.univ) isCompact_univ
  refine ⟨δ / 3, div_pos hδ (by norm_num), fun N hN => ?_⟩
  have : NeZero N := ⟨by omega⟩
  have hK := ManyBody.isGapped_zero_iff.mp (hGap () (Set.mem_univ ()) N hN)
  refine ManyBody.isGapped_zero_iff.mpr ⟨?_, ?_⟩
  · rw [ManyBody.groundSpace_zero, mixedEndpoint_ker_hamiltonian_translationInvariant_eq A₀ A₁ hN,
      ← ManyBody.groundSpace_zero]
    exact hK.1
  · exact mixedEndpoint_hamiltonian_translationInvariant_gap A₀ A₁ hN hδ hK.2

end MPOSymmetry
end MPSTensor
