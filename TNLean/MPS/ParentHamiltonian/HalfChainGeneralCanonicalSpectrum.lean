/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.HalfChainPhysicalStability
import TNLean.MPS.ParentHamiltonian.HalfChainCanonicalSpectrum
import TNLean.MPS.ParentHamiltonian.WeightedCanonicalSectors

/-!
# The half-chain spectrum of a general weighted canonical MPS under C2

The normalized generic C2 condition counts eigenvalues with algebraic
multiplicity. It determines the unique unit-weight normal block of the
actual weighted canonical tensor. The physical remainder tends to zero;
the canonical dual fixed point supplies positive diagonal weights of sum
one. The actual finite normalization and dimension-independent spectral
stability then transport the one-block half-chain limit to the original
weighted tensor, including multiplicities and zero padding.

Source: PGVWC07, arXiv:quant-ph/0608197, Condition C2 and Theorem 6,
lines 954–993. The multiplicity, normalization and indexing conventions
are recorded in `docs/paper-gaps/pgvwc07_half_chain_spectrum_conventions.tex`.
-/

noncomputable section

open Filter Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder Topology BigOperators

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

/-- The actual normalized half-chain ordered spectrum of a general
weighted canonical tensor converges to the doubled diagonal fixed-point
spectrum of its derived dominant block. No block, stationary density,
normalization, decay estimate or spectral limit is an added hypothesis.
C2 is the source's generic, algebraic-multiplicity condition, rather than
uniqueness of the peripheral eigenvalue as a distinct value.
Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6, lines 954–993;
`docs/paper-gaps/pgvwc07_half_chain_spectrum_conventions.tex`. -/
theorem PGVWC07CanonicalFormData.exists_halfChainSpectrumLimit_of_c2
    (h : PGVWC07CanonicalFormData A)
    (hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1)
    (hC2 : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → ‖μ‖ = 1 →
      μ = 1 ∧ (Kraus.transferMap A).charpoly.rootMultiplicity μ = 1) :
    ∃ k : Fin h.r, h.weight k = 1 ∧ (∀ j, h.weight j = 1 → j = k) ∧
      IsNormalTensor (h.blocks k) ∧
      ∃ lam : Fin (h.dim k) → ℝ, ∃ hlam : ∀ a, 0 < lam a, (∑ a, lam a = 1) ∧
        (∑ i, (h.blocks k i)ᴴ * (Matrix.diagonal fun a ↦ (lam a : ℂ)) * h.blocks k i =
          Matrix.diagonal fun a ↦ (lam a : ℂ)) ∧
        (∀ᶠ L : ℕ in atTop, 0 < halfChainNormSq A L) ∧
        ∀ i : ℕ, Tendsto (fun L ↦ halfChainEigenvalues A L i) atTop
          (𝓝 ((posSemidef_halfChainSpectrumLimit lam
            (fun a ↦ (hlam a).le)).isHermitian.paddedEigenvalues i)) := by
  classical
  obtain ⟨k, hk, hUnique, hNormal, hPhysical⟩ :=
    h.exists_dominantNormalBlock_physical_limit_of_c2 hRadius hC2
  obtain ⟨lam, hlam, htr, hfix⟩ := h.exists_normalized_diagonal_dualFixedPoint k
  have hZ := (halfChainNormSq_unital (h.blocks k) hNormal lam
    (fun a ↦ (hlam a).le) htr (h.unital k) hfix).1
  have hNorm : Tendsto (fun L : ℕ ↦ ‖mpvState (h.blocks k) (L + L)‖) atTop (𝓝 1) := by
    have hsqrt := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hZ
    simpa only [halfChainNormSq_eq_norm_mpvState_sq, Function.comp_def,
      Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_one] using hsqrt
  have hLength : Tendsto (fun L : ℕ ↦ L + L) atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    exact eventually_atTop.mpr ⟨M, fun L hL ↦ by omega⟩
  have hPhysicalEven := hPhysical.comp hLength
  have hNormalized := tendsto_normalizedMPVState_sub_of_mpvState_sub
    A (h.blocks k) (fun L ↦ L + L) hPhysicalEven hNorm
  have hNonzero : ∀ᶠ L : ℕ in atTop, 0 < halfChainNormSq A L := by
    have hSmall := hPhysicalEven.eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
    have hLarge := hNorm.eventually
      (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
    filter_upwards [hSmall, hLarge] with L hSmallL hLargeL
    have hDiff := (abs_le.mp (abs_norm_sub_norm_le (mpvState A (L + L))
      (mpvState (h.blocks k) (L + L)))).1
    have hPos : 0 < ‖mpvState A (L + L)‖ := by
      change ‖mpvState A (L + L) - mpvState (h.blocks k) (L + L)‖ < 1 / 4 at hSmallL
      linarith
    rw [halfChainNormSq_eq_norm_mpvState_sq]
    exact sq_pos_of_pos hPos
  refine ⟨k, hk, hUnique, hNormal, lam, hlam, htr, hfix, hNonzero, fun i ↦ ?_⟩
  apply tendsto_halfChainEigenvalues_of_normalizedMPVState_sub A (h.blocks k) hNormalized i
  exact tendsto_halfChainEigenvalues_unital (h.blocks k) hNormal lam
    (fun a ↦ (hlam a).le) htr (h.unital k) hfix i

end MPSTensor
