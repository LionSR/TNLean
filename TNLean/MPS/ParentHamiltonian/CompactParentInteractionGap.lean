/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactKernelGap
import TNLean.MPS.ParentHamiltonian.CompactBlockParentGap
import TNLean.MPS.ParentHamiltonian.CompactNormalParentGap
import TNLean.MPS.ParentHamiltonian.Martingale.ParentInteractionGap

/-!
# Compact families of positive parent interactions

For a continuous family of positive local parent interactions, continuity of
the local ground-space projection gives a positive comparison constant with
the canonical parent projection uniform on a compact parameter set. Hence a
compact-family canonical gap transfers to the chosen interactions, uniformly
in both the parameter and the periodic chain length.

This is the comparison needed for the non-projector interactions in
arXiv:1010.3732, Appendix A, lines 2477--2480. The local positive comparison
is the projector reduction in arXiv:2011.12127, lines 2170--2172.
-/

open scoped Topology ComplexOrder

namespace MPSTensor

/-- A compact continuous family of positive parent interactions bounds the
canonical parent projections below by one positive constant. Source:
arXiv:1010.3732, Appendix A; arXiv:2011.12127, lines 2170--2172. -/
theorem exists_uniform_pos_parentInteractionES_le_of_compact
    {X : Type*} [TopologicalSpace X] {d D R : ℕ}
    (A : X → MPSTensor d D)
    (hProj : Continuous fun x => (groundSpaceES (A x) R).starProjection)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction (A x) R (H x).toLinearMap)
    {S : Set X} (hS : IsCompact S) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ S,
      (κ : ℂ) • parentInteractionES (A x) R ≤ (H x).toLinearMap := by
  have hK : Continuous fun x => (LinearMap.ker (H x).toLinearMap).starProjection := by
    simpa only [(hParent _).ker_eq] using hProj
  obtain ⟨κ, hκ, hGap⟩ :=
    ContinuousLinearMap.exists_uniform_norm_gap_of_compact H hH hK hS
  refine ⟨κ, hκ, fun x hx ↦ ?_⟩
  simpa only [(hParent x).ker_eq, parentInteractionES] using
    (hParent x).isPositive.smul_orthogonal_ker_projection_le_of_norm_gap
      hκ.le (hGap x hx)

/-- A canonical gap uniform on a compact parameter set transfers to a
continuous family of positive parent interactions with the same local kernels.
Source: arXiv:1010.3732, Appendix A, lines 2477--2480 and 2575--2578. -/
theorem exists_uniform_periodicInteractionHamiltonianES_gap_of_compact_canonical_gap
    {X : Type*} [TopologicalSpace X] {d D R N₀ : ℕ}
    (A : X → MPSTensor d D)
    (hProj : Continuous fun x => (groundSpaceES (A x) R).starProjection)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction (A x) R (H x).toLinearMap)
    {S : Set X} (hS : IsCompact S) (hR : 0 < R) {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ x ∈ S, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) R N))ᗮ,
        γ * ‖v‖ ≤ ‖parentHamiltonianES (A x) R N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  obtain ⟨κ, hκ, hLower⟩ :=
    exists_uniform_pos_parentInteractionES_le_of_compact A hProj H hH hParent hS
  refine ⟨κ * γ, mul_pos hκ hγ, fun x hx N hN ↦ ?_⟩
  obtain ⟨_, C, _, hC, hComparison⟩ := (hParent x).exists_pos_periodic_comparison hR
  have hLowerN : (κ : ℂ) • parentHamiltonianES (A x) R N ≤
      periodicInteractionHamiltonianES (H x).toLinearMap N := by
    simpa only [periodicInteractionHamiltonianES_smul,
      periodicInteractionHamiltonianES_parentInteractionES (A x) hR] using
      periodicInteractionHamiltonianES_mono (hLower x hx) N
  simpa only [div_one] using
    (parentHamiltonianES_isPositive (A x) R N).norm_gap_of_smul_le_of_le_smul
      (periodicInteractionHamiltonianES_isPositive (hParent x).isPositive N)
      (b := 1) hκ zero_lt_one hC hγ
      (by simpa only [Complex.ofReal_one, one_smul] using hLowerN)
      (by simpa only [Complex.ofReal_one, one_smul] using (hComparison N).2)
      (hGap x hx N hN)

/-- The compact normal-family gap holds for continuous positive parent
interactions at every fixed range \(R\ge D^4+1\), for all \(N\ge R\).
Source: arXiv:1010.3732, Appendix A, single-block case;
arXiv:0909.5347, lines 828--831. -/
theorem exists_uniform_parentInteraction_gap_of_compact_isNormal_at_range
    {X : Type*} [TopologicalSpace X] {d D R : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hNormal : ∀ x, Kraus.IsNormal (A x)) (hR : D ^ 4 + 1 ≤ R)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction (A x) R (H x).toLinearMap)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  have hInj (x : X) : Kraus.IsNBlkInjective (A x) R :=
    isNBlkInjective_of_le (pow_pos (NeZero.pos D) 4)
      (isNBlkInjective_pow_four_of_isNormal (A x) (hNormal x)) (by omega)
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_uniform_parentHamiltonianES_gap_of_compact_isNormal_at_range A hA hNormal hR hS
  exact exists_uniform_periodicInteractionHamiltonianES_gap_of_compact_canonical_gap A
    (continuous_groundSpaceES_starProjection_family A hA R hInj) H hH hParent hS
    (by omega) hγ hGap


/-- Compact normal families retain a common gap for continuous positive
parent interactions at the explicit range \(D^4+1\). Source:
arXiv:1010.3732, Appendix A, single-block case; arXiv:0909.5347, Theorem 1. -/
theorem exists_uniform_parentInteraction_gap_of_compact_isNormal
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hNormal : ∀ x, Kraus.IsNormal (A x))
    (H : X → EuclideanSpace ℂ (Cfg d (D ^ 4 + 1)) →L[ℂ]
      EuclideanSpace ℂ (Cfg d (D ^ 4 + 1)))
    (hH : Continuous H)
    (hParent : ∀ x, IsParentInteraction (A x) (D ^ 4 + 1) (H x).toLinearMap)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ N : ℕ, D ^ 4 + 1 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  exact exists_uniform_parentInteraction_gap_of_compact_isNormal_at_range
    A hA hNormal le_rfl H hH hParent hS

/-- Continuous positive interactions for several blocks have a uniform gap
at every range exceeding a common simultaneous injectivity length. Nonzero
weights need not be continuous. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_block_parentInteraction_gap_of_compact
    {X : Type*} [TopologicalSpace X] {d r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R)
    (H : X → EuclideanSpace ℂ (Cfg d R) →L[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hH : Continuous H)
    (hParent : ∀ x, IsParentInteraction
      (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R (H x).toLinearMap)
    {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES (H x).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES (H x).toLinearMap N v‖ := by
  have hSpanR (x : X) : WordTupleSpanTop (A x) R :=
    wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega)
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_uniform_parentHamiltonianES_toTensorFromBlocks_gap_of_compact_all_lengths
      μ A hμ hA hS hSpan hR hK
  exact exists_uniform_periodicInteractionHamiltonianES_gap_of_compact_canonical_gap
    (fun x => toTensorFromBlocks (d := d) (μ := μ x) (A x))
    (continuous_groundSpaceES_toTensorFromBlocks_starProjection_family μ A hμ hA R hSpanR)
    H hH hParent hK (by omega) hγ hGap


end MPSTensor
