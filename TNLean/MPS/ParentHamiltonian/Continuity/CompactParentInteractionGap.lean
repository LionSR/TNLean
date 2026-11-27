/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.EigenvalueGap
import TNLean.MPS.ParentHamiltonian.Continuity.CompactBlockParentGap
import TNLean.MPS.ParentHamiltonian.Continuity.CompactNormalParentGap
import TNLean.MPS.ParentHamiltonian.Interaction.ParentInteractionGap

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

open MPTensor

open scoped Topology ComplexOrder MatrixOrder

namespace MPSTensor

/-- A compact continuous family of positive parent interactions, given by their matrices, bounds
the canonical parent projections below by one positive constant. Source:
arXiv:1010.3732, Appendix A; arXiv:2011.12127, lines 2170--2172. -/
theorem exists_uniform_pos_toMatrix'_parentInteraction_le_of_compact
    {X : Type*} [TopologicalSpace X] {d D R : ℕ}
    (A : X → MPSTensor d D)
    (hProj : Continuous fun x => ((groundSpace (A x) R).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection)
    (H : X → Matrix (Cfg d R) (Cfg d R) ℂ)
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction (A x) R (Matrix.toEuclideanLin (H x)))
    {S : Set X} (hS : IsCompact S) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ S,
      (κ : ℂ) • LinearMap.toMatrix' (parentInteraction (A x) R) ≤ H x := by
  let e := (Matrix.toEuclideanCLM : Matrix (Cfg d R) (Cfg d R) ℂ ≃⋆ₐ[ℂ] _)
  have hH' : Continuous fun x ↦ e (H x) :=
    e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp hH
  have hParent' : ∀ x, IsParentInteraction (A x) R (e (H x)).toLinearMap := hParent
  have hK : Continuous fun x ↦ (LinearMap.ker (e (H x)).toLinearMap).starProjection := by
    simpa only [(hParent' _).ker_eq] using hProj
  obtain ⟨κ, hκ, hGap⟩ :=
    ContinuousLinearMap.exists_uniform_norm_gap_of_compact (fun x ↦ e (H x)) hH' hK hS
  refine ⟨κ, hκ, fun x hx ↦ ?_⟩
  rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff, map_smul,
    toEuclideanLin_toMatrix'_parentInteraction]
  have h := (hParent' x).isPositive.smul_orthogonal_ker_projection_le_of_norm_gap
    hκ.le (hGap x hx)
  rw [(hParent' x).ker_eq] at h
  exact h

/-- A gap of the canonical parent Hamiltonians uniform on a compact parameter set transfers to
a continuous family of positive parent interactions with the same local kernels: every eigenvalue
other than zero of their Hamiltonians on the rings is at least one common constant.
Source: arXiv:1010.3732, Appendix A, lines 2477--2480 and 2575--2578. -/
theorem exists_uniform_hamiltonian_translationInvariant_gap_of_compact_canonical_gap
    {X : Type*} [TopologicalSpace X] {d D R N₀ : ℕ}
    (A : X → MPSTensor d D)
    (hProj : Continuous fun x => ((groundSpace (A x) R).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection)
    (H : X → Matrix (Cfg d R) (Cfg d R) ℂ)
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction (A x) R (Matrix.toEuclideanLin (H x)))
    {S : Set X} (hS : IsCompact S) {γ : ℝ} (hγ : 0 < γ)
    (hGap : ∀ x ∈ S, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) R N).hamiltonian) μ →
          μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant N (H x)).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨κ, hκ, hLower⟩ :=
    exists_uniform_pos_toMatrix'_parentInteraction_le_of_compact A hProj H hH hParent hS
  refine ⟨κ * γ, mul_pos hκ hγ, fun x hx N _ hN ↦ ?_⟩
  obtain ⟨_, C, _, hC, hComparison⟩ := (hParent x).exists_pos_periodic_comparison
  have hLowerN : (κ : ℂ) • (parentRingInteraction (A x) R N).hamiltonian ≤
      (ManyBody.Interaction.translationInvariant N (H x)).hamiltonian := by
    rw [← ManyBody.Interaction.hamiltonian_translationInvariant_smul]
    exact ManyBody.Interaction.hamiltonian_translationInvariant_mono (hLower x hx)
  exact ManyBody.forall_hasEigenvalue_of_smul_le_of_le_smul
    (posSemidef_hamiltonian_parentRingInteraction (A x) R N)
    (ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant
      (Matrix.isPositive_toEuclideanLin_iff.mp (hParent x).isPositive))
    hκ hC hγ hLowerN (hComparison N).2 (hGap x hx N hN)

/-- The compact normal-family gap holds for continuous positive parent
interactions at every fixed range \(R\ge D^4+1\), on all rings of \(N\ge R\) sites.
Source: arXiv:1010.3732, Appendix A, single-block case;
arXiv:0909.5347, lines 828--831. -/
theorem exists_uniform_parentInteraction_gap_of_compact_isNormal_at_range
    {X : Type*} [TopologicalSpace X] {d D R : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hNormal : ∀ x, Kraus.IsNormal (A x)) (hR : D ^ 4 + 1 ≤ R)
    (H : X → Matrix (Cfg d R) (Cfg d R) ℂ)
    (hH : Continuous H) (hParent : ∀ x, IsParentInteraction (A x) R (Matrix.toEuclideanLin (H x)))
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ (N : ℕ) (hN : R ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant N (H x)).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  have hInj (x : X) : Kraus.IsNBlkInjective (A x) R :=
    Kraus.isNBlkInjective_of_le (pow_pos (NeZero.pos D) 4)
      (isNBlkInjective_pow_four_of_isNormal (A x) (hNormal x)) (by omega)
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNormal_at_range
      A hA hNormal hR hS
  obtain ⟨δ, hδ, h⟩ :=
    exists_uniform_hamiltonian_translationInvariant_gap_of_compact_canonical_gap (N₀ := R) A
      (continuous_map_groundSpace_starProjection_family A hA R hInj) H hH hParent hS hγ
      fun x hx N _ hN ↦ (ManyBody.isGapped_zero_iff.mp (hGap x hx N hN)).2
  exact ⟨δ, hδ, fun x hx N hN ↦
    haveI : NeZero N := ⟨by omega⟩
    h x hx N hN⟩

/-- Compact normal families retain a common gap for continuous positive
parent interactions at the explicit range \(D^4+1\). Source:
arXiv:1010.3732, Appendix A, single-block case; arXiv:0909.5347, Theorem 1. -/
theorem exists_uniform_parentInteraction_gap_of_compact_isNormal
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hNormal : ∀ x, Kraus.IsNormal (A x))
    (H : X → Matrix (Cfg d (D ^ 4 + 1)) (Cfg d (D ^ 4 + 1)) ℂ)
    (hH : Continuous H)
    (hParent : ∀ x, IsParentInteraction (A x) (D ^ 4 + 1) (Matrix.toEuclideanLin (H x)))
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ (N : ℕ) (hN : D ^ 4 + 1 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant N (H x)).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ :=
  exists_uniform_parentInteraction_gap_of_compact_isNormal_at_range
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
    (H : X → Matrix (Cfg d R) (Cfg d R) ℂ)
    (hH : Continuous H)
    (hParent : ∀ x, IsParentInteraction
      (toTensorFromBlocks (α := Fin d) (μ := μ x) (A x)) R (Matrix.toEuclideanLin (H x)))
    {K : Set X} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ (N : ℕ) (hN : R ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ∀ z : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant N (H x)).hamiltonian) z →
          z = 0 ∨ (δ : ℂ) ≤ z := by
  have hSpanR (x : X) : WordTupleSpanTop (A x) R :=
    wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega)
  obtain ⟨γ, hγ, hGap⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_all_lengths
      μ A hμ hA hS hSpan hR hK
  obtain ⟨δ, hδ, h⟩ :=
    exists_uniform_hamiltonian_translationInvariant_gap_of_compact_canonical_gap (N₀ := R)
      (fun x => toTensorFromBlocks (α := Fin d) (μ := μ x) (A x))
      (continuous_map_groundSpace_toTensorFromBlocks_starProjection_family μ A hμ hA R hSpanR)
      H hH hParent hK hγ fun x hx N _ hN ↦ hGap x hx N hN
  exact ⟨δ, hδ, fun x hx N hN ↦
    haveI : NeZero N := ⟨by omega⟩
    h x hx N hN⟩

end MPSTensor
