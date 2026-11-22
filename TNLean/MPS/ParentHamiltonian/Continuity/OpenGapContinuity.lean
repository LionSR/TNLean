/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.CompactKernelGap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockGroundSpaceContinuity
import TNLean.MPS.ParentHamiltonian.Gap.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockWordSpanSeparation
import QICLean.Spectral.Perturbation.KernelGapPerturbation

/-!
# Compact uniform gaps on bounded open intervals

At a common positive simultaneous injectivity length, the open ground
projections and the finite-interval parent Hamiltonians vary continuously.
Compactness supplies a positive gap on each fixed admissible interval, and a
finite minimum makes the bound uniform over all intervals below a fixed upper
length. The constant is allowed to depend on that upper length.

The nonzero block weights do not change the local ground spaces, and therefore
need no continuity assumption. This is the finite-window continuity step of
arXiv:1010.3732, Appendix A, lines 2575--2578.

## Continuity of gaps on finitely many open intervals

At a common positive simultaneous injectivity length, the local ground
projections vary continuously with the block tensors. A strict norm gap on
one admissible open interval therefore persists near its parameter. A finite
intersection of these neighborhoods treats every interval below a fixed upper
length with the same strict lower bound.

Nonzero block weights do not affect the local spaces, and no continuity of
these weights is required. This is the finite-window continuity argument in
arXiv:1010.3732, Appendix A, lines 2575--2578.
-/

section

open scoped Topology ComplexOrder

namespace MPSTensor

variable {d : ℕ}

/-- A compact continuous family of simultaneously injective blocks has one positive gap above the
kernel of the Hamiltonian of the parent interaction on the open chain on each fixed admissible
interval: every eigenvalue is `0` or at least the gap. Nonzero block weights need no continuity
assumption. Source: arXiv:1010.3732, Appendix A,
lines 2575--2578, for the finite-window continuity argument. -/
theorem exists_uniform_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_fixed_volume
    {X : Type*} [TopologicalSpace X] {r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x ↦ A x j)
    {S R N : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    {K : Set X} (hK : IsCompact K) (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ ν : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian) ν →
      ν = 0 ∨ (δ : ℂ) ≤ ν := by
  have hProjR := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA R (fun x ↦ wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega))
  have hProjN := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA N (fun x ↦ wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega))
  exact hK.exists_uniform_forall_hasEigenvalue
    (H := fun x ↦ (parentChainInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian)
    (continuous_hamiltonian_parentChainInteraction_family_of_groundProjection
      (fun x ↦ toTensorFromBlocks (μ x) (A x)) hProjR)
    (fun x ↦ posSemidef_hamiltonian_parentChainInteraction _ R N)
    (by
      simpa only [ManyBody.groundSpace_zero,
        ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_wordTupleSpanTop
          (μ _) (A _) (hμ _) hS (hSpan _) hR hRN] using hProjN)

/-- A finite upper bound on the interval length gives one positive gap above the kernel of the
Hamiltonian of the parent interaction on the open chain, uniform over the compact tensor family
and every admissible interval below that bound. The constant may depend on the upper bound. Source:
arXiv:1010.3732, Appendix A, lines 2575--2578, by finite minima. -/
theorem exists_uniform_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_bounded_volumes
    {X : Type*} [TopologicalSpace X] {r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x ↦ A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    {K : Set X} (hK : IsCompact K) (hR : S + 1 ≤ R) (M : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, N ≤ M → R ≤ N → ∀ x ∈ K, ∀ ν : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction
          (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian) ν → ν = 0 ∨ (δ : ℂ) ≤ ν := by
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ N ≤ M → R ≤ N → ∀ x ∈ K, ∀ ν : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction
          (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian) ν → ν = 0 ∨ (δ : ℂ) ≤ ν)
    ?_ ?_ (M := M + 1) zero_lt_one ?_
  · exact fun N γ δ hle hgap hNM hRN x hx ν hν ↦
      (hgap hNM hRN x hx ν hν).imp_right (Complex.real_le_real.mpr hle).trans
  · intro N
    by_cases hN : R ≤ N
    · exact (exists_uniform_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_fixed_volume
        μ A hμ hA hS hSpan hK hR hN).imp fun δ h ↦ ⟨h.1, fun _ _ ↦ h.2⟩
    · exact ⟨1, one_pos, fun _ hRN ↦ (hN hRN).elim⟩
  · exact fun N hMN hNM ↦ False.elim (by omega)

end MPSTensor

end

section

open scoped Topology

namespace MPSTensor
variable {d : ℕ}
/-- A strict norm gap of the Hamiltonian of the parent interaction on the open chain at a fixed
admissible volume persists near its parameter when the block tensors vary continuously. Source:
arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem eventually_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_fixed_volume
    {X : Type*} [TopologicalSpace X] {r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x ↦ A x j)
    {S R N : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) (hRN : R ≤ N) {x₀ : X} {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : δ < γ)
    (hgap : ∀ v ∈ (groundSpaceES (toTensorFromBlocks (μ x₀) (A x₀)) N)ᗮ,
      γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (μ x₀) (A x₀)) R N).hamiltonian v‖) :
    ∀ᶠ x in 𝓝 x₀, ∀ v ∈ (groundSpaceES (toTensorFromBlocks (μ x) (A x)) N)ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian v‖ := by
  have hProjR := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA R (fun x ↦ wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega))
  have hProjN := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA N (fun x ↦ wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega))
  have hCLM : Continuous fun M : Matrix (Cfg d N) (Cfg d N) ℂ ↦
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) := by
    let f : Matrix (Cfg d N) (Cfg d N) ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ (Cfg d N) →L[ℂ] EuclideanSpace ℂ (Cfg d N)) :=
      LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ Matrix.toEuclideanLin.toLinearMap
    exact f.continuous_of_finiteDimensional
  exact ContinuousLinearMap.eventually_norm_gap_on_orthogonal
    (fun x ↦ LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      (parentChainInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian))
    (fun x ↦ groundSpaceES (toTensorFromBlocks (μ x) (A x)) N)
    (hCLM.comp (continuous_hamiltonian_parentChainInteraction_family_of_groundProjection
      (fun x ↦ toTensorFromBlocks (μ x) (A x)) hProjR)).continuousAt
    hProjN.continuousAt
    (groundSpaceES_le_ker_hamiltonian_parentChainInteraction
      (toTensorFromBlocks (μ x₀) (A x₀)) R N) hγ hδ hgap

/-- A common strict norm gap of the Hamiltonians of the parent interaction on the open chain on
finitely many admissible volumes persists on one parameter neighborhood. Source:
arXiv:1010.3732, Appendix A, lines 2575--2578, by a finite intersection of neighborhoods. -/
theorem eventually_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_bounded_volumes
    {X : Type*} [TopologicalSpace X] {r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x ↦ A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) (M : ℕ) {x₀ : X} {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : δ < γ)
    (hgap : ∀ N : ℕ, R ≤ N → N ≤ M →
      ∀ v ∈ (groundSpaceES (toTensorFromBlocks (μ x₀) (A x₀)) N)ᗮ,
        γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks (μ x₀) (A x₀)) R N).hamiltonian v‖) :
    ∀ᶠ x in 𝓝 x₀, ∀ N : ℕ, R ≤ N → N ≤ M →
      ∀ v ∈ (groundSpaceES (toTensorFromBlocks (μ x) (A x)) N)ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian v‖ := by
  have hnear : ∀ N ∈ Finset.Icc R M, ∀ᶠ x in 𝓝 x₀,
      ∀ v ∈ (groundSpaceES (toTensorFromBlocks (μ x) (A x)) N)ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
          (parentChainInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian v‖ := by
    intro N hN
    exact eventually_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_fixed_volume
      μ A hμ hA hS hSpan hR (Finset.mem_Icc.mp hN).1 hγ hδ
      (hgap N (Finset.mem_Icc.mp hN).1 (Finset.mem_Icc.mp hN).2)
  filter_upwards [(Finset.Icc R M).eventually_all.2 hnear] with x hx
  exact fun N hRN hNM ↦ hx N (Finset.mem_Icc.mpr ⟨hRN, hNM⟩)

end MPSTensor

end
