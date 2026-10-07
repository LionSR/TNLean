/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactKernelGap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceContinuity
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.BlockWordSpanSeparation

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
-/

open scoped Topology ComplexOrder

namespace MPSTensor

variable {d : ℕ}

/-- A compact continuous family of simultaneously injective blocks has one
positive gap on each fixed admissible open interval. Nonzero block weights
need no continuity assumption. Source: arXiv:1010.3732, Appendix A,
lines 2575--2578, for the finite-window continuity argument. -/
theorem exists_uniform_openParentHamiltonianES_toTensorFromBlocks_gap_fixed_volume
    {X : Type*} [TopologicalSpace X] {r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x ↦ A x j)
    {S R N : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    {K : Set X} (hK : IsCompact K) (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N v‖ := by
  have hProjR := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA R (fun x ↦ wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega))
  have hProjN := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA N (fun x ↦ wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega))
  have hKernel : Continuous fun x ↦ (LinearMap.ker (openParentHamiltonianES
      (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N)).starProjection := by
    simpa only [ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_wordTupleSpanTop
      (μ _) (A _) (hμ _) hS (hSpan _) hR hRN] using hProjN
  exact ContinuousLinearMap.exists_uniform_norm_gap_of_compact
    (fun x ↦ (openParentHamiltonianES
      (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N).toContinuousLinearMap)
    (continuous_openParentHamiltonianES_family_of_groundProjection
      (fun x ↦ toTensorFromBlocks (d := d) (μ := μ x) (A x)) hRN hProjR)
    hKernel hK
/-- A finite upper bound on the interval length gives one positive open-chain
gap uniform over the compact tensor family and every admissible interval below
that bound. The constant may depend on the upper bound. Source:
arXiv:1010.3732, Appendix A, lines 2575--2578, by finite minima. -/
theorem exists_uniform_openParentHamiltonianES_toTensorFromBlocks_gap_bounded_volumes
    {X : Type*} [TopologicalSpace X] {r : ℕ} {dim : Fin r → ℕ}
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x ↦ A x j)
    {S R : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    {K : Set X} (hK : IsCompact K) (hR : S + 1 ≤ R) (M : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, N ≤ M → R ≤ N → ∀ x ∈ K, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N v‖ := by
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N δ ↦ N ≤ M → R ≤ N → ∀ x ∈ K, ∀ v ∈
      (LinearMap.ker (openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N))ᗮ,
      δ * ‖v‖ ≤ ‖openParentHamiltonianES
        (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N v‖)
    ?_ ?_ (M := M + 1) zero_lt_one ?_
  · exact fun N γ δ hle hgap hNM hRN x hx v hv ↦
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap hNM hRN x hx v hv)
  · intro N
    by_cases hN : R ≤ N
    · exact (exists_uniform_openParentHamiltonianES_toTensorFromBlocks_gap_fixed_volume
        μ A hμ hA hS hSpan hK hR hN).imp fun δ h ↦ ⟨h.1, fun _ _ ↦ h.2⟩
    · exact ⟨1, one_pos, fun _ hRN ↦ (hN hRN).elim⟩
  · exact fun N hMN hNM ↦ False.elim (by omega)

end MPSTensor
