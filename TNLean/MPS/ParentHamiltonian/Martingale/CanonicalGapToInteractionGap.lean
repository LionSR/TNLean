/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteractionRangeComparison

/-!
# Transfer of canonical gaps to a positive interaction

Suppose the canonical parent Hamiltonians have exact MPS boundary kernels
and uniform gaps at every sufficiently large interaction range. Any positive
interaction whose open kernels eventually agree with those same spaces then
has one positive norm gap at every volume, measured above its actual kernel.

On one sufficiently long interval, finite dimensionality supplies a positive
multiple of the canonical excitation projection below the given Hamiltonian.
The interval comparison extends to larger chains with the usual window
multiplicity. The finitely many shorter chains require only their individual
finite-dimensional gaps. No relation between the given local kernel and the
MPS space at its interaction range is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2,
lines 933--947, condition C1, and Section 6, lines 2593--2675.
-/

open Filter
open scoped Topology ComplexOrder
namespace MPSTensor
variable {d D : ℕ}

/-- Uniform canonical gaps at all sufficiently large ranges transfer to any
positive interaction whose open kernels eventually equal the same MPS
boundary spaces. The conclusion holds at every volume above its actual
kernel; neither a local parent-kernel identity nor an injectivity hypothesis
is required. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, lines 933--947, condition C1, lines 1030--1041,
and Section 6, lines 2593--2675. This is a generic finite-window criterion;
canonical gaps are explicit inputs. -/
theorem exists_openInteractionHamiltonianES_gap_of_canonical_gaps_of_eventual_kernel
    (A : MPSTensor d D) {R₀ : ℕ} (_hR₀ : 0 < R₀)
    (hCanonical : ∀ W, R₀ ≤ W →
      (∀ N, W ≤ N → LinearMap.ker (openParentHamiltonianES A W N) = groundSpaceES A N) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ N,
        ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A W N))ᗮ,
          δ * ‖v‖ ≤ ‖openParentHamiltonianES A W N v‖)
    {R : ℕ} (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hR : 0 < R) (hh : h.IsPositive)
    (hKernel : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES h N) = groundSpaceES A N) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N,
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES h N))ᗮ,
        γ * ‖v‖ ≤ ‖openInteractionHamiltonianES h N v‖ := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hKernel
  let W := max R (max N₀ R₀)
  have hBounds : R ≤ W ∧ N₀ ≤ W ∧ R₀ ≤ W := by omega
  obtain ⟨hCanonicalKernel, δ, hδ, hCanonicalGap⟩ := hCanonical W hBounds.2.2
  obtain ⟨κ, hκ, hLocal⟩ :=
    LinearMap.IsPositive.exists_pos_smul_orthogonal_ker_projection_le
      (openInteractionHamiltonianES_isPositive hh W)
  rw [hN₀ W hBounds.2.1] at hLocal
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N γ => ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES h N))ᗮ,
      γ * ‖v‖ ≤ ‖openInteractionHamiltonianES h N v‖)
    (fun N γ η hle hgap v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv))
    (fun N => LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openInteractionHamiltonianES h N))
    (M := W) (δ := κ * δ / (W - R + 1 : ℕ))
    (div_pos (mul_pos hκ hδ) (Nat.cast_pos.mpr (by omega))) ?_
  intro N hN
  rw [hN₀ N (hBounds.2.1.trans hN)]
  refine openInteractionHamiltonianES_gap_of_long_gap_at_length
    A h hh hR hBounds.1 hN hκ hδ hLocal
    (hN₀ N (hBounds.2.1.trans hN)) (hCanonicalKernel N hN) ?_
  simpa only [hCanonicalKernel N hN] using hCanonicalGap N

end MPSTensor
