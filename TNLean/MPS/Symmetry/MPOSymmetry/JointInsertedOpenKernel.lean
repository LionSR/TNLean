/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointInsertedIntersection
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenKernel

/-!
# Exact open kernels for joint inserted boundaries

Let \(h=1-P_{\operatorname{range}\Gamma'_2}\). For every chain length
\(N\geq2\), the nonwrapping sum of translates of \(h\) has kernel exactly
\(\operatorname{range}\Gamma'_N\). The proof uses positivity and the joint
restriction intersection theorem, retaining all cross-block physical overlaps.
Its dimension is \(\sum_xD_x^2\), and its orthogonal projector is continuous
along any continuous family satisfying simultaneous one-site spanning and
nonzero insertions in every block.

Source: arXiv:2203.12563, Section 5, lines 1695–1777. This establishes a
finite-volume open-kernel assertion. It does not establish an endpoint gap,
periodic endpoint identification, MPO commutation, or a gapped phase path.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {d r N : ℕ} {dim : Fin r → ℕ}

/-- The joint complementary support projection vanishes exactly on the two-site range.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem mem_ker_blockInsertedParentInteraction_iff
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) :
    v ∈ LinearMap.ker (1 - (blockInsertedBoundaryMap A W 2).range.starProjection).toLinearMap ↔
      v ∈ (blockInsertedBoundaryMap A W 2).range := by
  change v - (blockInsertedBoundaryMap A W 2).range.starProjection v = 0 ↔ _
  rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- The exact open-chain kernel is the full joint extended boundary range,
including when any of the nonzero block insertions is singular.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem ker_openInteractionHamiltonianES_blockInserted_eq
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap A W 2).range.starProjection).toLinearMap N) =
      (blockInsertedBoundaryMap A W N).range := by
  by_cases hd : d = 0
  · subst d
    have : IsEmpty (Cfg 0 N) := ⟨fun σ => (σ ⟨0, by omega⟩).elim0⟩
    ext v
    have hv : v = 0 := Subsingleton.elim _ _
    simp only [hv, Submodule.zero_mem]
  let : NeZero d := ⟨hd⟩
  have hpos :
      (1 - (blockInsertedBoundaryMap A W 2).range.starProjection).toLinearMap.IsPositive := by
    simpa only [Submodule.starProjection_orthogonal'] using
      (Submodule.isSymmetricProjection_starProjection
        ((blockInsertedBoundaryMap A W 2).range)ᗮ).isPositive
  ext v
  rw [mem_ker_openInteractionHamiltonianES_iff hpos hN,
    mem_range_blockInsertedBoundaryMap_iff]
  simp only [mem_ker_blockInsertedParentInteraction_iff]
  constructor
  · intro hv
    apply contiguous_mem_of_restriction_intersection_submodules
      (blockInsertedGroundSpace A W) (by omega : 0 < 2) hN ?_ ?_
    · intro M hM
      ext ψ
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      exact (blockInsertedGroundSpace_iff_left_right A hA W hW (by omega)).symm
    · intro s hs τ
      have hlocal := hv ⟨⟨s, by omega⟩, hs⟩ τ
      rw [mem_range_blockInsertedBoundaryMap_iff] at hlocal
      change cyclicRestrictₗ (by omega) 2 ⟨s, by omega⟩ τ
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d N) v) ∈
          blockInsertedGroundSpace A W 2 at hlocal
      rwa [cyclicRestrictₗ_eq_contiguousRestrictₗ _ hN hs] at hlocal
  · intro hv i τ
    rw [mem_range_blockInsertedBoundaryMap_iff]
    change cyclicRestrictₗ (Fin.pos i.1) 2 i.1 τ
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N) v) ∈ blockInsertedGroundSpace A W 2
    rw [cyclicRestrictₗ_eq_contiguousRestrictₗ _ hN i.2]
    exact contiguousRestrictₗ_blockInsertedGroundSpace_mem A W
      (by omega) i.1.val i.2 τ hv

/-- The joint open kernel has the sum of the squared block dimensions.
Source: arXiv:2203.12563, line 319 and Section 5, lines 1695–1777. -/
theorem finrank_ker_openInteractionHamiltonianES_blockInserted
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap A W 2).range.starProjection).toLinearMap N)) =
      ∑ x, dim x * dim x := by
  rw [ker_openInteractionHamiltonianES_blockInserted_eq A hA W hW hN]
  exact finrank_range_blockInsertedBoundaryMap A hA W hW (by omega)

/-- The projector onto the exact joint open kernel varies continuously.
This is finite-volume continuity and contains no uniform spectral-gap claim.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem continuous_ker_openInteractionHamiltonianES_blockInserted_starProjection
    {X : Type*} [TopologicalSpace X]
    (A : X → (x : Fin r) → MPSTensor d (dim x))
    (hA : ∀ x, Continuous fun t => A t x)
    (W : X → (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, Continuous fun t => W t x)
    (hSpan : ∀ t, WordTupleSpanTop (A t) 1)
    (hne : ∀ t x, W t x ≠ 0) (hN : 2 ≤ N) :
    Continuous fun t => (LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap (A t) (W t) 2).range.starProjection).toLinearMap
        N)).starProjection := by
  simp_rw [ker_openInteractionHamiltonianES_blockInserted_eq _ (hSpan _) _ (hne _) hN]
  have hP := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun t => blockInsertedBoundaryMap (A t) (W t) N)
    (continuous_blockInsertedBoundaryMap_family A hA W hW N)
    (fun t => blockInsertedBoundaryMap_injective (A t) (hSpan t) (W t) (hne t) (by omega))
  simpa only [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection] using hP

end MPSTensor.MPOSymmetry
