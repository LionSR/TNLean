/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryMap.OpenChain
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport

/-!
# Adjacent open-chain excitation projections

This file identifies, on the explicit three-site Hilbert space, the two
complementary open-chain ground projections with the range-two terms based at sites \(0\) and
\(1\) of the parent interaction on the ring (`parentRingInteraction`).

The coordinate identifications compare the open-chain `restrictLast` and tail
`restrictFirst` slices with the cyclic restrictions of the terms.
They yield the individual kernel identities before projection uniqueness is
applied; no injectivity or nonzero bond-dimension assumption is needed.

## Main results

* `MPSTensor.ker_toEuclideanLin_term_two_three_zero` identifies the
  site-\(0\) kernel with the left open-chain ground space.
* `MPSTensor.ker_toEuclideanLin_term_two_three_one` identifies the
  site-\(1\) kernel with the tail open-chain ground space.
* `MPSTensor.openChainLeftGroundSpaceES_orthogonal_starProjection_eq_parentRingInteraction_term`
  and `MPSTensor.openChainTailGroundSpaceES_orthogonal_starProjection_eq_parentRingInteraction_term`
  identify the complementary excitation projections with those terms.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, eqs. (2.4)--(2.5).
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127,
  Section IV.C, lines 2013--2078.
-/

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

/-! ### Open-chain and cyclic coordinate identifications -/

/-- Fixing the sole prefix site of a three-site state by `tailRestrictₗ` is
exactly `restrictFirst` at that coordinate.

This coordinate identity is used to realize the tail open-chain ground
projection in Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4). -/
theorem tailRestrictₗ_one_eq_restrictFirst (u : Fin 1 → α)
    (ψ : NSiteSpace α (1 + 2)) :
    tailRestrictₗ u ψ = restrictFirst ψ (u 0) := by
  ext σ
  simp only [tailRestrictₗ_apply, restrictFirst_apply]
  apply congrArg ψ
  rw [Fin.append_left_eq_cons]
  funext k
  exact congrArg (Fin.cons (u 0) σ) (Fin.ext (by simp))

private theorem range_eq_orthogonal_ker_of_isSymmetricProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {P : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) :
    LinearMap.range P = (LinearMap.ker P)ᗮ := by
  have horth : (LinearMap.range P)ᗮ = LinearMap.ker P := hP.isSymmetric.orthogonal_range
  rw [← horth, Submodule.orthogonal_orthogonal]

/-! ### The terms of the parent interaction on the ring of three sites -/

/-- On the explicit three-site chain, the kernel of the operator of the range-two term at site
\(0\) of the parent interaction on the ring is the left open-chain ground space.

Source terminology: this is the ground condition on \(Λ_n\) inside \(Λ_{n+1}\) in
Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4). -/
theorem ker_toEuclideanLin_term_two_three_zero (B : MPTensor α (Fin D)) :
    LinearMap.ker (Matrix.toEuclideanLin ((parentRingInteraction B 2 3).term 0)) =
      openChainLeftGroundSpaceES B 2 := by
  ext v
  rw [LinearMap.mem_ker, mem_openChainLeftGroundSpaceES_iff,
    toEuclideanLin_parentRingInteraction_term_eq_zero_iff B (by norm_num : 2 ≤ 3)]
  constructor
  · intro hv j
    have h := hv (fun _ => j)
    rw [mem_map_groundSpace_iff] at h
    rwa [restrictLast_eq_withLpMap_cyclicRestrictₗ_zero v (fun _ => j)]
  · intro hv τ
    rw [mem_map_groundSpace_iff, ← restrictLast_eq_withLpMap_cyclicRestrictₗ_zero v τ]
    exact hv (τ (Fin.last 2))

/-- On the explicit three-site chain, the kernel of the operator of the range-two term at site
\(1\) of the parent interaction on the ring is the one-site-prefix tail open-chain ground space.

Source terminology: this is the tail condition on \(Λ_{n+1} \ Λ_{n-l}\) inside \(Λ_{n+1}\) in
Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4). -/
theorem ker_toEuclideanLin_term_two_three_one (B : MPTensor α (Fin D)) :
    LinearMap.ker (Matrix.toEuclideanLin ((parentRingInteraction B 2 3).term 1)) =
      openChainTailGroundSpaceES B 1 2 := by
  ext v
  rw [LinearMap.mem_ker, mem_openChainTailGroundSpaceES_iff,
    toEuclideanLin_parentRingInteraction_term_eq_zero_iff B (by norm_num : 2 ≤ 3)]
  constructor
  · intro hv u
    rw [tailRestrictₗ_one_eq_restrictFirst]
    have h := hv (fun _ => u 0)
    rw [mem_map_groundSpace_iff] at h
    rwa [restrictFirst_eq_withLpMap_cyclicRestrictₗ_one (by omega) v (fun _ => u 0)]
  · intro hv τ
    rw [mem_map_groundSpace_iff, ← restrictFirst_eq_withLpMap_cyclicRestrictₗ_one (by omega) v τ,
      ← tailRestrictₗ_one_eq_restrictFirst (fun _ => τ 0)]
    exact hv (fun _ => τ 0)

/-- On the explicit three-site chain, the complementary left open-chain ground projection is the
operator of the range-two term at site \(0\) of the parent interaction on the ring: both are
symmetric projections with the same kernel. -/
theorem openChainLeftGroundSpaceES_orthogonal_starProjection_eq_parentRingInteraction_term
    (B : MPTensor α (Fin D)) :
    (openChainLeftGroundSpaceES B 2)ᗮ.starProjection.toLinearMap =
      Matrix.toEuclideanLin ((parentRingInteraction B 2 3).term 0) := by
  have hP := isSymmetricProjection_toEuclideanLin_parentRingInteraction_term B 2 (0 : Fin 3)
  apply (Submodule.isSymmetricProjection_starProjection
    ((openChainLeftGroundSpaceES B 2)ᗮ)).ext hP
  rw [Submodule.range_starProjection, range_eq_orthogonal_ker_of_isSymmetricProjection hP,
    ker_toEuclideanLin_term_two_three_zero]

/-- On the explicit three-site chain, the complementary tail open-chain ground projection is the
operator of the range-two term at site \(1\) of the parent interaction on the ring: both are
symmetric projections with the same kernel. -/
theorem openChainTailGroundSpaceES_orthogonal_starProjection_eq_parentRingInteraction_term
    (B : MPTensor α (Fin D)) :
    (openChainTailGroundSpaceES B 1 2)ᗮ.starProjection.toLinearMap =
      Matrix.toEuclideanLin ((parentRingInteraction B 2 3).term 1) := by
  have hP := isSymmetricProjection_toEuclideanLin_parentRingInteraction_term B 2 (1 : Fin 3)
  apply (Submodule.isSymmetricProjection_starProjection
    ((openChainTailGroundSpaceES B 1 2)ᗮ)).ext hP
  rw [Submodule.range_starProjection, range_eq_orthogonal_ker_of_isSymmetricProjection hP,
    ker_toEuclideanLin_term_two_three_one]

end MPSTensor
