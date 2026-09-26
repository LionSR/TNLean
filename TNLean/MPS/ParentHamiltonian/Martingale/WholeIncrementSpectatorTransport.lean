/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport

/-!
# Spectator transport for whole interval increments

The interval projector error in Nachtergaele's condition C3′ is unchanged
by adding free sites to the right, up to the norm contraction of the finite
fiber extension. Kernel identifications are supplied for the active volumes,
so the argument applies to block-diagonal tensors as well as primitive ones.
See arXiv:cond-mat/9410110, condition C3′, lines 1095--1107.
-/

private theorem norm_projection_difference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U V W : Submodule ℂ E) (hWV : W ≤ V) :
    ‖V.starProjection.comp (U.starProjection - W.starProjection)‖ =
      ‖W.starProjection - U.starProjection.comp V.starProjection‖ := by
  have hVW : V.starProjection.comp W.starProjection = W.starProjection := by
    ext x
    exact V.starProjection_eq_self_iff.mpr (hWV (Submodule.starProjection_apply_mem W x))
  rw [ContinuousLinearMap.comp_sub, hVW]
  change ‖V.starProjection * U.starProjection - W.starProjection‖ =
    ‖W.starProjection - U.starProjection * V.starProjection‖
  rw [← norm_star (V.starProjection * U.starProjection - W.starProjection),
    star_sub, star_mul, (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq, (isSelfAdjoint_starProjection W).star_eq,
    norm_sub_rev]

namespace MPSTensor

variable {d D : ℕ}

/-- A vector lies in the extended left ground space precisely when every
right-coordinate restriction lies in the active local ground space. -/
theorem mem_range_leftBoundaryMapES_iff_rightFiber
    (A : MPSTensor d D) (n r : ℕ)
    (v : EuclideanSpace ℂ (Cfg d (n + r))) :
    v ∈ (leftBoundaryMapES A n r).range ↔ ∀ s : Cfg d r,
      ContinuousLinearMap.rightFiber
        (rightSpectatorConfigLinearIsometryEquiv d n r v) s ∈ groundSpaceES A n := by
  simp only [leftBoundaryMapES, LinearMap.coe_toContinuousLinearMap,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.mem_map_equiv, mem_groundSpaceES_iff]
  rw [← SetLike.mem_coe, leftBoundaryMap_range_eq]
  rfl

/-- An identification of the active open-chain kernel with the local ground
space identifies the larger-volume prefix kernel with its right extension. -/
theorem ker_openPrefixParentHamiltonianES_eq_range_leftBoundaryMapES
    (A : MPSTensor d D) {R n r : ℕ} (hR : 0 < R)
    (hker : LinearMap.ker (openParentHamiltonianES A R n) = groundSpaceES A n) :
    LinearMap.ker (openPrefixParentHamiltonianES A R (n + r) n) =
      (leftBoundaryMapES A n r).range := by
  ext v
  have hconj : rightSpectatorConfigLinearIsometryEquiv d n r
      (openPrefixParentHamiltonianES A R (n + r) n v) =
      ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        (LinearMap.toContinuousLinearMap (openPrefixParentHamiltonianES A R n n))
        (rightSpectatorConfigLinearIsometryEquiv d n r v) := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply] using
      LinearMap.congr_fun
        (openPrefixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
          A (n := n) (r := r) (p := n) hR le_rfl)
        (rightSpectatorConfigLinearIsometryEquiv d n r v)
  rw [mem_range_leftBoundaryMapES_iff_rightFiber, LinearMap.mem_ker,
    ← (rightSpectatorConfigLinearIsometryEquiv d n r).map_eq_zero_iff, hconj]
  change (rightSpectatorConfigLinearIsometryEquiv d n r v) ∈
    LinearMap.ker (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
      (LinearMap.toContinuousLinearMap (openPrefixParentHamiltonianES A R n n))).toLinearMap ↔ _
  rw [ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff,
    LinearMap.coe_toContinuousLinearMap,
    openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES, hker]

/-- Reassociation transports any length-indexed subspace to the same subspace
in the equal ambient length. -/
theorem physicalReassocES_map_submodule
    (S : ∀ n, Submodule ℂ (EuclideanSpace ℂ (Cfg d n))) (K L Q : ℕ) :
    (S (K + (L + Q))).map
      (physicalReassocES (d := d) K L Q).toLinearEquiv.toLinearMap =
      S (K + L + Q) := by
  suffices ∀ (n m : ℕ) (h : n = m),
      (S n).map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.arrowCongr (finCongr h) (Equiv.refl (Fin d)))).toLinearEquiv.toLinearMap =
      S m from this _ _ (Nat.add_assoc K L Q).symm
  rintro n m rfl
  change (S n).map LinearMap.id = S n
  exact Submodule.map_id _

/-- The reassociated right interval is the kernel of the parent interaction
on the full suffix window. -/
theorem range_reassocTailBoundaryMapES_eq_ker_openSuffixParentHamiltonianES
    (A : MPSTensor d D) {K L Q : ℕ} (hR : 0 < L + Q) :
    (reassocTailBoundaryMapES A K L Q).range =
      LinearMap.ker (openSuffixParentHamiltonianES A (L + Q) (L + Q)
        (K + L + Q) (K + L + Q)) := by
  rw [reassocTailBoundaryMapES, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, range_tailBoundaryMapES,
    ← ker_openSuffixParentHamiltonianES_eq_openChainTailGroundSpaceES A hR]
  exact physicalReassocES_map_submodule
    (fun n ↦ LinearMap.ker (openSuffixParentHamiltonianES A (L + Q) (L + Q) n n)) K L Q

/-- The active grouped martingale error is the three-interval projector
error, provided the two prefix kernels are their boundary-condition spaces.
This is the projector identity underlying Nachtergaele's condition C3-prime,
arXiv:cond-mat/9410110, lines 1095--1107. -/
theorem norm_suffixProjection_comp_prefixDifference_eq_projector_defect
    (A : MPSTensor d D) {K L Q : ℕ} (hR : 0 < L + Q)
    (hleft : LinearMap.ker (openParentHamiltonianES A (L + Q) (K + L)) =
      groundSpaceES A (K + L))
    (hfull : LinearMap.ker (openParentHamiltonianES A (L + Q) (K + L + Q)) =
      groundSpaceES A (K + L + Q)) :
    ‖LinearMap.toContinuousLinearMap
      ((LinearMap.ker (openSuffixParentHamiltonianES A (L + Q) (L + Q)
        (K + L + Q) (K + L + Q))).starProjection.toLinearMap.comp
        (openPrefixGroundProjectionES A (L + Q) (K + L + Q) (K + L) -
          openPrefixGroundProjectionES A (L + Q) (K + L + Q) (K + L + Q)))‖ =
      ‖(groundSpaceES A (K + L + Q)).starProjection -
        (leftBoundaryMapES A (K + L) Q).range.starProjection.comp
          (reassocTailBoundaryMapES A K L Q).range.starProjection‖ := by
  have hWV : groundSpaceES A (K + L + Q) ≤
      (reassocTailBoundaryMapES A K L Q).range := by
    rw [← range_groundSpaceMapES,
      ← reassocTailBoundaryMapES_comp_tailVirtualMapES A K L Q]
    exact LinearMap.range_comp_le_range _ _
  simp only [openPrefixGroundProjectionES,
    ker_openPrefixParentHamiltonianES_eq_range_leftBoundaryMapES A hR hleft,
    openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES, hfull,
    ← range_reassocTailBoundaryMapES_eq_ker_openSuffixParentHamiltonianES A hR]
  exact norm_projection_difference _ _ _ hWV

end MPSTensor
