/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport

/-!
# Spectator extension of a grouped martingale error

Extending a chain by sites to its right does not increase the norm of a suffix
kernel projection composed with a difference of two prefix kernel projections.
All three Hamiltonians act trivially on the added sites; their kernel
projections therefore extend fiberwise. No injectivity assumption is needed.

This is the fixed-volume passage for the grouped martingale estimate in
Nachtergaele, arXiv:cond-mat/9410110, condition C3-prime and Theorem 2.1(ii).
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Adding right spectator sites does not increase the norm of the grouped
martingale expression. The active suffix ends at the full active volume, and
both prefix endpoints lie within that volume. This is the fixed-volume
extension of Nachtergaele's condition C3-prime, arXiv:cond-mat/9410110,
lines 1095--1104. -/
theorem norm_suffixGroundProjection_comp_prefixDifference_le_active
    (A : MPSTensor d D) {R l n r p : ℕ} (hR : 0 < R) (hp : p ≤ n) :
    ‖LinearMap.toContinuousLinearMap
      (((LinearMap.ker
        (openSuffixParentHamiltonianES A R l (n + r) n)).starProjection.toLinearMap).comp
        (openPrefixGroundProjectionES A R (n + r) p -
          openPrefixGroundProjectionES A R (n + r) n))‖ ≤
      ‖LinearMap.toContinuousLinearMap
        (((LinearMap.ker (openSuffixParentHamiltonianES A R l n n)).starProjection.toLinearMap).comp
          (openPrefixGroundProjectionES A R n p - openPrefixGroundProjectionES A R n n))‖ := by
  let U := rightSpectatorConfigLinearIsometryEquiv d n r
  have hproj
      (G : EuclideanSpace ℂ (Cfg d (n + r)) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d (n + r)))
      (H : EuclideanSpace ℂ (Cfg d n) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d n))
      (hc : U.toLinearEquiv.conj G =
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
          (LinearMap.toContinuousLinearMap H)).toLinearMap) :
      U.toLinearEquiv.conj (LinearMap.ker G).starProjection.toLinearMap =
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
          (LinearMap.ker H).starProjection).toLinearMap := by
    simpa only [ContinuousLinearMap.ker_starProjection_rightFiberwiseMap,
      LinearMap.coe_toContinuousLinearMap, LinearEquiv.conj_apply, LinearMap.comp_assoc] using!
      ker_starProjection_conj_linearIsometryEquiv U G _ hc
  have hP (q : ℕ) (hq : q ≤ n) := hproj _ _
    (openPrefixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
      A (r := r) hR hq)
  have hQ := hproj _ _
    (openSuffixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
      A (l := l) (n := n) (r := r) hR le_rfl)
  have hprod : U.toLinearEquiv.conj
      (((LinearMap.ker
        (openSuffixParentHamiltonianES A R l (n + r) n)).starProjection.toLinearMap).comp
        (openPrefixGroundProjectionES A R (n + r) p -
          openPrefixGroundProjectionES A R (n + r) n)) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d r)
        ((LinearMap.ker (openSuffixParentHamiltonianES A R l n n)).starProjection.comp
          ((LinearMap.ker (openPrefixParentHamiltonianES A R n p)).starProjection -
            (LinearMap.ker
              (openPrefixParentHamiltonianES A R n n)).starProjection))).toLinearMap := by
    simp only [LinearEquiv.conj_comp, map_sub, openPrefixGroundProjectionES,
      hQ, hP p hp, hP n le_rfl]
    rw [← ContinuousLinearMap.toLinearMap_sub, ← ContinuousLinearMap.toLinearMap_comp,
      ← ContinuousLinearMap.rightFiberwiseMap_sub, ContinuousLinearMap.rightFiberwiseMap_comp]
  exact (ContinuousLinearMap.norm_conj_linearIsometryEquiv U _).symm.trans_le
    ((congrArg (fun f ↦ ‖LinearMap.toContinuousLinearMap f‖) hprod).trans_le
      (ContinuousLinearMap.norm_rightFiberwiseMap_le _))

end MPSTensor
