/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison
import TNLean.MPS.ParentHamiltonian.Martingale.WholeIncrementSpectatorTransport
/-!
# Terminal interval kernels and boundary spaces

A finite terminal interval acts independently of its free sites. Consequently,
its kernel depends only on its active finite-interval kernel. This identifies
the terminal kernel with the boundary space in the three-interval projector
estimate of Nachtergaele, arXiv:cond-mat/9410110, condition C3-prime.
-/

open scoped ComplexOrder
namespace MPSTensor
variable {d D : ℕ}
/-- Equality of the active local kernel with the MPS ground space identifies
an embedded terminal Hamiltonian with the full-window terminal ground space.
This is the interval kernel identification used in Nachtergaele,
arXiv:cond-mat/9410110, condition C3-prime, lines 1095--1107. -/
theorem ker_openSuffixParentHamiltonianES_eq_of_local_kernel (A : MPSTensor d D) {R W N n : ℕ}
    (hR : 0 < R) (hRW : R ≤ W) (hWn : W ≤ n) (hnN : n ≤ N)
    (hker : LinearMap.ker (openParentHamiltonianES A R W) = groundSpaceES A W) :
    LinearMap.ker (openSuffixParentHamiltonianES A R W N n) =
      LinearMap.ker (openSuffixParentHamiltonianES A W W N n) := by
  ext v
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (hWn.trans hnN) ⟨n - W, by omega⟩
  have hconj (T : ℕ) (hT : 0 < T) (hTW : T ≤ W) :
      U (openSuffixParentHamiltonianES A T W N n v) =
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
          (openParentHamiltonianES A T W).toContinuousLinearMap (U v) := by
    simpa only [U, LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply] using
      LinearMap.congr_fun (openSuffixParentHamiltonianES_conj_cyclicActiveBlock
        A hT hTW hWn hnN) (U v)
  rw [LinearMap.mem_ker, ← U.map_eq_zero_iff, hconj R hR hRW,
    LinearMap.mem_ker, ← U.map_eq_zero_iff, hconj W (hR.trans_le hRW) le_rfl]
  change U v ∈ LinearMap.ker
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
      (openParentHamiltonianES A R W).toContinuousLinearMap).toLinearMap ↔
    U v ∈ LinearMap.ker
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
      (openParentHamiltonianES A W W).toContinuousLinearMap).toLinearMap
  rw [ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff,
    ContinuousLinearMap.mem_ker_rightFiberwiseMap_iff, LinearMap.coe_toContinuousLinearMap,
    hker, openParentHamiltonianES_self_eq_parentInteractionES A (hR.trans_le hRW)]
  simp only [LinearMap.coe_toContinuousLinearMap, parentInteractionES,
    Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
/-- The kernel of a terminal interval Hamiltonian is the reassociated tail
boundary space whenever its active finite-interval kernel is the MPS ground
space. Source: Nachtergaele, arXiv:cond-mat/9410110, condition C3-prime,
lines 1095--1107. -/
theorem ker_openSuffixParentHamiltonianES_eq_range_reassocTailBoundaryMapES
    (A : MPSTensor d D) {R K L Q : ℕ}
    (hR : 0 < R) (hRW : R ≤ L + Q)
    (hker : LinearMap.ker (openParentHamiltonianES A R (L + Q)) =
      groundSpaceES A (L + Q)) :
    LinearMap.ker (openSuffixParentHamiltonianES A R (L + Q)
      (K + L + Q) (K + L + Q)) = (reassocTailBoundaryMapES A K L Q).range := by
  simpa only [ker_openSuffixParentHamiltonianES_eq_of_local_kernel
    A hR hRW (by omega : L + Q ≤ K + L + Q) le_rfl hker] using
    (range_reassocTailBoundaryMapES_eq_ker_openSuffixParentHamiltonianES
      A (hR.trans_le hRW)).symm
end MPSTensor
