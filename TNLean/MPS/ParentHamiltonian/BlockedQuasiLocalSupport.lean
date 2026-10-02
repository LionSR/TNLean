/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalUniqueness
import TNLean.MPS.ParentHamiltonian.QuasiLocalCommutatorLocality

/-!
# MPS support on aligned blocked intervals

A positive normalized quasi-local state is supported in every nonempty MPS
interval if and only if it is supported in the intervals aligned with a fixed
positive blocking length. Every interval is contained in an aligned one.
The universal restriction property of open-boundary MPS vectors makes the
larger ground projection a subprojection of the extended smaller projection.
Positivity then transfers support to the smaller interval.

No primitivity, translation invariance, or spectral-gap assumption is required.
These are support-space consequences of the blocking convention in
Nachtergaele, arXiv:cond-mat/9410110, Section 3, and the local ground-space
restriction property used in equation (3.12).
-/

open SpinChain
open scoped Matrix MatrixOrder ComplexOrder
namespace MPSTensor
variable {d D : ℕ}

/-- The ground projection on a contained nonwrapping window fixes the full
open-boundary MPS ground projection. No injectivity is required.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12), its
frustration-free restriction direction. -/
theorem chainWindowOperator_groundSpaceProjection_mul
    (A : MPSTensor d D) {k N b : ℕ} (hk : 0 < k) (hb : b + k ≤ N) :
    chainWindowOperator N b (groundSpaceProjectionMatrix A k) *
      groundSpaceProjectionMatrix A N = groundSpaceProjectionMatrix A N := by
  let i : Fin N := ⟨b, by omega⟩
  have hkill : (localTermES A k i).toContinuousLinearMap.comp
      (groundSpaceES A N).starProjection = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    exact localTermES_eq_zero_of_openParentHamiltonianES_eq_zero A k N
      (LinearMap.mem_ker.mp (groundSpaceES_le_ker_openParentHamiltonianES A k N
        ((groundSpaceES A N).starProjection_apply_mem v))) ⟨i, hb⟩
  have hc : Matrix.toEuclideanLin (1 - groundSpaceProjectionMatrix A k) =
      parentInteractionES A k := by
    change (Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ)
      (1 - groundSpaceProjectionMatrix A k)).toLinearMap = _
    rw [map_sub, map_one, groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply]
    rw [parentInteractionES, Submodule.starProjection_orthogonal]
    rfl
  have hlocal := periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator
    (show k ≤ N by omega) i (1 - groundSpaceProjectionMatrix A k)
  rw [hc, periodicLocalInteractionES_parentInteractionES A hk] at hlocal
  have hwindow : Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (chainWindowOperator N b (1 - groundSpaceProjectionMatrix A k)) =
        (localTermES A k i).toContinuousLinearMap := by
    exact ContinuousLinearMap.coe_injective (by
      simpa only [chainWindowOperator, dite_eq_left (show k ≤ N ∧ b < N by omega), i,
        Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, LinearMap.coe_toContinuousLinearMap]
        using hlocal.symm)
  rw [chainWindowOperator_sub (by omega) hb, chainWindowOperator_one (by omega) hb,
    map_sub, map_one] at hwindow
  apply (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)).injective
  change Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (chainWindowOperator N b (groundSpaceProjectionMatrix A k) *
        groundSpaceProjectionMatrix A N) =
    Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (groundSpaceProjectionMatrix A N)
  simp only [map_mul, groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply]
  change (localTermES A k i).toContinuousLinearMap *
    (groundSpaceES A N).starProjection = 0 at hkill
  rw [← hwindow, sub_mul, one_mul] at hkill
  exact (sub_eq_zero.mp hkill).symm
variable [NeZero d]

/-- Support in an MPS interval implies support in every contained nonempty
interval. Positivity supplies the support-compression identity.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, finite-interval
support spaces and equation (3.12). -/
theorem quasiLocalState_groundSpaceProjection_eq_one_of_contained_interval
    (A : MPSTensor d D) (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d) (a : ℤ) {k N b : ℕ}
    (hk : 0 < k) (hb : b + k ≤ N)
    (hSupport : φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix A N)) = 1) :
    φ (quasiLocalIntervalObservable d (a + (b : ℤ)) k
      (groundSpaceProjectionMatrix A k)) = 1 := by
  let p := groundSpaceProjectionMatrix A N
  let q := chainWindowOperator N b (groundSpaceProjectionMatrix A k)
  let f := intervalStateFunctional φ hφ.2.2 a N
  have hf : f p = f 1 := by
    simpa only [f, p, intervalStateFunctional_apply, map_one, hφ.2.1] using hSupport
  have hcomp := f.apply_projection_compression_eq p q
    (isStarProjection_groundSpaceProjectionMatrix A N).isSelfAdjoint.star_eq
    (isStarProjection_groundSpaceProjectionMatrix A N).isIdempotentElem hf
  have hpqp : p * q * p = p := by
    rw [mul_assoc, chainWindowOperator_groundSpaceProjection_mul A hk hb,
      (isStarProjection_groundSpaceProjectionMatrix A N).isIdempotentElem]
  rw [hpqp] at hcomp
  simpa only [f, p, q, intervalStateFunctional_apply,
    quasiLocalIntervalObservable_chainWindowOperator a N b _ hk hb]
    using hcomp.symm.trans hSupport
/-- Support in all nonempty original MPS intervals is equivalent to support
in the intervals aligned with any fixed positive blocking length. No
primitivity or translation invariance is assumed.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, the blocking
convention and finite-interval support spaces. -/
theorem quasiLocalState_groundSpaceProjection_eq_one_iff_aligned
    (A : MPSTensor d D) (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d) {L : ℕ} (hL : 0 < L) :
    (∀ (a : ℤ) (N : ℕ), 0 < N →
      φ (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1) ↔
    (∀ (a : ℤ) (N : ℕ), 0 < N →
      φ (quasiLocalIntervalObservable d (a * (L : ℤ)) (N * L)
        (groundSpaceProjectionMatrix A (N * L))) = 1) := by
  constructor
  · exact fun h a N hN => h (a * (L : ℤ)) (N * L) (Nat.mul_pos hN hL)
  · intro h a N hN
    let b := (a % (L : ℤ)).toNat
    have hb : ((b : ℕ) : ℤ) = a % (L : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast (Nat.ne_of_gt hL)))
    have hpos : 0 < b + N := by omega
    have hSupport := quasiLocalState_groundSpaceProjection_eq_one_of_contained_interval
      A φ hφ ((a / (L : ℤ)) * (L : ℤ)) hN (Nat.le_mul_of_pos_right (b + N) hL)
      (h (a / (L : ℤ)) (b + N) hpos)
    simpa only [hb, Int.ediv_mul_add_emod] using hSupport
end MPSTensor
