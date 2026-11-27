/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.PrimitiveQuasiLocalUniqueness
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalCommutatorLocality

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
open ManyBody (placeAlong chainWindow)
namespace MPSTensor
variable {d D : ℕ}

/-- The ground projection placed on a contained window of the open chain fixes
the full open-boundary MPS ground projection. No injectivity is required.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12), its
frustration-free restriction direction. -/
theorem placeAlong_chainWindow_groundSpaceProjection_mul
    (A : MPSTensor d D) {k N b : ℕ} (hb : b + k ≤ N) :
    placeAlong (X := fun _ ↦ Fin d) (chainWindow b hb) (groundSpaceProjectionMatrix A k) *
      groundSpaceProjectionMatrix A N = groundSpaceProjectionMatrix A N := by
  have hP : 1 - groundSpaceProjectionMatrix A k = LinearMap.toMatrix' (parentInteraction A k) := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_toMatrix'_parentInteraction]
    change (Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ)
      (1 - groundSpaceProjectionMatrix A k)).toLinearMap = _
    rw [map_sub, map_one, groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply,
      Submodule.starProjection_orthogonal]
    rfl
  have hkill : (parentChainInteraction A k N).term ⟨b, by omega⟩ *
      groundSpaceProjectionMatrix A N = 0 := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin_mul, map_zero]
    ext1 v
    have hmem : Matrix.toEuclideanLin (groundSpaceProjectionMatrix A N) v ∈ ((groundSpace A N).map
        (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
      change (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (groundSpaceProjectionMatrix A N)) v ∈ _
      rw [groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply]
      exact ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection_apply_mem v
    have hv := map_groundSpace_le_ker_hamiltonian_parentChainInteraction A k N hmem
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    generalize Matrix.toEuclideanLin (groundSpaceProjectionMatrix A N) v = w at hv ⊢
    rw [Matrix.toLpLin_apply, WithLp.toLp_eq_zero]
    exact (parentChainInteraction_term_mulVec_eq_zero_iff A _ _).mpr fun τ ↦
      contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv
        b hb τ
  rw [ManyBody.Interaction.ofPlaceAlong_term, ← hP, ManyBody.placeAlong_sub,
    ManyBody.placeAlong_one, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hkill
  exact hkill.symm
variable [NeZero d]

/-- Support in an MPS interval implies support in every contained
interval. Positivity supplies the support-compression identity.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, finite-interval
support spaces and equation (3.12). -/
theorem quasiLocalState_groundSpaceProjection_eq_one_of_contained_interval
    (A : MPSTensor d D) (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d) (a : ℤ) {k N b : ℕ}
    (hb : b + k ≤ N)
    (hSupport : φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix A N)) = 1) :
    φ (quasiLocalIntervalObservable d (a + (b : ℤ)) k
      (groundSpaceProjectionMatrix A k)) = 1 := by
  let p := groundSpaceProjectionMatrix A N
  let q := placeAlong (X := fun _ ↦ Fin d) (chainWindow b hb) (groundSpaceProjectionMatrix A k)
  let f := intervalStateFunctional φ hφ.2.2 a N
  have hf : f p = f 1 := by
    simpa only [f, p, intervalStateFunctional_apply, map_one, hφ.2.1] using hSupport
  have hcomp := f.apply_projection_compression_eq p q
    (isStarProjection_groundSpaceProjectionMatrix A N).isSelfAdjoint.star_eq
    (isStarProjection_groundSpaceProjectionMatrix A N).isIdempotentElem hf
  have hpqp : p * q * p = p := by
    rw [mul_assoc, placeAlong_chainWindow_groundSpaceProjection_mul A hb,
      (isStarProjection_groundSpaceProjectionMatrix A N).isIdempotentElem]
  rw [hpqp] at hcomp
  simpa only [f, p, q, intervalStateFunctional_apply,
    quasiLocalIntervalObservable_placeAlong_chainWindow a N b _ hb]
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
      A φ hφ ((a / (L : ℤ)) * (L : ℤ)) (Nat.le_mul_of_pos_right (b + N) hL)
      (h (a / (L : ℤ)) (b + N) hpos)
    simpa only [hb, Int.ediv_mul_add_emod] using hSupport
end MPSTensor
