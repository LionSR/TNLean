/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalGroundStateSupport
import TNLean.MPS.ParentHamiltonian.QuasiLocalParentGroundStateFace
import TNLean.MPS.ParentHamiltonian.BlockedQuasiLocalSupport

/-!
# Zero local energy and support in every finite MPS interval

Suppose a positive interaction of positive range has the prescribed open MPS
space as its kernel on every sufficiently long chain. A normalized positive
quasi-local state has zero expectation on every translated interaction exactly
when its expectation on every nonempty interval MPS projection is one.

The forward implication starts with sufficiently large symmetric intervals and
uses the restriction of open MPS spaces to contained intervals. Conversely,
support in one sufficiently long interval annihilates the open Hamiltonian
expectation by projection compression. Each positive summand then has zero
expectation. The proof concerns all states, without translation invariance,
normality of the tensor, or an injectivity bound on the interaction range.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, and Section 3, finite-interval support spaces.
-/

open Filter SpinChain
open scoped Matrix MatrixOrder ComplexOrder BigOperators
namespace MPSTensor

variable {d D : ℕ} [NeZero d]

/-- Eventual support on expanding symmetric intervals implies exact support
on every contained positive-length interval. This is the finite-support
restriction used in Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 907--915, and Section 3. No translation invariance is assumed. -/
theorem quasiLocalState_groundSpaceProjection_eq_one_of_eventual_symmetric_support
    (A : MPSTensor d D) (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d)
    (hSupport : ∀ᶠ n : ℕ in atTop,
      φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
        (groundSpaceProjectionMatrix A (2 * n + 1))) = 1)
    (a : ℤ) (N : ℕ) (hN : 0 < N) :
    φ (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1 := by
  obtain ⟨n, hn, hlarge⟩ :=
    (hSupport.and (eventually_ge_atTop (a.natAbs + N))).exists
  have ha : -(a.natAbs : ℤ) ≤ a := by
    simpa only [Int.natAbs_neg, neg_le] using Int.le_natAbs (a := -a)
  have hb : (((a + (n : ℤ)).toNat : ℕ) : ℤ) = a + (n : ℤ) :=
    Int.toNat_of_nonneg (by omega)
  have hcontained : (a + (n : ℤ)).toNat + N ≤ 2 * n + 1 := by
    have h := Int.le_natAbs (a := a)
    omega
  have h := quasiLocalState_groundSpaceProjection_eq_one_of_contained_interval
    A φ hφ (-(n : ℤ)) hN hcontained hn
  simpa only [show -(n : ℤ) + ((a + (n : ℤ)).toNat : ℤ) = a by omega] using h

/-- Under the eventual open-chain kernel identity, a normalized positive
state has zero local interaction energy precisely when it has full expectation
on every nonempty interval MPS projection.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, and Section 3, finite-interval support spaces. The tensor is
arbitrary; there is no injectivity requirement on the interaction range. -/
theorem mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
    (A : MPSTensor d D) {R : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES A N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    φ ∈ parentGroundStateFace h ↔
      φ ∈ quasiLocalStateSpace d ∧ ∀ (a : ℤ) (N : ℕ), 0 < N →
        φ (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1 := by
  constructor
  · exact fun hφ => ⟨hφ.1, fun a N hN =>
      quasiLocalState_groundSpaceProjection_eq_one_of_eventual_symmetric_support
        A φ hφ.1
        (eventually_quasiLocalState_symmetric_groundSpaceProjection_eq_one_of_eventual_kernel
          A h hR hh hker φ hφ.1 hφ.2) a N hN⟩
  · rintro ⟨hφ, hSupport⟩
    refine ⟨hφ, fun a => ?_⟩
    obtain ⟨N, hkerN, hRN⟩ := (hker.and (eventually_ge_atTop R)).exists
    have hHP : openInteractionMatrix h N * groundSpaceProjectionMatrix A N = 0 := by
      apply EquivLike.injective (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ))
      simp only [map_mul, map_zero, groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply]
      refine ContinuousLinearMap.ext fun v => ?_
      change Matrix.toEuclideanLin (openInteractionMatrix h N)
        ((groundSpaceES A N).starProjection v) = 0
      rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix h hR hRN]
      exact LinearMap.mem_ker.mp
        (hkerN.symm ▸ (groundSpaceES A N).starProjection_apply_mem v)
    let f := intervalStateFunctional φ hφ.2.2 a N
    have hf : f (groundSpaceProjectionMatrix A N) = f 1 := by
      simpa only [f, intervalStateFunctional_apply, map_one, hφ.2.1] using
        hSupport a N (lt_of_lt_of_le hR hRN)
    have hcomp := f.apply_projection_compression_eq (groundSpaceProjectionMatrix A N)
      (openInteractionMatrix h N)
      (isStarProjection_groundSpaceProjectionMatrix A N).isSelfAdjoint.star_eq
      (isStarProjection_groundSpaceProjectionMatrix A N).isIdempotentElem hf
    have hzero : φ (quasiLocalIntervalObservable d a N (openInteractionMatrix h N)) = 0 := by
      simpa only [Matrix.mul_assoc, hHP, Matrix.mul_zero, map_zero,
        f, intervalStateFunctional_apply] using hcomp.symm
    rw [quasiLocalIntervalObservable_openInteractionMatrix a h hR N, map_sum] at hzero
    have hnonneg (i : ℕ) :
        0 ≤ φ (quasiLocalIntervalObservable d (a + (i : ℤ)) R h) :=
      (intervalStateFunctional φ hφ.2.2 (a + (i : ℤ)) R).map_nonneg hh.nonneg
    simpa only [Nat.cast_zero, add_zero] using
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero
        0 (Finset.mem_range.mpr (by omega))

end MPSTensor

