/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.PrimitiveQuasiLocalUniqueness
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalOpenInteractionExpectation
import TNLean.MPS.ParentHamiltonian.BulkObservable.PrimitiveLocalParentInteractionGap
import TNLean.MPS.ParentHamiltonian.Gap.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalParentGroundStateFace
import TNLean.MPS.ParentHamiltonian.Blocking.BlockedQuasiLocalSupport
import QICLean.Analysis.Order.PosSemidefCommute

/-!
# Local zero energy implies finite-interval ground-space support

A finite positive Hamiltonian dominates a positive multiple of the projection
onto the complement of its kernel. A normalized positive functional vanishing
on the Hamiltonian therefore assigns expectation one to its kernel projection.
For a weighted multiblock tensor at simultaneous injectivity, the open-chain
kernel is the joint MPS space. Vanishing expectations on every translated
parent term imply support in that space on every sufficiently large interval.
Translation invariance of the state and a uniform spectral gap are unnecessary.
A further theorem uses the source's eventual finite-volume kernel identity
directly, without a local parent-kernel hypothesis or an injectivity bound on
the interaction range.

**Scope restriction (sufficient interaction range):** The simultaneous-word-span
consequences assume a positive simultaneous injectivity length \(S\) and range
at least \(S+1\). See
docs/paper-gaps/cpgsv21_block_parent_interaction_range.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
equation (3.12), and the finite-interval support discussion in Section 3.

It also contains the following results.

* `MPSTensor.quasiLocalState_groundSpaceProjection_eq_one_of_eventual_symmetric_support`,
  `MPSTensor.mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel`: zero local
  energy and support in every finite MPS interval.
-/

open MPTensor

section QuasiLocalGroundStateSupport

open scoped ComplexOrder
open ManyBody.Interaction (chainTranslates)

open SpinChain
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
namespace MPSTensor
variable {d D : ℕ} [NeZero d]
/-- Zero expectation of a finite positive Hamiltonian with prescribed MPS
kernel gives expectation one on the MPS support projection. No uniform gap is
required. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3. -/
theorem quasiLocalState_groundSpaceProjection_eq_one_of_interval_eq_zero
    (A : MPSTensor d D) (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d) (a : ℤ) {N : ℕ}
    (H : Matrix (Cfg d N) (Cfg d N) ℂ) (hH : H.PosSemidef)
    (hker : LinearMap.ker (Matrix.toEuclideanLin H) = ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap))
    (hzero : φ (quasiLocalIntervalObservable d a N H) = 0) :
    φ (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1 := by
  obtain ⟨κ, hκ, hLower⟩ :=
    (Matrix.isPositive_toEuclideanLin_iff.mpr hH).exists_pos_smul_orthogonal_ker_projection_le
  rw [hker] at hLower
  have hLowerMatrix : (κ : ℂ) • (1 - groundSpaceProjectionMatrix A N) ≤ H := by
    rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff]
    simpa only [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, map_sub, map_smul,
      map_one, groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply,
      Submodule.starProjection_orthogonal, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_one, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.coe_id, Module.End.one_eq_id]
      using LinearMap.le_def.mp hLower
  refine PositiveLinearMap.apply_projection_eq_one_of_le_of_apply_eq_zero
    (intervalStateFunctional φ hφ.2.2 a N) (groundSpaceProjectionMatrix A N) H
    (isStarProjection_groundSpaceProjectionMatrix A N) ?_ hzero hκ hLowerMatrix
  simpa only [intervalStateFunctional_apply, map_one] using hφ.2.1

/-- A state with zero expectation on every translated parent term is supported
in the joint MPS space of each interval of length at least the interaction range.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1 and equation (3.12);
CPGSV21, arXiv:2011.12127, lines 2114--2129. -/
theorem quasiLocalState_groundSpaceProjection_eq_one_of_isParentInteraction_wordTupleSpanTop
    {b : ℕ} {dim : Fin b → ℕ} [∀ i, NeZero (dim i)]
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (dim i)) (hμ : ∀ i, μ i ≠ 0)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0)
    (a : ℤ) {N : ℕ} (hN : R ≤ N) :
    φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix (toTensorFromBlocks (α := Fin d) (μ := μ) A) N)) = 1 := by
  refine quasiLocalState_groundSpaceProjection_eq_one_of_interval_eq_zero
    (toTensorFromBlocks (α := Fin d) (μ := μ) A) φ hφ a
      ((chainTranslates R N h).hamiltonian) ?_ ?_ ?_
  · exact ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates
      (Matrix.isPositive_toEuclideanLin_iff.mp hh.isPositive) N
  · rw [hh.ker_hamiltonian_chainTranslates_eq_ker_parentChainInteraction]
    exact ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_of_wordTupleSpanTop
      μ A hμ hS hSpan hR hN
  · exact apply_quasiLocalIntervalObservable_hamiltonian_chainTranslates_eq_zero
      φ.toLinearMap h hzero a N

/-- Local zero energy gives eventual joint MPS support on the symmetric
intervals with endpoints tending to both infinities. No invariance is assumed.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1 and Section 3. -/
theorem eventually_quasiLocalState_symmetric_groundSpaceProjection_eq_one
    {b : ℕ} {dim : Fin b → ℕ} [∀ i, NeZero (dim i)]
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (dim i)) (hμ : ∀ i, μ i ≠ 0)
    {S R : ℕ} (hS : 0 < S) (hSpan : WordTupleSpanTop A S) (hR : S + 1 ≤ R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hh : IsParentInteraction (toTensorFromBlocks (α := Fin d) (μ := μ) A) R
      (Matrix.toEuclideanLin h))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
        (groundSpaceProjectionMatrix (toTensorFromBlocks (α := Fin d) (μ := μ) A)
          (2 * n + 1))) = 1 := by
  filter_upwards [Filter.eventually_ge_atTop R] with n hn
  exact quasiLocalState_groundSpaceProjection_eq_one_of_isParentInteraction_wordTupleSpanTop
    μ A hμ hS hSpan hR h hh φ hφ hzero (-(n : ℤ)) (by omega)
/-- The source's eventual finite-volume kernel hypothesis gives joint support
on expanding symmetric intervals for every locally zero-energy state. This
requires no parent-kernel condition at the interaction range and no simultaneous
injectivity bound on that range. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, and Section 3. -/
theorem eventually_quasiLocalState_symmetric_groundSpaceProjection_eq_one_of_eventual_kernel
    (A : MPSTensor d D) {R : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d)
    (hzero : ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      φ (quasiLocalIntervalObservable d (-(n : ℤ)) (2 * n + 1)
        (groundSpaceProjectionMatrix A (2 * n + 1))) = 1 := by
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => by dsimp only [id]; omega) Filter.tendsto_id
  filter_upwards [hlim.eventually hker] with n hkerN
  exact quasiLocalState_groundSpaceProjection_eq_one_of_interval_eq_zero
    A φ hφ (-(n : ℤ)) ((chainTranslates R (2 * n + 1) h).hamiltonian)
    (ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates hh _) hkerN
    (apply_quasiLocalIntervalObservable_hamiltonian_chainTranslates_eq_zero
      φ.toLinearMap h hzero (-(n : ℤ)) (2 * n + 1))

end MPSTensor

end QuasiLocalGroundStateSupport

section EventualKernelGroundStateSupport

/-!
## Zero local energy and support in every finite MPS interval

Suppose the open-chain Hamiltonian of a positive interaction of positive range has
the prescribed open MPS space as its kernel on every sufficiently long chain. A normalized positive
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
open ManyBody.Interaction (chainTranslates)

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
    A φ hφ (-(n : ℤ)) hcontained hn
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
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    φ ∈ parentGroundStateFace h ↔
      φ ∈ quasiLocalStateSpace d ∧ ∀ (a : ℤ) (N : ℕ), 0 < N →
        φ (quasiLocalIntervalObservable d a N (groundSpaceProjectionMatrix A N)) = 1 := by
  constructor
  · exact fun hφ => ⟨hφ.1, fun a N hN =>
      quasiLocalState_groundSpaceProjection_eq_one_of_eventual_symmetric_support
        A φ hφ.1
        (eventually_quasiLocalState_symmetric_groundSpaceProjection_eq_one_of_eventual_kernel
          A h hh hker φ hφ.1 hφ.2) a N hN⟩
  · rintro ⟨hφ, hSupport⟩
    refine ⟨hφ, fun a => ?_⟩
    obtain ⟨N, hkerN, hRN⟩ := (hker.and (eventually_ge_atTop R)).exists
    have hHP : (chainTranslates R N h).hamiltonian * groundSpaceProjectionMatrix A N = 0 := by
      apply EquivLike.injective (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ))
      simp only [map_mul, map_zero, groundSpaceProjectionMatrix, StarAlgEquiv.apply_symm_apply]
      refine ContinuousLinearMap.ext fun v => ?_
      change Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian)
        (((groundSpace A N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection v) = 0
      exact LinearMap.mem_ker.mp
        (hkerN.symm ▸ ((groundSpace A N).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap).starProjection_apply_mem v)
    let f := intervalStateFunctional φ hφ.2.2 a N
    have hf : f (groundSpaceProjectionMatrix A N) = f 1 := by
      simpa only [f, intervalStateFunctional_apply, map_one, hφ.2.1] using
        hSupport a N (lt_of_lt_of_le hR hRN)
    have hcomp := f.apply_projection_compression_eq (groundSpaceProjectionMatrix A N)
      ((chainTranslates R N h).hamiltonian)
      (isStarProjection_groundSpaceProjectionMatrix A N).isSelfAdjoint.star_eq
      (isStarProjection_groundSpaceProjectionMatrix A N).isIdempotentElem hf
    have hzero :
        φ (quasiLocalIntervalObservable d a N ((chainTranslates R N h).hamiltonian)) = 0 := by
      simpa only [Matrix.mul_assoc, hHP, Matrix.mul_zero, map_zero,
        f, intervalStateFunctional_apply] using hcomp.symm
    rw [quasiLocalIntervalObservable_hamiltonian_chainTranslates a h N, map_sum] at hzero
    have hnonneg (i : ℕ) :
        0 ≤ φ (quasiLocalIntervalObservable d (a + (i : ℤ)) R h) :=
      (intervalStateFunctional φ hφ.2.2 (a + (i : ℤ)) R).map_nonneg hh.nonneg
    simpa only [Nat.cast_zero, add_zero] using
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero
        0 (Finset.mem_range.mpr (by omega))

end MPSTensor

end EventualKernelGroundStateSupport
