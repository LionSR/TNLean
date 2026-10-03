/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.PeriodicBoundaryReduction
import TNLean.MPS.ParentHamiltonian.Nonvanishing
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteRangeKnabeGap
import TNLean.Algebra.CompactKernelGap

/-!
# Continuity of short periodic parent-Hamiltonian ground lines

For an injective one-site tensor and every periodic chain of length at least
two, the ground space is the line spanned by its nonzero matrix product
vector. The line projection varies continuously with the tensor. This
controls the finitely many lengths below a large-chain uniform gap threshold.
-/

namespace MPSTensor

open scoped Topology

/-- The periodic MPS vector, viewed in the Euclidean configuration Hilbert
space, varies continuously with a continuous tensor family. -/
theorem continuous_mpvES_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (N : ℕ) :
    Continuous fun x =>
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv (A x)) := by
  let e := EuclideanSpace.equiv (Cfg d N) ℂ
  apply e.symm.continuous.comp
  apply continuous_pi
  intro σ
  have hTrace := (continuous_evalWord_family A hA (List.ofFn σ)).matrix_trace
  convert hTrace using 1
  ext x
  rfl

/-- The MPS vector is the range of the scalar-to-state map. -/
noncomputable def periodicMpvLineMap {d D : ℕ} (A : MPSTensor d D) (N : ℕ) :
    ℂ →L[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  (1 : ℂ →L[ℂ] ℂ).smulRight
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A))

/-- The scalar-to-state map varies continuously with the tensor. -/
theorem continuous_periodicMpvLineMap_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (N : ℕ) :
    Continuous fun x => periodicMpvLineMap (A x) N := by
  exact (ContinuousLinearMap.smulRightL ℂ ℂ (EuclideanSpace ℂ (Cfg d N))
    (1 : ℂ →L[ℂ] ℂ)).continuous.comp (continuous_mpvES_family A hA N)

/-- One-site injectivity makes the scalar-to-state map injective at every
periodic length at least two. -/
theorem periodicMpvLineMap_injective_of_isInjective
    {d D N : ℕ} [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsInjective A) (hN : 2 ≤ N) :
    Function.Injective (periodicMpvLineMap A N) := by
  have hψ : (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A) ≠ 0 := by
    intro hzero
    have h := congrArg (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)) hzero
    have hmpv : (mpv A : NSiteSpace d N) ≠ 0 :=
      mpv_ne_zero_of_isNBlkInjective
        (Kraus.isNBlkInjective_one_of_isInjective hA) (by norm_num : 0 < 1)
        (by omega : 1 + 1 ≤ N)
    exact hmpv (by simpa using h)
  intro c c' hcc
  have hsmul : (c - c') •
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A) = 0 := by
    simpa [periodicMpvLineMap, sub_smul] using congrArg (fun v => v - periodicMpvLineMap A N c') hcc
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hψ)

/-- The kernel of the two-site periodic parent Hamiltonian is precisely the
range of the scalar-to-state map when the tensor is one-site injective and
the chain has at least two sites. -/
theorem ker_parentHamiltonianES_two_eq_range_periodicMpvLineMap
    {d D N : ℕ} [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsInjective A) (hN : 2 ≤ N) :
    LinearMap.ker (parentHamiltonianES A 2 N) =
      (periodicMpvLineMap A N).range := by
  rw [← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace A (by omega : 0 < N)
      (by omega : 2 ≤ N),
    chainGroundSpace_eq_mpvSubmodule hA hN (by norm_num : 1 < 2)
      (by omega : 2 ≤ N)]
  simp only [mpvSubmodule, periodicMpvLineMap]
  rw [Submodule.map_span]
  simp only [Set.image_singleton]
  change (ℂ ∙ ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A))) = _
  exact
    (ContinuousLinearMap.range_smulRight_apply
      (by norm_num : (1 : ℂ →L[ℂ] ℂ) ≠ 0)
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A))).symm

/-- At every fixed periodic length at least two, the orthogonal projector
onto the parent-Hamiltonian kernel is continuous along a continuous family
of one-site injective tensors. -/
theorem continuous_parentHamiltonianES_two_kernelProjection_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) {N : ℕ} (hN : 2 ≤ N) :
    Continuous fun x =>
      (LinearMap.ker (parentHamiltonianES (A x) 2 N)).starProjection := by
  have hT := continuous_periodicMpvLineMap_family A hA N
  have hTinj (x : X) : Function.Injective (periodicMpvLineMap (A x) N) :=
    periodicMpvLineMap_injective_of_isInjective (A x) (hInj x) hN
  have hProj := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun x => periodicMpvLineMap (A x) N) hT hTinj
  have heq :
      (fun x => ContinuousLinearMap.injectiveRangeProjector
        (periodicMpvLineMap (A x) N) (hTinj x)) =
      (fun x => (LinearMap.ker (parentHamiltonianES (A x) 2 N)).starProjection) := by
    funext x
    rw [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection]
    exact congrArg
      (fun K : Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) => K.starProjection)
      (ker_parentHamiltonianES_two_eq_range_periodicMpvLineMap
        (A x) (hInj x) hN).symm
  rw [← heq]
  exact hProj

/-- For each fixed periodic length at least two, a continuous compact family
of one-site injective tensors has one positive parent-Hamiltonian gap bound.
The bound may depend on the length. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_parentHamiltonianES_two_gap_fixed_volume
    {X : Type*} [TopologicalSpace X] {d D : ℕ} [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ x, Kraus.IsInjective (A x)) {S : Set X} (hS : IsCompact S)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) 2 N v‖ := by
  have hBlock (x : X) : Kraus.IsNBlkInjective (A x) 2 :=
    isNBlkInjective_of_le (by omega : 0 < 1)
      (Kraus.isNBlkInjective_one_of_isInjective (hInj x))
      (by omega : 1 ≤ 2)
  have hH := continuous_parentHamiltonianES_family A hA hN hBlock
  have hK := continuous_parentHamiltonianES_two_kernelProjection_family A hA hInj hN
  exact ContinuousLinearMap.exists_uniform_norm_gap_of_compact
    (fun x => LinearMap.toContinuousLinearMap (parentHamiltonianES (A x) 2 N))
    hH hK hS

end MPSTensor
