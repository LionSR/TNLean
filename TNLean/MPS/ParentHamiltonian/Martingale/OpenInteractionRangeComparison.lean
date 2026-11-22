/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction

/-!
# Coordinate form of an extended local interaction on the ring

An extended local interaction acts on its window with all outside coordinates fixed, and its
conjugation by the cyclic block reindexing is the corresponding local interaction of the active
block. These are the coordinate forms of the finite-range extension by the identity in
Nachtergaele, arXiv:cond-mat/9410110, equation (3.12).

The finite-window comparison of the open-chain Hamiltonians of a positive local matrix and the
transfer of a gap along it are `hamiltonian_chainTranslates_comparison_of_local` and
`toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length`.

**Transitional (#10948).** Both declarations are stated for the Euclidean-space operator
`periodicLocalInteractionES` and are kept until its last users are converted.
-/
open scoped BigOperators ComplexOrder
namespace MPSTensor
variable {d D : ℕ}
/-- An extended local interaction acts on the restricted window, with all
outside coordinates fixed. This is the coordinate form of finite-range
extension by the identity in Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem periodicLocalInteractionES_apply {R N : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hR : 0 < R) (hRN : R ≤ N) (i : Fin N)
    (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    periodicLocalInteractionES h i v σ =
      h (cyclicRestrictES (Fin.pos i) R i σ v) (extractWindow R i σ) := by
  unfold periodicLocalInteractionES
  rw [dite_eq_left hRN]
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply]
  change ((cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i).symm
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
      (LinearMap.toContinuousLinearMap h)
      (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v))) σ = _
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply]
  change h (ContinuousLinearMap.rightFiber
    (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v)
    ((cyclicActiveBlockConfigEquiv d R hRN i) σ).2) (extractWindow R i σ) = _
  apply congrArg (fun w : EuclideanSpace ℂ (Cfg d R) => h w (extractWindow R i σ))
  ext ω
  change v ((cyclicActiveBlockConfigEquiv d R hRN i).symm
      (ω, ((cyclicActiveBlockConfigEquiv d R hRN i) σ).2)) =
    v (cyclicCfg (Fin.pos i) R i ω σ)
  have hfull (ξ : Cfg d R) : cyclicCfg hR R (⟨0, hR⟩ : Fin R) ω ξ = ω := by
    funext j
    simp [cyclicCfg, Nat.mod_eq_of_lt j.isLt]
  have hj := cyclicCfg_join_cyclicActiveBlock hRN i (⟨0, hR⟩ : Fin R)
    (by simp) ω ((cyclicActiveBlockConfigEquiv d R hRN i) σ).1
      ((cyclicActiveBlockConfigEquiv d R hRN i) σ).2
  simp only [cyclicForwardSite_zero, hfull, Prod.mk.eta,
    Equiv.symm_apply_apply] at hj
  exact congrArg v hj.symm

/-- A local interaction inside an active interval acts independently on each
spectator configuration. Source: Nachtergaele, arXiv:cond-mat/9410110,
equation (3.12). -/
theorem periodicLocalInteractionES_conj_cyclicActiveBlock
    {N W R : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hR : 0 < R) (hWN : W ≤ N) (s : Fin N) (q : Fin W) (hqR : q.val + R ≤ W) :
    (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).toLinearEquiv.toLinearMap.comp
      ((periodicLocalInteractionES h (cyclicForwardSite s q.val)).comp
        (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (periodicLocalInteractionES h q))).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  simp only [LinearMap.comp_apply]
  change periodicLocalInteractionES h (cyclicForwardSite s q.val)
      ((cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x)
        ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)) =
    periodicLocalInteractionES h q (ContinuousLinearMap.rightFiber x τ) σ
  rw [periodicLocalInteractionES_apply h hR (by omega),
    periodicLocalInteractionES_apply h hR (by omega)]
  have hrestrict :
      cyclicRestrictES (d := d) (Fin.pos (cyclicForwardSite s q.val)) R
          (cyclicForwardSite s q.val)
          ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ))
          ((cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x) =
        cyclicRestrictES (d := d) (Fin.pos q) R q σ
          (ContinuousLinearMap.rightFiber x τ) := by
    apply PiLp.ext
    intro ω
    change (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x
        (cyclicCfg (Fin.pos (cyclicForwardSite s q.val)) R
          (cyclicForwardSite s q.val) ω
          ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ))) =
      x (cyclicCfg (Fin.pos q) R q ω σ, τ)
    rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply,
      cyclicCfg_join_cyclicActiveBlock hWN s q hqR]
    simp
  rw [hrestrict, extractWindow_join_cyclicActiveBlock hWN s q hqR σ τ]
end MPSTensor
