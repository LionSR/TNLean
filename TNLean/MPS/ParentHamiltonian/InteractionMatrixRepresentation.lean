/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction
import TNLean.MPS.Symmetry.GappedInteractionPath

/-!
# Matrix coordinates for general periodic interactions

The periodic sum of an arbitrary local operator in Euclidean coordinates agrees
with the sum of its embedded configuration-basis matrices. No positivity or
projection hypothesis is needed. This extends the canonical-parent identities
to the continuously extended local interactions of arXiv:2203.12563, Section 5.
-/

open scoped BigOperators Matrix

namespace MPSTensor

variable {d R N : ℕ}

private theorem cyclicActiveBlockConfigEquiv_fst_eq_extractWindow
    (hRN : R ≤ N) (i : Fin N) (σ : Cfg d N) :
    (cyclicActiveBlockConfigEquiv d R hRN i σ).1 = extractWindow R i σ := by
  let e := cyclicActiveBlockConfigEquiv d R hRN i
  funext r
  have h := cyclicActiveBlockConfigEquiv_symm_apply_window hRN i
    (e σ).1 (e σ).2 r
  simpa only [Prod.mk.eta, e, Equiv.symm_apply_apply, extractWindow,
    cyclicForwardSite] using h.symm

private theorem cyclicActiveBlockConfigEquiv_symm_eq_replaceWindow
    (hRN : R ≤ N) (i : Fin N) (σ : Cfg d N) (τ : Cfg d R) :
    (cyclicActiveBlockConfigEquiv d R hRN i).symm
        (τ, (cyclicActiveBlockConfigEquiv d R hRN i σ).2) =
      replaceWindow R hRN i σ τ := by
  let e := cyclicActiveBlockConfigEquiv d R hRN i
  funext k
  obtain ⟨x, rfl⟩ := (cyclicWindowIndexEquiv R N hRN i).surjective k
  rcases x with r | r
  · rw [cyclicWindowIndexEquiv_inl]
    change e.symm (τ, (e σ).2) (cyclicForwardSite i r.val) = _
    rw [cyclicActiveBlockConfigEquiv_symm_apply_window]
    exact (congrFun (extractWindow_replaceWindow R hRN i σ τ) r).symm
  · rw [cyclicWindowIndexEquiv_inr]
    have hsite : (⟨(i.val + R + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ : Fin N) =
        cyclicForwardSite i (R + r.val) := by
      apply Fin.ext
      simp only [cyclicForwardSite, Nat.add_assoc]
    rw [hsite]
    rw [cyclicActiveBlockConfigEquiv_symm_apply_spectator]
    have hs := cyclicActiveBlockConfigEquiv_symm_apply_spectator hRN i
      (e σ).1 (e σ).2 r
    have hs' : (e σ).2 r = σ (cyclicForwardSite i (R + r.val)) := by
      simpa only [Prod.mk.eta, e, Equiv.symm_apply_apply] using hs.symm
    rw [hs']
    have hoff : (((i.val + (R + r.val)) % N + N - i.val) % N) = R + r.val :=
      offset_mod_eq i.isLt (by omega)
    simp only [replaceWindow, cyclicForwardSite, Fin.val_mk, hoff,
      show ¬ R + r.val < R from by omega, dite_false]

/-- An arbitrary Euclidean local interaction has the same cyclic extension
as its configuration-basis matrix. This is the local coordinate identity for
the Hamiltonian convention of arXiv:2203.12563, Section 5. -/
theorem periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator
    (h : MPOTensor.ChainOperator d R) (hRN : R ≤ N) (i : Fin N) :
    periodicLocalInteractionES (Matrix.toEuclideanLin h) i =
      Matrix.toEuclideanLin (MPOTensor.embedLocalOperator R N hRN i h) := by
  classical
  let e := cyclicActiveBlockConfigEquiv d R hRN i
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro σ
  unfold periodicLocalInteractionES
  rw [dite_eq_left hRN]
  change (U.symm (ContinuousLinearMap.rightFiberwiseMap
    (S := Cfg d (N - R)) (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin h))
    (U v))) σ = (MPOTensor.embedLocalOperator R N hRN i h).mulVec v.ofLp σ
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply,
    MPOTensor.embedLocalOperator_mulVec_apply]
  change (∑ τ : Cfg d R, h (e σ).1 τ * U v (τ, (e σ).2)) =
    ∑ τ : Cfg d R, h (extractWindow R i σ) τ *
      v (replaceWindow R hRN i σ τ)
  rw [cyclicActiveBlockConfigEquiv_fst_eq_extractWindow]
  apply Finset.sum_congr rfl
  intro τ _
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply,
    cyclicActiveBlockConfigEquiv_symm_eq_replaceWindow]

/-- The full Euclidean periodic sum agrees with the sum of embedded local
matrices, for every interaction range that fits in the chain. -/
theorem periodicInteractionHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator
    (h : MPOTensor.ChainOperator d R) (hRN : R ≤ N) :
    periodicInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      Matrix.toEuclideanLin
        (∑ i : Fin N, MPOTensor.embedLocalOperator R N hRN i h) := by
  rw [periodicInteractionHamiltonianES, map_sum]
  simp_rw [periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator h hRN]

/-- The Euclidean periodic Hamiltonian of a two-site matrix is the matrix
Hamiltonian used for physical isometric gap transport. -/
theorem periodicInteractionHamiltonianES_eq_toEuclideanLin_interactionHamiltonian
    (h : MPOTensor.ChainOperator d 2) (hN : 2 ≤ N) :
    periodicInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      Matrix.toEuclideanLin (interactionHamiltonian h hN) :=
  periodicInteractionHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator h hN

end MPSTensor
