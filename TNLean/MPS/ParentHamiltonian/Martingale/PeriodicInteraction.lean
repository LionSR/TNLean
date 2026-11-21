/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicRangeComparison

/-!
# Periodic sums of a fixed local interaction

A local operator is extended by the identity on the remaining sites and
translated around the periodic chain. This construction preserves positivity
and order, and agrees with the canonical parent Hamiltonian when the local
operator is the complementary ground-space projection. Interactions longer
than the chain give zero, matching the existing parent-Hamiltonian convention.

These are the local-to-global comparisons for positive parent interactions
in CPGSV21, arXiv:2011.12127, Section IV.C, lines 1995--2007 and 2183--2187.

**Transitional (#10948).** The declarations about `periodicLocalInteractionES` and
`periodicInteractionHamiltonianES` are kept until their last users are converted; those whose
statements lack `R ≤ N` are converted once QICLean has a ring interaction defined for every
range. The last section states the facts for the terms of
`ManyBody.Interaction.translationInvariant`.
-/

open scoped BigOperators ComplexOrder

namespace MPSTensor

variable {d R N : ℕ}

/-- Translate a fixed range-\(R\) interaction to the cyclic window starting at
\(i\), extending it by the identity on the complementary physical sites. -/
noncomputable def periodicLocalInteractionES
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (i : Fin N) : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  if hRN : R ≤ N then
    (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i).symm.toLinearEquiv.conj
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
        (LinearMap.toContinuousLinearMap h)).toLinearMap
  else 0

/-- Cyclic active-block coordinates expose the actual translated interaction
as its right-spectator extension. Source: PGVWC07, arXiv:quant-ph/0608197,
Theorem 11 proof, lines 1418–1422. -/
theorem cyclicActiveBlock_periodicLocalInteractionES_apply
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) (ψ : EuclideanSpace ℂ (Cfg d N)) :
    cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
        (periodicLocalInteractionES h i ψ) =
      ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
        (LinearMap.toContinuousLinearMap h)
        (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i ψ) := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  let G := ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
    (LinearMap.toContinuousLinearMap h)
  rw [periodicLocalInteractionES, dite_eq_left hRN]
  change U (U.symm (G (U ψ))) = G (U ψ)
  exact U.apply_symm_apply _

/-- Sum the cyclic translates of one fixed local interaction. -/
noncomputable def periodicInteractionHamiltonianES
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (N : ℕ) : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i : Fin N, periodicLocalInteractionES h i

/-- Cyclic extension preserves local operator inequalities. -/
theorem periodicLocalInteractionES_mono
    {h k : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hle : h ≤ k) (i : Fin N) :
    periodicLocalInteractionES h i ≤ periodicLocalInteractionES k i := by
  unfold periodicLocalInteractionES
  split_ifs with hRN
  · exact ((cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i).symm.conj_le_conj_iff
      _ _).mpr (ContinuousLinearMap.rightFiberwiseMap_mono hle)
  · exact le_rfl

/-- Extending the canonical local projection gives the existing translated
parent-Hamiltonian term. -/
theorem periodicLocalInteractionES_parentInteractionES
    {D : ℕ} (A : MPSTensor d D) (hR : 0 < R) (i : Fin N) :
    periodicLocalInteractionES (parentInteractionES A R) i = localTermES A R i := by
  by_cases hRN : R ≤ N
  · let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
    have hConj : U.toLinearEquiv.conj (localTermES A R i) =
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
          (LinearMap.toContinuousLinearMap (parentInteractionES A R))).toLinearMap := by
      simpa only [U, Fin.val_mk, cyclicForwardSite_zero,
        localTermES_self_zero_eq_parentInteractionES A hR,
        LinearEquiv.conj_apply, LinearMap.comp_assoc] using!
        (localTermES_conj_cyclicActiveBlockConfigLinearIsometryEquiv A
          (R := R) hRN i ⟨0, hR⟩ (by simp))
    unfold periodicLocalInteractionES
    rw [dite_eq_left hRN]
    change U.toLinearEquiv.symm.conj _ = _
    apply U.toLinearEquiv.conj.injective
    rw [LinearEquiv.conj_conj_symm]
    exact hConj.symm
  · simp [periodicLocalInteractionES, localTermES, localTerm, hRN]

/-- Cyclic extension commutes with scalar multiplication. -/
theorem periodicLocalInteractionES_smul (c : ℂ)
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (i : Fin N) :
    periodicLocalInteractionES (c • h) i = c • periodicLocalInteractionES h i := by
  unfold periodicLocalInteractionES
  split_ifs with hRN
  · simp only [map_smul, ContinuousLinearMap.rightFiberwiseMap_smul,
      ContinuousLinearMap.toLinearMap_smul]
  · simp

/-- Extending the zero local interaction gives zero. -/
@[simp] theorem periodicLocalInteractionES_zero (i : Fin N) :
    periodicLocalInteractionES
      (0 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) i = 0 := by
  simp [periodicLocalInteractionES]

/-- Extension to a cyclic window preserves positivity. -/
theorem periodicLocalInteractionES_isPositive
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : h.IsPositive) (i : Fin N) :
    (periodicLocalInteractionES h i).IsPositive := by
  apply LinearMap.nonneg_iff_isPositive.mp
  simpa only [periodicLocalInteractionES_zero] using
    periodicLocalInteractionES_mono (LinearMap.nonneg_iff_isPositive.mpr hh) i

/-- A zero local interaction gives a zero periodic Hamiltonian. -/
@[simp] theorem periodicInteractionHamiltonianES_zero (N : ℕ) :
    periodicInteractionHamiltonianES
      (0 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) N = 0 := by
  simp [periodicInteractionHamiltonianES, periodicLocalInteractionES]

/-- Summing cyclic translates preserves operator inequalities. -/
theorem periodicInteractionHamiltonianES_mono
    {h k : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hle : h ≤ k) (N : ℕ) :
    periodicInteractionHamiltonianES h N ≤ periodicInteractionHamiltonianES k N :=
  Finset.sum_le_sum fun i _ ↦ periodicLocalInteractionES_mono hle i

/-- The periodic sum depends linearly on a scalar multiple of the local interaction. -/
theorem periodicInteractionHamiltonianES_smul (c : ℂ)
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) (N : ℕ) :
    periodicInteractionHamiltonianES (c • h) N = c • periodicInteractionHamiltonianES h N := by
  simp only [periodicInteractionHamiltonianES, periodicLocalInteractionES_smul, Finset.smul_sum]

/-- A fixed positive local interaction gives a positive periodic Hamiltonian. -/
theorem periodicInteractionHamiltonianES_isPositive
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : h.IsPositive) (N : ℕ) :
    (periodicInteractionHamiltonianES h N).IsPositive := by
  apply LinearMap.nonneg_iff_isPositive.mp
  simpa only [periodicInteractionHamiltonianES_zero] using
    periodicInteractionHamiltonianES_mono (LinearMap.nonneg_iff_isPositive.mpr hh) N

/-- The periodic sum of the canonical parent projection is the canonical
parent Hamiltonian at every volume. -/
theorem periodicInteractionHamiltonianES_parentInteractionES
    {D : ℕ} (A : MPSTensor d D) (hR : 0 < R) (N : ℕ) :
    periodicInteractionHamiltonianES (parentInteractionES A R) N =
      parentHamiltonianES A R N := by
  simp only [periodicInteractionHamiltonianES,
    periodicLocalInteractionES_parentInteractionES A hR, parentHamiltonianES_eq_sum_localTermES]

/-! ### Translates of a local matrix on the ring

The same facts for the terms of the translation-invariant interaction of a local matrix `h`
(`ManyBody.Interaction.translationInvariant`), for `R ≤ N`. The statements about
`periodicLocalInteractionES` and `periodicInteractionHamiltonianES` without `R ≤ N` wait for the
total ring interaction of QICLean. -/

/-- A term of the translates of `h` on the ring acts at a configuration \(σ\) as `h` on the
cyclic restriction to its window, read at the window of \(σ\). -/
theorem toEuclideanLin_translationInvariant_term_apply {R N : ℕ} (hRN : R ≤ N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N))
    (σ : Cfg d N) :
    Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant hRN h).term i) v σ =
      Matrix.toEuclideanLin h (cyclicRestrictES (Fin.pos i) R i σ v) (extractWindow R i σ) := by
  rw [ManyBody.Interaction.translates_term, Matrix.toLpLin_apply, Matrix.toLpLin_apply]
  change Matrix.mulVec (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.ringWindow hRN i) h)
    (WithLp.ofLp v) σ = Matrix.mulVec h _ _
  rw [ManyBody.placeAlong_mulVec_apply_of _ _ _ σ (replaceWindow R hRN i σ)
    (replaceWindow_ringWindow hRN i σ)
    (fun τ _ hv ↦ replaceWindow_of_forall_ringWindow_ne hRN i σ τ hv)]
  rfl

/-- In the cyclic active-block coordinates of its window, a term of the translates of `h` on the
ring is `h` on the active block, acting independently on every spectator configuration. Source:
PGVWC07, arXiv:quant-ph/0608197, Theorem 11 proof, lines 1418–1422. -/
theorem cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply {R N : ℕ}
    (hRN : R ≤ N) (h : Matrix (Cfg d R) (Cfg d R) ℂ) (i : Fin N)
    (ψ : EuclideanSpace ℂ (Cfg d N)) :
    cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
        (Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant hRN h).term i) ψ) =
      ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin h))
        (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i ψ) := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  let e := cyclicActiveBlockConfigEquiv d R hRN i
  apply U.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  ext σ
  rw [toEuclideanLin_translationInvariant_term_apply,
    cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply]
  change Matrix.toEuclideanLin h _ (extractWindow R i σ) =
    Matrix.toEuclideanLin h (ContinuousLinearMap.rightFiber (U ψ) (e σ).2) (extractWindow R i σ)
  apply congrArg
    (fun w : EuclideanSpace ℂ (Cfg d R) => Matrix.toEuclideanLin h w (extractWindow R i σ))
  ext ω
  change ψ (cyclicCfg (Fin.pos i) R i ω σ) = ψ (e.symm (ω, (e σ).2))
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · have hω : ω = (e σ).1 := Subsingleton.elim _ _
    rw [hω, Prod.mk.eta, Equiv.symm_apply_apply]
    exact congrArg ψ (funext fun k ↦ by simp [cyclicCfg])
  · have hfull (ξ : Cfg d R) : cyclicCfg hR R (⟨0, hR⟩ : Fin R) ω ξ = ω := by
      funext j
      simp [cyclicCfg, Nat.mod_eq_of_lt j.isLt]
    have hj := cyclicCfg_join_cyclicActiveBlock hRN i (⟨0, hR⟩ : Fin R)
      (by simp) ω (e σ).1 (e σ).2
    simp only [cyclicForwardSite_zero, hfull, Prod.mk.eta] at hj
    rw [Equiv.symm_apply_apply] at hj
    exact congrArg ψ hj

end MPSTensor
