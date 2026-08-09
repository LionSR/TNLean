/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrobeniusHilbert
import TNLean.Algebra.RectangularChoi
import TNLean.Analysis.InjectiveRangeProjector
import TNLean.MPS.ParentHamiltonian.BlockStrip
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.Spectral.MixedTransfer

import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Gram operators for MPS ground-space maps

This file realizes the boundary map \(\Gamma_L\) between finite-dimensional
Hilbert spaces and identifies its Gram operator with the exact reshuffling of
the Choi matrix of the iterated transfer map.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

section FrobeniusRealization

open scoped Matrix.Norms.Frobenius

/-- The boundary map \(\Gamma_L\), with the virtual matrix space carrying the
Hilbert--Schmidt inner product and the physical configuration space carrying
the standard \(\ell^2\) inner product. -/
noncomputable def groundSpaceMapES (A : MPSTensor d D) (L : ℕ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toLinearMap.comp
      ((groundSpaceMap A L).comp
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm.toLinearEquiv.toLinearMap)

@[simp]
theorem groundSpaceMapES_frobeniusEquivEuclidean_apply
    (A : MPSTensor d D) (L : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    groundSpaceMapES A L (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm (groundSpaceMap A L X) := by
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
      (groundSpaceMap A L
        ((Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X))) = _
  rw [(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]

/-- The Hilbert-space realization has exactly the physical local ground space
as its range. -/
theorem range_groundSpaceMapES (A : MPSTensor d D) (L : ℕ) :
    (groundSpaceMapES A L).range = groundSpaceES A L := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨X, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
      (groundSpaceMap A L X) ∈ groundSpaceES A L
    exact ⟨groundSpaceMap A L X, ⟨X, rfl⟩, rfl⟩
  · rintro ⟨ψ, ⟨X, rfl⟩, rfl⟩
    exact ⟨Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X,
      groundSpaceMapES_frobeniusEquivEuclidean_apply A L X⟩

/-- Block injectivity at length \(L\) makes the Hilbert-space boundary map
\(\Gamma_L^{\mathrm{ES}}\) injective. -/
theorem groundSpaceMapES_injective_of_isNBlkInjective {A : MPSTensor d D} {L : ℕ}
    (hInj : IsNBlkInjective A L) :
    Function.Injective (groundSpaceMapES A L) := by
  intro x y hxy
  obtain ⟨X, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective y
  apply congrArg (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D))
  apply groundSpaceMap_injective_of_isNBlkInjective hInj
  apply (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.injective
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply] at hxy
  exact hxy

/-- If \(A\) is block-injective at a positive length \(L₀\), then its
Hilbert-space boundary map is injective at every length \(L \ge L₀\). -/
theorem groundSpaceMapES_injective_of_isNBlkInjective_of_le
    {A : MPSTensor d D} {L₀ L : ℕ} (hL₀ : 0 < L₀)
    (hInj : IsNBlkInjective A L₀) (hL : L₀ ≤ L) :
    Function.Injective (groundSpaceMapES A L) :=
  groundSpaceMapES_injective_of_isNBlkInjective
    (isNBlkInjective_of_le hL₀ hInj hL)

/-- If \(A\) is block-injective at length \(L\), the inverse-Gram range
projector of \(\Gamma_L^{\mathrm{ES}}\) is the orthogonal projector onto the
physical local ground space. This is the physical range projector, not the
virtual transfer fixed-point projector `fixedPointProj`; it does not assert an
overlapping-window estimate. -/
theorem injectiveRangeProjector_groundSpaceMapES_eq_starProjection
    (A : MPSTensor d D) (L : ℕ) (hInj : IsNBlkInjective A L) :
    ContinuousLinearMap.injectiveRangeProjector (groundSpaceMapES A L)
      (groundSpaceMapES_injective_of_isNBlkInjective hInj) =
        (groundSpaceES A L).starProjection := by
  rw [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection]
  exact congrArg (fun K : Submodule ℂ (EuclideanSpace ℂ (Cfg d L)) => K.starProjection)
    (range_groundSpaceMapES A L)

/-- If \(L₀ > 0\), \(A\) is \(L₀\)-block injective, and \(L \ge L₀\), then
\[
  P_{G_L^{\mathrm{ES}}(A)} = \Gamma_L^{\mathrm{ES}}
    ((\Gamma_L^{\mathrm{ES}})^\dagger \Gamma_L^{\mathrm{ES}})^{-1}
    (\Gamma_L^{\mathrm{ES}})^\dagger.
\]
Here the inverse is `ContinuousLinearMap.inverseGram`. This is the physical
range projector, not the virtual `fixedPointProj`; it does not assert an
overlapping-window estimate. -/
theorem groundSpaceES_starProjection_eq_groundSpaceMapES_comp_inverseGram_comp_adjoint
    (A : MPSTensor d D) {L₀ L : ℕ} (hL₀ : 0 < L₀)
    (hInj : IsNBlkInjective A L₀) (hL : L₀ ≤ L) :
    (groundSpaceES A L).starProjection =
      (groundSpaceMapES A L).comp
        ((ContinuousLinearMap.inverseGram (groundSpaceMapES A L)
          (groundSpaceMapES_injective_of_isNBlkInjective_of_le hL₀ hInj hL)).comp
            (groundSpaceMapES A L).adjoint) := by
  exact (injectiveRangeProjector_groundSpaceMapES_eq_starProjection A L
    (isNBlkInjective_of_le hL₀ hInj hL)).symm

@[simp]
theorem groundSpaceMapES_single (A : MPSTensor d D) (L : ℕ) (a b : Fin D) :
    groundSpaceMapES A L (EuclideanSpace.single (b, a) 1) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
        (groundSpaceMap A L (Matrix.single a b 1)) := by
  rw [← groundSpaceMapES_frobeniusEquivEuclidean_apply A L (Matrix.single a b 1)]
  apply congrArg (groundSpaceMapES A L)
  apply PiLp.ext
  rintro ⟨j, i⟩
  simp [Matrix.frobeniusEquivEuclidean_apply, EuclideanSpace.single]

end FrobeniusRealization

/-- The finite-dimensional Gram operator \(\Gamma_L^\dagger\Gamma_L\). -/
noncomputable def groundSpaceGram (A : MPSTensor d D) (L : ℕ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  (groundSpaceMapES A L).adjoint.comp (groundSpaceMapES A L)

/-- Matrix-unit entry of the MPS Gram operator.  The right-hand side is the
precise Choi reshuffling: it is not the Hilbert--Schmidt pairing with the
iterated transfer map. -/
theorem inner_single_groundSpaceGram_single_eq_rectangularChoi
    (A : MPSTensor d D) (L : ℕ) (a b c e : Fin D) :
    inner ℂ (EuclideanSpace.single (b, a) 1)
      (groundSpaceGram A L (EuclideanSpace.single (e, c) 1)) =
      Matrix.rectangularChoi ((transferMap (d := d) (D := D) A) ^ L)
        (c, e) (a, b) := by
  classical
  rw [groundSpaceGram, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [groundSpaceMapES_single, groundSpaceMapES_single]
  change inner ℂ
    (WithLp.toLp 2 (groundSpaceMap A L (Matrix.single a b 1)))
    (WithLp.toLp 2 (groundSpaceMap A L (Matrix.single c e 1))) = _
  rw [EuclideanSpace.inner_toLp_toLp, Matrix.rectangularChoi_apply,
    transferMap_pow_apply']
  have hmul (W : Matrix (Fin D) (Fin D) ℂ) :
      ((W * Matrix.single c a 1 * Wᴴ : Matrix (Fin D) (Fin D) ℂ) e b) =
        W e c * star (W b a) := by
    rw [Matrix.mul_apply]
    calc
      ∑ j, ((W * Matrix.single c a 1 : Matrix (Fin D) (Fin D) ℂ) e j) * Wᴴ j b =
          ((W * Matrix.single c a 1 : Matrix (Fin D) (Fin D) ℂ) e a) * Wᴴ a b := by
        apply Finset.sum_eq_single a
        · intro j _ hja
          rw [Matrix.mul_apply]
          simp [hja.symm]
        · simp
      _ = W e c * star (W b a) := by
        rw [Matrix.mul_apply]
        simp [Matrix.single_apply]
  rw [show (∑ σ : Fin L → Fin d,
      evalWord A (List.ofFn σ) * Matrix.single c a 1 *
        (evalWord A (List.ofFn σ))ᴴ) =
      ∑ σ ∈ (Finset.univ : Finset (Fin L → Fin d)),
        evalWord A (List.ofFn σ) * Matrix.single c a 1 *
          (evalWord A (List.ofFn σ))ᴴ by rfl, Matrix.sum_apply]
  simp_rw [hmul]
  simp [groundSpaceMap_apply, Matrix.trace_mul_single, dotProduct]

end MPSTensor
