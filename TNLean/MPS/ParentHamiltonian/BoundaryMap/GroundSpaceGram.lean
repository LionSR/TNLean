/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Norm.FrobeniusHilbert
import QICLean.Channel.Choi.RectangularChoi
import QICLean.Analysis.Projection.InjectiveRangeProjector
import QICLean.Kraus.Transfer
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonian
import TNLean.MPS.Tensor.GroundSpace.IntersectionProperty
import TNLean.MPS.Tensor.Words.WordSpan
import QICLean.Kraus.MixedMap.Basic

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

/-- The operator form of the boundary map `groundSpaceMap A L`, used for the Hilbert-space
statements: \(\Gamma_L\) transported along the Frobenius identification of the virtual matrix
space with \(\ell^2(D \times D)\) and the identification of the physical configuration space
with \(\ell^2\). Its facts that are not about the Hilbert structure (adjoint, Gram operator,
range, inverse-Gram projection) are those of `groundSpaceMap A L`, read through
`groundSpaceMapES_frobeniusEquivEuclidean_apply`. -/
noncomputable def groundSpaceMapES (A : MPSTensor d D) (L : ℕ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toLinearMap.comp
      ((groundSpaceMap A L).comp
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm.toLinearEquiv.toLinearMap)

/-- The Frobenius identification sends the matrix unit `Matrix.single a b 1` to the basis vector
at `(b, a)`. -/
theorem _root_.Matrix.frobeniusEquivEuclidean_single (a b : Fin D) :
    Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (Matrix.single a b 1) =
      EuclideanSpace.single (b, a) (1 : ℂ) := by
  apply PiLp.ext
  rintro ⟨j, i⟩
  simp [Matrix.frobeniusEquivEuclidean_apply, EuclideanSpace.single]

/-- **The unfolding of `groundSpaceMapES`**: on the Frobenius image of a matrix it is the
boundary map `groundSpaceMap`. -/
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
    (groundSpaceMapES A L).range = ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap) := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨X, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
      (groundSpaceMap A L X) ∈ ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
    exact ⟨groundSpaceMap A L X, ⟨X, rfl⟩, rfl⟩
  · rintro ⟨ψ, ⟨X, rfl⟩, rfl⟩
    exact ⟨Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X,
      groundSpaceMapES_frobeniusEquivEuclidean_apply A L X⟩

/-- If \(A\) is block-injective at length \(L\), the inverse-Gram range
projector of \(\Gamma_L^{\mathrm{ES}}\) is the orthogonal projector onto the
physical local ground space. This is the physical range projector, not the
virtual transfer fixed-point projector `fixedPointProj`; it does not assert an
overlapping-window estimate. -/
theorem injectiveRangeProjector_groundSpaceMapES_eq_starProjection
    (A : MPSTensor d D) (L : ℕ) (hInj : Kraus.IsNBlkInjective A L) :
    ContinuousLinearMap.injectiveRangeProjector (groundSpaceMapES A L)
      (show Function.Injective (groundSpaceMapES A L) from
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.injective.comp
          ((groundSpaceMap_injective_of_isNBlkInjective hInj).comp
            (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm.injective)) =
        ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection := by
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
theorem map_groundSpace_starProjection_eq_groundSpaceMapES_comp_inverseGram_comp_adjoint
    (A : MPSTensor d D) {L₀ L : ℕ} (hL₀ : 0 < L₀)
    (hInj : Kraus.IsNBlkInjective A L₀) (hL : L₀ ≤ L) :
    ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection =
      (groundSpaceMapES A L).comp
        ((ContinuousLinearMap.inverseGram (groundSpaceMapES A L)
          (show Function.Injective (groundSpaceMapES A L) from
            (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.injective.comp
              ((groundSpaceMap_injective_of_isNBlkInjective
                (Kraus.isNBlkInjective_of_le hL₀ hInj hL)).comp
                  (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm.injective))).comp
            (groundSpaceMapES A L).adjoint) := by
  exact (injectiveRangeProjector_groundSpaceMapES_eq_starProjection A L
    (Kraus.isNBlkInjective_of_le hL₀ hInj hL)).symm

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
      Matrix.rectangularChoi ((Kraus.transferMap (ι := Fin d) (n := Fin D) A) ^ L)
        (c, e) (a, b) := by
  classical
  rw [groundSpaceGram, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [← Matrix.frobeniusEquivEuclidean_single, ← Matrix.frobeniusEquivEuclidean_single,
    groundSpaceMapES_frobeniusEquivEuclidean_apply, groundSpaceMapES_frobeniusEquivEuclidean_apply]
  change inner ℂ
    (WithLp.toLp 2 (groundSpaceMap A L (Matrix.single a b 1)))
    (WithLp.toLp 2 (groundSpaceMap A L (Matrix.single c e 1))) = _
  rw [EuclideanSpace.inner_toLp_toLp, Matrix.rectangularChoi_apply,
    Kraus.mapLM_pow_apply]
  have hmul (W : Matrix (Fin D) (Fin D) ℂ) :
      ((W * Matrix.single c a 1 * Wᴴ : Matrix (Fin D) (Fin D) ℂ) e b) =
        W e c * star (W b a) := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [show (∑ σ : Fin L → Fin d,
      Kraus.evalWord A (List.ofFn σ) * Matrix.single c a 1 *
        (Kraus.evalWord A (List.ofFn σ))ᴴ) =
      ∑ σ ∈ (Finset.univ : Finset (Fin L → Fin d)),
        Kraus.evalWord A (List.ofFn σ) * Matrix.single c a 1 *
          (Kraus.evalWord A (List.ofFn σ))ᴴ by rfl, Matrix.sum_apply]
  simp_rw [hmul]
  simp [groundSpaceMap_apply, Matrix.trace_mul_single, dotProduct]

/-- The Gram operator of \(\Gamma_L\) equals the reshuffling of the Choi matrix
of the \(L\)-fold transfer map. -/
theorem groundSpaceGram_eq_gramReshuffle (A : MPSTensor d D) (L : ℕ) :
    groundSpaceGram A L = Matrix.gramReshuffle ((Kraus.transferMap A) ^ L) := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin D × Fin D) ℂ).toBasis.ext fun ⟨e, c⟩ => ?_
  apply PiLp.ext
  rintro ⟨b, a⟩
  have h := (inner_single_groundSpaceGram_single_eq_rectangularChoi A L a b c e).trans
    (Matrix.inner_single_gramReshuffle_single ((Kraus.transferMap A) ^ L) a b c e).symm
  simpa [PiLp.inner_apply] using h

end MPSTensor
