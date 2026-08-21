/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.Spectrum
import Mathlib.Analysis.Matrix.Normed

/-!
# Anti-linear conjugation and spectrum

Entrywise complex conjugation `σ X = X.map (starRingEnd ℂ)` is an anti-linear
involution of the matrix space. Conjugating a matrix endomorphism `Φ` by `σ`
produces the linear endomorphism `σ ∘ Φ ∘ σ`, and this transport conjugates all
spectral data: the spectrum, the eigenvalues, and the peripheral eigenvalues of
`σ ∘ Φ ∘ σ` are the complex conjugates of those of `Φ`, while the spectral
radius and peripheral-spectrum primitivity are invariant.

These statements transport the spectral clauses of the normal-tensor definition
of arXiv:1606.00608, lines 231--235, across entrywise conjugation of the tensor,
since entrywise conjugation of a tensor conjugates its transfer map
anti-linearly.

## Main definitions

* `entrywiseConjTransport`: the transport `Φ ↦ σ ∘ Φ ∘ σ` of a matrix
  endomorphism along entrywise conjugation.
* `entrywiseConjTransportRingEquiv`: the same transport as a ring automorphism
  of the endomorphism ring.

## Main results

* `spectrum_entrywiseConjTransport`: the spectrum of `σ ∘ Φ ∘ σ` is the complex
  conjugate of the spectrum of `Φ`.
* `hasEigenvalue_entrywiseConjTransport_iff`: eigenvalues conjugate accordingly.
* `peripheralEigenvalues_entrywiseConjTransport`: the peripheral eigenvalues of
  `σ ∘ Φ ∘ σ` are the complex conjugates of those of `Φ`.
* `spectralRadius_entrywiseConjTransport`: the spectral radius is invariant.
* `IsPrimitive.entrywiseConjTransport_iff`: primitivity is invariant.
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal Matrix.Norms.Operator

variable {D : ℕ}

namespace Matrix

/-- Entrywise conjugation of a matrix is an involution. -/
@[simp] theorem map_starRingEnd_map_starRingEnd {m n : Type*} (X : Matrix m n ℂ) :
    (X.map (starRingEnd ℂ)).map (starRingEnd ℂ) = X := by
  ext i j
  simp [Matrix.map_apply]

/-- Entrywise conjugation of a matrix is an involution, composed-function form. -/
@[simp] theorem map_starRingEnd_comp_starRingEnd {m n : Type*} (X : Matrix m n ℂ) :
    X.map (⇑(starRingEnd ℂ) ∘ ⇑(starRingEnd ℂ)) = X := by
  ext i j
  simp [Matrix.map_apply]

/-- Entrywise conjugation is anti-linear: it conjugates scalars. -/
theorem map_smul_starRingEnd {m n : Type*} (c : ℂ) (X : Matrix m n ℂ) :
    (c • X).map (starRingEnd ℂ) = star c • X.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.map_apply]

end Matrix

/-- Transport of a matrix endomorphism along entrywise complex conjugation:
`Φ ↦ σ ∘ Φ ∘ σ`, where `σ X = X.map (starRingEnd ℂ)` is the anti-linear
involution given by entrywise conjugation. Both anti-linear factors conjugate
the scalars, so the composite is again linear.

This is the anti-linear conjugacy through which entrywise conjugation of a
tensor acts on its transfer map (arXiv:1606.00608, lines 219--225). -/
noncomputable def entrywiseConjTransport
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun X := (Φ (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)
  map_add' X Y := by
    rw [Matrix.map_add (starRingEnd ℂ) (map_add (starRingEnd ℂ)) X Y, map_add,
      Matrix.map_add (starRingEnd ℂ) (map_add (starRingEnd ℂ))]
  map_smul' c X := by
    rw [Matrix.map_smul_starRingEnd, map_smul, Matrix.map_smul_starRingEnd, star_star]
    rfl

@[simp] theorem entrywiseConjTransport_apply
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    entrywiseConjTransport Φ X = (Φ (X.map (starRingEnd ℂ))).map (starRingEnd ℂ) := rfl

/-- Transport along entrywise conjugation is an involution on endomorphisms. -/
@[simp] theorem entrywiseConjTransport_entrywiseConjTransport
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    entrywiseConjTransport (entrywiseConjTransport Φ) = Φ := by
  apply LinearMap.ext
  intro X
  simp

/-- Transport along entrywise conjugation is multiplicative for composition. -/
theorem entrywiseConjTransport_mul
    (Φ Ψ : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) :
    entrywiseConjTransport (Φ * Ψ) =
      entrywiseConjTransport Φ * entrywiseConjTransport Ψ := by
  apply LinearMap.ext
  intro X
  simp [Module.End.mul_apply]

/-- Transport along entrywise conjugation sends the scalar `μ` to `conj μ`. -/
theorem entrywiseConjTransport_algebraMap (μ : ℂ) :
    entrywiseConjTransport
        (algebraMap ℂ (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) μ) =
      algebraMap ℂ (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (star μ) := by
  apply LinearMap.ext
  intro X
  rw [entrywiseConjTransport_apply, Module.algebraMap_end_apply,
    Module.algebraMap_end_apply, Matrix.map_smul_starRingEnd,
    Matrix.map_starRingEnd_map_starRingEnd]

/-- Transport along entrywise conjugation as a ring automorphism of the
endomorphism ring of the matrix space. On scalars it acts by complex
conjugation (`entrywiseConjTransport_algebraMap`), so it is a ring
automorphism but not an algebra automorphism. -/
noncomputable def entrywiseConjTransportRingEquiv (D : ℕ) :
    Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) ≃+*
      Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) where
  toFun := entrywiseConjTransport
  invFun := entrywiseConjTransport
  left_inv := entrywiseConjTransport_entrywiseConjTransport
  right_inv := entrywiseConjTransport_entrywiseConjTransport
  map_mul' := entrywiseConjTransport_mul
  map_add' Φ Ψ := by
    apply LinearMap.ext
    intro X
    simp [Matrix.map_add (starRingEnd ℂ) (map_add (starRingEnd ℂ))]

/-- The spectrum of the anti-linear conjugate `σ ∘ Φ ∘ σ` is the complex
conjugate of the spectrum of `Φ`.

This is the spectral half of the anti-linear conjugacy used to transport the
normalization of arXiv:1606.00608, lines 224--225, across entrywise
conjugation. -/
theorem spectrum_entrywiseConjTransport
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    spectrum ℂ (entrywiseConjTransport Φ) = star '' spectrum ℂ Φ := by
  have key : ∀ μ : ℂ,
      μ ∈ spectrum ℂ (entrywiseConjTransport Φ) ↔ star μ ∈ spectrum ℂ Φ := by
    intro μ
    rw [spectrum.mem_iff, spectrum.mem_iff]
    have hmap :
        (entrywiseConjTransportRingEquiv D)
            (algebraMap ℂ (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (star μ) - Φ) =
          algebraMap ℂ (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) μ -
            entrywiseConjTransport Φ := by
      rw [map_sub]
      congr 1
      rw [show ((entrywiseConjTransportRingEquiv D)
          (algebraMap ℂ (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (star μ))) =
        entrywiseConjTransport
          (algebraMap ℂ (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (star μ)) from rfl,
        entrywiseConjTransport_algebraMap, star_star]
    rw [← hmap]
    exact not_congr (MulEquiv.isUnit_map (entrywiseConjTransportRingEquiv D))
  ext μ
  rw [Set.mem_image, key μ]
  constructor
  · intro h
    exact ⟨star μ, h, star_star μ⟩
  · rintro ⟨ν, hν, rfl⟩
    simpa [star_star] using hν

/-- Eigenvalues of the anti-linear conjugate `σ ∘ Φ ∘ σ` are the complex
conjugates of the eigenvalues of `Φ`: an eigenvector transports to its
entrywise conjugate. Supports the transport of clause (ii) of the
normal-tensor definition, arXiv:1606.00608, lines 233--235. -/
theorem hasEigenvalue_entrywiseConjTransport_iff
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (μ : ℂ) :
    Module.End.HasEigenvalue (entrywiseConjTransport Φ) μ ↔
      Module.End.HasEigenvalue Φ (star μ) := by
  have forward :
      ∀ (Ψ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (ν : ℂ),
        Module.End.HasEigenvalue (entrywiseConjTransport Ψ) ν →
          Module.End.HasEigenvalue Ψ (star ν) := by
    intro Ψ ν h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    apply hasEigenvalue_of_eigenvector_eq Ψ (star ν) (v.map (starRingEnd ℂ))
    · have happ := congrArg (fun M => M.map (starRingEnd ℂ)) hv.apply_eq_smul
      simpa [Matrix.map_smul_starRingEnd] using happ
    · intro h0
      apply hv.2
      have := congrArg (fun M => M.map (starRingEnd ℂ)) h0
      simpa using this
  constructor
  · exact forward Φ μ
  · intro h
    have h' : Module.End.HasEigenvalue
        (entrywiseConjTransport (entrywiseConjTransport Φ)) (star μ) := by
      rw [entrywiseConjTransport_entrywiseConjTransport]
      exact h
    simpa [star_star] using forward (entrywiseConjTransport Φ) (star μ) h'

/-- The peripheral eigenvalues of the anti-linear conjugate `σ ∘ Φ ∘ σ` are the
complex conjugates of the peripheral eigenvalues of `Φ`. Supports the transport
of clause (ii) of the normal-tensor definition, arXiv:1606.00608, lines
233--235. -/
theorem peripheralEigenvalues_entrywiseConjTransport
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    peripheralEigenvalues (entrywiseConjTransport Φ) =
      star '' peripheralEigenvalues Φ := by
  ext μ
  simp only [peripheralEigenvalues, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hEig, hNorm⟩
    exact ⟨star μ, ⟨(hasEigenvalue_entrywiseConjTransport_iff Φ μ).1 hEig,
      by simpa only [norm_star] using hNorm⟩, star_star μ⟩
  · rintro ⟨ν, ⟨hEig, hNorm⟩, rfl⟩
    refine ⟨(hasEigenvalue_entrywiseConjTransport_iff Φ (star ν)).2 ?_,
      by simpa only [norm_star] using hNorm⟩
    simpa [star_star] using hEig

/-- Peripheral-spectrum primitivity is invariant under anti-linear conjugation
by entrywise conjugation: the peripheral eigenvalues conjugate, and `{1}` is
fixed by conjugation. Supports the transport of clause (ii) of the
normal-tensor definition, arXiv:1606.00608, lines 233--235. -/
theorem IsPrimitive.entrywiseConjTransport_iff
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    _root_.IsPrimitive (entrywiseConjTransport Φ) ↔ _root_.IsPrimitive Φ := by
  rw [isPrimitive_iff, isPrimitive_iff, peripheralEigenvalues_entrywiseConjTransport]
  constructor
  · intro h
    have := congrArg (star '' ·) h
    simpa [Set.image_image] using this
  · intro h
    simp [h]

/-- The spectral radius is invariant under anti-linear conjugation by entrywise
conjugation, since the spectrum conjugates and conjugation preserves the
modulus. This transports the spectral-radius-one normalization of
arXiv:1606.00608, lines 224--225 and 233--235, across entrywise conjugation. -/
theorem spectralRadius_entrywiseConjTransport
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (entrywiseConjTransport Φ)) =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) Φ) := by
  have hspec :
      spectrum ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (entrywiseConjTransport Φ)) =
        star ''
          spectrum ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) Φ) := by
    rw [AlgEquiv.spectrum_eq, AlgEquiv.spectrum_eq, spectrum_entrywiseConjTransport]
  rw [spectralRadius, spectralRadius, hspec, iSup_image]
  simp only [nnnorm_star]
