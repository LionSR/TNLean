/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixOperatorSpace
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.UnitalKraus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Adjoint spectra of Kraus maps

Eigenvalues of the adjoint of a linear map on a finite-dimensional complex
inner product space are the complex conjugates of the eigenvalues of the map.
For a finite Kraus map with the Frobenius inner product, the adjoint is the
Kraus map of the conjugate-transposed family, so the peripheral spectrum of the
conjugate-transposed family is the star-image of the peripheral spectrum.
Combining this with the operator-norm contraction bound for unital Kraus maps
gives the spectral-radius bound for trace-preserving Kraus maps.

## Main statements

* `Matrix.charpoly_conjTranspose`: the characteristic polynomial of the
  conjugate transpose is the coefficient-wise complex conjugate.
* `Module.End.hasEigenvalue_adjoint_iff`: eigenvalues of the adjoint are
  complex conjugates.
* `IsPrimitive.adjoint_iff`: peripheral-spectrum primitivity is invariant
  under adjoint.
* `Kraus.mapLM_conjTranspose_eq_adjoint`: the Frobenius adjoint of a finite
  Kraus map is the Kraus map of the conjugate-transposed family.
* `Kraus.peripheralEigenvalues_mapLM_conjTranspose`: the peripheral spectrum of
  the conjugate-transposed family is the star-image of the peripheral spectrum.
* `Kraus.eigenvalue_norm_le_one_of_isTP`,
  `Kraus.spectralRadius_mapLM_le_one_of_isTP`: eigenvalue and spectral-radius
  bounds for trace-preserving Kraus maps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1 and
  Section 6.2][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal ENNReal TNOperatorSpace
open Matrix Finset Complex

section AdjointEigenvalues

open scoped ComplexConjugate

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The characteristic polynomial of the conjugate transpose is the coefficient-wise complex
conjugate of the characteristic polynomial.

We phrase this using `Polynomial.map` along `starRingEnd ℂ` (complex conjugation on coefficients).
-/
lemma charpoly_conjTranspose (M : Matrix n n ℂ) :
    (Mᴴ).charpoly = M.charpoly.map (starRingEnd ℂ) := by
  classical
  -- `Mᴴ` is the transpose of `M` with conjugated entries.
  have h : Mᴴ = (M.map (starRingEnd ℂ))ᵀ := by
    ext i j
    change star (M j i) = starRingEnd ℂ (M j i)
    simp only [starRingEnd_apply]
  calc
    (Mᴴ).charpoly = ((M.map (starRingEnd ℂ))ᵀ).charpoly := by
      simp only [h]
    _ = (M.map (starRingEnd ℂ)).charpoly :=
      Matrix.charpoly_transpose (M := M.map (starRingEnd ℂ))
    _ = M.charpoly.map (starRingEnd ℂ) :=
      Matrix.charpoly_map (M := M) (f := starRingEnd ℂ)

end Matrix

section LinearMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- Eigenvalues of the adjoint are complex conjugates.

This is proved via characteristic polynomials, using an orthonormal basis and the fact that the
matrix of the adjoint is the conjugate transpose of the matrix.
-/
theorem Module.End.hasEigenvalue_adjoint_iff (E : V →ₗ[ℂ] V) (μ : ℂ) :
    Module.End.HasEigenvalue E μ ↔ Module.End.HasEigenvalue E.adjoint (star μ) := by
  classical
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly (f := E) (μ := μ),
    Module.End.hasEigenvalue_iff_isRoot_charpoly (f := E.adjoint) (μ := star μ)]
  let v : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V :=
    stdOrthonormalBasis ℂ V
  have hE : (LinearMap.toMatrix v.toBasis v.toBasis E).charpoly = E.charpoly := by
    simpa only using (LinearMap.charpoly_toMatrix (f := E) v.toBasis)
  have hEadj :
      (LinearMap.toMatrix v.toBasis v.toBasis E.adjoint).charpoly = E.adjoint.charpoly := by
    simpa only using (LinearMap.charpoly_toMatrix (f := E.adjoint) v.toBasis)
  have hMatAdj :
      LinearMap.toMatrix v.toBasis v.toBasis E.adjoint =
        (LinearMap.toMatrix v.toBasis v.toBasis E)ᴴ := by
    simpa only using (LinearMap.toMatrix_adjoint (v₁ := v) (v₂ := v) (f := E))
  have hchar : E.adjoint.charpoly = E.charpoly.map (starRingEnd ℂ) := by
    calc
      E.adjoint.charpoly
          = (LinearMap.toMatrix v.toBasis v.toBasis E.adjoint).charpoly :=
              hEadj.symm
      _ = ((LinearMap.toMatrix v.toBasis v.toBasis E)ᴴ).charpoly := by
            rw [hMatAdj]
      _ = (LinearMap.toMatrix v.toBasis v.toBasis E).charpoly.map (starRingEnd ℂ) :=
            Matrix.charpoly_conjTranspose (M := LinearMap.toMatrix v.toBasis v.toBasis E)
      _ = E.charpoly.map (starRingEnd ℂ) := by
            rw [hE]
  simp [hchar]

/-- Peripheral-spectrum primitivity is invariant under adjoint. -/
theorem IsPrimitive.adjoint_iff (E : V →ₗ[ℂ] V) :
    _root_.IsPrimitive E.adjoint ↔ _root_.IsPrimitive E := by
  classical
  rw [isPrimitive_iff, isPrimitive_iff]
  constructor
  · intro hAdj
    ext μ
    constructor
    · rintro ⟨hEig, hNorm⟩
      have hEigAdj : Module.End.HasEigenvalue E.adjoint (star μ) :=
        (Module.End.hasEigenvalue_adjoint_iff (E := E) (μ := μ)).1 hEig
      have hNormAdj : ‖star μ‖ = 1 := by
        simpa only [RCLike.star_def, RCLike.norm_conj] using hNorm
      have hMemAdj : star μ ∈ peripheralEigenvalues E.adjoint :=
        ⟨hEigAdj, hNormAdj⟩
      have hStarEq : star μ = 1 := by
        have : star μ ∈ ({1} : Set ℂ) := by
          simpa only [RCLike.star_def, Set.mem_singleton_iff, hAdj] using hMemAdj
        simpa only [RCLike.star_def, Set.mem_singleton_iff] using this
      have hμEq : μ = 1 := by
        have := congrArg star hStarEq
        simpa only [RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply, star_one]
          using this
      simp [hμEq]
    · intro hμ
      have hμEq : μ = 1 := by simpa only [Set.mem_singleton_iff] using hμ
      subst hμEq
      have honeAdj : (1 : ℂ) ∈ peripheralEigenvalues E.adjoint := by
        simp [hAdj]
      rcases honeAdj with ⟨hEigAdj, _hnormAdj⟩
      have hEig : Module.End.HasEigenvalue E (1 : ℂ) :=
        (Module.End.hasEigenvalue_adjoint_iff (E := E) (μ := (1 : ℂ))).2
          (by
            simpa only [star_one, zero_lt_one,
              Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one] using hEigAdj)
      exact ⟨hEig, by simp⟩
  · intro h
    ext μ
    constructor
    · rintro ⟨hEigAdj, hNormAdj⟩
      have hEig : Module.End.HasEigenvalue E (star μ) := by
        have hback := (Module.End.hasEigenvalue_adjoint_iff (E := E) (μ := star μ)).2
        exact hback
          (by
            simpa only [RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply,
              zero_lt_one, Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one] using hEigAdj)
      have hNorm : ‖star μ‖ = 1 := by
        simpa only [RCLike.star_def, RCLike.norm_conj] using hNormAdj
      have hMem : star μ ∈ peripheralEigenvalues E :=
        ⟨hEig, hNorm⟩
      have hStarEq : star μ = 1 := by
        have : star μ ∈ ({1} : Set ℂ) := by
          simpa only [RCLike.star_def, Set.mem_singleton_iff, h] using hMem
        simpa only [RCLike.star_def, Set.mem_singleton_iff] using this
      have hμEq : μ = 1 := by
        have := congrArg star hStarEq
        simpa only [RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply, star_one]
          using this
      simp [hμEq]
    · intro hμ
      have hμEq : μ = 1 := by simpa only [Set.mem_singleton_iff] using hμ
      subst hμEq
      have hone : (1 : ℂ) ∈ peripheralEigenvalues E := by
        simp [h]
      rcases hone with ⟨hEig, _hnorm⟩
      have hEigAdj : Module.End.HasEigenvalue E.adjoint (star (1 : ℂ)) :=
        (Module.End.hasEigenvalue_adjoint_iff (E := E) (μ := (1 : ℂ))).1 hEig
      have : Module.End.HasEigenvalue E.adjoint (1 : ℂ) := by
        simpa only [zero_lt_one, Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one,
          star_one] using hEigAdj
      exact ⟨this, by simp⟩

end LinearMap

end AdjointEigenvalues

/-!
## Frobenius adjoint of a Kraus map

We equip `Matrix (Fin D) (Fin D) ℂ` with the Frobenius inner product coming from
`Matrix.toMatrixInnerProductSpace` with weight matrix `1`. With this choice, the
adjoint of `Kraus.mapLM K` is the Kraus map of the conjugate-transposed family
`i ↦ (K i)ᴴ`.
-/

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

noncomputable section

-- Frobenius norm / inner product from the weight matrix `1`.
local instance : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1
    (Matrix.PosDef.one (n := Fin D) (R := ℂ))

local instance : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1
    (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef

/-- The adjoint of `mapLM K` (Frobenius inner product) is the Kraus map of the
conjugate-transposed family. -/
lemma mapLM_conjTranspose_eq_adjoint (K : Fin d → Mat) :
    mapLM (fun i => (K i)ᴴ) = (mapLM K).adjoint := by
  classical
  refine (LinearMap.eq_adjoint_iff (A := mapLM fun i => (K i)ᴴ)
      (B := mapLM K)).2 ?_
  intro X Y
  change Matrix.trace (Y * (1 : Mat) * (mapLM (fun i => (K i)ᴴ) X)ᴴ) =
    Matrix.trace (mapLM K Y * (1 : Mat) * Xᴴ)
  simp only [mul_one]
  have hconj : (mapLM (fun i => (K i)ᴴ) X)ᴴ = mapLM (fun i => (K i)ᴴ) (Xᴴ) := by
    simpa only [mapLM_apply] using (map_conjTranspose (K := fun i => (K i)ᴴ) X)
  have htrace :
      Matrix.trace (Y * mapLM (fun i => (K i)ᴴ) (Xᴴ)) =
        Matrix.trace (adjointMap (fun i => (K i)ᴴ) Y * Xᴴ) := by
    simpa only [mapLM_apply] using
      (trace_mul_map_eq_trace_adjointMap_mul (K := fun i => (K i)ᴴ) Y (Xᴴ))
  have hadj : adjointMap (fun i => (K i)ᴴ) Y = mapLM K Y := by
    simp [adjointMap, mapLM_apply, map, Matrix.conjTranspose_conjTranspose]
  calc
    Matrix.trace (Y * (mapLM (fun i => (K i)ᴴ) X)ᴴ)
        = Matrix.trace (Y * mapLM (fun i => (K i)ᴴ) (Xᴴ)) := by
          simpa only using congrArg (fun Z => Matrix.trace (Y * Z)) hconj
    _ = Matrix.trace (adjointMap (fun i => (K i)ᴴ) Y * Xᴴ) := htrace
    _ = Matrix.trace (mapLM K Y * Xᴴ) := by rw [hadj]

/-- Eigenvalues of the conjugate-transposed Kraus family are the complex conjugates
of the eigenvalues of the original family. -/
theorem hasEigenvalue_mapLM_conjTranspose_iff (K : Fin d → Mat) (μ : ℂ) :
    Module.End.HasEigenvalue (mapLM fun i => (K i)ᴴ) μ ↔
      Module.End.HasEigenvalue (mapLM K) (star μ) := by
  rw [mapLM_conjTranspose_eq_adjoint]
  constructor
  · intro h
    have := (Module.End.hasEigenvalue_adjoint_iff (E := mapLM K) (μ := star μ)).2
    simpa using this (by simpa using h)
  · intro h
    have := (Module.End.hasEigenvalue_adjoint_iff (E := mapLM K) (μ := star μ)).1 h
    simpa using this

/-- The peripheral spectrum of the conjugate-transposed Kraus family is the
star-image of the peripheral spectrum of the original family. -/
theorem peripheralEigenvalues_mapLM_conjTranspose (K : Fin d → Mat) :
    peripheralEigenvalues (mapLM fun i => (K i)ᴴ) =
      star '' peripheralEigenvalues (mapLM K) := by
  ext μ
  constructor
  · rintro ⟨hEig, hNorm⟩
    refine ⟨star μ, ⟨?_, ?_⟩, by simp⟩
    · exact (hasEigenvalue_mapLM_conjTranspose_iff K μ).1 hEig
    · simpa only [RCLike.star_def, RCLike.norm_conj] using hNorm
  · rintro ⟨ν, ⟨hEig, hNorm⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (hasEigenvalue_mapLM_conjTranspose_iff K (star ν)).2 (by simpa using hEig)
    · simpa only [RCLike.star_def, RCLike.norm_conj] using hNorm

end

/-!
## Spectral-radius bound for trace-preserving Kraus maps

A trace-preserving finite Kraus map has all eigenvalues in the closed unit
disk: its conjugate-transposed family is unital, the unital contraction bound
applies there, and eigenvalues transfer as complex conjugates.
-/

/-- Every eigenvalue of a trace-preserving finite Kraus map has modulus at most one.

This is the trace-preserving form of the spectral bound in Wolf, Proposition 6.1. -/
theorem eigenvalue_norm_le_one_of_isTP
    (K : Fin d → Mat) (hTP : IsTP K)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mapLM K) μ) :
    ‖μ‖ ≤ 1 := by
  classical
  -- The conjugate-transposed family is unital.
  have hUnital : IsUnital (fun i => (K i)ᴴ) := by
    simpa only [IsUnital, Matrix.conjTranspose_conjTranspose] using hTP
  have hOne : mapLM (fun i => (K i)ᴴ) (1 : Mat) = 1 := by
    simpa only [mapLM_apply] using map_one_of_isUnital (fun i => (K i)ᴴ) hUnital
  have hKrausCP : IsKrausCP (mapLM fun i => (K i)ᴴ) :=
    ⟨d, fun i => (K i)ᴴ, fun X => by simp [mapLM_apply, map_apply]⟩
  -- Transfer the eigenvalue to the conjugate-transposed family.
  have hEigAdj : Module.End.HasEigenvalue (mapLM fun i => (K i)ᴴ) (star μ) := by
    refine (hasEigenvalue_mapLM_conjTranspose_iff K (star μ)).2 ?_
    simpa using hμ
  have hBound : ‖star μ‖ ≤ 1 :=
    hKrausCP.eigenvalue_norm_le_one_of_map_one_eq_one hOne (star μ) hEigAdj
  simpa only [RCLike.star_def, RCLike.norm_conj] using hBound

/-- A trace-preserving finite Kraus map has spectral radius at most one. -/
theorem spectralRadius_mapLM_le_one_of_isTP
    (K : Fin d → Mat) (hTP : IsTP K) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mapLM K)) ≤ 1 := by
  classical
  let Φ : (Mat →ₗ[ℂ] Mat) ≃ₐ[ℂ] TNLean.MatrixCLM (Fin D) :=
    Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
  have hSpec : spectrum ℂ (Φ (mapLM K)) = spectrum ℂ (mapLM K) :=
    AlgEquiv.spectrum_eq Φ (mapLM K)
  change spectralRadius ℂ (Φ (mapLM K)) ≤ 1
  rw [spectralRadius]
  refine iSup₂_le fun μ hμ ↦ ?_
  have hμE : μ ∈ spectrum ℂ (mapLM K) := hSpec ▸ hμ
  have hEig : Module.End.HasEigenvalue (mapLM K) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμE
  have hBound : ‖μ‖ ≤ 1 := eigenvalue_norm_le_one_of_isTP K hTP μ hEig
  exact_mod_cast hBound

end Kraus
