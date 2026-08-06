/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrobeniusHilbert
import TNLean.Channel.KrausCPTP
import TNLean.Channel.Schwarz.PositiveMapProperties
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Operator-norm bounds for unital Kraus maps

A unital completely positive endomorphism of a finite matrix algebra is a contraction for the
matrix operator norm. Consequently, every eigenvalue lies in the closed unit disk.

## Main statements

* `IsKrausCP.norm_apply_le_of_map_one_eq_one`: operator-norm contractivity of a unital Kraus map.
* `IsKrausCP.eigenvalue_norm_le_one_of_map_one_eq_one`: the spectral bound for a unital Kraus map.
* `IsKrausCP.spectralRadius_frobeniusEuclideanMap_le_one_of_map_one_eq_one`:
  the corresponding bound after Frobenius vectorization.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal ENNReal
open Matrix

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-- A unital Kraus completely positive endomorphism is a contraction for the matrix operator norm.
-/
theorem IsKrausCP.norm_apply_le_of_map_one_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {E : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hE : IsKrausCP E) (hOne : E 1 = 1) (X : Matrix α α ℂ) :
    ‖E X‖ ≤ ‖X‖ := by
  letI : CStarAlgebra (Matrix α α ℂ) := Matrix.matrixCStarAlgebra
  have hPos : IsPositiveMap E := fun _ hA ↦ hE.map_posSemidef hA
  have hXX :
      Xᴴ * X ≤ (algebraMap ℝ (Matrix α α ℂ)) (‖X‖ ^ 2) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X))
  have hEXX :
      E (Xᴴ * X) ≤ (algebraMap ℝ (Matrix α α ℂ)) (‖X‖ ^ 2) := by
    calc
      E (Xᴴ * X) ≤ E ((algebraMap ℝ (Matrix α α ℂ)) (‖X‖ ^ 2)) :=
        hPos.map_le_map hXX
      _ = (algebraMap ℝ (Matrix α α ℂ)) (‖X‖ ^ 2) := by
        rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul_of_tower, hOne]
  have hKS :
      (E X)ᴴ * E X ≤ E (Xᴴ * X) := by
    exact Matrix.le_iff.mpr (hE.kadison_schwarz_of_map_one_eq_one hOne X)
  have hSq : ‖E X‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    have hnorm :
        ‖(E X)ᴴ * E X‖ ≤ ‖X‖ ^ 2 :=
      (CStarAlgebra.norm_le_iff_le_algebraMap
        ((E X)ᴴ * E X) (sq_nonneg ‖X‖)
        ((Matrix.posSemidef_conjTranspose_mul_self (E X)).nonneg)).mpr
          (hKS.trans hEXX)
    rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hnorm
    simpa only [pow_two] using hnorm
  exact (sq_le_sq₀ (norm_nonneg (E X)) (norm_nonneg X)).mp hSq

/-- Every eigenvalue of a unital Kraus completely positive endomorphism has modulus at most one.

This is the unital form of the spectral bound in Wolf, Proposition 6.1. -/
theorem IsKrausCP.eigenvalue_norm_le_one_of_map_one_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {E : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hE : IsKrausCP E) (hOne : E 1 = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue E μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨X, hXmem, hXne⟩ := hμ.exists_hasEigenvector
  have hEig : E X = μ • X := Module.End.mem_eigenspace_iff.mp hXmem
  have hContract := hE.norm_apply_le_of_map_one_eq_one hOne X
  rw [hEig, norm_smul] at hContract
  have hXpos : 0 < ‖X‖ := norm_pos_iff.mpr hXne
  exact le_of_mul_le_mul_right (by simpa using hContract) hXpos

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius-vectorized form of a unital Kraus completely positive
endomorphism has spectral radius at most one. This statement also covers the
zero-dimensional matrix algebra. -/
theorem IsKrausCP.spectralRadius_frobeniusEuclideanMap_le_one_of_map_one_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {E : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hE : IsKrausCP E) (hOne : E 1 = 1) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (EuclideanSpace ℂ (α × α)))
        (Matrix.frobeniusEuclideanMap E)) ≤ 1 := by
  let V := EuclideanSpace ℂ (α × α)
  let Ê : V →ₗ[ℂ] V := Matrix.frobeniusEuclideanMap E
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) :=
    Module.End.toContinuousLinearMap V
  have hSpecCLM : spectrum ℂ (Φ Ê) = spectrum ℂ Ê :=
    AlgEquiv.spectrum_eq Φ Ê
  have hSpecFrob : spectrum ℂ Ê = spectrum ℂ E := by
    dsimp only [Ê]
    rw [Matrix.frobeniusEuclideanMap_eq_conj]
    exact AlgEquiv.spectrum_eq
      ((Matrix.frobeniusEquivEuclidean α α).toLinearEquiv.conjAlgEquiv ℂ) E
  change spectralRadius ℂ (Φ Ê) ≤ 1
  rw [spectralRadius]
  refine iSup₂_le fun μ hμ ↦ ?_
  have hμE : μ ∈ spectrum ℂ E := hSpecFrob ▸ (hSpecCLM ▸ hμ)
  have hEig : Module.End.HasEigenvalue E μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμE
  have hBound : ‖μ‖ ≤ 1 :=
    hE.eigenvalue_norm_le_one_of_map_one_eq_one hOne μ hEig
  exact_mod_cast hBound
