/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixOperatorSpace
import TNLean.Algebra.ShiftedTracePowerSpectrum
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.TransferMatrix

/-!
# Shifted Transfer Traces and Primitivity

This file transfers the shifted trace-power criterion for a transfer matrix to spectral
radius and primitivity of the represented matrix endomorphism.

No positivity, normality, diagonalizability, or first-moment hypothesis is used.
-/

open scoped Matrix ENNReal NNReal Matrix.Norms.Operator

variable {D : ℕ}

/-- If every transfer-matrix power of exponent greater than one has trace one, then the
represented matrix endomorphism has spectral radius one and is primitive.

The proof first applies the shifted nonzero-spectrum theorem to the transfer matrix and
then transports its eigenvalues through `transferMatrix_hasEigenvalue_iff`.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Proposition
`prop:normal-tensor`, lines 349--354. -/
theorem spectralRadius_eq_one_and_isPrimitive_of_transferMatrix_shifted_trace [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (htrace : ∀ N : ℕ, 1 < N → Matrix.trace (transferMatrix T ^ N) = 1) :
    spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) = 1 ∧
      IsPrimitive T := by
  let M := transferMatrix T
  have hnonzero : spectrum ℂ M \ {0} = {1} :=
    Matrix.spectrum_diff_zero_eq_singleton_of_forall_trace_pow_eq_one_of_one_lt M htrace
  have hclass : ∀ z : ℂ, z ∈ spectrum ℂ M → z = 0 ∨ z = 1 := by
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      have hz' : z ∈ spectrum ℂ M \ {0} := ⟨hz, by simpa using hz0⟩
      rw [hnonzero] at hz'
      simpa using hz'
  have hmatrix_of_eigenvalue :
      ∀ z : ℂ, Module.End.HasEigenvalue T z → z ∈ spectrum ℂ M := by
    intro z hz
    have hzM : Module.End.HasEigenvalue M.toLin' z :=
      (transferMatrix_hasEigenvalue_iff T z).mp hz
    have hzSpec : z ∈ spectrum ℂ M.toLin' :=
      Module.End.hasEigenvalue_iff_mem_spectrum.mp hzM
    simpa [M, Matrix.spectrum_toLin'] using hzSpec
  have h1M : (1 : ℂ) ∈ spectrum ℂ M := by
    have : (1 : ℂ) ∈ spectrum ℂ M \ {0} := by rw [hnonzero]; simp
    exact this.1
  have h1EigM : Module.End.HasEigenvalue M.toLin' (1 : ℂ) := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    simpa [Matrix.spectrum_toLin'] using h1M
  have h1EigT : Module.End.HasEigenvalue T (1 : ℂ) := by
    exact (transferMatrix_hasEigenvalue_iff T 1).mpr h1EigM
  have hspecCont :
      spectrum ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) =
        spectrum ℂ T :=
    AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T
  have hrad :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) = 1 := by
    apply le_antisymm
    · rw [spectralRadius]
      refine iSup₂_le fun z hz => ?_
      have hzT : z ∈ spectrum ℂ T := hspecCont ▸ hz
      have hzEig : Module.End.HasEigenvalue T z :=
        Module.End.hasEigenvalue_iff_mem_spectrum.mpr hzT
      rcases hclass z (hmatrix_of_eigenvalue z hzEig) with rfl | rfl <;> norm_num
    · rw [spectralRadius]
      have h1T : (1 : ℂ) ∈ spectrum ℂ T :=
        Module.End.hasEigenvalue_iff_mem_spectrum.mp h1EigT
      have h1Cont : (1 : ℂ) ∈
          spectrum ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) :=
        hspecCont.symm ▸ h1T
      simpa using (@le_iSup₂ ENNReal ℂ (· ∈ spectrum ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T)) _
          (fun z _ => (‖z‖₊ : ENNReal)) 1 h1Cont)
  refine ⟨hrad, ?_⟩
  change peripheralEigenvalues T = {1}
  ext z
  constructor
  · intro hz
    change Module.End.HasEigenvalue T z ∧ ‖z‖ = 1 at hz
    have hzM := hmatrix_of_eigenvalue z hz.1
    have hz0 : z ≠ 0 := by
      intro hz0
      subst z
      norm_num at hz
    have hzDiff : z ∈ spectrum ℂ M \ {0} := ⟨hzM, by simpa using hz0⟩
    rw [hnonzero] at hzDiff
    exact hzDiff
  · intro hz
    have hz1 : z = 1 := by simpa using hz
    subst z
    exact ⟨h1EigT, by simp⟩
