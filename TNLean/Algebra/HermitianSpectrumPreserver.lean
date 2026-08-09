/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianSpectrumMultiplicity
import TNLean.Algebra.HermitianSpectrumPerturbation
import TNLean.Algebra.MatrixTracePowerContinuity
import TNLean.Algebra.NewtonGirard

/-!
# Characteristic-polynomial preservation from Hermitian set spectra

Wolf's Chapter 1 spectrum-preserver argument assumes equality of spectra as
sets on Hermitian inputs, not equality counting multiplicities.  This file
derives the latter information internally.

For a Hermitian matrix `A`, explicit positive perturbations split its ordered
eigenvalues and converge to `A`.  Set-spectrum equality on each perturbed
matrix then gives equality of characteristic-root multisets, because the input
roots are distinct and both matrices have the same finite dimension.  Hence all
trace powers agree on the perturbations.  Continuity of the linear map and of
matrix trace powers passes these identities to `A`; Newton--Girard then gives
characteristic-polynomial equality.

The proof includes matrix dimension zero and assumes no density theorem.

## Main declaration

* `Matrix.charpoly_map_eq_of_preserves_hermitian_spectrum`: Wolf's exact
  set-spectrum hypothesis implies characteristic-polynomial preservation on
  Hermitian matrices.
-/

open scoped Matrix

namespace Matrix

variable {d : ℕ}

/-- A complex-linear Hermiticity-preserving map that preserves the complex
spectrum as a set on every Hermitian input also preserves characteristic
polynomials on Hermitian inputs.

This is the multiplicity step in Wolf, Chapter 1, "Spectrum preserving maps".
Characteristic-polynomial preservation is a conclusion, not a hypothesis. -/
theorem charpoly_map_eq_of_preserves_hermitian_spectrum
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hHermitian : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.IsHermitian → (T A).IsHermitian)
    (hSpectrum : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.IsHermitian → spectrum ℂ (T A) = spectrum ℂ A)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    (T A).charpoly = A.charpoly := by
  apply Matrix.charpoly_eq_of_trace_pow_eq_of_le_card
  intro k _hkPos _hkCard
  let P : ℕ → Matrix (Fin d) (Fin d) ℂ := fun n =>
    hA.simpleSpectrumPerturbation (1 / (n + 1 : ℝ))
  have hP : Filter.Tendsto P Filter.atTop (nhds A) := by
    simpa [P] using hA.tendsto_simpleSpectrumPerturbation_one_div
  have hTP : Filter.Tendsto (fun n => T (P n)) Filter.atTop (nhds (T A)) :=
    T.continuous_of_finiteDimensional.continuousAt.tendsto.comp hP
  have hLeft := Matrix.tendsto_trace_pow hTP k
  have hRight := Matrix.tendsto_trace_pow hP k
  have hTracePerturbation : ∀ n,
      Matrix.trace ((T (P n)) ^ k) = Matrix.trace ((P n) ^ k) := by
    intro n
    have hε : 0 < (1 / (n + 1 : ℝ)) := by positivity
    have hPn : (P n).IsHermitian := by
      exact hA.simpleSpectrumPerturbation_isHermitian _
    exact hPn.trace_pow_eq_of_spectrum_eq_of_roots_nodup
      (hHermitian (P n) hPn) (hSpectrum (P n) hPn)
      (hA.simpleSpectrumPerturbation_roots_nodup hε) k
  have hFunctions :
      (fun n => Matrix.trace ((T (P n)) ^ k)) =
        fun n => Matrix.trace ((P n) ^ k) :=
    funext hTracePerturbation
  rw [hFunctions] at hLeft
  exact tendsto_nhds_unique hLeft hRight

end Matrix
