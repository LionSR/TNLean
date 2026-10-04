/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Channel.KrausMap
import QICLean.Kraus.Transfer
import QICLean.Algebra.OrthogonalProjection
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TNLean.Spectral.MPVOverlapDecayRect
import TNLean.MPS.Preparation.SecondOrderOverlap

/-!
# Decay of a complementary diagonal tensor corner

Let a unital MPS tensor have a one-dimensional transfer fixed space. For a
nonzero orthogonal projection `P` satisfying `P Aᵢ (1 - P) = 0`, every nonzero
transfer eigenvector of the complementary corner is supported on that corner
and lifts to an ambient transfer eigenvector. The eigenvalue one is excluded:
an ambient fixed vector is a scalar identity, which cannot be supported on the
complement of a nonzero projection.

Consequently, a bound below one on the ambient nonunit spectrum implies decay
of the complementary periodic MPS norm. The complementary letters may be
nonzero, and no equality of the recurrent and ambient finite-ring rays is
assumed or concluded.

Source context: Pérez-García, Verstraete, Wolf, and Cirac,
arXiv:quant-ph/0608197, proof of the TI canonical-form theorem,
`Th:TIcanonical`, lines 785–815. The statements below are auxiliary spectral
estimates for the explicit triangular corner used in that trace decomposition.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators Matrix.Norms.Operator

attribute [local instance]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toSeminormedRing

namespace MPSTensor

private theorem map_corner_supported {d D : ℕ} (A : MPSTensor d D)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Q * Kraus.map (fun i => Q * A i * Q) X * Q =
      Kraus.map (fun i => Q * A i * Q) X := by
  classical
  simp only [Kraus.map_apply, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.conjTranspose_mul, hQ.1.eq]
  simp only [← Matrix.mul_assoc, hQ.2]
  simp only [Matrix.mul_assoc, hQ.2]

private theorem map_corner_eq_of_supported {d D : ℕ} (A : MPSTensor d D)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (hUpper : ∀ i, (1 - Q) * A i * Q = 0)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : Q * X * Q = X) :
    Kraus.map (fun i => Q * A i * Q) X = Kraus.map A X := by
  classical
  have hAQ : ∀ i, Q * A i * Q = A i * Q := by
    intro i
    have h := hUpper i
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h.symm
  simp only [Kraus.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hAQ, Matrix.conjTranspose_mul, hQ.1.eq]
  calc
    A i * Q * X * (Q * (A i)ᴴ) = A i * (Q * X * Q) * (A i)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = A i * X * (A i)ᴴ := by rw [hX]

/-- The transfer spectrum of a transient diagonal corner inherits the bound
on the ambient nonunit spectrum. A one-dimensional ambient fixed space rules
out eigenvalue one in the corner complementary to a nonzero projection. -/
theorem spectrum_transferMap_transientCorner_norm_le
    {d D : ℕ} [NeZero D] (A : MPSTensor d D) (hUnital : Kraus.IsUnital A)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P) (hPZero : P ≠ 0)
    (hUpper : ∀ i, P * A i * (1 - P) = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q) :
    ∀ z ∈ spectrum ℂ (Kraus.transferMap (fun i => (1 - P) * A i * (1 - P))),
      ‖z‖ ≤ q := by
  let Q : Matrix (Fin D) (Fin D) ℂ := 1 - P
  have hQ : IsOrthogonalProjection Q :=
    hP.isStarProjection.one_sub.isOrthogonalProjection
  have hUpperQ : ∀ i, (1 - Q) * A i * Q = 0 := by
    simpa only [Q, sub_sub_cancel] using hUpper
  intro z hz
  by_cases hzZero : z = 0
  · simpa only [hzZero, norm_zero] using hq
  obtain ⟨X, hX⟩ :=
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  have hEigen : Kraus.map (fun i => Q * A i * Q) X = z • X :=
    Module.End.mem_eigenspace_iff.mp hX.1
  have hSupport : Q * X * Q = X := by
    apply (smul_right_injective (Matrix (Fin D) (Fin D) ℂ) hzZero)
    calc
      z • (Q * X * Q) = Q * (z • X) * Q := by
        simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = Q * Kraus.map (fun i => Q * A i * Q) X * Q := by rw [hEigen]
      _ = Kraus.map (fun i => Q * A i * Q) X := map_corner_supported A Q hQ X
      _ = z • X := hEigen
  have hAmbient : Kraus.transferMap A X = z • X := by
    change Kraus.map A X = z • X
    rw [← map_corner_eq_of_supported A Q hQ hUpperQ X hSupport]
    exact hEigen
  have hzOne : z ≠ 1 := by
    intro hzOne
    have hOne : Kraus.transferMap A 1 = 1 := Kraus.map_one_of_isUnital A hUnital
    have hFixedSpace : Module.End.eigenspace (Kraus.transferMap A) 1 =
        Submodule.span ℂ {(1 : Matrix (Fin D) (Fin D) ℂ)} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hDim
        (Module.End.mem_eigenspace_iff.mpr (by simpa only [one_smul] using hOne))
        one_ne_zero
    have hXFixed : X ∈ Module.End.eigenspace (Kraus.transferMap A) 1 := by
      apply Module.End.mem_eigenspace_iff.mpr
      simpa only [hzOne, one_smul] using hAmbient
    rw [hFixedSpace] at hXFixed
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hXFixed
    have hcZero : c ≠ 0 := by
      intro hcZero
      apply hX.2
      rw [← hc, hcZero, zero_smul]
    have hQOne : Q = 1 := by
      apply (smul_right_injective (Matrix (Fin D) (Fin D) ℂ) hcZero)
      simpa only [← hc, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hQ.2] using hSupport
    apply hPZero
    simpa only [Q, sub_eq_self] using hQOne
  exact hspec z
    (Module.End.hasEigenvalue_iff_mem_spectrum.mp
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hAmbient, hX.2⟩)) hzOne

/-- A complementary diagonal corner with no peripheral transfer eigenvalues
has a periodic MPS norm tending to zero. In combination with the exact
triangular trace split, this permits asymptotic comparison with the recurrent
corner without asserting equality of their finite-ring rays. -/
theorem norm_mpvState_transientCorner_tendsto_zero_of_transfer_spectrum
    {d D : ℕ} [NeZero D] (A : MPSTensor d D) (hUnital : Kraus.IsUnital A)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P) (hPZero : P ≠ 0)
    (hUpper : ∀ i, P * A i * (1 - P) = 0)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q) :
    Filter.Tendsto
      (fun N : ℕ => ‖mpvState (fun i => (1 - P) * A i * (1 - P)) N‖)
      Filter.atTop (nhds (0 : ℝ)) := by
  let R : MPSTensor d D := fun i => (1 - P) * A i * (1 - P)
  have hBound : ∀ z ∈ spectrum ℂ (Kraus.transferMap R), ‖z‖ ≤ q :=
    spectrum_transferMap_transientCorner_norm_le A hUnital hDim P hP hPZero
      hUpper q hq hspec
  have hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap R)) < 1 := by
    apply spectralRadius_lt_of_forall_quasispectrum_lt (r := 1)
    intro z hz
    rw [quasispectrum_eq_spectrum_union_zero] at hz
    rcases hz with hz | hz
    · rw [AlgEquiv.spectrum_eq] at hz
      have hlt : ‖z‖ < 1 := lt_of_le_of_lt (hBound z hz) hqOne
      exact_mod_cast hlt
    · have hzZero : z = 0 := hz
      rw [hzZero]
      norm_num
  have hOverlap : Filter.Tendsto (fun N => mpvOverlap R R N)
      Filter.atTop (nhds (0 : ℂ)) :=
    mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one R R
      (by simpa only [Kraus.mixedMapLM_self] using hRadius)
  have hSquare : Filter.Tendsto (fun N => ‖mpvState R N‖ ^ 2)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, ← ofReal_norm_mpvState_sq,
      Complex.ofReal_re, Complex.zero_re]
      using (Complex.continuous_re.tendsto (0 : ℂ)).comp hOverlap
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero]
    using hSquare.sqrt

end MPSTensor
