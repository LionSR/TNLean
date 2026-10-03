/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.SupportedCompressionIrreducible
import TNLean.MPS.CanonicalForm.Definitions
import QICLean.Channel.Peripheral.SpectralRadius
import QICLean.Channel.KrausCornerCompression
import QICLean.Algebra.MatrixAux
import QICLean.Algebra.MatrixUnitaryBetween


/-!
# Preparation on the full stationary support

A unital tensor with a unique normalized adjoint stationary density restricts
to a unital irreducible tensor on the entire support of that density. The
compressed density is faithful, normalized, and adjoint stationary. Stationarity
supplies the required one-sided letter invariance; no periodic-ray identity is
asserted. A supplied spectral bound below one on all nontrivial ambient
transfer eigenvalues further implies normality of the support compression.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. This module proves
auxiliary preparation and spectral consequences and does not derive stationary support data
from a physical Hamiltonian path.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder

namespace MPSTensor

/-- An isometric compression of a unital tensor is unital when the orthogonal
complement of its range is invariant under every letter. Equivalently, the
range is invariant under every adjoint letter. This finite-dimensional
auxiliary result is used in the support reduction of arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
private theorem isUnital_compression_of_isUnital_of_upperZero
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K) (hB : Kraus.IsUnital B)
    (hUpper : ∀ i, (K * Kᴴ) * B i * (1 - K * Kᴴ) = 0) :
    Kraus.IsUnital A := by
  change Kᴴ * K = 1 at hK
  let P := K * Kᴴ
  have hKP : Kᴴ * P = Kᴴ := by
    change Kᴴ * (K * Kᴴ) = Kᴴ
    rw [← Matrix.mul_assoc, hK, Matrix.one_mul]
  have hPB : ∀ i, P * B i * P = P * B i := fun i =>
    (sub_eq_zero.mp (by simpa only [Matrix.mul_sub, Matrix.mul_one] using hUpper i)).symm
  have hKB : ∀ i, Kᴴ * B i * P = Kᴴ * B i := fun i => by
    simpa only [← Matrix.mul_assoc, hKP] using
      congrArg (fun X => Kᴴ * X) (hPB i)
  have hterm : ∀ i, A i * (A i)ᴴ = Kᴴ * B i * (B i)ᴴ * K := fun i => by
    calc
      _ = (Kᴴ * B i * P) * (B i)ᴴ * K := by
        simp only [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          P, Matrix.mul_assoc]
      _ = Kᴴ * B i * (B i)ᴴ * K := by
        rw [hKB]
  simpa only [Kraus.IsUnital, Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_assoc,
    ← hterm, Matrix.mul_one, hK] using congrArg (fun X => Kᴴ * X * K) hB

/-- The full support compression of a unital tensor with a unique normalized
adjoint stationary density is unital and irreducible. Its compressed density
is faithful, normalized, and adjoint stationary. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717; stationary support invariance
and irreducibility are Wolf, Lemma 6.4 and Theorem 6.3. This is an auxiliary
preparation result; it asserts no equality of finite periodic rays. -/
theorem prepare_stationary_support_compression
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K) (hB : Kraus.IsUnital B)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (huniq : ∀ Z : Matrix (Fin k) (Fin k) ℂ,
      Kraus.adjointMap B Z = Z → Z.trace = 1 → Z = σ) :
    Kraus.IsUnital A ∧ IsIrreducibleMap (Kraus.mapLM A) ∧
      (Kᴴ * σ * K).PosDef ∧ (Kᴴ * σ * K).trace = 1 ∧
      Kraus.adjointMap A (Kᴴ * σ * K) = Kᴴ * σ * K := by
  have hfix' : Kraus.map (fun i => (B i)ᴴ) σ = σ := by
    simpa only [Kraus.map_apply, Matrix.conjTranspose_conjTranspose,
      Kraus.adjointMap_apply] using hfix
  have hInv := Kraus.lowerZero_of_posSemidef_fixedPoint
    (fun i => (B i)ᴴ) σ hσ hfix'
  have hUpper : ∀ i, (K * Kᴴ) * B i * (1 - K * Kᴴ) = 0 := fun i => by
    simpa only [Kraus.stationaryProj, ← hsupport, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, Matrix.mul_assoc]
      using congrArg Matrix.conjTranspose (hInv.2 i)
  have hUnital := isUnital_compression_of_isUnital_of_upperZero B A K hK hA hB hUpper
  have hD := Matrix.supportFrame_dimension_pos_of_trace_one K σ hσ hsupport htrace
  let : NeZero D := ⟨Nat.ne_of_gt hD⟩
  have hIrr := isIrreducibleMap_of_unital_support_compression
    B A K hK hA hUnital σ hσ hsupport hfix htrace huniq
  obtain ⟨hρfix, hρtrace, _⟩ := stationaryMatrix_compression_unique
    B A K hK hA σ hσ hsupport hfix htrace huniq
  refine ⟨hUnital, hIrr, ?_, hρtrace, hρfix⟩
  simpa only [Matrix.conjTranspose_conjTranspose] using
    hσ.compression_on_support_posDef (V := Kᴴ)
      (by simpa only [Matrix.conjTranspose_conjTranspose] using
        (show Kᴴ * K = 1 from hK))
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hsupport)

/-- Isometric support expansion preserves nonzero adjoint eigenvectors. -/
private theorem hasEigenvalue_adjointMap_compression_lift
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (Kraus.adjointMapLM A) μ) :
    Module.End.HasEigenvalue (Kraus.adjointMapLM B) μ := by
  obtain ⟨Z, hZ⟩ := hμ.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := K * Z * Kᴴ) ?_
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · simpa only [Kraus.adjointMapLM_apply, Matrix.mul_smul, Matrix.smul_mul] using
      (adjointMap_compression_lift B A K hK hA σ hσ hsupport hfix Z).trans
        (congrArg (fun X => K * X * Kᴴ) hZ.apply_eq_smul)
  · intro hzero
    apply hZ.2
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ K,
      show Kᴴ * K = 1 from hK, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul] using
      congrArg (fun X => Kᴴ * X * K) hzero

/-- The transfer spectrum on a stationary support lies in the ambient spectrum. -/
private theorem hasEigenvalue_mapLM_support_compression
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (Kraus.mapLM A) μ) :
    Module.End.HasEigenvalue (Kraus.mapLM B) μ := by
  apply (Matrix.traceAdjointMap_hasEigenvalue_iff (Kraus.mapLM B) μ).mp
  rw [Kraus.traceAdjointMap_mapLM]
  apply hasEigenvalue_adjointMap_compression_lift B A K hK hA σ hσ hsupport hfix μ
  simpa only [Kraus.traceAdjointMap_mapLM] using
    (Matrix.traceAdjointMap_hasEigenvalue_iff (Kraus.mapLM A) μ).mpr hμ

/-- A full stationary support compression is a normal tensor when every
ambient transfer eigenvalue other than one has modulus bounded by a fixed
number below one. The spectral bound is supplied, not inferred from a physical
Hamiltonian gap. Source context: Wolf, Proposition 6.1 and Theorem 6.8;
arXiv:1606.00608, lines 231–235; arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isNormalTensor_of_unital_stationary_support_compression
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K) (hB : Kraus.IsUnital B)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (huniq : ∀ Z : Matrix (Fin k) (Fin k) ℂ,
      Kraus.adjointMap B Z = Z → Z.trace = 1 → Z = σ)
    (q : ℝ) (hq : q < 1)
    (hspec : ∀ μ ∈ spectrum ℂ (Kraus.mapLM B), μ ≠ 1 → ‖μ‖ ≤ q) :
    IsNormalTensor A := by
  obtain ⟨hUnital, hIrr, _, _, _⟩ := prepare_stationary_support_compression
    B A K hK hA hB σ hσ hsupport hfix htrace huniq
  let : NeZero D := ⟨Nat.ne_of_gt
    (Matrix.supportFrame_dimension_pos_of_trace_one K σ hσ hsupport htrace)⟩
  have hOne : Kraus.mapLM A 1 = 1 := Kraus.map_one_of_isUnital A hUnital
  refine ⟨Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hIrr,
    (Kraus.isPositiveMap_mapLM A).spectralRadius_eq_one_of_map_one_eq_one hOne, ?_⟩
  change peripheralEigenvalues (Kraus.mapLM A) = {1}
  ext μ
  change (Module.End.HasEigenvalue (Kraus.mapLM A) μ ∧ ‖μ‖ = 1) ↔ μ = 1
  constructor
  · rintro ⟨hμ, hnorm⟩
    by_contra hne
    exact (not_le_of_gt hq) (by
      simpa only [hnorm] using hspec μ (Module.End.hasEigenvalue_iff_mem_spectrum.mp
        (hasEigenvalue_mapLM_support_compression B A K hK hA σ hσ hsupport hfix μ hμ)) hne)
  · rintro rfl
    exact ⟨eigenvalue_one_of_map_one_eq_one hOne, norm_one⟩

end MPSTensor
