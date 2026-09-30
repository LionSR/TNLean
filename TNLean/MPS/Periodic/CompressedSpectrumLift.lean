/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.CompressedFixedLift

/-!
# Spectrum of a reducing Kraus compression

An eigenmatrix of a compressed Kraus map lifts isometrically to a nonzero
eigenmatrix of the ambient map. Consequently the entire compressed spectrum,
and in particular its peripheral part, is contained in the ambient spectrum.
This is the upper-bound step for periods of blocked cyclic sectors in
arXiv:1708.00029, Section 4.1.
-/

open scoped Matrix

namespace MPSTensor

/-- Every eigenvalue of a reducing compressed tensor map is an eigenvalue
of the ambient map. Source: arXiv:1708.00029, Section 4.1. -/
theorem compressedTensorMap_hasEigenvalue_lift {d D n : ℕ}
    (B : MPSTensor d D) (C : MPSTensor d n)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1)
    (hcomm : ∀ i, Commute (V * Vᴴ) (B i))
    (hC : ∀ i, C i = Vᴴ * B i * V)
    (μ : ℂ) :
    Module.End.HasEigenvalue (Kraus.mapLM C) μ →
      Module.End.HasEigenvalue (Kraus.mapLM B) μ := by
  intro hμ
  obtain ⟨σ, hσ⟩ := hμ.exists_hasEigenvector
  have hσne : σ ≠ 0 := hσ.2
  have hliftne : V * σ * Vᴴ ≠ 0 := by
    intro hzero
    have h := congrArg (fun X : Matrix (Fin D) (Fin D) ℂ => Vᴴ * X * V) hzero
    apply hσne
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V,
      hV, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul] using h
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_, hliftne⟩
  rw [Module.End.mem_eigenspace_iff]
  change Kraus.map B (V * σ * Vᴴ) = μ • (V * σ * Vᴴ)
  rw [compressedTensorMap_lift_of_commute B C V hV hcomm hC]
  have heig : Kraus.map C σ = μ • σ := by
    simpa only [Kraus.mapLM_apply] using
      (Module.End.mem_eigenspace_iff.mp hσ.1)
  rw [heig]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The spectrum of a reducing compression is contained in the ambient
Kraus-map spectrum. This includes peripheral eigenvalues without requiring
a separate modulus assumption. Source: arXiv:1708.00029, Section 4.1. -/
theorem compressedTensorMap_spectrum_subset {d D n : ℕ}
    (B : MPSTensor d D) (C : MPSTensor d n)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1)
    (hcomm : ∀ i, Commute (V * Vᴴ) (B i))
    (hC : ∀ i, C i = Vᴴ * B i * V) :
    spectrum ℂ (Kraus.mapLM C) ⊆ spectrum ℂ (Kraus.mapLM B) := by
  intro μ hμ
  exact (compressedTensorMap_hasEigenvalue_lift B C V hV hcomm hC μ
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)).mem_spectrum

end MPSTensor
