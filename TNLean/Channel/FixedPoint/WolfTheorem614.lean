/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixGramUnitary
import TNLean.Channel.FixedPoint.SupportCompressedDensityBlocks

/-!
# Fixed points of positive trace-preserving maps

This file proves the density-block classification of the fixed points of a
positive trace-preserving map whose trace adjoint satisfies the Schwarz
inequality.  Restriction to maximal stationary support gives the full-support
density blocks.  A unitary extension of the support isometry places the
orthogonal complement in one zero summand.

## Reference

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
  Equation (6.63); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1469--1494.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

variable {D : ℕ}

local notation "MatD" => Matrix (Fin D) (Fin D) ℂ

/-- **Wolf Theorem 6.14, Equation (6.63).** Let `T` be positive and trace
preserving, and suppose that its trace adjoint satisfies the Schwarz
inequality.  Then, after a unitary change of basis, the fixed-point space is
one zero summand followed by density-weighted full matrix blocks.  Every
density matrix is positive definite and has trace one.

The formalization orders each nonzero summand as
`ℂ^{m k} ⊗ ℂ^{d k}`, so its matrices are `σ k ⊗ₖ X k`.  This differs from
Wolf's displayed order only by the canonical interchange of the two tensor
factors.

Source: Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
Equation (6.63); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1469--1494. -/
theorem IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero
    {T : MatD →ₗ[ℂ] MatD} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    ∃ (n K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
      (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (σ k).PosDef) ∧ (∀ k, (σ k).trace = 1) ∧
        ∀ B : MatD, T B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e₀ e₀
              (Matrix.fromBlocks 0 0 0
                (Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k))) := by
  obtain ⟨_, n, V, _, hV, _, _, hambientFixed, hblocks⟩ :=
    hT.exists_block_densities_of_maximalSupportCompression hTP hSchwarz
  obtain ⟨K, d, m, e, Uc, σ, hUc, hd, hm, hσ, hσtrace, hcompressedFixed⟩ :=
    hblocks
  have hUcLeft : star Uc * Uc = 1 := Matrix.mem_unitaryGroup_iff'.mp hUc
  have hUcRight : Uc * star Uc = 1 := Matrix.mem_unitaryGroup_iff.mp hUc
  let W : Matrix (Fin D) (Fin n) ℂ := V * Uc
  have hWH : Wᴴ = star Uc * Vᴴ := by
    simp [W, Matrix.conjTranspose_mul]
  have hW : Wᴴ * W = 1 := by
    rw [hWH]
    dsimp only [W]
    calc
      star Uc * Vᴴ * (V * Uc) = star Uc * (Vᴴ * V) * Uc := by
        simp only [Matrix.mul_assoc]
      _ = star Uc * Uc := by rw [hV]; simp
      _ = 1 := hUcLeft
  obtain ⟨e₀, Uunitary, hzeroExtension⟩ :=
    Matrix.exists_unitary_zero_extension_eq W hW
  let U : Matrix (Fin D) (Fin D) ℂ := Uunitary
  have hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ := Uunitary.property
  have hULeft : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hURight : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  refine ⟨n, K, d, m, e, e₀, U, σ, hU, hd, hm, hσ, hσtrace, fun B ↦ ?_⟩
  constructor
  · intro hBfix
    obtain ⟨Y, hYfix, hBY⟩ := (hambientFixed B).mp hBfix
    obtain ⟨X, hYcoord⟩ := (hcompressedFixed Y).mp hYfix
    let A : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.reindex e e (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)
    have hYeq : Y = Uc * A * star Uc := by
      calc
        Y = (Uc * star Uc) * Y * (Uc * star Uc) := by rw [hUcRight]; simp
        _ = Uc * (star Uc * Y * Uc) * star Uc := by
          simp only [Matrix.mul_assoc]
        _ = Uc * A * star Uc := by rw [hYcoord]
    have hBzero :
        B = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := by
      calc
        B = V * Y * Vᴴ := hBY
        _ = W * A * Wᴴ := by rw [hYeq, W, hWH]; simp [Matrix.mul_assoc]
        _ = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := by
          simpa only [U] using hzeroExtension A
    refine ⟨X, ?_⟩
    rw [hBzero]
    simp [hULeft, Matrix.mul_assoc]
  · rintro ⟨X, hBcoord⟩
    let A : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.reindex e e (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)
    let Y : Matrix (Fin n) (Fin n) ℂ := Uc * A * star Uc
    have hYcoord : star Uc * Y * Uc = A := by
      dsimp only [Y]
      simp [hUcLeft, Matrix.mul_assoc]
    have hYfix : IsPositiveMap.stationarySupportCompression T V Y = Y :=
      (hcompressedFixed Y).mpr ⟨X, hYcoord⟩
    have hBeq : B = V * Y * Vᴴ := by
      have hBzero :
          B = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := by
        calc
          B = (U * star U) * B * (U * star U) := by rw [hURight]; simp
          _ = U * (star U * B * U) * star U := by
            simp only [Matrix.mul_assoc]
          _ = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := by
            rw [hBcoord]
      calc
        B = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := hBzero
        _ = W * A * Wᴴ := by
          simpa only [U] using (hzeroExtension A).symm
        _ = V * Y * Vᴴ := by rw [Y, W, hWH]; simp [Matrix.mul_assoc]
    exact (hambientFixed B).mpr ⟨Y, hYfix, hBeq⟩
