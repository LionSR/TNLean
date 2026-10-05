/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.StationaryPhysicalDensity
import QICLean.Algebra.TracePurity
import QICLean.Algebra.TraceReindex

/-!
# Physical density overlaps as quadratic transfer contractions

The overlap of two stationary physical block densities is a quadratic
expression in a mixed transfer iterate. All virtual factors have dimension
D² and are independent of the physical block length. Decay of the mixed
transfer iterates therefore forces the physical density overlaps to zero.

## References

* Pérez-García, Wolf, Sanz, Verstraete and Cirac, arXiv:0802.0447,
  proof of Theorem 2, lines 311–323.
-/

open scoped Matrix BigOperators Kronecker ComplexOrder MatrixOrder Topology
open Filter

namespace MPSTensor

variable {d D : ℕ}

/-- The density factors through the positive square root of its fixed
D²-dimensional virtual boundary. Source: arXiv:0802.0447, proof of Theorem 2. -/
theorem stationaryBlockDensity_eq_mul_conjTranspose
    (A : MPSTensor d D) {Λ : Matrix (Fin D) (Fin D) ℂ}
    (hΛ : Λ.PosSemidef) (N : ℕ) :
    let S := CFC.sqrt (Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))
    let F := physicalMatrix (blockTensor A N) * S
    stationaryBlockDensity A Λ N = F * Fᴴ := by
  dsimp only
  have hK := hΛ.transpose.kronecker (Matrix.PosSemidef.one (R := ℂ) (n := Fin D))
  have hS : (CFC.sqrt (Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))ᴴ =
      CFC.sqrt (Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq
  rw [Matrix.conjTranspose_mul, hS]
  simp only [stationaryBlockDensity, Matrix.mul_assoc,
    ← Matrix.mul_assoc (CFC.sqrt _) (CFC.sqrt _), CFC.sqrt_mul_sqrt_self _ hK.nonneg]

/-- The physical purity is bounded below uniformly in N by D⁻². The
Cauchy–Schwarz bound is applied on the virtual pair space, whose dimension
does not grow with N. Source: arXiv:0802.0447, proof of Theorem 2, lines 316–320. -/
theorem inv_sq_le_purity_stationaryBlockDensity [NeZero D]
    (A : MPSTensor d D) {Λ : Matrix (Fin D) (Fin D) ℂ}
    (hΛ : Λ.PosSemidef) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : Kraus.transferMap A 1 = 1) (N : ℕ) :
    (D : ℝ)⁻¹ ^ 2 ≤ (Matrix.trace (stationaryBlockDensity A Λ N ^ 2)).re := by
  let S := CFC.sqrt (Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))
  let F := physicalMatrix (blockTensor A N) * S
  have hρ : stationaryBlockDensity A Λ N = F * Fᴴ :=
    stationaryBlockDensity_eq_mul_conjTranspose A hΛ N
  let G := Matrix.reindex finProdFinEquiv finProdFinEquiv (Fᴴ * F)
  have hG : G.IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self F).submatrix _
  have hGtr : G.trace = 1 := by
    rw [Matrix.trace_reindex, Matrix.trace_mul_comm, ← hρ]
    exact trace_stationaryBlockDensity_eq_one A Λ hΛtr hNorm N
  have hGsq : (G ^ 2).trace = (stationaryBlockDensity A Λ N ^ 2).trace := by
    rw [pow_two, Matrix.trace_mul_self_eq_of_reindex_eq
      finProdFinEquiv (Fᴴ * F) G rfl, hρ, pow_two]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm Fᴴ (F * Fᴴ * F)
  have h := hG.trace_re_sq_le_card_mul_trace_sq_re
  rw [hGtr, hGsq] at h
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (NeZero.pos D)
  have hDsq : (0 : ℝ) < (D : ℝ) ^ 2 := sq_pos_of_pos hD
  have h' : 1 ≤ (D : ℝ) ^ 2 * (stationaryBlockDensity A Λ N ^ 2).trace.re := by
    simpa [Nat.cast_mul, pow_two] using h
  have hdiv : 1 / (D : ℝ) ^ 2 ≤ (stationaryBlockDensity A Λ N ^ 2).trace.re :=
    (div_le_iff₀ hDsq).mpr (by simpa only [mul_comm] using h')
  simpa only [one_div, inv_pow] using hdiv


/-- The physical density overlap is a quadratic contraction of the mixed
virtual Gram matrix, with boundary factors independent of N.
Source: arXiv:0802.0447, proof of Theorem 2, lines 316–320. -/
theorem trace_stationaryBlockDensity_mul_eq (A B : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) :
    let K := Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)
    let G := (physicalMatrix (blockTensor A N))ᴴ * physicalMatrix (blockTensor B N)
    Matrix.trace (stationaryBlockDensity A Λ N * stationaryBlockDensity B Λ N) =
      Matrix.trace (K * G * K * Gᴴ) := by
  dsimp only
  simp only [stationaryBlockDensity, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
    (physicalMatrix (blockTensor A N))
    ((Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
      (physicalMatrix (blockTensor A N))ᴴ * physicalMatrix (blockTensor B N) *
      (Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
      (physicalMatrix (blockTensor B N))ᴴ)

/-- Decay of the mixed transfer map gives decay of the physical block density
overlap. Source: arXiv:0802.0447, proof of Theorem 2, lines 316–320. -/
theorem stationaryBlockDensity_overlap_tendsto_zero
    (A B : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hdecay : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      Tendsto (fun N => (Kraus.mixedMapLM B A ^ N) X) atTop (𝓝 0)) :
    Tendsto (fun N => Matrix.trace
      (stationaryBlockDensity A Λ N * stationaryBlockDensity B Λ N)) atTop (𝓝 0) := by
  let K := Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)
  have hG : Tendsto (fun N =>
      (physicalMatrix (blockTensor A N))ᴴ * physicalMatrix (blockTensor B N))
      atTop (𝓝 (0 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)) := by
    refine tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => ?_
    simpa only [conjTranspose_physicalMatrix_mul_physicalMatrix_apply,
      mixedMapLM_blockTensor_apply, Matrix.zero_apply] using
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hdecay (Matrix.single b.2 a.2 1)) b.1) a.1
  have hcontinuous : Continuous (fun G : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ =>
      Matrix.trace (K * G * K * Gᴴ)) := by
    fun_prop
  have h := (hcontinuous.tendsto 0).comp hG
  simpa only [trace_stationaryBlockDensity_mul_eq, K, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.trace_zero, Function.comp_def] using h


end MPSTensor
