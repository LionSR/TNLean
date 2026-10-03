/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AffineGramTransfer
import TNLean.MPS.MPU.BalancedGramMetrics
import TNLean.Algebra.FinSumPermutation
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Real affine hulls of MPU prefix Grams

The physical prefix Grams are obtained from all density matrices on a prefix.
Their real affine hull also permits negative affine coefficients. Interval
transfer maps this hull into the corresponding hull of the longer prefix.
The density matrices may be entangled within each of the two intervals.

These are the compatibility identities in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. They do not assert the
existence of the determinant maximizer or the complete circuit theorem.
-/

open Matrix
open scoped Matrix ComplexOrder Kronecker

namespace MPUCircuit

variable {o i m : Type*} [Fintype o] [Fintype i]

/-- Physical prefix Grams range over all positive semidefinite input states
of trace one. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def densityPrefixGrams (F : o → i → Matrix Unit m ℂ) :
    Set (Matrix m m ℂ) :=
  {P | ∃ ρ : Matrix i i ℂ, ρ.PosSemidef ∧ trace ρ = 1 ∧ prefixInputGram F ρ = P}

/-- The real affine hull of physical prefix Grams. Points in this hull need
not themselves be physical prefix Grams. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def prefixGramAffineHull (F : o → i → Matrix Unit m ℂ) :
    AffineSubspace ℝ (Matrix m m ℂ) :=
  affineSpan ℝ (densityPrefixGrams F)

/-- The prefix Gram is a sum of positive matrix sandwiches. The transpose
of the density matrix follows from the convention `ρ c b` in the Gram
transfer. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prefixInputGram_eq_sum_sandwich (F : o → i → Matrix Unit m ℂ)
    (ρ : Matrix i i ℂ) :
    prefixInputGram F ρ =
      ∑ a, (Matrix.of fun b x ↦ F a b () x)ᴴ * ρᵀ *
        (Matrix.of fun b x ↦ F a b () x) := by
  classical
  ext x y
  simp only [prefixInputGram, intervalGramTransfer, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_apply, conjTranspose_apply, transpose_apply, of_apply]
  simp only [Fintype.sum_unique, Matrix.one_apply_eq, mul_one]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro b _ c _
  ring

/-- Density-weighted prefix Grams are positive semidefinite. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prefixInputGram_posSemidef [Finite m]
    (F : o → i → Matrix Unit m ℂ) {ρ : Matrix i i ℂ} (hρ : ρ.PosSemidef) :
    (prefixInputGram F ρ).PosSemidef := by
  rw [prefixInputGram_eq_sum_sandwich]
  exact posSemidef_sum _ fun a _ ↦
    hρ.transpose.conjTranspose_mul_mul_same (Matrix.of fun b x ↦ F a b () x)

/-- Every physical prefix Gram is positive semidefinite. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem posSemidef_of_mem_densityPrefixGrams [Finite m]
    (F : o → i → Matrix Unit m ℂ) {P : Matrix m m ℂ}
    (hP : P ∈ densityPrefixGrams F) : P.PosSemidef := by
  rcases hP with ⟨ρ, hρ, _, rfl⟩
  exact prefixInputGram_posSemidef F hρ

/-- The entire real affine hull of physical prefix Grams is Hermitian.
Positivity is not asserted for arbitrary points of the affine hull. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isHermitian_of_mem_prefixGramAffineHull [Finite m]
    (F : o → i → Matrix Unit m ℂ) {P : Matrix m m ℂ}
    (hP : P ∈ prefixGramAffineHull F) : P.IsHermitian := by
  exact isHermitian_of_mem_real_affineSpan
    (fun X hX ↦ (posSemidef_of_mem_densityPrefixGrams F hX).isHermitian) hP

variable [Fintype m]

/-- Interval transfer, restricted from complex scalars to real scalars and
viewed as an affine map. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def intervalGramTransferAffineMap {o' i' n : Type*}
    [Fintype o'] [Fintype i'] (A : o' → i' → Matrix m n ℂ)
    (σ : Matrix i' i' ℂ) : Matrix m m ℂ →ᵃ[ℝ] Matrix n n ℂ :=
  ((intervalGramTransferLinearMap A σ).restrictScalars ℝ).toAffineMap

/-- A physical prefix Gram transfers to a physical Gram of the concatenated
prefix. Product density is used only between the two intervals; each factor
may be internally entangled. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem intervalGramTransfer_mem_densityPrefixGrams_concat
    {o' i' n : Type*} [Fintype o'] [Fintype i']
    (F : o → i → Matrix Unit m ℂ) (A : o' → i' → Matrix m n ℂ)
    {σ : Matrix i' i' ℂ} (hσ : σ.PosSemidef) (hσtrace : trace σ = 1)
    {P : Matrix m m ℂ} (hP : P ∈ densityPrefixGrams F) :
    intervalGramTransfer A σ P ∈ densityPrefixGrams
      (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2) := by
  rcases hP with ⟨ρ, hρ, hρtrace, rfl⟩
  refine ⟨ρ ⊗ₖ σ, hρ.kronecker hσ, ?_, ?_⟩
  · rw [trace_kronecker, hρtrace, hσtrace, one_mul]
  · exact prefixInputGram_concat F A ρ σ

/-- Interval transfer maps the full real affine hull of prefix Grams into
the hull of the longer prefix. Negative affine coefficients are allowed;
the interval input is an arbitrary density matrix. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem intervalGramTransfer_mem_prefixGramAffineHull_concat
    {o' i' n : Type*} [Fintype o'] [Fintype i']
    (F : o → i → Matrix Unit m ℂ) (A : o' → i' → Matrix m n ℂ)
    {σ : Matrix i' i' ℂ} (hσ : σ.PosSemidef) (hσtrace : trace σ = 1)
    {P : Matrix m m ℂ} (hP : P ∈ prefixGramAffineHull F) :
    intervalGramTransfer A σ P ∈ prefixGramAffineHull
      (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2) := by
  let T := intervalGramTransferAffineMap A σ
  have himage : T '' densityPrefixGrams F ⊆ densityPrefixGrams
      (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2) := by
    rintro _ ⟨X, hX, rfl⟩
    exact intervalGramTransfer_mem_densityPrefixGrams_concat F A hσ hσtrace hX
  have hspan : (prefixGramAffineHull F).map T ≤ prefixGramAffineHull
      (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2) := by
    rw [prefixGramAffineHull, AffineSubspace.map_span, prefixGramAffineHull]
    exact affineSpan_mono ℝ himage
  exact hspan (AffineSubspace.mem_map_of_mem T hP)

end MPUCircuit
