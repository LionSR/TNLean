/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.SingularValues
import TNLean.MPS.ParentHamiltonian.FNWBoundaryEstimate

/-!
# FNW lower boundary constant

This module formalizes the lower boundary constant in Fannes--Nachtergaele--Werner,
*Communications in Mathematical Physics* 144 (1992), 443--490, Lemma 5.3.
For the boundary map \(F_N\), the source constant is

\[
  a_-(N)=\inf_{B\ne 0}\frac{\lVert F_N(B)\rVert^2}{\lVert B\rVert_\rho^2}.
\]

Equation (5.9) gives \(1-a(N)\le a_-(N)\). Stationarity of the faithful density
and the exact boundary recursion show that \(a_-(N)\) is nondecreasing.
No finite-Gram, singular-value, or periodic-chain estimate is used here.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- FNW 1992, equation (5.9), with its right-hand side written using the source
mixing quantity \(a(N)\). -/
theorem norm_inner_fnwBoundaryMapCLM_sub_rhoWeighted_le_fnwMixingQuantity
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (N : ℕ) (B C : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwBoundaryMapCLM ρ hρ A N B)
        (fnwBoundaryMapCLM ρ hρ A N C) - inner ℂ B C‖ ≤
      fnwMixingQuantity ρ hρ A htr N * ‖B‖ * ‖C‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  simpa only [fnwMixingQuantity, fnwTraceInverseFactor] using
    norm_inner_fnwBoundaryMapCLM_sub_rhoWeighted_le ρ hρ htr A N B C

/-- The diagonal specialization of equation (5.9): the absolute defect of the
boundary norm square is at most \(a(N)\lVert B\rVert_\rho^2\). -/
theorem abs_fnwBoundaryMapCLM_norm_sq_sub_rhoWeighted_norm_sq_le
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (N : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    |‖fnwBoundaryMapCLM ρ hρ A N B‖ ^ 2 - ‖B‖ ^ 2| ≤
      fnwMixingQuantity ρ hρ A htr N * ‖B‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have hbound :=
    norm_inner_fnwBoundaryMapCLM_sub_rhoWeighted_le_fnwMixingQuantity
      ρ hρ htr A N B B
  calc
    |‖fnwBoundaryMapCLM ρ hρ A N B‖ ^ 2 - ‖B‖ ^ 2| =
        ‖((‖fnwBoundaryMapCLM ρ hρ A N B‖ ^ 2 - ‖B‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖inner ℂ (fnwBoundaryMapCLM ρ hρ A N B)
          (fnwBoundaryMapCLM ρ hρ A N B) - inner ℂ B B‖ := by
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      congr 1
      norm_cast
    _ ≤ fnwMixingQuantity ρ hρ A htr N * ‖B‖ * ‖B‖ := hbound
    _ = fnwMixingQuantity ρ hρ A htr N * ‖B‖ ^ 2 := by ring

/-- Equation (5.9) gives the quadratic lower estimate
\((1-a(N))\lVert B\rVert_\rho^2\le\lVert F_N(B)\rVert^2\).
No nonnegativity assumption on \(a(N)\) is needed. -/
theorem one_sub_fnwMixingQuantity_mul_norm_sq_le_fnwBoundaryMapCLM_norm_sq
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (N : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    (1 - fnwMixingQuantity ρ hρ A htr N) * ‖B‖ ^ 2 ≤
      ‖fnwBoundaryMapCLM ρ hρ A N B‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have hbound := abs_le.mp
    (abs_fnwBoundaryMapCLM_norm_sq_sub_rhoWeighted_norm_sq_le
      ρ hρ htr A N B)
  nlinarith only [hbound.1]

/-- The nonzero boundary norm-square ratio whose infimum is the source constant
\(a_-(N)\). -/
noncomputable def fnwBoundaryNormRatio
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ)
    (B : {B : Mat // B ≠ 0}) : ℝ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  exact ‖fnwBoundaryMapCLM ρ hρ A N B.1‖ ^ 2 / ‖B.1‖ ^ 2

/-- The weighted Gram operator \(F_N^*F_N\) on the virtual matrix Hilbert space. -/
noncomputable def fnwBoundaryGram
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    Mat →ₗ[ℂ] Mat := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  exact LinearMap.adjoint (fnwBoundaryMapCLM ρ hρ A N).toLinearMap ∘ₗ
    (fnwBoundaryMapCLM ρ hρ A N).toLinearMap

/-- The boundary norm-square ratio is exactly the Rayleigh quotient of the
weighted Gram operator \(F_N^*F_N\). -/
theorem fnwBoundaryNormRatio_eq_gram_rayleighQuotient
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ)
    (B : Mat) (hB : B ≠ 0) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    fnwBoundaryNormRatio ρ hρ A N ⟨B, hB⟩ =
      RCLike.re (inner ℂ (fnwBoundaryGram ρ hρ A N B) B) / ‖B‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  rw [fnwBoundaryGram]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [LinearMap.adjoint_inner_left]
  simp only [inner_self_eq_norm_sq]
  rfl

/-- The lower boundary constant \(a_-(N)\) from FNW 1992, Lemma 5.3. It is the
infimum of the boundary norm-square ratio over nonzero virtual matrices. -/
noncomputable def fnwLowerBoundaryConstant [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) : ℝ :=
  ⨅ B : {B : Mat // B ≠ 0}, fnwBoundaryNormRatio ρ hρ A N B

/-- The source infimum is the infimum of the Rayleigh quotient of the weighted
Gram operator. -/
theorem fnwLowerBoundaryConstant_eq_gram_rayleigh_iInf [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    fnwLowerBoundaryConstant ρ hρ A N =
      ⨅ B : {B : Mat // B ≠ 0},
        RCLike.re (inner ℂ (fnwBoundaryGram ρ hρ A N B.1) B.1) / ‖B.1‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  rw [fnwLowerBoundaryConstant]
  apply iInf_congr
  intro B
  exact fnwBoundaryNormRatio_eq_gram_rayleighQuotient ρ hρ A N B B.2

/-- The weighted Gram operator is symmetric. -/
theorem fnwBoundaryGram_isSymmetric
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    (fnwBoundaryGram ρ hρ A N).IsSymmetric := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  exact (fnwBoundaryMapCLM ρ hρ A N).toLinearMap.isSymmetric_adjoint_comp_self

/-- FNW's identity \(a_-(N)=\inf\operatorname{spec}(F_N^*F_N)\), packaged
without ordering the complex spectrum: \(a_-(N)\), coerced to \(ℂ\), belongs to
the spectrum of the weighted Gram operator. -/
theorem fnwLowerBoundaryConstant_mem_spectrum_fnwBoundaryGram [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    (fnwLowerBoundaryConstant ρ hρ A N : ℂ) ∈
      spectrum ℂ (fnwBoundaryGram ρ hρ A N) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  rw [fnwLowerBoundaryConstant_eq_gram_rayleigh_iInf]
  exact (fnwBoundaryGram_isSymmetric ρ hρ A N).hasEigenvalue_iInf_of_finiteDimensional

private theorem fnwBoundaryNormRatio_bddBelow [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) :
    BddBelow (Set.range (fnwBoundaryNormRatio ρ hρ A N)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨B, rfl⟩
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The lower boundary constant is at most every nonzero boundary norm-square
ratio. -/
theorem fnwLowerBoundaryConstant_le_ratio [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ)
    (B : Mat) (hB : B ≠ 0) :
    fnwLowerBoundaryConstant ρ hρ A N ≤
      fnwBoundaryNormRatio ρ hρ A N ⟨B, hB⟩ := by
  exact ciInf_le (fnwBoundaryNormRatio_bddBelow ρ hρ A N) ⟨B, hB⟩

/-- Every spectral value of the weighted Gram operator has real part at least
\(a_-(N)\). Together with
`fnwLowerBoundaryConstant_mem_spectrum_fnwBoundaryGram`, this is the ordered
meaning of \(a_-(N)=\inf\operatorname{spec}(F_N^*F_N)\). -/
theorem fnwLowerBoundaryConstant_le_re_of_mem_spectrum_fnwBoundaryGram [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ)
    (z : ℂ) (hz : z ∈ spectrum ℂ (fnwBoundaryGram ρ hρ A N)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    fnwLowerBoundaryConstant ρ hρ A N ≤ z.re := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have heig : Module.End.HasEigenvalue (fnwBoundaryGram ρ hρ A N) z :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz
  have hzreal : (z.re : ℂ) = z :=
    RCLike.conj_eq_iff_re.mp
      ((fnwBoundaryGram_isSymmetric ρ hρ A N).conj_eigenvalue_eq_self heig)
  rw [← hzreal] at heig
  obtain ⟨B, hB⟩ := heig.exists_hasEigenvector
  have hle := fnwLowerBoundaryConstant_le_ratio ρ hρ A N B hB.2
  rw [fnwBoundaryNormRatio_eq_gram_rayleighQuotient ρ hρ A N B hB.2] at hle
  rw [hB.apply_eq_smul] at hle
  simp only [inner_smul_left, inner_self_eq_norm_sq_to_K,
    Complex.conj_ofReal] at hle
  convert hle using 1
  field_simp [norm_ne_zero_iff.mpr hB.2]
  norm_cast
  change z.re * ‖B‖ ^ 2 =
    ((z.re : ℂ) * ((‖B‖ ^ 2 : ℝ) : ℂ)).re
  rw [Complex.mul_re]
  norm_cast
  ring

/-- The source constant gives its universal quadratic lower bound, including at
the zero matrix. -/
theorem fnwLowerBoundaryConstant_mul_norm_sq_le [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    fnwLowerBoundaryConstant ρ hρ A N * ‖B‖ ^ 2 ≤
      ‖fnwBoundaryMapCLM ρ hρ A N B‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  rcases eq_or_ne B 0 with rfl | hB
  · simp
  · exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hB))).mp
      (fnwLowerBoundaryConstant_le_ratio ρ hρ A N B hB)

/-- A real number is at most the lower boundary constant exactly when it is a
universal quadratic lower bound for the boundary map. -/
theorem le_fnwLowerBoundaryConstant_iff [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) (c : ℝ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    c ≤ fnwLowerBoundaryConstant ρ hρ A N ↔
      ∀ B : Mat, c * ‖B‖ ^ 2 ≤ ‖fnwBoundaryMapCLM ρ hρ A N B‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  constructor
  · intro hc B
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans
      (fnwLowerBoundaryConstant_mul_norm_sq_le ρ hρ A N B)
  · intro hc
    let _ : Nonempty {B : Mat // B ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
    apply le_ciInf
    rintro ⟨B, hB⟩
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hB))).mpr (hc B)

/-- FNW 1992, Lemma 5.3: equation (5.9) implies
\(1-a(N)\le a_-(N)\). -/
theorem one_sub_fnwMixingQuantity_le_fnwLowerBoundaryConstant [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (N : ℕ) :
    1 - fnwMixingQuantity ρ hρ A htr N ≤
      fnwLowerBoundaryConstant ρ hρ A N := by
  rw [le_fnwLowerBoundaryConstant_iff]
  exact one_sub_fnwMixingQuantity_mul_norm_sq_le_fnwBoundaryMapCLM_norm_sq
    ρ hρ htr A N

/-- The lower boundary constant is strictly positive whenever the source mixing
quantity is strictly below one. -/
theorem fnwLowerBoundaryConstant_pos [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (N : ℕ)
    (ha : fnwMixingQuantity ρ hρ A htr N < 1) :
    0 < fnwLowerBoundaryConstant ρ hρ A N :=
  lt_of_lt_of_le (sub_pos.mpr ha)
    (one_sub_fnwMixingQuantity_le_fnwLowerBoundaryConstant ρ hρ htr A N)

/-- Stationarity of \(ρ\) gives the weighted right-multiplication identity
\(\sum_\mu\lVert BA^\mu\rVert_ρ^2=\lVert B\rVert_ρ^2\). -/
theorem sum_rhoWeighted_norm_sq_mul_eq
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    ∑ μ : Fin d, ‖B * A μ‖ ^ 2 = ‖B‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  simp_rw [Matrix.rhoWeighted_norm_sq ρ hρ]
  have htrace :
      ∑ μ : Fin d, Matrix.trace (ρ * (B * A μ)ᴴ * (B * A μ)) =
        Matrix.trace (Kraus.transferMap A ρ * Bᴴ * B) := by
    rw [Kraus.transferMap_apply, Matrix.sum_mul, Finset.sum_mul,
      Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro μ _
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm (ρ * (A μ)ᴴ * Bᴴ * B) (A μ)
  calc
    ∑ μ : Fin d, (Matrix.trace (ρ * (B * A μ)ᴴ * (B * A μ))).re =
        (∑ μ : Fin d, Matrix.trace (ρ * (B * A μ)ᴴ * (B * A μ))).re :=
      (map_sum Complex.reCLM
        (fun μ : Fin d ↦ Matrix.trace (ρ * (B * A μ)ᴴ * (B * A μ)))
        Finset.univ).symm
    _ = (Matrix.trace (Kraus.transferMap A ρ * Bᴴ * B)).re :=
      congrArg Complex.re htrace
    _ = (Matrix.trace (ρ * Bᴴ * B)).re := by rw [hρfix]

/-- Stationarity and the exact boundary recursion make the lower boundary
constant nondecreasing in one step. -/
theorem fnwLowerBoundaryConstant_le_succ [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (N : ℕ) :
    fnwLowerBoundaryConstant ρ hρ A N ≤
      fnwLowerBoundaryConstant ρ hρ A (N + 1) := by
  rw [le_fnwLowerBoundaryConstant_iff]
  intro B
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  calc
    fnwLowerBoundaryConstant ρ hρ A N * ‖B‖ ^ 2 =
        ∑ μ : Fin d, fnwLowerBoundaryConstant ρ hρ A N * ‖B * A μ‖ ^ 2 := by
      rw [← Finset.mul_sum, sum_rhoWeighted_norm_sq_mul_eq ρ hρ A hρfix B]
    _ ≤ ∑ μ : Fin d, ‖fnwBoundaryMapCLM ρ hρ A N (B * A μ)‖ ^ 2 :=
      Finset.sum_le_sum fun μ _ ↦
        fnwLowerBoundaryConstant_mul_norm_sq_le ρ hρ A N (B * A μ)
    _ = ‖fnwBoundaryMapCLM ρ hρ A (N + 1) B‖ ^ 2 :=
      (fnwBoundaryMapCLM_norm_sq_succ ρ hρ A N B).symm

/-- The lower boundary constants are nondecreasing with the boundary length. -/
theorem fnwLowerBoundaryConstant_mono [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) :
    Monotone (fnwLowerBoundaryConstant ρ hρ A) := by
  intro N M hNM
  induction M, hNM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hNM ih =>
      exact ih.trans (fnwLowerBoundaryConstant_le_succ ρ hρ A hρfix M)

/-- Primitive-MPS specialization of lower-boundary monotonicity. -/
theorem IsPrimitiveMPS.fnwLowerBoundaryConstant_mono [NeZero D]
    {ρ : Mat} {A : MPSTensor d D} (hP : IsPrimitiveMPS A ρ)
    (hρ : ρ.PosDef) :
    Monotone (fnwLowerBoundaryConstant ρ hρ A) :=
  MPSTensor.fnwLowerBoundaryConstant_mono ρ hρ A hP.fixedPoint_is_fixed

end

end MPSTensor
