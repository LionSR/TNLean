/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceMulBound
import QICLean.Analysis.TraceDistance
import QICLean.Channel.PartialTrace
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalCorrelation

/-!
# Expectations from the approximate factorization of the ground-state projector

Let `O_B`, `O_L`, `O_R` be positive semidefinite contractions with
`‖O_B O_L O_R − |Ψ⟩⟨Ψ|‖ ≤ ε`, the conclusion of Hastings' Lemma 1. In the proof of the area law
(arXiv:0705.2024v4, lines 413–446) the expectations of these operators in the ground state `Ψ`
are close to one, and so is the expectation `y` of `O_L O_R` in the product of the two marginals
of `Ψ`. This file proves those bounds.

**Local fix (explicit constants):** line 446 asserts `y ≥ 1 − 2ε` for the product state without
derivation; `one_sub_four_mul_le_re_trace_kronecker_marginals_mul` proves the derivable
`y ≥ (1 − ε)⁴ ≥ 1 − 4ε`, which moves only the unnamed constant `C₂`. Documented in
`docs/paper-gaps/hastings07_relent_constants.tex`.

## Main results

* `sq_one_sub_le_re_inner_boundary`: `⟨Ψ, O_B Ψ⟩ ≥ (1 − ε)²`, the bound of line 422.
* `sq_one_sub_le_re_inner_left`, `sq_one_sub_le_re_inner_right`: the same for `O_L`, `O_R`.
* `one_sub_four_mul_le_re_trace_kronecker_marginals_mul`: `y ≥ 1 − 4ε` for `O_L = M_L ⊗ 1`,
  `O_R = 1 ⊗ M_R` and the product `ρ_L ⊗ ρ_R` of the two marginals.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 413–446.
-/

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator MatrixOrder Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The expectation `⟪x, A y⟫` as a dot product of coordinate vectors. -/
theorem inner_toEuclideanCLM_eq_dotProduct (A : Matrix n n ℂ) (x y : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanCLM (n := n) (𝕜 := ℂ) A y⟫_ℂ = star x.ofLp ⬝ᵥ (A *ᵥ y.ofLp) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM, dotProduct_comm]

/-- Real parts of expectations are monotone in the Loewner order. -/
theorem re_inner_toEuclideanCLM_mono {A B : Matrix n n ℂ} (hAB : A ≤ B)
    (x : EuclideanSpace ℂ n) :
    (⟪x, toEuclideanCLM (n := n) (𝕜 := ℂ) A x⟫_ℂ).re ≤
      (⟪x, toEuclideanCLM (n := n) (𝕜 := ℂ) B x⟫_ℂ).re := by
  have h := (Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg x.ofLp
  rw [sub_mulVec, dotProduct_sub] at h
  rw [inner_toEuclideanCLM_eq_dotProduct, inner_toEuclideanCLM_eq_dotProduct]
  have h' := (Complex.le_def.mp h).1
  rw [Complex.zero_re, Complex.sub_re] at h'
  linarith

/-- For a positive semidefinite contraction `A`, `‖A x‖² ≤ re ⟪x, A x⟫`. -/
theorem PosSemidef.norm_sq_toEuclideanCLM_le_re_inner {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : ‖A‖ ≤ 1) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 ≤
      (⟪x, toEuclideanCLM (n := n) (𝕜 := ℂ) A x⟫_ℂ).re := by
  have hsq : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ^ 2 =
      (⟪x, toEuclideanCLM (n := n) (𝕜 := ℂ) (A * A) x⟫_ℂ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hA.isHermitian.inner_toEuclideanCLM_left, map_mul,
      mul_apply_eq_comp]
    rfl
  rw [hsq]
  exact re_inner_toEuclideanCLM_mono
    (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hA.nonneg hA1) x

/-- A contraction does not increase the norm of a vector. -/
theorem norm_toEuclideanCLM_le_of_norm_le_one {A : Matrix n n ℂ} (hA1 : ‖A‖ ≤ 1)
    (x : EuclideanSpace ℂ n) : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ≤ ‖x‖ :=
  ((toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm x).trans
    (mul_le_of_le_one_left (norm_nonneg x) hA1)

/-- The rank-one projection `|Ψ⟩⟨Ψ|` fixes the unit vector `Ψ`. -/
theorem toEuclideanCLM_vecMulVec_star_self_of_norm_eq_one {Ψ : EuclideanSpace ℂ n}
    (hΨ : ‖Ψ‖ = 1) :
    toEuclideanCLM (n := n) (𝕜 := ℂ) (vecMulVec Ψ.ofLp (star Ψ.ofLp)) Ψ = Ψ := by
  apply WithLp.ofLp_injective
  have h : star Ψ.ofLp ⬝ᵥ Ψ.ofLp = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hΨ]
    norm_num
  rw [ofLp_toEuclideanCLM, vecMulVec_mulVec, h, MulOpposite.op_one, one_smul]

end Matrix

namespace TNLean.MPS.AreaLaw.Hastings

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `‖O_B Z - |Ψ⟩⟨Ψ|‖ ≤ ε` for a unit vector `Ψ`, then `‖O_B Z Ψ - Ψ‖ ≤ ε`.
Hastings, arXiv:0705.2024v4, `law16.tex` lines 413–446. -/
theorem norm_toEuclideanCLM_mul_sub_le {Ψ : EuclideanSpace ℂ n} (hΨ : ‖Ψ‖ = 1)
    {OB Z : Matrix n n ℂ} {ε : ℝ} (hprod : ‖OB * Z - vecMulVec Ψ.ofLp (star Ψ.ofLp)‖ ≤ ε) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) OB (toEuclideanCLM (n := n) (𝕜 := ℂ) Z Ψ) - Ψ‖ ≤ ε := by
  set X := OB * Z - vecMulVec Ψ.ofLp (star Ψ.ofLp)
  have e : toEuclideanCLM (n := n) (𝕜 := ℂ) X Ψ =
      toEuclideanCLM (n := n) (𝕜 := ℂ) OB (toEuclideanCLM (n := n) (𝕜 := ℂ) Z Ψ) - Ψ := by
    rw [map_sub, map_mul, _root_.sub_apply, mul_apply_eq_comp,
      toEuclideanCLM_vecMulVec_star_self_of_norm_eq_one hΨ]
  rw [← e]
  calc ‖toEuclideanCLM (n := n) (𝕜 := ℂ) X Ψ‖ ≤ ‖toEuclideanCLM (n := n) (𝕜 := ℂ) X‖ * ‖Ψ‖ :=
        (toEuclideanCLM (n := n) (𝕜 := ℂ) X).le_opNorm Ψ
    _ = ‖X‖ := by rw [hΨ, mul_one]; rfl
    _ ≤ ε := hprod

/-- From the product bound, the operator `Z` keeps the norm of `Ψ` at least `1 - ε`,
since `O_B` is a contraction.
Hastings, arXiv:0705.2024v4, `law16.tex` lines 413–446. -/
theorem one_sub_le_norm_toEuclideanCLM {Ψ : EuclideanSpace ℂ n} (hΨ : ‖Ψ‖ = 1)
    {OB Z : Matrix n n ℂ} (hOB1 : ‖OB‖ ≤ 1) {ε : ℝ}
    (hprod : ‖OB * Z - vecMulVec Ψ.ofLp (star Ψ.ofLp)‖ ≤ ε) :
    1 - ε ≤ ‖toEuclideanCLM (n := n) (𝕜 := ℂ) Z Ψ‖ := by
  have h1 := norm_toEuclideanCLM_mul_sub_le hΨ hprod
  have h2 := norm_toEuclideanCLM_le_of_norm_le_one hOB1 (toEuclideanCLM (n := n) (𝕜 := ℂ) Z Ψ)
  have h3 := norm_sub_norm_le Ψ (toEuclideanCLM (n := n) (𝕜 := ℂ) OB
    (toEuclideanCLM (n := n) (𝕜 := ℂ) Z Ψ))
  rw [norm_sub_rev, hΨ] at h3
  linarith

/-- From `‖O_B O_L O_R - |Ψ⟩⟨Ψ|‖ ≤ ε`, the vector `O_L O_R Ψ` has norm at least `1 - ε`.
Hastings, arXiv:0705.2024v4, `law16.tex` lines 413–446. -/
theorem one_sub_le_norm_toEuclideanCLM_mul {Ψ : EuclideanSpace ℂ n} (hΨ : ‖Ψ‖ = 1)
    {OB OL OR : Matrix n n ℂ} (hOB1 : ‖OB‖ ≤ 1) {ε : ℝ}
    (hprod : ‖OB * OL * OR - vecMulVec Ψ.ofLp (star Ψ.ofLp)‖ ≤ ε) :
    1 - ε ≤ ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (OL * OR) Ψ‖ := by
  rw [mul_assoc] at hprod
  exact one_sub_le_norm_toEuclideanCLM hΨ hOB1 hprod

/-- From the product bound, the expectation of the right factor `O_R` is at least `(1 - ε)²`.
Hastings, arXiv:0705.2024v4, `law16.tex` lines 413–446. -/
theorem sq_one_sub_le_re_inner_right {Ψ : EuclideanSpace ℂ n} (hΨ : ‖Ψ‖ = 1)
    {OB OL OR : Matrix n n ℂ} (hOB1 : ‖OB‖ ≤ 1) (hOL1 : ‖OL‖ ≤ 1)
    (hOR : OR.PosSemidef) (hOR1 : ‖OR‖ ≤ 1) {ε : ℝ} (hε : ε ≤ 1)
    (hprod : ‖OB * OL * OR - vecMulVec Ψ.ofLp (star Ψ.ofLp)‖ ≤ ε) :
    (1 - ε) ^ 2 ≤ (⟪Ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) OR Ψ⟫_ℂ).re := by
  have h1 := one_sub_le_norm_toEuclideanCLM_mul hΨ hOB1 hprod
  rw [map_mul, mul_apply_eq_comp] at h1
  have h2 := h1.trans (norm_toEuclideanCLM_le_of_norm_le_one hOL1
    (toEuclideanCLM (n := n) (𝕜 := ℂ) OR Ψ))
  exact (pow_le_pow_left₀ (by linarith) h2 2).trans
    (hOR.norm_sq_toEuclideanCLM_le_re_inner hOR1 Ψ)

/-- From the product bound with commuting `O_L` and `O_R`, the expectation of the left factor
`O_L` is at least `(1 - ε)²`.
Hastings, arXiv:0705.2024v4, `law16.tex` lines 413–446. -/
theorem sq_one_sub_le_re_inner_left {Ψ : EuclideanSpace ℂ n} (hΨ : ‖Ψ‖ = 1)
    {OB OL OR : Matrix n n ℂ} (hOB1 : ‖OB‖ ≤ 1) (hOL : OL.PosSemidef) (hOL1 : ‖OL‖ ≤ 1)
    (hOR1 : ‖OR‖ ≤ 1) (hcomm : Commute OL OR) {ε : ℝ} (hε : ε ≤ 1)
    (hprod : ‖OB * OL * OR - vecMulVec Ψ.ofLp (star Ψ.ofLp)‖ ≤ ε) :
    (1 - ε) ^ 2 ≤ (⟪Ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) OL Ψ⟫_ℂ).re := by
  rw [mul_assoc, hcomm.eq, ← mul_assoc] at hprod
  exact sq_one_sub_le_re_inner_right hΨ hOB1 hOR1 hOL hOL1 hε hprod

/-- From the product bound, the expectation of `O_B` is at least `(1 - ε)²`.
Hastings, arXiv:0705.2024v4, `law16.tex` lines 413–446 (the first expectation bound). -/
theorem sq_one_sub_le_re_inner_boundary {Ψ : EuclideanSpace ℂ n} (hΨ : ‖Ψ‖ = 1)
    {OB OL OR : Matrix n n ℂ} (hOB : OB.PosSemidef) (hOB1 : ‖OB‖ ≤ 1) (hOL1 : ‖OL‖ ≤ 1)
    (hOR1 : ‖OR‖ ≤ 1) {ε : ℝ} (hε : ε ≤ 1)
    (hprod : ‖OB * OL * OR - vecMulVec Ψ.ofLp (star Ψ.ofLp)‖ ≤ ε) :
    (1 - ε) ^ 2 ≤ (⟪Ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) OB Ψ⟫_ℂ).re := by
  set T := toEuclideanCLM (n := n) (𝕜 := ℂ)
  set y := T (OL * OR) Ψ
  rw [mul_assoc] at hprod
  have hy : ‖y‖ ≤ 1 := by
    have := norm_toEuclideanCLM_le_of_norm_le_one
      ((l2_opNorm_mul OL OR).trans
        ((mul_le_mul hOL1 hOR1 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))) Ψ
    rwa [hΨ] at this
  have h1 : ‖T OB y - Ψ‖ ≤ ε := norm_toEuclideanCLM_mul_sub_le hΨ hprod
  have hsplit : ⟪Ψ, T OB y⟫_ℂ = 1 + ⟪Ψ, T OB y - Ψ⟫_ℂ := by
    rw [inner_sub_right, inner_self_eq_norm_sq_to_K, hΨ]
    push_cast
    ring
  have h2 : ‖⟪Ψ, T OB y - Ψ⟫_ℂ‖ ≤ ε := by
    have := norm_inner_le_norm (𝕜 := ℂ) Ψ (T OB y - Ψ)
    rw [hΨ, one_mul] at this
    exact this.trans h1
  have h3 : 1 - ε ≤ ‖⟪Ψ, T OB y⟫_ℂ‖ := by
    have h4 := norm_sub_norm_le (1 : ℂ) (-⟪Ψ, T OB y - Ψ⟫_ℂ)
    rw [sub_neg_eq_add, ← hsplit, norm_neg, norm_one] at h4
    linarith
  have h5 : ‖⟪Ψ, T OB y⟫_ℂ‖ ≤ ‖T OB Ψ‖ := by
    rw [← hOB.isHermitian.inner_toEuclideanCLM_left]
    exact (norm_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hy)
  exact (pow_le_pow_left₀ (by linarith) (h3.trans h5) 2).trans
    (hOB.norm_sq_toEuclideanCLM_le_re_inner hOB1 Ψ)

variable {l r : Type*} [Fintype l] [DecidableEq l] [Fintype r] [DecidableEq r]

/-- The expectation in a pure state is the trace against its projection:
`tr (|Ψ⟩⟨Ψ| A) = ⟪Ψ, A Ψ⟫`. -/
theorem trace_vecMulVec_star_mul (Ψ : EuclideanSpace ℂ n) (A : Matrix n n ℂ) :
    (vecMulVec Ψ.ofLp (star Ψ.ofLp) * A).trace =
      ⟪Ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A Ψ⟫_ℂ := by
  rw [vecMulVec_mul, trace_vecMulVec, inner_toEuclideanCLM_eq_dotProduct, dotProduct_comm,
    dotProduct_mulVec]

/-- The product of the two marginals of `|Ψ⟩⟨Ψ|` gives the product of the two one-sided
expectations: `tr ((ρ_L ⊗ ρ_R)(O_L O_R)) = tr (ρ_L M_L) tr (ρ_R M_R) = ⟨O_L⟩ ⟨O_R⟩`,
where `O_L = M_L ⊗ 1` and `O_R = 1 ⊗ M_R`.
Hastings, arXiv:0705.2024v4, `law16.tex` lines 413–446. -/
theorem trace_kronecker_marginals_mul (Ψ : EuclideanSpace ℂ (l × r)) (ML : Matrix l l ℂ)
    (MR : Matrix r r ℂ) :
    ((partialTraceRight (vecMulVec Ψ.ofLp (star Ψ.ofLp)) ⊗ₖ
        partialTraceLeft (vecMulVec Ψ.ofLp (star Ψ.ofLp))) *
        ((ML ⊗ₖ (1 : Matrix r r ℂ)) * ((1 : Matrix l l ℂ) ⊗ₖ MR))).trace =
      (partialTraceRight (vecMulVec Ψ.ofLp (star Ψ.ofLp)) * ML).trace *
        (partialTraceLeft (vecMulVec Ψ.ofLp (star Ψ.ofLp)) * MR).trace ∧
    (partialTraceRight (vecMulVec Ψ.ofLp (star Ψ.ofLp)) * ML).trace *
        (partialTraceLeft (vecMulVec Ψ.ofLp (star Ψ.ofLp)) * MR).trace =
      ⟪Ψ, toEuclideanCLM (n := l × r) (𝕜 := ℂ) (ML ⊗ₖ (1 : Matrix r r ℂ)) Ψ⟫_ℂ *
        ⟪Ψ, toEuclideanCLM (n := l × r) (𝕜 := ℂ)
          ((1 : Matrix l l ℂ) ⊗ₖ MR) Ψ⟫_ℂ := by
  refine ⟨?_, ?_⟩
  · rw [← mul_kronecker_mul, mul_one, one_mul, ← mul_kronecker_mul, trace_kronecker]
  · rw [trace_partialTraceRight_mul, trace_partialTraceLeft_mul, trace_vecMulVec_star_mul,
      trace_vecMulVec_star_mul]

/-- **The product-of-marginals bound.** If `M_L`, `M_R`, `O_B` are positive semidefinite
contractions and `‖O_B O_L O_R - |Ψ⟩⟨Ψ|‖ ≤ ε` with `O_L = M_L ⊗ 1` and `O_R = 1 ⊗ M_R`, then the
product state `σ = ρ_L ⊗ ρ_R` of the two marginals of `Ψ` satisfies
`1 - 4 ε ≤ re tr (σ O_L O_R)`.
Hastings, arXiv:0705.2024v4, `law16.tex` lines 413–446. -/
theorem one_sub_four_mul_le_re_trace_kronecker_marginals_mul {Ψ : EuclideanSpace ℂ (l × r)}
    (hΨ : ‖Ψ‖ = 1) {ML : Matrix l l ℂ} {MR : Matrix r r ℂ} {OB : Matrix (l × r) (l × r) ℂ}
    (hML : ML.PosSemidef) (hML1 : ‖ML‖ ≤ 1) (hMR : MR.PosSemidef) (hMR1 : ‖MR‖ ≤ 1)
    (hOB1 : ‖OB‖ ≤ 1) {ε : ℝ}
    (hprod : ‖OB * (ML ⊗ₖ (1 : Matrix r r ℂ)) * ((1 : Matrix l l ℂ) ⊗ₖ MR) -
      vecMulVec Ψ.ofLp (star Ψ.ofLp)‖ ≤ ε) :
    1 - 4 * ε ≤ ((partialTraceRight (vecMulVec Ψ.ofLp (star Ψ.ofLp)) ⊗ₖ
        partialTraceLeft (vecMulVec Ψ.ofLp (star Ψ.ofLp))) *
        ((ML ⊗ₖ (1 : Matrix r r ℂ)) * ((1 : Matrix l l ℂ) ⊗ₖ MR))).trace.re := by
  obtain ⟨h1, h2⟩ := trace_kronecker_marginals_mul Ψ ML MR
  rw [h1, h2]
  set OL := ML ⊗ₖ (1 : Matrix r r ℂ)
  set OR := (1 : Matrix l l ℂ) ⊗ₖ MR
  have hOL : OL.PosSemidef := hML.kronecker PosSemidef.one
  have hOR : OR.PosSemidef := PosSemidef.one.kronecker hMR
  have hOL1 : ‖OL‖ ≤ 1 := (l2_opNorm_kronecker_one_le ML).trans hML1
  have hOR1 : ‖OR‖ ≤ 1 := (l2_opNorm_one_kronecker_le MR).trans hMR1
  have hcomm : Commute OL OR := by
    simp only [Commute, SemiconjBy, OL, OR, ← mul_kronecker_mul, mul_one, one_mul]
  -- both expectations are nonnegative reals
  have hreal : ∀ {A : Matrix (l × r) (l × r) ℂ}, A.PosSemidef →
      0 ≤ ⟪Ψ, toEuclideanCLM (n := l × r) (𝕜 := ℂ) A Ψ⟫_ℂ := fun hA ↦ by
    rw [inner_toEuclideanCLM_eq_dotProduct]
    exact hA.dotProduct_mulVec_nonneg _
  have hL := hreal hOL
  have hR := hreal hOR
  set a := ⟪Ψ, toEuclideanCLM (n := l × r) (𝕜 := ℂ) OL Ψ⟫_ℂ
  set b := ⟪Ψ, toEuclideanCLM (n := l × r) (𝕜 := ℂ) OR Ψ⟫_ℂ
  have hai := (Complex.nonneg_iff.mp hL).2
  have hbi := (Complex.nonneg_iff.mp hR).2
  have hre : (a * b).re = a.re * b.re := by
    rw [Complex.mul_re, ← hai, ← hbi, mul_zero, sub_zero]
  have ha0 : 0 ≤ a.re := (Complex.nonneg_iff.mp hL).1
  have hb0 : 0 ≤ b.re := (Complex.nonneg_iff.mp hR).1
  rw [hre]
  rcases le_or_gt ε 1 with hε | hε
  · have ha := sq_one_sub_le_re_inner_left hΨ hOB1 hOL hOL1 hOR1 hcomm hε hprod
    have hb := sq_one_sub_le_re_inner_right hΨ hOB1 hOL1 hOR hOR1 hε hprod
    have hab : (1 - ε) ^ 2 * (1 - ε) ^ 2 ≤ a.re * b.re :=
      mul_le_mul ha hb (sq_nonneg _) ha0
    nlinarith [sq_nonneg ε, sq_nonneg (1 - ε), mul_nonneg (sq_nonneg ε) (sq_nonneg (ε - 2))]
  · nlinarith [mul_nonneg ha0 hb0]

end TNLean.MPS.AreaLaw.Hastings
