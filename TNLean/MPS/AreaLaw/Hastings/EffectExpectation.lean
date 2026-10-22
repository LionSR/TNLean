/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceMulBound
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import QICLean.Analysis.PosSemidefCommute

/-!
# The expectation of `O_B` in the product of the marginals

In Hastings' proof of the one-dimensional area law (arXiv:0705.2024v4, lines 440–461), the
operator `O_B` of Lemma 1 has expectation at least `1 − 2ε` in the ground state but small
expectation `x` in the product `σ = ρ_{1,j} ⊗ ρ_{j+1,N}` of its two marginals, eq. `xbd`. The
proof bounds `x` by a Cauchy–Schwarz inequality for the expectation of a product of two
operators (lines 449–454). This file proves that inequality for density matrices and the bound
on `x`, with Lemma 1's conclusion and the bounds on `tr(σ P₀)` and on the expectation `y` of
`O_L O_R` as hypotheses.

**Local fix (explicit constants):** the hypothesis on `y` is `y ≥ 1 − 4ε`, the bound derivable
for the product state, where line 446 asserts `y ≥ 1 − 2ε` without derivation; and `ε ≤ 1/68`
gives the explicit `x ≤ 36 ε`. Documented in `docs/paper-gaps/hastings07_relent_constants.tex`.

## Main results

* `Matrix.PosSemidef.sub_sqrt_mul_sqrt_le_re_trace_mul_mul`: for a density matrix `σ` and
  positive semidefinite contractions `A`, `B`, with `a = tr(σA)` and `b = tr(σB)`,
  `a b − √(a − a²) √(b − b²) ≤ Re tr(σ A B)`.
* `TNLean.MPS.AreaLaw.Hastings.re_trace_mul_le_of_projector_factorization`: eq. `xbd` in the
  form `x ≤ 36 ε`.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 440–461.
-/

open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Cauchy–Schwarz for the expectation in a positive semidefinite matrix `σ`: for Hermitian
`X` and `Y`, `|Re tr(σ X Y)| ≤ √(Re tr(σ X X)) √(Re tr(σ Y Y))`. -/
theorem PosSemidef.abs_re_trace_mul_mul_le {σ X Y : Matrix n n ℂ} (hσ : σ.PosSemidef)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    |(σ * X * Y).trace.re| ≤
      Real.sqrt (σ * X * X).trace.re * Real.sqrt (σ * Y * Y).trace.re := by
  let _ := σ.toMatrixSeminormedAddCommGroup hσ
  let _ := σ.toMatrixInnerProductSpace hσ
  have hinner (Z W : Matrix n n ℂ) (hZ : Z.IsHermitian) :
      inner ℂ Z W = (σ * Z * W).trace := by
    change (W * σ * Zᴴ).trace = _
    rw [hZ.eq, Matrix.mul_assoc, trace_mul_comm]
  have hnorm (Z : Matrix n n ℂ) (hZ : Z.IsHermitian) :
      ‖Z‖ = Real.sqrt (σ * Z * Z).trace.re := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner Z Z hZ]
    rfl
  calc |(σ * X * Y).trace.re| ≤ ‖(σ * X * Y).trace‖ := Complex.abs_re_le_norm _
    _ = ‖inner ℂ X Y‖ := by rw [hinner X Y hX]
    _ ≤ ‖X‖ * ‖Y‖ := norm_inner_le_norm X Y
    _ = _ := by rw [hnorm X hX, hnorm Y hY]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- For a positive semidefinite `σ` and a positive semidefinite contraction `A`,
`Re tr(σ A A) ≤ Re tr(σ A)`, since `A A ≤ A`. -/
theorem PosSemidef.re_trace_mul_mul_self_le {σ A : Matrix n n ℂ} (hσ : σ.PosSemidef)
    (hA : A.PosSemidef) (hA1 : ‖A‖ ≤ 1) :
    (σ * A * A).trace.re ≤ (σ * A).trace.re := by
  have hle : A * A ≤ A := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hA.nonneg hA1
  have h := (Complex.nonneg_iff.mp (hσ.trace_mul_nonneg (Matrix.le_iff.mp hle))).1
  rw [Matrix.mul_sub, trace_sub, Complex.sub_re, ← Matrix.mul_assoc] at h
  simpa using h

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- Cauchy–Schwarz lower bound for the expectation of a product of two positive semidefinite
contractions `A` and `B` in a density matrix `σ`: with `a = Re tr(σ A)` and `b = Re tr(σ B)`,
`a b - √(a - a²) √(b - b²) ≤ Re tr(σ A B)`.

Source: Hastings, arXiv:0705.2024v4, `law16.tex` lines 449–454. -/
theorem PosSemidef.sub_sqrt_mul_sqrt_le_re_trace_mul_mul {σ A B : Matrix n n ℂ}
    (hσ : σ.PosSemidef) (hσ1 : σ.trace = 1)
    (hA : A.PosSemidef) (hA1 : ‖A‖ ≤ 1) (hB : B.PosSemidef) (hB1 : ‖B‖ ≤ 1) :
    (σ * A).trace.re * (σ * B).trace.re -
        Real.sqrt ((σ * A).trace.re - (σ * A).trace.re ^ 2) *
          Real.sqrt ((σ * B).trace.re - (σ * B).trace.re ^ 2) ≤
      (σ * A * B).trace.re := by
  set a := (σ * A).trace.re with ha
  set b := (σ * B).trace.re with hb
  have hX : (A - a • (1 : Matrix n n ℂ)).IsHermitian :=
    hA.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all a))
  have hY : (B - b • (1 : Matrix n n ℂ)).IsHermitian :=
    hB.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all b))
  have hσre : σ.trace.re = 1 := by rw [hσ1, Complex.one_re]
  have hXY : (σ * (A - a • 1) * (B - b • 1)).trace.re = (σ * A * B).trace.re - a * b := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      trace_sub, trace_smul, Complex.sub_re, Complex.real_smul, Complex.re_ofReal_mul,
      ← ha, ← hb, hσre]
    ring
  have hXX : (σ * (A - a • 1) * (A - a • 1)).trace.re = (σ * A * A).trace.re - a ^ 2 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      trace_sub, trace_smul, Complex.sub_re, Complex.real_smul, Complex.re_ofReal_mul,
      ← ha, hσre]
    ring
  have hYY : (σ * (B - b • 1) * (B - b • 1)).trace.re = (σ * B * B).trace.re - b ^ 2 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      trace_sub, trace_smul, Complex.sub_re, Complex.real_smul, Complex.re_ofReal_mul,
      ← hb, hσre]
    ring
  have hcs := hσ.abs_re_trace_mul_mul_le hX hY
  rw [hXY, hXX, hYY] at hcs
  have hAA := hσ.re_trace_mul_mul_self_le hA hA1
  have hBB := hσ.re_trace_mul_mul_self_le hB hB1
  have hsq : Real.sqrt ((σ * A * A).trace.re - a ^ 2) * Real.sqrt ((σ * B * B).trace.re - b ^ 2)
      ≤ Real.sqrt (a - a ^ 2) * Real.sqrt (b - b ^ 2) := by
    gcongr
  linarith [neg_abs_le ((σ * A * B).trace.re - a * b)]


open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The expectation of a positive semidefinite contraction in a density matrix lies in
`[0, 1]`. -/
theorem PosSemidef.re_trace_mul_mem_Icc {σ A : Matrix n n ℂ} (hσ : σ.PosSemidef)
    (hσ1 : σ.trace = 1) (hA : A.PosSemidef) (hA1 : ‖A‖ ≤ 1) :
    0 ≤ (σ * A).trace.re ∧ (σ * A).trace.re ≤ 1 := by
  refine ⟨(Complex.nonneg_iff.mp (hσ.trace_mul_nonneg hA)).1, ?_⟩
  have h := hσ.norm_trace_mul_le A
  rw [hσ1] at h
  calc (σ * A).trace.re ≤ ‖(σ * A).trace‖ := Complex.re_le_norm _
    _ ≤ _ := h
    _ ≤ 1 := by simpa using hA1

end Matrix

namespace TNLean.MPS.AreaLaw.Hastings

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Eq. `xbd`.** Hastings, arXiv:0705.2024v4, lines 440–461. Let `O_B`, `O_L`, `O_R` be positive
semidefinite contractions, `O_L` and `O_R` commuting, with `‖O_B O_L O_R − P₀‖ ≤ ε` for a
rank-one projector `P₀` (the conclusion of Lemma 1). Let `σ` be a density matrix whose overlap
`tr(σ P₀)` with `P₀` is at most `2ε` (lines 484–490), and in which `O_L O_R` has expectation
`y ≥ 1 − 4ε`. If `ε ≤ 1/68`, then `x = tr(σ O_B) ≤ 36 ε`. The proof is the Cauchy–Schwarz step of
lines 449–454: `x y − √(x − x²) √(y − y²) ≤ tr(σ O_B O_L O_R) ≤ tr(σ P₀) + ε`. -/
theorem re_trace_mul_le_of_projector_factorization {σ OB OL OR P : Matrix n n ℂ} {ε : ℝ}
    (hσ : σ.PosSemidef) (hσ1 : σ.trace = 1)
    (hOB : OB.PosSemidef) (hOL : OL.PosSemidef) (hOR : OR.PosSemidef)
    (hOB1 : ‖OB‖ ≤ 1) (hOL1 : ‖OL‖ ≤ 1) (hOR1 : ‖OR‖ ≤ 1) (hLR : Commute OL OR)
    (hprod : ‖OB * OL * OR - P‖ ≤ ε) (hP : (σ * P).trace.re ≤ 2 * ε)
    (hy : 1 - 4 * ε ≤ (σ * (OL * OR)).trace.re) (hε : ε ≤ 1 / 68) :
    (σ * OB).trace.re ≤ 36 * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hprod
  have hZ : (OL * OR).PosSemidef := hOL.mul_of_commute hOR hLR
  have hZ1 : ‖OL * OR‖ ≤ 1 :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg OL, norm_nonneg OR])
  set x := (σ * OB).trace.re
  set y := (σ * (OL * OR)).trace.re
  have hx := hσ.re_trace_mul_mem_Icc hσ1 hOB hOB1
  have hyI := hσ.re_trace_mul_mem_Icc hσ1 hZ hZ1
  have hcov := hσ.sub_sqrt_mul_sqrt_le_re_trace_mul_mul hσ1 hOB hOB1 hZ hZ1
  -- `tr(σ O_B O_L O_R) ≤ tr(σ P₀) + ε`
  have hdiff : (σ * OB * (OL * OR)).trace.re ≤ (σ * P).trace.re + ε := by
    have h := hσ.norm_trace_mul_le (OB * OL * OR - P)
    rw [hσ1, Complex.one_re, one_mul] at h
    have e : (σ * OB * (OL * OR)).trace.re =
        (σ * (OB * OL * OR - P)).trace.re + (σ * P).trace.re := by
      rw [Matrix.mul_sub, trace_sub, Complex.sub_re]
      simp only [Matrix.mul_assoc]
      ring
    rw [e]
    linarith [Complex.re_le_norm (σ * (OB * OL * OR - P)).trace]
  -- `√(x − x²) ≤ √x` and `√(y − y²) ≤ 2√ε`
  have hsx : Real.sqrt (x - x ^ 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
  have hsy : Real.sqrt (y - y ^ 2) ≤ 2 * Real.sqrt ε := by
    rw [show 2 * Real.sqrt ε = Real.sqrt (4 * ε) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsx0 := Real.sqrt_nonneg x
  have hse0 := Real.sqrt_nonneg ε
  have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.1
  have hee : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε0
  have hprod' : Real.sqrt (x - x ^ 2) * Real.sqrt (y - y ^ 2) ≤ Real.sqrt x * (2 * Real.sqrt ε) :=
    mul_le_mul hsx hsy (Real.sqrt_nonneg _) hsx0
  -- `x (1 − 4ε) ≤ 3ε + 2 √ε √x`, hence `√x ≤ 6 √ε`
  have hmain : x * (1 - 4 * ε) ≤ 3 * ε + 2 * Real.sqrt ε * Real.sqrt x := by nlinarith
  by_contra hcon
  rw [not_le] at hcon
  have ht : 6 * Real.sqrt ε < Real.sqrt x := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  nlinarith

end TNLean.MPS.AreaLaw.Hastings
