/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixSqrt
import TNLean.Analysis.RelativeEntropySupportIntegral

/-!
# Support-domain left-right quadratic forms

For positive-semidefinite matrices \(A\) and \(B\), this file identifies the
two quadratic forms associated with the left-right operator
\[
  X \longmapsto AX+tXB
\]
with the finite spectral integrand for relative entropy. The source in the
first quadratic form is \(A P_B\), where \(P_B\) is the support projection of
\(B\). This projection removes the zero-reference eigenspaces before forming
the quadratic form. Under \(\ker B\subseteq\ker A\), one has \(A P_B=A\), so
the projected form agrees with the unprojected source-\(A\) form.

The generalized inverse used here is the support inverse of the left-right
operator \(A\otimes 1+t(1\otimes B^{\mathsf T})\). It is distinct from the
ordinary inverse of the shifted relative-modular operator
\(t1+A\otimes(B^+)^{\mathsf T}\).

## Main results

* `Matrix.supportLeftRightSuperoperator_posSemidef` proves positivity of the
  left-right operator.
* `Matrix.supportSourceAQuadratic_spectral` and
  `Matrix.supportSourceBQuadratic_spectral` give the two spectral expansions.
* `Matrix.supportRelativeEntropyLeftRightIntegrand_eq_spectral` identifies the
  coordinate-free quadratic expression with the support spectral integrand.

## References

* A. Jenčová and M. B. Ruskai, *A Unified Treatment of Convexity of Relative
  Entropy and Related Trace Functions, with Conditions for Equality*,
  arXiv:0903.2895v4, §2.1 and lines 717--720.
-/

open Set Topology
open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Kronecker matrix representing the left-right operator
\(X\mapsto AX+tXB\) under \(X\mapsto\operatorname{vec}(X^{\mathsf T})\). -/
noncomputable def supportLeftRightSuperoperator
    (A B : Matrix n n ℂ) (t : ℝ) : Matrix (n × n) (n × n) ℂ :=
  A ⊗ₖ (1 : Matrix n n ℂ) +
    t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)

omit [Fintype n] in
/-- The left-right operator \(X\mapsto AX+tXB\) is positive semidefinite
when \(A\) and \(B\) are positive semidefinite and \(t\geq 0\).

This is the positive-semidefinite form of the matrix lift `(intAB)` in
Jenčová--Ruskai, arXiv:0903.2895v4, §2.1, lines 423--427. -/
theorem supportLeftRightSuperoperator_posSemidef
    [Finite n] {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    (supportLeftRightSuperoperator A B t).PosSemidef := by
  letI := Fintype.ofFinite n
  have hI : (1 : Matrix n n ℂ).PosSemidef := Matrix.PosSemidef.one
  exact (hA.kronecker hI).add ((hI.kronecker hB.transpose).smul ht)

/-- The support inverse of the positive-semidefinite left-right operator.
For negative \(t\) it is set to zero; all mathematical statements below use
\(t>0\).

This is the generalized inverse of \(A\otimes 1+t(1\otimes B^{\mathsf T})\),
not the inverse of \(t1+A\otimes(B^+)^{\mathsf T}\). -/
noncomputable def supportLeftRightSupportInv
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) : Matrix (n × n) (n × n) ℂ :=
  if ht : 0 ≤ t then
    (supportLeftRightSuperoperator_posSemidef hA hB ht).supportInv
  else 0

/-- On the nonnegative half-line, the left-right support inverse is the
generalized inverse furnished by positive semidefiniteness. -/
theorem supportLeftRightSupportInv_eq
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    supportLeftRightSupportInv hA hB t =
      (supportLeftRightSuperoperator_posSemidef hA hB ht).supportInv := by
  simp only [supportLeftRightSupportInv, dif_pos ht]

/-- The source-\(A\) quadratic form on the support of \(B\). Its source vector
is \(\operatorname{vec}((A P_B)^{\mathsf T})\), so zero eigenvalues of \(B\)
are removed before the generalized inverse is applied. -/
noncomputable def supportSourceAQuadratic
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) : ℝ :=
  let b := vec (A * hB.isHermitian.supportProj)ᵀ
  (star b ⬝ᵥ (supportLeftRightSupportInv hA hB t *ᵥ b)).re

/-- The unprojected source-\(A\) quadratic form for a positive-semidefinite
left-right operator. It agrees with `supportSourceAQuadratic` under
\(\ker B\subseteq\ker A\), but not for arbitrary positive-semidefinite pairs. -/
noncomputable def rawSupportSourceAQuadratic
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) : ℝ :=
  (star (vec Aᵀ) ⬝ᵥ
    (supportLeftRightSupportInv hA hB t *ᵥ vec Aᵀ)).re

/-- Under \(\ker B\subseteq\ker A\), projecting the source \(A\) to the
support of \(B\) does not change the source-\(A\) quadratic form. -/
theorem supportSourceAQuadratic_eq_raw_of_kernel_le
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0) (t : ℝ) :
    supportSourceAQuadratic hA hB t =
      rawSupportSourceAQuadratic hA hB t := by
  rw [supportSourceAQuadratic, rawSupportSourceAQuadratic,
    hB.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker]

/-- The source-\(B\) quadratic form for the positive-semidefinite left-right
operator. -/
noncomputable def supportSourceBQuadratic
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) : ℝ :=
  (star (vec Bᵀ) ⬝ᵥ
    (supportLeftRightSupportInv hA hB t *ᵥ vec Bᵀ)).re

/-- The support-domain two-source left-right integrand. The coefficient \(t\)
on the source-\(B\) form is the coefficient in the finite Weyl formulas
`(intspec)` and `(intAB)` of Jenčová--Ruskai, arXiv:0903.2895v4, §2.1,
lines 406--427. -/
noncomputable def supportRelativeEntropyLeftRightIntegrand
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) : ℝ :=
  (supportSourceAQuadratic hA hB t - (Matrix.trace B).re +
      t * supportSourceBQuadratic hA hB t) / (1 + t)

/-- For \(t>0\), the spectral source-\(A\) construction solves the singular
left--right equation
\[
  AX+tXB=AP_B,
\]
where \(P_B\) is the support projection of \(B\).

This is the support-domain source \(X_j=A_jK\), with \(K=1\), in the
Jenčová--Ruskai residual calculation, arXiv:0903.2895v4, Appendix,
equations `(Mj)`, `(eq:Schz1)`, and `(eq:Schwzt)`. -/
theorem supportLeftRight_sourceA_solution
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
    let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
    let α : n → ℝ := hA.isHermitian.eigenvalues
    let β : n → ℝ := hB.isHermitian.eigenvalues
    let W := star UA * UB
    let Y : Matrix n n ℂ := fun i j =>
      if 0 < β j then
        (α i / (α i + t * β j) : ℂ) * W i j
      else 0
    let X := UA * Y * star UB
    A * X + t • (X * B) = A * hB.isHermitian.supportProj := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let Dα : Matrix n n ℂ := diagonal fun i => (α i : ℂ)
  let Dβ : Matrix n n ℂ := diagonal fun j => (β j : ℂ)
  let Qβ : Matrix n n ℂ :=
    diagonal fun j => if 0 < β j then (1 : ℂ) else 0
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    if 0 < β j then
      (α i / (α i + t * β j) : ℂ) * W i j
    else 0
  let X : Matrix n n ℂ := UA * Y * star UB
  have hcore : Dα * Y + t • (Y * Dβ) = Dα * W * Qβ := by
    ext i j
    simp only [Dα, Dβ, Qβ, Y, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    by_cases hβ : 0 < β j
    · simp only [hβ, if_true]
      have hden : (α i : ℂ) + t * β j ≠ 0 := by
        exact_mod_cast
          (ne_of_gt (add_pos_of_nonneg_of_pos
            (hA.eigenvalues_nonneg i) (mul_pos ht hβ)))
      field_simp
    · have hβzero : β j = 0 :=
        le_antisymm (not_lt.mp hβ) (hB.eigenvalues_nonneg j)
      simp [hβzero]
  have hAform : A = UA * Dα * star UA := by
    simpa only [UA, Dα, α] using hA.isHermitian.spectral_form
  have hBform : B = UB * Dβ * star UB := by
    simpa only [UB, Dβ, β] using hB.isHermitian.spectral_form
  have hPform :
      hB.isHermitian.supportProj = UB * Qβ * star UB := by
    unfold Matrix.IsHermitian.supportProj
    have hfun :
        (fun j => if hB.isHermitian.eigenvalues j ≠ 0 then (1 : ℂ) else 0) =
          fun j => if 0 < β j then (1 : ℂ) else 0 := by
      funext j
      by_cases hβ : 0 < β j
      · simp [β, hβ, ne_of_gt hβ]
      · have hβzero : β j = 0 :=
          le_antisymm (not_lt.mp hβ) (hB.eigenvalues_nonneg j)
        simp [β, hβzero]
    rw [hfun]
  have hUA : star UA * UA = 1 := by
    simpa only [UA] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hstarUB : star UB * UB = 1 := by
    simpa only [UB] using
      Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  calc
    A * X + t • (X * B) =
        (UA * Dα * star UA) * X +
          t • (X * (UB * Dβ * star UB)) := by rw [hAform, hBform]
    _ = UA * (Dα * Y + t • (Y * Dβ)) * star UB := by
      simp only [X, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star UA), hUA, Matrix.one_mul,
        ← Matrix.mul_assoc (star UB) UB, hstarUB, Matrix.one_mul]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
        Matrix.mul_smul, Matrix.smul_mul]
    _ = UA * (Dα * W * Qβ) * star UB := by rw [hcore]
    _ = (UA * Dα * star UA) * (UB * Qβ * star UB) := by
      simp only [W, Matrix.mul_assoc]
    _ = A * hB.isHermitian.supportProj := by rw [hAform, hPform]

private lemma spectral_support_sourceB_solution
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
    let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
    let α : n → ℝ := hA.isHermitian.eigenvalues
    let β : n → ℝ := hB.isHermitian.eigenvalues
    let W := star UA * UB
    let Y : Matrix n n ℂ := fun i j =>
      if 0 < β j then
        (β j / (α i + t * β j) : ℂ) * W i j
      else 0
    let X := UA * Y * star UB
    A * X + t • (X * B) = B := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let Dα : Matrix n n ℂ := diagonal fun i => (α i : ℂ)
  let Dβ : Matrix n n ℂ := diagonal fun j => (β j : ℂ)
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    if 0 < β j then
      (β j / (α i + t * β j) : ℂ) * W i j
    else 0
  let X : Matrix n n ℂ := UA * Y * star UB
  have hcore : Dα * Y + t • (Y * Dβ) = W * Dβ := by
    ext i j
    simp only [Dα, Dβ, Y, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    by_cases hβ : 0 < β j
    · simp only [hβ, if_true]
      have hden : (α i : ℂ) + t * β j ≠ 0 := by
        exact_mod_cast
          (ne_of_gt (add_pos_of_nonneg_of_pos
            (hA.eigenvalues_nonneg i) (mul_pos ht hβ)))
      rw [div_eq_mul_inv]
      calc
        (α i : ℂ) *
              (((β j : ℂ) * ((α i : ℂ) + t * β j)⁻¹) * W i j) +
            t * ((((β j : ℂ) * ((α i : ℂ) + t * β j)⁻¹) * W i j) * β j) =
            W i j * β j *
              (((α i : ℂ) + t * β j) *
                ((α i : ℂ) + t * β j)⁻¹) := by ring
        _ = W i j * β j := by rw [mul_inv_cancel₀ hden, mul_one]
    · have hβzero : β j = 0 :=
        le_antisymm (not_lt.mp hβ) (hB.eigenvalues_nonneg j)
      simp [hβzero]
  have hAform : A = UA * Dα * star UA := by
    simpa only [UA, Dα, α] using hA.isHermitian.spectral_form
  have hBform : B = UB * Dβ * star UB := by
    simpa only [UB, Dβ, β] using hB.isHermitian.spectral_form
  have hUA : star UA * UA = 1 := by
    simpa only [UA] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hUAstar : UA * star UA = 1 := by
    simpa only [UA] using
      Unitary.mul_star_self_of_mem hA.isHermitian.eigenvectorUnitary.prop
  have hstarUB : star UB * UB = 1 := by
    simpa only [UB] using
      Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  calc
    A * X + t • (X * B) =
        (UA * Dα * star UA) * X +
          t • (X * (UB * Dβ * star UB)) := by rw [hAform, hBform]
    _ = UA * (Dα * Y + t • (Y * Dβ)) * star UB := by
      simp only [X, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star UA), hUA, Matrix.one_mul,
        ← Matrix.mul_assoc (star UB) UB, hstarUB, Matrix.one_mul]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
        Matrix.mul_smul, Matrix.smul_mul]
    _ = UA * (W * Dβ) * star UB := by rw [hcore]
    _ = UB * Dβ * star UB := by
      simp only [W, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc UA (star UA), hUAstar, Matrix.one_mul]
    _ = B := hBform.symm

private lemma spectral_support_sourceA_pairing
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (_ht : 0 < t) :
    let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
    let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
    let α : n → ℝ := hA.isHermitian.eigenvalues
    let β : n → ℝ := hB.isHermitian.eigenvalues
    let W := star UA * UB
    let Y : Matrix n n ℂ := fun i j =>
      if 0 < β j then
        (α i / (α i + t * β j) : ℂ) * W i j
      else 0
    let X := UA * Y * star UB
    (star (vec (A * hB.isHermitian.supportProj)ᵀ) ⬝ᵥ vec Xᵀ).re =
      ∑ i, ∑ j,
        if 0 < β j then
          α i ^ 2 / (α i + t * β j) * Complex.normSq (W i j)
        else 0 := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let Dα : Matrix n n ℂ := diagonal fun i => (α i : ℂ)
  let Qβ : Matrix n n ℂ :=
    diagonal fun j => if 0 < β j then (1 : ℂ) else 0
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    if 0 < β j then
      (α i / (α i + t * β j) : ℂ) * W i j
    else 0
  let X : Matrix n n ℂ := UA * Y * star UB
  have hAform : A = UA * Dα * star UA := by
    simpa only [UA, Dα, α] using hA.isHermitian.spectral_form
  have hPform :
      hB.isHermitian.supportProj = UB * Qβ * star UB := by
    unfold Matrix.IsHermitian.supportProj
    have hfun :
        (fun j => if hB.isHermitian.eigenvalues j ≠ 0 then (1 : ℂ) else 0) =
          fun j => if 0 < β j then (1 : ℂ) else 0 := by
      funext j
      by_cases hβ : 0 < β j
      · simp [β, hβ, ne_of_gt hβ]
      · have hβzero : β j = 0 :=
          le_antisymm (not_lt.mp hβ) (hB.eigenvalues_nonneg j)
        simp [β, hβzero]
    rw [hfun]
  have hUA : star UA * UA = 1 := by
    simpa only [UA] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hUB : star UB * UB = 1 := by
    simpa only [UB] using
      Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  have hstarW : star W = star UB * UA := by
    simp only [W, star_mul, star_star]
  have hpair :
      star (vec (A * hB.isHermitian.supportProj)ᵀ) ⬝ᵥ vec Xᵀ =
        Matrix.trace (hB.isHermitian.supportProj * A * X) := by
    rw [Matrix.star_vec_dotProduct_vec,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm,
      Matrix.conjTranspose_mul, hB.isHermitian.supportProj_isHermitian.eq,
      hA.isHermitian.eq]
  rw [hpair]
  have htraceform :
      Matrix.trace (hB.isHermitian.supportProj * A * X) =
        Matrix.trace ((UB * Qβ * star UB) *
          (UA * Dα * star UA) * X) := by
    rw [hPform, hAform]
  rw [htraceform]
  simp only [X, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star UA), hUA, Matrix.one_mul]
  rw [Matrix.trace_mul_comm UB]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star UB), hUB, Matrix.mul_one]
  rw [← hstarW]
  rw [← Matrix.mul_assoc (star W) Dα Y]
  let Z : Matrix n n ℂ := fun i j => (α i : ℂ) * Y i j
  have hDY : Dα * Y = Z := by
    ext i j
    simp only [Dα, Z, Matrix.diagonal_mul]
  rw [Matrix.mul_assoc (star W) Dα Y, hDY]
  have hQ : Qβ * (star W * Z) =
      fun i j =>
        (if 0 < β i then (1 : ℂ) else 0) *
          (star W * Z) i j := by
    ext i j
    simp only [Qβ, Matrix.diagonal_mul]
  rw [hQ]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Z, Y,
    Matrix.star_apply, Complex.star_def, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change _ = ∑ i,
    if 0 < β j then
      α i ^ 2 / (α i + t * β j) * Complex.normSq (W i j)
    else 0
  by_cases hβ : 0 < β j
  · simp only [hβ, if_true, one_mul, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change
      (star (W i j) *
        ((α i : ℂ) *
          (((α i : ℂ) / ((α i : ℂ) + t * β j)) * W i j))).re =
        α i ^ 2 / (α i + t * β j) * Complex.normSq (W i j)
    have hnorm : star (W i j) * W i j =
        (Complex.normSq (W i j) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    rw [show
      star (W i j) *
          ((α i : ℂ) *
            (((α i : ℂ) / ((α i : ℂ) + t * β j)) * W i j)) =
        ((α i : ℂ) *
          ((α i : ℂ) / ((α i : ℂ) + t * β j))) *
            (star (W i j) * W i j) by ring, hnorm]
    rw [← Complex.ofReal_mul t (β j),
      ← Complex.ofReal_add (α i) (t * β j),
      ← Complex.ofReal_div (α i) (α i + t * β j),
      ← Complex.ofReal_mul (α i) (α i / (α i + t * β j)),
      ← Complex.ofReal_mul
        (α i * (α i / (α i + t * β j))) (Complex.normSq (W i j)),
      Complex.ofReal_re]
    ring
  · simp [hβ]

private lemma spectral_support_sourceB_pairing
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (_ht : 0 < t) :
    let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
    let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
    let α : n → ℝ := hA.isHermitian.eigenvalues
    let β : n → ℝ := hB.isHermitian.eigenvalues
    let W := star UA * UB
    let Y : Matrix n n ℂ := fun i j =>
      if 0 < β j then
        (β j / (α i + t * β j) : ℂ) * W i j
      else 0
    let X := UA * Y * star UB
    (star (vec Bᵀ) ⬝ᵥ vec Xᵀ).re =
      ∑ i, ∑ j,
        if 0 < β j then
          β j ^ 2 / (α i + t * β j) * Complex.normSq (W i j)
        else 0 := by
  classical
  dsimp only
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let Dβ : Matrix n n ℂ := diagonal fun j => (β j : ℂ)
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    if 0 < β j then
      (β j / (α i + t * β j) : ℂ) * W i j
    else 0
  let X : Matrix n n ℂ := UA * Y * star UB
  have hBform : B = UB * Dβ * star UB := by
    simpa only [UB, Dβ, β] using hB.isHermitian.spectral_form
  have hUB : star UB * UB = 1 := by
    simpa only [UB] using
      Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  have hstarW : star W = star UB * UA := by
    simp only [W, star_mul, star_star]
  have hpair : star (vec Bᵀ) ⬝ᵥ vec Xᵀ = Matrix.trace (B * X) := by
    rw [Matrix.star_vec_dotProduct_vec]
    rw [hB.isHermitian.transpose.eq, ← Matrix.transpose_mul,
      Matrix.trace_transpose, Matrix.trace_mul_comm]
  rw [hpair]
  have htraceform : Matrix.trace (B * X) =
      Matrix.trace ((UB * Dβ * star UB) * X) := by
    rw [hBform]
  rw [htraceform]
  simp only [X, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm UB]
  simp only [Matrix.mul_assoc]
  rw [hUB, Matrix.mul_one]
  rw [← Matrix.mul_assoc (star UB) UA Y, ← hstarW]
  have hD : Dβ * (star W * Y) =
      fun i j => (β i : ℂ) * (star W * Y) i j := by
    ext i j
    simp only [Dβ, Matrix.diagonal_mul]
  rw [hD]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Y,
    Matrix.star_apply, Complex.star_def, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change _ = ∑ i,
    if 0 < β j then
      β j ^ 2 / (α i + t * β j) * Complex.normSq (W i j)
    else 0
  by_cases hβ : 0 < β j
  · simp only [hβ, if_true]
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change
      ((β j : ℂ) * (star (W i j) *
        (((β j : ℂ) / ((α i : ℂ) + t * β j)) * W i j))).re =
        β j ^ 2 / (α i + t * β j) * Complex.normSq (W i j)
    have hnorm : star (W i j) * W i j =
        (Complex.normSq (W i j) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    rw [show
      (β j : ℂ) * (star (W i j) *
          (((β j : ℂ) / ((α i : ℂ) + t * β j)) * W i j)) =
        ((β j : ℂ) *
          ((β j : ℂ) / ((α i : ℂ) + t * β j))) *
            (star (W i j) * W i j) by ring, hnorm]
    rw [← Complex.ofReal_mul t (β j),
      ← Complex.ofReal_add (α i) (t * β j),
      ← Complex.ofReal_div (β j) (α i + t * β j),
      ← Complex.ofReal_mul (β j) (β j / (α i + t * β j)),
      ← Complex.ofReal_mul
        (β j * (β j / (α i + t * β j))) (Complex.normSq (W i j)),
      Complex.ofReal_re]
    ring
  · simp [hβ]

/-- The projected source-\(A\) quadratic form has the spectral expansion
\[
  \sum_{i,j:\,\beta_j>0}
    \frac{\alpha_i^2}{\alpha_i+t\beta_j}
      \lvert (U_A^\ast U_B)_{ij}\rvert^2 .
\]

The restriction \(\beta_j>0\) is produced by the source \(A P_B\). This is the
first term of `(intAB)` in Jenčová--Ruskai, arXiv:0903.2895v4, §2.1,
lines 423--427, with the support convention at lines 717--720. -/
theorem supportSourceAQuadratic_spectral
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    supportSourceAQuadratic hA hB t =
      ∑ i, ∑ j,
        if 0 < hB.isHermitian.eigenvalues j then
          hA.isHermitian.eigenvalues i ^ 2 /
              (hA.isHermitian.eigenvalues i +
                t * hB.isHermitian.eigenvalues j) *
            Complex.normSq
              ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
                (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j)
        else 0 := by
  classical
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    if 0 < β j then
      (α i / (α i + t * β j) : ℂ) * W i j
    else 0
  let X : Matrix n n ℂ := UA * Y * star UB
  let S : Matrix (n × n) (n × n) ℂ :=
    supportLeftRightSuperoperator A B t
  let b : n × n → ℂ := vec (A * hB.isHermitian.supportProj)ᵀ
  have hsolution : A * X + t • (X * B) =
      A * hB.isHermitian.supportProj := by
    simpa only [UA, UB, α, β, W, Y, X] using
      supportLeftRight_sourceA_solution hA hB ht
  have hvec : S *ᵥ vec Xᵀ = b := by
    change
      (A ⊗ₖ (1 : Matrix n n ℂ) +
        t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)) *ᵥ vec Xᵀ =
          vec (A * hB.isHermitian.supportProj)ᵀ
    rw [leftRight_mulVec_vec_transpose, hsolution]
  have hS : S.PosSemidef := by
    simpa only [S] using
      supportLeftRightSuperoperator_posSemidef hA hB ht.le
  have hpair :
      star b ⬝ᵥ (hS.supportInv *ᵥ b) =
        star b ⬝ᵥ vec Xᵀ :=
    hS.star_dotProduct_supportInv_mulVec_eq_of_mulVec_eq b (vec Xᵀ) hvec
  unfold supportSourceAQuadratic
  rw [supportLeftRightSupportInv_eq hA hB ht.le]
  change
    (star b ⬝ᵥ
      ((supportLeftRightSuperoperator_posSemidef hA hB ht.le).supportInv *ᵥ b)).re = _
  rw [show
    (supportLeftRightSuperoperator_posSemidef hA hB ht.le).supportInv =
      hS.supportInv from rfl, hpair]
  simpa only [UA, UB, α, β, W, Y, X, b] using
    spectral_support_sourceA_pairing hA hB ht

/-- The source-\(B\) quadratic form has the spectral expansion
\[
  \sum_{i,j:\,\beta_j>0}
    \frac{\beta_j^2}{\alpha_i+t\beta_j}
      \lvert (U_A^\ast U_B)_{ij}\rvert^2 .
\]

This is the second term of `(intAB)` in Jenčová--Ruskai,
arXiv:0903.2895v4, §2.1, lines 423--427, with the support convention at
lines 717--720. -/
theorem supportSourceBQuadratic_spectral
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    supportSourceBQuadratic hA hB t =
      ∑ i, ∑ j,
        if 0 < hB.isHermitian.eigenvalues j then
          hB.isHermitian.eigenvalues j ^ 2 /
              (hA.isHermitian.eigenvalues i +
                t * hB.isHermitian.eigenvalues j) *
            Complex.normSq
              ((star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
                (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j)
        else 0 := by
  classical
  let UA : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ := star UA * UB
  let Y : Matrix n n ℂ := fun i j =>
    if 0 < β j then
      (β j / (α i + t * β j) : ℂ) * W i j
    else 0
  let X : Matrix n n ℂ := UA * Y * star UB
  let S : Matrix (n × n) (n × n) ℂ :=
    supportLeftRightSuperoperator A B t
  let b : n × n → ℂ := vec Bᵀ
  have hsolution : A * X + t • (X * B) = B := by
    simpa only [UA, UB, α, β, W, Y, X] using
      spectral_support_sourceB_solution hA hB ht
  have hvec : S *ᵥ vec Xᵀ = b := by
    change
      (A ⊗ₖ (1 : Matrix n n ℂ) +
        t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ)) *ᵥ vec Xᵀ = vec Bᵀ
    rw [leftRight_mulVec_vec_transpose, hsolution]
  have hS : S.PosSemidef := by
    simpa only [S] using
      supportLeftRightSuperoperator_posSemidef hA hB ht.le
  have hpair :
      star b ⬝ᵥ (hS.supportInv *ᵥ b) =
        star b ⬝ᵥ vec Xᵀ :=
    hS.star_dotProduct_supportInv_mulVec_eq_of_mulVec_eq b (vec Xᵀ) hvec
  unfold supportSourceBQuadratic
  rw [supportLeftRightSupportInv_eq hA hB ht.le]
  change
    (star b ⬝ᵥ
      ((supportLeftRightSuperoperator_posSemidef hA hB ht.le).supportInv *ᵥ b)).re = _
  rw [show
    (supportLeftRightSuperoperator_posSemidef hA hB ht.le).supportInv =
      hS.supportInv from rfl, hpair]
  simpa only [UA, UB, α, β, W, Y, X, b] using
    spectral_support_sourceB_pairing hA hB ht

/-- For \(t>0\), the coordinate-free support left-right integrand is the
existing support-domain spectral integrand:
\[
 \frac{Q_{A P_B}(t)-\operatorname{tr}B+tQ_B(t)}{1+t}
 =
 \sum_{i,j:\,\beta_j>0}
 r(\alpha_i,\beta_j,t)\lvert(U_A^\ast U_B)_{ij}\rvert^2 .
\]

The statement holds for all positive-semidefinite \(A\) and \(B\). No kernel
inclusion is required because the source in the first quadratic form is
\(A P_B\). This is the support form of `(intAB)` in Jenčová--Ruskai,
arXiv:0903.2895v4, §2.1, lines 423--427 and 717--720. -/
theorem supportRelativeEntropyLeftRightIntegrand_eq_spectral
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    supportRelativeEntropyLeftRightIntegrand hA hB t =
      supportRelativeEntropySpectralIntegrand hA hB t := by
  classical
  let α : n → ℝ := hA.isHermitian.eigenvalues
  let β : n → ℝ := hB.isHermitian.eigenvalues
  let W : Matrix n n ℂ :=
    star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hB.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  let P : n → n → ℝ := fun i j => Complex.normSq (W i j)
  have hWcol : star W * W = 1 := by
    simp only [W, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)]
    rw [Unitary.mul_star_self_of_mem
      hA.isHermitian.eigenvectorUnitary.prop, Matrix.one_mul]
    exact Unitary.coe_star_mul_self hB.isHermitian.eigenvectorUnitary
  have hcol (j : n) : ∑ i, P i j = 1 :=
    TNLean.Klein.col_sum_normSq_eq_one hWcol j
  have htrace : (Matrix.trace B).re = ∑ i, ∑ j, β j * P i j := by
    have htr : (Matrix.trace B).re = ∑ j, β j := by
      rw [hB.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
      exact Finset.sum_congr rfl fun j _ => Complex.ofReal_re _
    rw [htr, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← mul_one (β j), ← hcol j]
    rw [Finset.mul_sum]
  rw [supportRelativeEntropyLeftRightIntegrand,
    supportSourceAQuadratic_spectral hA hB ht,
    supportSourceBQuadratic_spectral hA hB ht]
  unfold supportRelativeEntropySpectralIntegrand
  change
    ((∑ i, ∑ j,
          if 0 < β j then
            α i ^ 2 / (α i + t * β j) * P i j
          else 0) -
        (Matrix.trace B).re +
        t * (∑ i, ∑ j,
          if 0 < β j then
            β j ^ 2 / (α i + t * β j) * P i j
          else 0)) /
      (1 + t) =
        ∑ i, ∑ j,
          if 0 < β j then
            relativeEntropyScalar (α i) (β j) t * P i j
          else 0
  rw [htrace, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hβ : 0 < β j
  · simp only [hβ, if_true, relativeEntropyScalar]
    ring
  · have hβzero : β j = 0 :=
      le_antisymm (not_lt.mp hβ) (hB.eigenvalues_nonneg j)
    simp [hβzero]

/-- Under \(\ker B\subseteq\ker A\), the unprojected source-\(A\) left-right
form may replace the projected source in the support-domain integrand. -/
theorem rawSupportSourceAQuadratic_sub_trace_add_sourceB_eq_spectral
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0)
    {t : ℝ} (ht : 0 < t) :
    (rawSupportSourceAQuadratic hA hB t - (Matrix.trace B).re +
        t * supportSourceBQuadratic hA hB t) / (1 + t) =
      supportRelativeEntropySpectralIntegrand hA hB t := by
  rw [← supportSourceAQuadratic_eq_raw_of_kernel_le hA hB hker t]
  exact supportRelativeEntropyLeftRightIntegrand_eq_spectral hA hB ht

/-- The support-domain spectral integrand is continuous for positive
resolvent parameter. -/
theorem supportRelativeEntropySpectralIntegrand_continuousOn
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ContinuousOn (supportRelativeEntropySpectralIntegrand hA hB) (Ioi 0) := by
  classical
  unfold supportRelativeEntropySpectralIntegrand
  apply continuousOn_finsetSum Finset.univ
  intro i _
  apply continuousOn_finsetSum Finset.univ
  intro j _
  by_cases hβ : 0 < hB.isHermitian.eigenvalues j
  · simp only [hβ, if_true]
    intro t ht
    have ht0 : 0 < t := ht
    have hden :
        hA.isHermitian.eigenvalues i +
            t * hB.isHermitian.eigenvalues j ≠ 0 := by
      exact ne_of_gt (add_pos_of_nonneg_of_pos
        (hA.eigenvalues_nonneg i) (mul_pos ht0 hβ))
    have h1 : 1 + t ≠ 0 := ne_of_gt (by linarith)
    apply ContinuousAt.continuousWithinAt
    unfold relativeEntropyScalar
    fun_prop
  · simp only [hβ, if_false]
    exact continuousOn_const

/-- The support-domain left-right quadratic integrand is continuous on
\((0,\infty)\). -/
theorem supportRelativeEntropyLeftRightIntegrand_continuousOn
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ContinuousOn (supportRelativeEntropyLeftRightIntegrand hA hB) (Ioi 0) := by
  refine (supportRelativeEntropySpectralIntegrand_continuousOn hA hB).congr
    (fun t ht => ?_)
  exact supportRelativeEntropyLeftRightIntegrand_eq_spectral hA hB ht

end Matrix
