/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarCommutant
import TNLean.Algebra.MatrixGramUnitary
import TNLean.MPS.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Commutant rigidity of normal tensors

A normal tensor spans the full matrix algebra after blocking, so any matrix
commuting with all of its matrices is a scalar multiple of the identity.
Applied to the Gram matrix $X^\dagger X$ of a nonzero gauge $X$, the scalar is
a positive real $\omega$ and $\omega^{-1/2}X$ is unitary.

These are the rigidity facts invoked at the step "since $M_\alpha$ is a NT in
the vertical direction" in the proof of Proposition 4.13 of arXiv:1606.00608,
line 1921: they produce equation eq3:proof.IV.12,
$X_{\alpha,k}^\dagger X_{\alpha,k} = \omega_{\alpha,k}
X_{\alpha,1}^\dagger X_{\alpha,1}$ and the unitary normalization of the
relative gauge $X_{\alpha,k}X_{\alpha,1}^{-1}$.  In the source normalization
$X_{\alpha,1} = \Id$, this is
$U_{\alpha,k} = \omega_{\alpha,k}^{-1/2} X_{\alpha,k}$ from lines 1906--1908.
The commutation hypothesis is the relative conclusion of the two displayed
diagrams at lines 1909--1919.  Hermiticity first gives a reflected marked-chain
identity whose adjoint reverses the unmarked tail.  Lemma L is then applied to
two sectors together, producing equality of their Gram conjugations.  The
resulting ratio of Gram matrices commutes with every matrix of the tensor.
The passage from this relative equality to eq3 is proved below.  The reflected
marked-chain argument and its specialization to the grouped vertical sectors
are proved in the matrix-product-density-operator canonical-form development.

## Main results

* `MPSTensor.IsNormal.eq_smul_one_of_commute`:
  a matrix commuting with every matrix of a normal tensor is scalar.
* `MPSTensor.IsNormal.conjTranspose_mul_self_eq_smul_one_of_commute`:
  if $X \ne 0$ and $X^\dagger X$ commutes with every matrix of a normal
  tensor, then $X^\dagger X = \omega\,\Id$ with $\omega > 0$.
* `MPSTensor.IsNormal.smul_mem_unitaryGroup_of_commute`:
  under the same hypotheses, $\omega^{-1/2}X$ is unitary.
* `Matrix.gram_conj_eq_conjTranspose_of_dressed_adjoint` /
  `Matrix.gram_conj_eq_gram_conj_of_dressed_adjoint` /
  `Matrix.commute_gram_of_dressed_adjoint_of_conjTranspose_eq`:
  same-letter specializations of the common-target argument.
* `Matrix.gram_conj_eq_of_dressed_target` /
  `Matrix.gram_conj_eq_gram_conj_of_common_dressed_target`:
  conditional algebraic consequences of an abstract common target.
* `MPSTensor.IsNormal.gram_eq_pos_smul_gram_of_gram_conj_eq` /
  `MPSTensor.IsNormal.gram_eq_pos_smul_gram_of_common_dressed_target`:
  the relative two-gauge form of eq3, without a self-adjoint-letter
  hypothesis.
* `MPSTensor.IsNormal.conjTranspose_mul_self_eq_smul_one_of_dressed_adjoint` /
  `MPSTensor.IsNormal.smul_mem_unitaryGroup_of_dressed_adjoint`:
  conditional same-letter specializations in the identity reference gauge.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  proof of Proposition 4.13, lines 1904--1921
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If conjugation by an invertible gauge carries `B` to the dressing of an
abstract target `C`, then conjugation by the Gram matrix carries `B` to `C`.

This is a conditional algebraic route to the relative Gram identity in
arXiv:1606.00608, proof of Proposition 4.13, lines 1909--1919.  The source's
reflected marked-chain argument does not identify such a target separately
for each sector. -/
theorem gram_conj_eq_of_dressed_target
    {X B C : Matrix n n ℂ} (hX : IsUnit X.det)
    (hdress : X * B * X⁻¹ = X⁻¹ᴴ * C * Xᴴ) :
    Xᴴ * X * B * (Xᴴ * X)⁻¹ = C := by
  have hXH : IsUnit (Xᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hX.star
  have h1 : Xᴴ * (X * B * X⁻¹) * X⁻¹ᴴ = Xᴴ * X * B * (Xᴴ * X)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
  have h2 : Xᴴ * (X⁻¹ᴴ * C * Xᴴ) * X⁻¹ᴴ = C := by
    rw [Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hXH, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hXH, Matrix.mul_one]
  rw [← h1, hdress, h2]

/-- **From the first displayed diagram to the second** (arXiv:1606.00608,
proof of Proposition 4.13, lines 1909--1919): if a letter dressed by an
invertible gauge equals its adjoint dressing,
$XBX^{-1} = (X^{-1})^\dagger B^\dagger X^\dagger$, then conjugation by the
Gram matrix $X^\dagger X$ carries the letter to its adjoint. -/
theorem gram_conj_eq_conjTranspose_of_dressed_adjoint
    {X B : Matrix n n ℂ} (hX : IsUnit X.det)
    (hdress : X * B * X⁻¹ = X⁻¹ᴴ * Bᴴ * Xᴴ) :
    Xᴴ * X * B * (Xᴴ * X)⁻¹ = Bᴴ :=
  gram_conj_eq_of_dressed_target hX hdress

/-- **The second displayed diagram** (arXiv:1606.00608, proof of Proposition
4.13, lines 1914--1919): two gauges whose dressings carry the same letter `B`
to the same target `C` have equal Gram conjugations. -/
theorem gram_conj_eq_gram_conj_of_common_dressed_target
    {X Y B C : Matrix n n ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hdX : X * B * X⁻¹ = X⁻¹ᴴ * C * Xᴴ)
    (hdY : Y * B * Y⁻¹ = Y⁻¹ᴴ * C * Yᴴ) :
    Xᴴ * X * B * (Xᴴ * X)⁻¹ = Yᴴ * Y * B * (Yᴴ * Y)⁻¹ := by
  rw [gram_conj_eq_of_dressed_target hX hdX,
    gram_conj_eq_of_dressed_target hY hdY]

/-- **The second displayed diagram** (arXiv:1606.00608, proof of Proposition
4.13, lines 1914--1919): two gauges whose dressings both equal the adjoint
dressing have equal Gram conjugations,
$X^\dagger X\,B\,(X^\dagger X)^{-1} = Y^\dagger Y\,B\,(Y^\dagger Y)^{-1}$. -/
theorem gram_conj_eq_gram_conj_of_dressed_adjoint
    {X Y B : Matrix n n ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hdX : X * B * X⁻¹ = X⁻¹ᴴ * Bᴴ * Xᴴ)
    (hdY : Y * B * Y⁻¹ = Y⁻¹ᴴ * Bᴴ * Yᴴ) :
    Xᴴ * X * B * (Xᴴ * X)⁻¹ = Yᴴ * Y * B * (Yᴴ * Y)⁻¹ :=
  gram_conj_eq_gram_conj_of_common_dressed_target hX hY hdX hdY

/-- **The relative commutant in the second displayed diagram**
(arXiv:1606.00608, proof of Proposition 4.13, lines 1914--1921): if two
invertible matrices have the same Gram conjugation of a matrix, then the
ratio of their Gram matrices commutes with that matrix. -/
theorem commute_gram_ratio_of_gram_conj_eq
    {X Y B : Matrix n n ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (h : Xᴴ * X * B * (Xᴴ * X)⁻¹ = Yᴴ * Y * B * (Yᴴ * Y)⁻¹) :
    (Yᴴ * Y)⁻¹ * (Xᴴ * X) * B =
      B * ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := by
  have hGX : IsUnit (Xᴴ * X).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hX.star.mul hX
  have hGY : IsUnit (Yᴴ * Y).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hY.star.mul hY
  have hGYinv : (Yᴴ * Y)⁻¹ * (Yᴴ * Y) = 1 :=
    Matrix.nonsing_inv_mul _ hGY
  calc
    (Yᴴ * Y)⁻¹ * (Xᴴ * X) * B =
        (Yᴴ * Y)⁻¹ * (Xᴴ * X) * B * ((Xᴴ * X)⁻¹ * (Xᴴ * X)) := by
          rw [Matrix.nonsing_inv_mul _ hGX, Matrix.mul_one]
    _ = (Yᴴ * Y)⁻¹ *
        (Xᴴ * X * B * (Xᴴ * X)⁻¹) * (Xᴴ * X) := by
          simp only [Matrix.mul_assoc]
    _ = (Yᴴ * Y)⁻¹ *
        (Yᴴ * Y * B * (Yᴴ * Y)⁻¹) * (Xᴴ * X) := by rw [h]
    _ = ((Yᴴ * Y)⁻¹ * (Yᴴ * Y)) * B *
        ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := by noncomm_ring
    _ = B * ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := by rw [hGYinv, Matrix.one_mul]

/-- For a self-adjoint matrix, equality with its dressing by the inverse
conjugate transpose makes the Gram matrix $X^\dagger X$ commute with it.

This is a purely algebraic same-letter specialization.  The vertical-sector
identity in arXiv:1606.00608, proof of Proposition 4.13, lines 1909--1919,
instead exchanges the two oriented horizontal bond indices. -/
theorem commute_gram_of_dressed_adjoint_of_conjTranspose_eq
    {X B : Matrix n n ℂ} (hX : IsUnit X.det)
    (hdress : X * B * X⁻¹ = X⁻¹ᴴ * Bᴴ * Xᴴ) (hB : Bᴴ = B) :
    Xᴴ * X * B = B * (Xᴴ * X) := by
  have hG : IsUnit (Xᴴ * X).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hX.star.mul hX
  have h := gram_conj_eq_conjTranspose_of_dressed_adjoint hX hdress
  rw [hB] at h
  calc
    Xᴴ * X * B = Xᴴ * X * B * ((Xᴴ * X)⁻¹ * (Xᴴ * X)) := by
      rw [Matrix.nonsing_inv_mul _ hG, Matrix.mul_one]
    _ = Xᴴ * X * B * (Xᴴ * X)⁻¹ * (Xᴴ * X) := by
      simp only [Matrix.mul_assoc]
    _ = B * (Xᴴ * X) := by rw [h]

/-- A relative Gram identity gives the unitary normalization of the relative
gauge.  This is the two-gauge form of the normalization used in
arXiv:1606.00608, proof of Proposition 4.13, lines 1904--1908. -/
theorem smul_mul_nonsing_inv_mem_unitaryGroup_of_gram_eq_smul
    {X Y : Matrix n n ℂ} (hY : IsUnit Y.det) {ω : ℝ} (hω : 0 < ω)
    (hgram : Xᴴ * X = (ω : ℂ) • (Yᴴ * Y)) :
    ((Real.sqrt ω : ℂ))⁻¹ • (X * Y⁻¹) ∈ Matrix.unitaryGroup n ℂ := by
  apply smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one hω
  have hYH : IsUnit (Yᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hY.star
  have hleft : Y⁻¹ᴴ * Yᴴ = 1 := by
    rw [Matrix.conjTranspose_nonsing_inv]
    exact Matrix.nonsing_inv_mul _ hYH
  have hright : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hY
  calc
    (X * Y⁻¹)ᴴ * (X * Y⁻¹) = Y⁻¹ᴴ * (Xᴴ * X) * Y⁻¹ := by
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = Y⁻¹ᴴ * ((ω : ℂ) • (Yᴴ * Y)) * Y⁻¹ := by rw [hgram]
    _ = (ω : ℂ) • ((Y⁻¹ᴴ * Yᴴ) * (Y * Y⁻¹)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      noncomm_ring
    _ = (ω : ℂ) • 1 := by rw [hleft, hright, Matrix.one_mul]

end Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- A matrix commuting with every matrix of a normal tensor is a scalar
multiple of the identity: commutation extends from the matrices to all word
evaluations, and after blocking these span the full matrix algebra.

This is the commutant triviality behind the step "since $M_\alpha$ is a NT in
the vertical direction" in the proof of Proposition 4.13 of arXiv:1606.00608,
line 1921. -/
theorem IsNormal.eq_smul_one_of_commute {A : MPSTensor d D} (hA : IsNormal A)
    {S : Matrix (Fin D) (Fin D) ℂ} (hS : ∀ i, S * A i = A i * S) :
    ∃ c : ℂ, S = c • 1 := by
  obtain ⟨N, _hNpos, hN⟩ := hA
  have hwords : ∀ M ∈ Set.range fun σ : Fin N → Fin d => evalWord A (List.ofFn σ),
      S * M = M * S := by
    rintro _ ⟨σ, rfl⟩
    exact commutes_evalWord_of_commutes_letters S A hS (List.ofFn σ)
  obtain ⟨c, hc⟩ := Matrix.isScalar_of_commute_span_eq_top S hN hwords
  refine ⟨c, ?_⟩
  rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

/-- **Relative equation eq3:proof.IV.12.**  If two invertible Gram matrices
induce the same conjugation on every letter of a normal tensor, then one Gram
matrix is a positive real multiple of the other:
$X^\dagger X=\omega Y^\dagger Y$ with $\omega>0$.

This is the conclusion drawn from the second displayed diagram in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1914--1921.  It compares the
sector $k$ directly with the distinguished sector $1$ and does not assume that
the letters of the representative tensor are self-adjoint. -/
theorem IsNormal.gram_eq_pos_smul_gram_of_gram_conj_eq
    {A : MPSTensor d D} (hA : IsNormal A)
    {X Y : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hgram : ∀ i,
      Xᴴ * X * A i * (Xᴴ * X)⁻¹ = Yᴴ * Y * A i * (Yᴴ * Y)⁻¹) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • (Yᴴ * Y) := by
  have hGY : IsUnit (Yᴴ * Y).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hY.star.mul hY
  have hcomm : ∀ i, (Yᴴ * Y)⁻¹ * (Xᴴ * X) * A i =
      A i * ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := fun i =>
    Matrix.commute_gram_ratio_of_gram_conj_eq hX hY (hgram i)
  obtain ⟨c, hc⟩ := hA.eq_smul_one_of_commute hcomm
  have hcGram : Xᴴ * X = c • (Yᴴ * Y) := by
    calc
      Xᴴ * X = (Yᴴ * Y) * ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGY, Matrix.one_mul]
      _ = (Yᴴ * Y) * (c • 1) := by rw [hc]
      _ = c • (Yᴴ * Y) := by
        rw [Matrix.mul_smul, Matrix.mul_one]
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst D
    refine ⟨1, by positivity, ?_⟩
    ext i
    exact i.elim0
  · let i : Fin D := ⟨0, hD⟩
    have hXunit : IsUnit X := (Matrix.isUnit_iff_isUnit_det X).mpr hX
    have hYunit : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).mpr hY
    have hGXpd : (Xᴴ * X).PosDef :=
      Matrix.PosDef.conjTranspose_mul_self X
        (Matrix.mulVec_injective_of_isUnit hXunit)
    have hGYpd : (Yᴴ * Y).PosDef :=
      Matrix.PosDef.conjTranspose_mul_self Y
        (Matrix.mulVec_injective_of_isUnit hYunit)
    have hcEntry : (Xᴴ * X) i i = c * (Yᴴ * Y) i i := by
      simpa [Matrix.smul_apply] using congr_fun (congr_fun hcGram i) i
    have hcPos : (0 : ℂ) < c := by
      apply pos_of_mul_pos_left
      · rw [← hcEntry]
        exact hGXpd.diag_pos
      · exact hGYpd.diag_pos.le
    obtain ⟨hcRe, hcIm⟩ := Complex.pos_iff.mp hcPos
    refine ⟨c.re, hcRe, ?_⟩
    rw [hcGram]
    congr 1
    exact (Complex.ext (Complex.ofReal_re c.re)
      (by rw [Complex.ofReal_im]; exact hcIm)).symm

/-- **Equation eq3 with the distinguished gauge fixed to the identity.**
If an invertible gauge's Gram conjugation fixes every letter of a normal
tensor, then its Gram matrix is a positive real multiple of the identity.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem IsNormal.gram_eq_pos_smul_one_of_gram_conj_eq
    {A : MPSTensor d D} (hA : IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det)
    (hgram : ∀ i, Xᴴ * X * A i * (Xᴴ * X)⁻¹ = A i) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • 1 := by
  have hOne : IsUnit (1 : Matrix (Fin D) (Fin D) ℂ).det := by
    simp
  obtain ⟨ω, hω, hGram⟩ :=
    hA.gram_eq_pos_smul_gram_of_gram_conj_eq hX hOne (fun i => by
      simpa using hgram i)
  exact ⟨ω, hω, by simpa using hGram⟩

/-- An invertible gauge whose Gram conjugation fixes a normal tensor becomes
unitary after division by the square root of its positive Gram scalar.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem IsNormal.exists_unitary_normalization_of_gram_conj_eq
    {A : MPSTensor d D} (hA : IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det)
    (hgram : ∀ i, Xᴴ * X * A i * (Xᴴ * X)⁻¹ = A i) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ • X ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  obtain ⟨ω, hω, hGram⟩ :=
    hA.gram_eq_pos_smul_one_of_gram_conj_eq hX hgram
  have hOne : IsUnit (1 : Matrix (Fin D) (Fin D) ℂ).det := by
    simp
  have hUnit := Matrix.smul_mul_nonsing_inv_mem_unitaryGroup_of_gram_eq_smul
    (X := X) (Y := (1 : Matrix (Fin D) (Fin D) ℂ)) hOne hω
    (by simpa using hGram)
  exact ⟨ω, hω, by simpa using hUnit⟩

/-- **Conditional relative equation eq3 from a common dressed target.**  If two
invertible gauges dress every letter of a normal tensor to the same target,
then their Gram matrices differ by a positive real scalar.  The target may
depend on the letter.

This is an algebraic consequence of the Figure 8 equality in
arXiv:1606.00608, proof of Proposition 4.13, lines 1909--1921.  It is not the
source-facing reflected marked-chain statement. -/
theorem IsNormal.gram_eq_pos_smul_gram_of_common_dressed_target
    {A C : MPSTensor d D} (hA : IsNormal A)
    {X Y : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hdX : ∀ i, X * A i * X⁻¹ = X⁻¹ᴴ * C i * Xᴴ)
    (hdY : ∀ i, Y * A i * Y⁻¹ = Y⁻¹ᴴ * C i * Yᴴ) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • (Yᴴ * Y) :=
  hA.gram_eq_pos_smul_gram_of_gram_conj_eq hX hY fun i =>
    Matrix.gram_conj_eq_gram_conj_of_common_dressed_target
      hX hY (hdX i) (hdY i)

/-- The relative gauge of the preceding theorem becomes unitary after
division by the square root of its positive Gram scalar.  In the normalization
$Y=\Id$, this is $\omega^{-1/2}X$ from arXiv:1606.00608, lines 1904--1908. -/
theorem IsNormal.smul_mul_nonsing_inv_mem_unitaryGroup_of_common_dressed_target
    {A C : MPSTensor d D} (hA : IsNormal A)
    {X Y : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hdX : ∀ i, X * A i * X⁻¹ = X⁻¹ᴴ * C i * Xᴴ)
    (hdY : ∀ i, Y * A i * Y⁻¹ = Y⁻¹ᴴ * C i * Yᴴ) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ • (X * Y⁻¹) ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  obtain ⟨ω, hω, hgram⟩ :=
    hA.gram_eq_pos_smul_gram_of_common_dressed_target hX hY hdX hdY
  exact ⟨ω, hω,
    Matrix.smul_mul_nonsing_inv_mem_unitaryGroup_of_gram_eq_smul hY hω hgram⟩

/-- **Equation eq3:proof.IV.12 in the normalization $X_{\alpha,1} = \Id$.**
If $X \ne 0$ and the Gram matrix $X^\dagger X$ commutes with every matrix of
a normal tensor, then $X^\dagger X = \omega\,\Id$ for a necessarily positive
constant $\omega$ (arXiv:1606.00608, proof of Proposition 4.13, lines
1904--1908 and 1921).  The source's gauges $X_{\alpha,k}$ are invertible;
only $X \ne 0$ is needed here, and invertibility of $X$ follows from the
conclusion. -/
theorem IsNormal.conjTranspose_mul_self_eq_smul_one_of_commute
    {A : MPSTensor d D} (hA : IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ≠ 0)
    (hcomm : ∀ i, Xᴴ * X * A i = A i * (Xᴴ * X)) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • 1 := by
  obtain ⟨c, hc⟩ := hA.eq_smul_one_of_commute hcomm
  have hW_psd : (Xᴴ * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have hW_ne : Xᴴ * X ≠ 0 := fun h0 =>
    hX (Matrix.conjTranspose_mul_self_eq_zero.mp h0)
  have hc_ne : c ≠ 0 := fun h0 => hW_ne (by rw [hc, h0, zero_smul])
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · exact absurd (by subst h0; exact Matrix.ext fun i => i.elim0) hX
    · exact h0
  have hc_nonneg : (0 : ℂ) ≤ c := by
    have hd := hW_psd.diag_nonneg (i := (⟨0, hD⟩ : Fin D))
    have hWii : (Xᴴ * X) (⟨0, hD⟩ : Fin D) (⟨0, hD⟩ : Fin D) = c := by
      rw [hc]
      simp [Matrix.smul_apply, Matrix.one_apply_eq]
    rwa [hWii] at hd
  obtain ⟨-, hc_im⟩ := Complex.nonneg_iff.mp hc_nonneg
  have hc_pos : (0 : ℂ) < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_ne)
  obtain ⟨hc_re_pos, -⟩ := Complex.pos_iff.mp hc_pos
  refine ⟨c.re, hc_re_pos, ?_⟩
  rw [hc]
  congr 1
  exact (Complex.ext (Complex.ofReal_re c.re)
    (by rw [Complex.ofReal_im]; exact hc_im)).symm

/-- **The isometric normalization $U_{\alpha,k} =
\omega_{\alpha,k}^{-1/2}X_{\alpha,k}$** (arXiv:1606.00608, proof of
Proposition 4.13, lines 1906--1908): a nonzero $X$ whose Gram matrix commutes
with every matrix of a normal tensor becomes unitary after dividing by the
square root of the positive constant from eq3:proof.IV.12. -/
theorem IsNormal.smul_mem_unitaryGroup_of_commute
    {A : MPSTensor d D} (hA : IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ≠ 0)
    (hcomm : ∀ i, Xᴴ * X * A i = A i * (Xᴴ * X)) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ • X ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  obtain ⟨ω, hω, hXX⟩ := hA.conjTranspose_mul_self_eq_smul_one_of_commute hX hcomm
  exact ⟨ω, hω,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one hω hXX⟩

/-- If the gauge-dressed letters of a normal tensor equal their adjoint
dressings and the letters themselves are self-adjoint, then
$X^\dagger X = \omega\,\Id$ for a necessarily positive constant $\omega$.

**Scope restriction (self-adjoint letters):** the reflected marked-chain
argument of Figure 7 does not assume $(A^v)^\dagger=A^v$ and does not assert
an individual dressed-adjoint identity.  Thus this theorem is only a
same-letter conditional specialization.  The source-facing relative theorem
is `IsNormal.gram_eq_pos_smul_gram_of_gram_conj_eq`.  See
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`. -/
theorem IsNormal.conjTranspose_mul_self_eq_smul_one_of_dressed_adjoint
    {A : MPSTensor d D} (hA : IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) (hX0 : X ≠ 0)
    (hdress : ∀ i, X * A i * X⁻¹ = X⁻¹ᴴ * (A i)ᴴ * Xᴴ)
    (hsa : ∀ i, (A i)ᴴ = A i) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • 1 :=
  hA.conjTranspose_mul_self_eq_smul_one_of_commute hX0 fun i =>
    Matrix.commute_gram_of_dressed_adjoint_of_conjTranspose_eq hX (hdress i) (hsa i)

/-- **The isometric normalization from the dressed-adjoint identities**
(arXiv:1606.00608, proof of Proposition 4.13, lines 1906--1908 and
1909--1919): under the hypotheses of the preceding theorem,
$\omega^{-1/2}X$ is unitary.

**Scope restriction (self-adjoint letters):** this is the normalization of the
same-letter specialization, not the relative two-gauge conclusion of the
source.  See `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`. -/
theorem IsNormal.smul_mem_unitaryGroup_of_dressed_adjoint
    {A : MPSTensor d D} (hA : IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) (hX0 : X ≠ 0)
    (hdress : ∀ i, X * A i * X⁻¹ = X⁻¹ᴴ * (A i)ᴴ * Xᴴ)
    (hsa : ∀ i, (A i)ᴴ = A i) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ • X ∈ Matrix.unitaryGroup (Fin D) ℂ :=
  hA.smul_mem_unitaryGroup_of_commute hX0 fun i =>
    Matrix.commute_gram_of_dressed_adjoint_of_conjTranspose_eq hX (hdress i) (hsa i)

end MPSTensor
