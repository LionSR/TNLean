/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.ScalarCommutant
import TNLean.Algebra.MatrixGramUnitary
import TNLean.MPS.CanonicalForm.CyclicSectors.Basic
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
X_{\alpha,1}^\dagger X_{\alpha,1}$, in the normalization $X_{\alpha,1} = \Id$,
together with the isometric normalization
$U_{\alpha,k} = \omega_{\alpha,k}^{-1/2} X_{\alpha,k}$ of lines 1906--1908.
The derivation of the commutation hypothesis from self-adjointness of the
sector compressions (the two displayed diagrams of lines 1909--1919) is a
separate step.

## Main results

* `MPSTensor.IsNormal.eq_smul_one_of_commute`:
  a matrix commuting with every matrix of a normal tensor is scalar.
* `MPSTensor.IsNormal.conjTranspose_mul_self_eq_smul_one_of_commute`:
  if $X \ne 0$ and $X^\dagger X$ commutes with every matrix of a normal
  tensor, then $X^\dagger X = \omega\,\Id$ with $\omega > 0$.
* `MPSTensor.IsNormal.smul_mem_unitaryGroup_of_commute`:
  under the same hypotheses, $\omega^{-1/2}X$ is unitary.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  proof of Proposition 4.13, lines 1904--1921
-/

open scoped Matrix ComplexOrder

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
  obtain ⟨N, hN⟩ := hA
  have hwords : ∀ M ∈ Set.range fun σ : Fin N → Fin d => evalWord A (List.ofFn σ),
      S * M = M * S := by
    rintro _ ⟨σ, rfl⟩
    exact commutes_evalWord_of_commutes_letters S A hS (List.ofFn σ)
  obtain ⟨c, hc⟩ := Matrix.isScalar_of_commute_span_eq_top S hN hwords
  refine ⟨c, ?_⟩
  rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

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

end MPSTensor
