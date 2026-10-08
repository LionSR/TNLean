/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableExpectation
import QICLean.Algebra.MatrixAux
import TNLean.Algebra.FinSumPermutation

/-!
# Faithfulness and finite MPS support

For any tensor and positive-definite virtual matrix, the insertion expectation
of a square observable vanishes precisely when the observable annihilates the
MPS boundary space. Thus the support of the finite positive functional is
exactly this boundary space. Tensor normalization, transfer invariance,
injectivity, and primitivity are unnecessary; the interval may have length zero.

**Scope restriction (supplied faithful generators):** This finite-dimensional
support characterization applies to the faithful minimal generators in
Nachtergaele, arXiv:cond-mat/9410110, lines 1724--1738, when they are
supplied. It does not construct these generators from an arbitrary GVBS
presentation; that passage is recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D k : ℕ}

private theorem physicalObservableTransfer_square (A : MPSTensor d D)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A k (Xᴴ * X) ρ =
      ∑ b : Cfg d k,
        (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)) * ρ *
          (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ))ᴴ := by
  classical
  simp only [physicalObservableTransfer_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.sum_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  simp only [Finset.smul_sum, smul_smul]
  exact Fintype.sum_reverse_three _

private theorem contracted_words_eq_zero_of_faithful_square_expectation
    [NeZero D] (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hzero : observableInsertionExpectation A ρ (Xᴴ * X) = 0) :
    ∀ b : Cfg d k, (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)) = 0 := by
  classical
  let C (b : Cfg d k) := ∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)
  have htr : Matrix.trace (physicalObservableTransfer A k (Xᴴ * X) ρ) = 0 := by
    simpa only [observableInsertionExpectation, div_eq_zero_iff,
      ne_of_gt hρ.trace_pos, or_false] using hzero
  have htrace : Matrix.trace (ρ * ∑ b : Cfg d k, (C b)ᴴ * C b) = 0 := by
    calc
      Matrix.trace (ρ * ∑ b : Cfg d k, (C b)ᴴ * C b) =
          ∑ b : Cfg d k, Matrix.trace (ρ * ((C b)ᴴ * C b)) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
      _ = ∑ b : Cfg d k, Matrix.trace (C b * ρ * (C b)ᴴ) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [← Matrix.mul_assoc]
        exact Matrix.trace_mul_cycle ρ (C b)ᴴ (C b)
      _ = Matrix.trace (physicalObservableTransfer A k (Xᴴ * X) ρ) := by
        rw [physicalObservableTransfer_square, Matrix.trace_sum]
      _ = 0 := htr
  have hsum : (∑ b : Cfg d k, (C b)ᴴ * C b) = 0 :=
    Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero
      (Matrix.posSemidef_sum Finset.univ fun b _ => Matrix.posSemidef_conjTranspose_mul_self (C b))
      hρ htrace
  exact Matrix.eq_zero_of_sum_conjTranspose_mul_self_eq_zero C hsum

open scoped Matrix.Norms.Frobenius

private theorem groundSpaceES_le_ker_of_contracted_words_eq_zero
    (A : MPSTensor d D) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hC : ∀ b : Cfg d k,
      (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)) = 0) :
    groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X) := by
  rw [← range_groundSpaceMapES]
  rintro ψ ⟨v, rfl⟩
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective v
  rw [LinearMap.mem_ker]
  change Matrix.toEuclideanLin X (groundSpaceMapES A k
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) Y)) = 0
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply]
  apply PiLp.ext
  intro b
  change ∑ σ : Cfg d k, X b σ * Matrix.trace
    (Kraus.evalWord A (List.ofFn σ) * Y) = 0
  have h := congrArg (fun C => Matrix.trace (C * Y)) (hC b)
  simpa only [Finset.sum_mul, smul_mul_assoc, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, zero_mul, Matrix.trace_zero] using h

private theorem contracted_words_eq_zero_of_groundSpaceES_le_ker
    (A : MPSTensor d D) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hX : groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X)) :
    ∀ b : Cfg d k, (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)) = 0 := by
  classical
  intro b
  apply (Matrix.trace_mul_right_eq_zero_iff _).mp
  intro Y
  have h := LinearMap.mem_ker.mp (hX ((range_groundSpaceMapES A k).le
    ⟨Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) Y, rfl⟩))
  change Matrix.toEuclideanLin X (groundSpaceMapES A k
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) Y)) = 0 at h
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply] at h
  have hb := congrArg (fun v : EuclideanSpace ℂ (Cfg d k) => v b) h
  change (∑ σ : Cfg d k, X b σ * Matrix.trace
    (Kraus.evalWord A (List.ofFn σ) * Y)) = 0 at hb
  simpa only [Finset.sum_mul, smul_mul_assoc, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul] using hb

/-- A faithful virtual matrix gives exactly the MPS boundary space as the finite
support: a square observable has zero insertion expectation if and only if
its factor annihilates the boundary space. No tensor normalization, transfer
invariance, injectivity, or primitivity is required. This is the finite support
identification used in Nachtergaele, arXiv:cond-mat/9410110, lines 1724--1738,
once faithful generating data are supplied. -/
theorem observableInsertionExpectation_conjTranspose_mul_self_eq_zero_iff
    [NeZero D] (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectation A ρ (Xᴴ * X) = 0 ↔
      groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X) := by
  constructor
  · intro hzero
    exact groundSpaceES_le_ker_of_contracted_words_eq_zero A X
      (contracted_words_eq_zero_of_faithful_square_expectation A hρ X hzero)
  · intro hX
    have hC := contracted_words_eq_zero_of_groundSpaceES_le_ker A X hX
    simp only [observableInsertionExpectation, physicalObservableTransfer_square,
      hC, zero_mul, Finset.sum_const_zero, Matrix.trace_zero, zero_div]

end MPSTensor
