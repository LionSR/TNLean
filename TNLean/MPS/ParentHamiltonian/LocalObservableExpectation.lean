/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import TNLean.MPS.ParentHamiltonian.LocalObservableInsertion

/-!
# Positivity and normalization of local MPS expectations

The local expectation is the trace of an observable insertion at a positive
transfer invariant matrix, divided by the trace of that matrix. Positivity
follows by expressing the insertion as a congruence of the positive matrix
formed from the transposed observable and the invariant matrix. Normalization
uses only invariance and a nonzero trace; primitivity is unnecessary. The
expectations agree when identity sites are adjoined on either side, using
trace preservation on the left and fixed-point invariance on the right.

These are the local state properties of the GVBS expectation in Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), used in the local expectation
limit in lines 2649--2675. No completion to an infinite-chain algebra is asserted.
-/

open scoped Matrix BigOperators Kronecker ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

set_option backward.isDefEq.respectTransparency false in
private theorem physicalObservableTransfer_wordMatrix (A : MPSTensor d D) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    let B : Matrix (Fin D) (Cfg d k × Fin D) ℂ :=
      fun i p => Kraus.evalWord A (List.ofFn p.1) i p.2
    physicalObservableTransfer A k X ρ = B * (Xᵀ ⊗ₖ ρ) * Bᴴ := by
  classical
  ext i j
  simp only [physicalObservableTransfer_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin D))
    (t := Finset.univ (α := Cfg d k))]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- A positive local observable inserts a positive map on virtual matrices.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem physicalObservableTransfer_posSemidef (A : MPSTensor d D) {k : ℕ}
    {X : Matrix (Cfg d k) (Cfg d k) ℂ} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hX : X.PosSemidef) (hρ : ρ.PosSemidef) :
    (physicalObservableTransfer A k X ρ).PosSemidef := by
  rw [physicalObservableTransfer_wordMatrix]
  exact (hX.transpose.kronecker hρ).mul_mul_conjTranspose_same _

/-- The expectation of the identity is one at any nonzero-trace transfer fixed
point. Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem observableInsertionExpectation_one (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hfix : Kraus.transferMap A ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (k : ℕ) :
    observableInsertionExpectation A ρ (1 : Matrix (Cfg d k) (Cfg d k) ℂ) = 1 := by
  have hpow : (Kraus.transferMap A ^ k) ρ = ρ := by
    rw [Module.End.pow_apply]
    exact Function.IsFixedPt.iterate hfix k
  simp only [observableInsertionExpectation, physicalObservableTransfer_one, hpow,
    div_self htr]

/-- A positive observable has a nonnegative local expectation at a positive
virtual matrix. Source: Nachtergaele, arXiv:cond-mat/9410110, equations
(3.1)--(3.2b). -/
theorem observableInsertionExpectation_nonneg (A : MPSTensor d D) {k : ℕ}
    {ρ : Matrix (Fin D) (Fin D) ℂ} {X : Matrix (Cfg d k) (Cfg d k) ℂ}
    (hρ : ρ.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ observableInsertionExpectation A ρ X := by
  exact div_nonneg (physicalObservableTransfer_posSemidef A hX hρ).trace_nonneg
    hρ.trace_nonneg

/-- Local expectations are additive in the observable. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem observableInsertionExpectation_add (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) {k : ℕ}
    (X Y : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectation A ρ (X + Y) =
      observableInsertionExpectation A ρ X + observableInsertionExpectation A ρ Y := by
  have h := congrArg (fun T => Matrix.trace (T ρ) / Matrix.trace ρ)
    ((physicalObservableTransferₗ A k).map_add X Y)
  simpa only [observableInsertionExpectation, physicalObservableTransferₗ_apply,
    LinearMap.add_apply, Matrix.trace_add, add_div] using h

/-- Local expectations are complex linear in the observable. Source:
Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem observableInsertionExpectation_smul (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) {k : ℕ} (c : ℂ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectation A ρ (c • X) =
      c * observableInsertionExpectation A ρ X := by
  have h := congrArg (fun T => Matrix.trace (T ρ) / Matrix.trace ρ)
    ((physicalObservableTransferₗ A k).map_smul c X)
  simpa only [observableInsertionExpectation, physicalObservableTransferₗ_apply,
    LinearMap.smul_apply, Matrix.trace_smul, smul_eq_mul, mul_div_assoc] using h

/-- Adjoining identity sites on the right preserves a local expectation at a
transfer fixed point. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), consistency of the finite local expectations. -/
theorem observableInsertionExpectation_appendObservable_one (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hfix : Kraus.transferMap A ρ = ρ)
    {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) (m : ℕ) :
    observableInsertionExpectation A ρ
      (appendObservable X (1 : Matrix (Cfg d m) (Cfg d m) ℂ)) =
        observableInsertionExpectation A ρ X := by
  have hpow : (Kraus.transferMap A ^ m) ρ = ρ := by
    rw [Module.End.pow_apply]
    exact Function.IsFixedPt.iterate hfix m
  simp only [observableInsertionExpectation, physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_one, Module.End.mul_apply, hpow]

/-- Adjoining identity sites on the left preserves a local expectation for a
trace-preserving tensor. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), consistency of the finite local expectations. -/
theorem observableInsertionExpectation_one_appendObservable (A : MPSTensor d D)
    (hTP : ∑ i, (A i)ᴴ * A i = 1) (ρ : Matrix (Fin D) (Fin D) ℂ)
    {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) (m : ℕ) :
    observableInsertionExpectation A ρ
      (appendObservable (1 : Matrix (Cfg d m) (Cfg d m) ℂ) X) =
        observableInsertionExpectation A ρ X := by
  have hpow : ∀ Y, Matrix.trace ((Kraus.transferMap A ^ m) Y) = Matrix.trace Y := by
    intro Y
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact (Kraus.isTracePreservingMap_mapLM_of_isTP A hTP _).trans ih
  simp only [observableInsertionExpectation, physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_one, Module.End.mul_apply, hpow]

/-- A normalized primitive tensor has normalized local expectations. Source:
Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem IsPrimitiveMPS.observableInsertionExpectation_one [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (k : ℕ) :
    observableInsertionExpectation A ρ (1 : Matrix (Cfg d k) (Cfg d k) ℂ) = 1 :=
  MPSTensor.observableInsertionExpectation_one A ρ hP.fixedPoint_is_fixed hP.trace_ne_zero k

/-- A normalized primitive tensor has positive local expectations. Source:
Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem IsPrimitiveMPS.observableInsertionExpectation_nonneg [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) {k : ℕ} {X : Matrix (Cfg d k) (Cfg d k) ℂ}
    (hX : X.PosSemidef) : 0 ≤ observableInsertionExpectation A ρ X :=
  MPSTensor.observableInsertionExpectation_nonneg A hP.fixedPoint_psd hX

end MPSTensor
