/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.CanonicalForm.Correlation.ZeroCorrelationLength
import QICLean.Channel.Dilation.Stinespring
import QICLean.Algebra.Combinatorics.FinSumPermutation
import TNLean.MPS.CanonicalForm.Correlation.WindowCorrelator

/-!
# One-site insertion coordinates for a supplied physical isometry

A supplied map from the virtual space to physical space tensor virtual space
has one matrix slice for each physical index. Its isometry condition is the
trace-preserving normalization of those slices, and its Heisenberg insertion
is trace-dual to the one-site physical observable transfer.

Source: Nachtergaele, arXiv:cond-mat/9410110, equation defEA, lines
1445--1450. These are coordinate identities for a supplied map. They do not
construct normalized generating data from an arbitrary GVBS presentation or
identify the source's ordering of multi-site expectations.

## Source-ordered Heisenberg insertions and reversed physical products

Nachtergaele's equation (3.5) composes Heisenberg insertions in the written
order of the source sites. Trace duality reverses this order for the
Schrödinger insertion used by the physical observable transfer. Thus the
source product of one-site observables is represented by their reversed
physical tensor product. The empty product is included.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.5)--(3.6),
lines 1436--1450. These are identities for supplied matrix generators;
constructing them from an arbitrary GVBS presentation remains separate.
-/

section

open scoped Matrix Kronecker BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- The physical matrix slices of a supplied virtual-to-physical-virtual map.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation defEA, lines 1445--1450. -/
def tensorOfPhysicalIsometry (V : Matrix (Fin d × Fin D) (Fin D) ℂ) : MPSTensor d D :=
  fun i a b => V (i, a) b

/-- The normalization sum is the Gram matrix of the supplied map.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation defEA, lines 1445--1450. -/
theorem sum_conjTranspose_mul_tensorOfPhysicalIsometry
    (V : Matrix (Fin d × Fin D) (Fin D) ℂ) :
    (∑ i, (tensorOfPhysicalIsometry V i)ᴴ * tensorOfPhysicalIsometry V i) = Vᴴ * V := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    tensorOfPhysicalIsometry, Fintype.sum_prod_type]

/-- An isometry yields trace-preserving physical matrix slices.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation defEA, lines 1445--1450. -/
theorem isLeftCanonical_tensorOfPhysicalIsometry
    (V : Matrix (Fin d × Fin D) (Fin D) ℂ) (hV : Vᴴ * V = 1) :
    IsLeftCanonical (tensorOfPhysicalIsometry V) := by
  exact (sum_conjTranspose_mul_tensorOfPhysicalIsometry V).trans hV

/-- A supplied physical map has the stated one-site Heisenberg insertion.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation defEA, lines 1445--1450. -/
theorem physicalIsometry_heisenbergInsertion
    (V : Matrix (Fin d × Fin D) (Fin D) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin D) (Fin D) ℂ) :
    Vᴴ * (X ⊗ₖ B) * V = ∑ i, ∑ j,
      X i j • ((tensorOfPhysicalIsometry V i)ᴴ * B * tensorOfPhysicalIsometry V j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensorOfPhysicalIsometry, Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_last_two_first_four]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  congr 2 with c
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The one-site physical insertion uses the physical matrix indices directly.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation defEA, lines 1445--1450,
and its trace-dual Schrödinger insertion. -/
theorem physicalObservableTransfer_oneSite_apply
    (A : MPSTensor d D) (X : Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A 1 (X.submatrix (fun σ => σ 0) (fun τ => τ 0)) ρ =
      ∑ i, ∑ j, X i j • (A j * ρ * (A i)ᴴ) := by
  rw [physicalObservableTransfer_apply]
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin d)).symm
    (fun σ : Fin 1 → Fin d => ∑ τ : Fin 1 → Fin d,
      X.submatrix (fun σ => σ 0) (fun τ => τ 0) τ σ •
        (Kraus.evalWord A (List.ofFn σ) * ρ * (Kraus.evalWord A (List.ofFn τ))ᴴ))]
  simp_rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin d)).symm]
  simp only [Matrix.submatrix_apply, Equiv.funUnique_symm_apply, uniqueElim_const,
    List.ofFn_succ, List.ofFn_zero, Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one]
  exact Finset.sum_comm

/-- Trace duality between the supplied-map Heisenberg insertion and the existing
one-site physical observable transfer. No isometry or stationary-state
hypothesis is needed for this identity.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation defEA, lines 1445--1450. -/
theorem trace_physicalIsometry_heisenbergInsertion
    (V : Matrix (Fin d × Fin D) (Fin D) ℂ) (X : Matrix (Fin d) (Fin d) ℂ)
    (B ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (ρ * (Vᴴ * (X ⊗ₖ B) * V)) =
      Matrix.trace (B * physicalObservableTransfer (tensorOfPhysicalIsometry V) 1
        (X.submatrix (fun σ => σ 0) (fun τ => τ 0)) ρ) := by
  rw [physicalIsometry_heisenbergInsertion, physicalObservableTransfer_oneSite_apply]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simpa only [Matrix.mul_assoc] using congrArg (fun z : ℂ => X i j • z)
    (Matrix.trace_mul_comm (ρ * (tensorOfPhysicalIsometry V i)ᴴ)
      (B * tensorOfPhysicalIsometry V j))

end MPSTensor

end

section

open scoped Matrix Kronecker BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- The tensor product of a list of one-site observables, in reversed physical
order. Source: the trace-dual order of Nachtergaele, arXiv:cond-mat/9410110,
equations (3.5)--(3.6), lines 1436--1450. -/
noncomputable def reversedProductObservable :
    (Xs : List (Matrix (Fin d) (Fin d) ℂ)) → Matrix (Cfg d Xs.length) (Cfg d Xs.length) ℂ
  | [] => 1
  | X :: Xs => appendObservable (reversedProductObservable Xs)
      (X.submatrix (fun σ : Cfg d 1 => σ 0) (fun τ => τ 0))

/-- Source-written Heisenberg composition is the expectation of the reversed
physical product in the existing Schrödinger insertion convention. No
normalization, positivity, or stationarity is needed for this trace identity.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.5)--(3.6),
lines 1436--1450. -/
theorem sourceOrderedHeisenberg_trace_eq_reversedProduct_transfer
    (V : Matrix (Fin d × Fin D) (Fin D) ℂ)
    (Xs : List (Matrix (Fin d) (Fin d) ℂ)) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (ρ * Xs.foldr (fun X B => Vᴴ * (X ⊗ₖ B) * V) 1) =
      Matrix.trace (physicalObservableTransfer (tensorOfPhysicalIsometry V)
        Xs.length (reversedProductObservable Xs) ρ) := by
  induction Xs generalizing ρ with
  | nil =>
    simp only [List.foldr_nil, mul_one, List.length_nil, reversedProductObservable,
      physicalObservableTransfer_one, pow_zero, Module.End.one_apply]
  | cons X Xs ih =>
    simp only [List.foldr_cons, List.length_cons, reversedProductObservable]
    rw [trace_physicalIsometry_heisenbergInsertion,
      physicalObservableTransfer_appendObservable, Module.End.mul_apply]
    rw [Matrix.trace_mul_comm]
    exact ih _

end MPSTensor

end
