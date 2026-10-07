/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SuppliedIsometryInsertion
import TNLean.MPS.Preparation.WindowCorrelator

/-!
# Source-ordered Heisenberg insertions and reversed physical products

Nachtergaele's equation (3.5) composes Heisenberg insertions in the written
order of the source sites. Trace duality reverses this order for the
Schrödinger insertion used by the physical observable transfer. Thus the
source product of one-site observables is represented by their reversed
physical tensor product. The empty product is included.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.5)--(3.6),
lines 1436--1450. These are identities for supplied matrix generators;
constructing them from an arbitrary GVBS presentation remains separate.
-/

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
