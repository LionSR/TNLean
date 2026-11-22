/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SitePermutation

/-!
# Products of single-site permutation gates

A permutation `σ` of the labels of one site acts on vectors by its permutation matrix. A product
of single-site permutation matrices acts by permuting the label of every site
(`Matrix.finKronecker_permMatrix_mulVec`): these are the single-site shifts `X^c` of the
measurement-assisted preparation of GHZ-type states in arXiv:2103.13367, Example 1, generalizing
the Pauli corrections from qubits to qudits.

## Main results

* `Matrix.finKronecker_permMatrix_mulVec`.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ}

/-- **Single-site permutations.** The Kronecker product of the permutation matrices of
permutations `σ i` of the labels of the sites `i` acts on vectors as `v ↦ v ∘ σ`, where `σ`
applies `σ i` at every site `i`. -/
theorem _root_.Matrix.finKronecker_permMatrix_mulVec {N : ℕ} (σ : Fin N → Equiv.Perm (Fin d))
    (v : (Fin N → Fin d) → ℂ) :
    finKronecker (fun i => (σ i).permMatrix ℂ) *ᵥ v = fun x => v fun i => σ i (x i) := by
  classical
  funext x
  have h : ∀ y : Fin N → Fin d, finKronecker (fun i => (σ i).permMatrix ℂ) x y =
      if y = (fun i => σ i (x i)) then 1 else 0 := fun y => by
    simp only [finKronecker_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies, funext_iff, eq_comm]
  simp only [mulVec, dotProduct, h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

end QuantumCircuit
