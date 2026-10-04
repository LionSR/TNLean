/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphInsertedBondState
/-!
# Actual regular contractions with arbitrary diagonal bond weights

The diagonal weight acts on the tail register before the oriented group
insertion. Independent head and tail summation therefore gives an actual
weighted contraction; no span of diagonal matrices by group matrices is used.
Source: SCP10, arXiv:1001.3807, charge insertions, lines 2449–2486, and
charge–flux transport, lines 2569–2581. This is an auxiliary finite-graph
coefficient calculation, without a physical or Hamiltonian conclusion.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Arbitrary diagonal tail weights are retained in the literal regular
bond contraction. Source: SCP10, lines 2449–2486 and 2569–2581. -/
theorem graphInsertedBondNetwork_leftRegular_mul_diagonal {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (u : Edge Γ → G) (f : Edge Γ → G → ℂ) (σ : (v : V) → P v) :
    graphInsertedBondNetwork
      (fun e => leftRegularMatrix G (u e) * Matrix.diagonal (f e)) a σ =
      ∑ η : Edge Γ → G, (∏ e, f e (η e)) *
        ∏ v, a v (regularTwistedLabels u v (fun e => η e.1)) (σ v) := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Edge Γ) (fun _ => G) (fun _ => G)
  unfold graphInsertedBondNetwork
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [E, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk,
    Matrix.mul_diagonal, leftRegularMatrix_apply, Finset.prod_mul_distrib,
    Fintype.prod_boole, ← funext_iff]
  rw [Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext e
  rcases e.2 with ht | hh
  · have hn : ¬ v = e.1.1.2 := fun h => ne_of_lt e.1.2.1 (ht.trans h)
    simp [graphSiteBondEndpointEquiv, regularTwistedLabels, ht, hn]
  · have hn : ¬ e.1.1.1 = v := fun h => ne_of_lt e.1.2.1 (h.trans hh.symm)
    simp [graphSiteBondEndpointEquiv, regularTwistedLabels, hh, hn]
end TNLean.PEPS
