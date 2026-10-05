/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularGraphSurplusSite
import TNLean.PEPS.GraphInsertedBondState

/-!
# Inserted regular bonds leave the surplus Bell registers unchanged

The relative-coordinate change on a bundle of regular bonds puts an arbitrary
edgewise regular insertion on its distinguished bond and the identity on every
surplus register. This gives an exact factorization of the actual independent
endpoint contraction with the original physical tensor retained. The row of an
inserted matrix is the head label and its column is the tail label, as in
`graphInsertedBondNetwork`; reversing an edge therefore retains the inverse
regular insertion rather than changing that convention.

Source: SCP10, arXiv:1001.3807, Observations 6.5–6.6, lines 1840–1909,
and the oriented insertions in equation `eq:2d:peps-with-ug-uh`, lines 1515–1525.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (K : Type*) [Fintype K] [DecidableEq K]
/-- Reversing the matrix endpoints in a regular bundle inverts its group
label. Source: SCP10, oriented regular insertions, lines 1515–1525. -/
theorem regularBundleMatrix_transpose (g : G) :
    (regularBundleMatrix K g).transpose = regularBundleMatrix K g⁻¹ := by
  ext x y
  simp only [Matrix.transpose_apply, regularBundleMatrix_apply, eq_inv_smul_iff,
    eq_comm]

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {P : V → Type*}

private theorem graphInsertedBondNetwork_regularBundle_eq_labels
    (a : (v : V) → (IncidentEdge Γ v → G × (K → G)) → P v → ℂ)
    (u : Edge Γ → G) (σ : (v : V) → P v) :
    graphInsertedBondNetwork (fun e => regularBundleMatrix K (u e)) a σ =
      graphBondNetwork (fun v η s =>
        a v (fun f => if v = f.1.1.2 then u f.1 • η f else η f) s) σ := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Edge Γ)
    (fun _ => G × (K → G)) (fun _ => G × (K → G))
  unfold graphInsertedBondNetwork
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [E, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk,
    regularBundleMatrix_apply, Fintype.prod_boole, ← funext_iff]
  rw [Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold graphBondNetwork
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext f
  rcases f.2 with ht | hh
  · have hn : ¬ v = f.1.1.2 := fun h => ne_of_lt f.1.2.1 (ht.trans h)
    simp [graphSiteBondEndpointEquiv, ht, hn]
  · have hn : ¬ f.1.1.1 = v := fun h => ne_of_lt f.1.2.1 (h.trans hh.symm)
    simp [graphSiteBondEndpointEquiv, hh, hn]

omit [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K] [Fintype V]
  [DecidableRel Γ.Adj] in
/-- Edgewise simultaneous regular insertions act only on the distinguished
relative coordinate. All surplus coordinates stay fixed, including at the
head of a twisted edge. Source: SCP10, lines 1840–1873 and 1515–1525. -/
theorem regularSurplusCoordinates_twisted
    (u : Edge Γ → G) (v : V) (η : IncidentEdge Γ v → G × (K → G)) :
    regularSurplusCoordinates K _
        (fun f => if v = f.1.1.2 then u f.1 • η f else η f) =
      (regularTwistedLabels u v (regularSurplusCoordinates K _ η).1,
        (regularSurplusCoordinates K _ η).2) := by
  apply Prod.ext
  · funext f
    simp only [regularSurplusCoordinates, regularTwistedLabels, Equiv.coe_fn_mk]
    split_ifs <;> rfl
  · funext f k
    simp only [regularSurplusCoordinates, Equiv.coe_fn_mk]
    split_ifs <;> simp [Pi.smul_apply, mul_inv_rev, mul_assoc]

/-- The actual inserted surplus network is exactly the original network with
the same oriented regular insertions, times the untwisted surplus Bell product.
No local isometry hypothesis or global state identity is assumed. The formula
holds for every edge-label assignment, so one physical construction treats all
inserted sectors. Source: SCP10, Observations 6.5–6.6 and
`eq:2d:peps-with-ug-uh`, lines 1840–1909 and 1515–1525. -/
theorem graphInsertedBondNetwork_regularGraphSurplusSite
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (u : Edge Γ → G) (σ : (v : V) → P v)
    (τ : (v : V) → IncidentEdge Γ v → K → G) :
    graphInsertedBondNetwork (fun e => regularBundleMatrix K (u e))
        (regularGraphSurplusSite K a) (fun v => (σ v, τ v)) =
      graphInsertedBondNetwork (fun e => leftRegularMatrix G (u e)) a σ *
        regularGraphResidualBell K τ := by
  rw [graphInsertedBondNetwork_regularBundle_eq_labels,
    graphInsertedBondNetwork_leftRegular_eq_labels]
  have hs : (fun v η s => regularGraphSurplusSite K a v
      (fun f => if v = f.1.1.2 then u f.1 • η f else η f) s) =
      regularGraphSurplusSite K
        (fun v η s => a v (regularTwistedLabels u v η) s) := by
    funext v η s
    simp only [regularGraphSurplusSite, regularSurplusCoordinates_twisted]
  rw [hs, graphBondNetwork_regularGraphSurplusSite]

end TNLean.PEPS
