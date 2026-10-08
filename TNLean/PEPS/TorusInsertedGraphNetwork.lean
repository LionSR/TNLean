/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusOrientedIncidentGInjectivity
import TNLean.PEPS.GraphInsertedBondState
import TNLean.PEPS.TorusProjectorExpansion

/-!
# Actual native torus contractions as inserted graph contractions

The native arrows point right and down. Reversing an arrow relative to the
ordered graph edge transposes its inserted matrix. Reindexing all virtual
endpoint labels identifies the two actual contraction formulas.
Source: SCP10, arXiv:1001.3807, equation `eq:2d:peps-with-ug-uh`.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {X : Type*} [Fintype X] [DecidableEq X]
local notation "TV" => TorusVertex width height
local notation "TG" => torusGraph width height

/-- Native torus bond matrices expressed in ordered graph coordinates.
Source: SCP10, equation `eq:2d:peps-with-ug-uh`. -/
def torusGraphBondMatrix (Oh Ov : TV → Matrix X X ℂ) (e : Edge TG) : Matrix X X ℂ :=
  match torusEdgeEquiv.symm e with
  | .inl v => if e.1.1 = v then Oh v else (Oh v).transpose
  | .inr v => if e.1.1 = v then (Ov v).transpose else Ov v

omit [Fintype X] [DecidableEq X] in
@[simp] theorem torusGraphBondMatrix_right (Oh Ov : TV → Matrix X X ℂ) (v : TV) :
    torusGraphBondMatrix Oh Ov (torusRightEdge v) =
      if (torusRightEdge v).1.1 = v then Oh v else (Oh v).transpose := by
  unfold torusGraphBondMatrix
  rw [show torusEdgeEquiv.symm (torusRightEdge v) = Sum.inl v from
    torusEdgeEquiv.symm_apply_apply (Sum.inl v)]

omit [Fintype X] [DecidableEq X] in
@[simp] theorem torusGraphBondMatrix_up (Oh Ov : TV → Matrix X X ℂ) (v : TV) :
    torusGraphBondMatrix Oh Ov (torusUpEdge v) =
      if (torusUpEdge v).1.1 = v then (Ov v).transpose else Ov v := by
  unfold torusGraphBondMatrix
  rw [show torusEdgeEquiv.symm (torusUpEdge v) = Sum.inr v from
    torusEdgeEquiv.symm_apply_apply (Sum.inr v)]

omit [Fact (2 < width)] [Fact (2 < height)] [DecidableEq X] in
private theorem torusBondNetwork_eq_sum_site (A : TV → (X × X × X × X) → ℂ)
    (Oh Ov : TV → Matrix X X ℂ) :
    torusBondNetwork A Oh Ov = ∑ η : TV → X × X × X × X,
      (∏ v, Oh v (η (v.1 + 1, v.2)).2.2.2 (η v).2.1 *
        Ov v (η v).1 (η (v.1, v.2 + 1)).2.2.1) * ∏ v, A v (η v) := by
  unfold torusBondNetwork
  rw [← (torusBondSiteLabelsEquiv (V := X) (width := width) (height := height)).symm.sum_comp]
  simp only [torusBondSiteLabelsEquiv, Equiv.coe_fn_symm_mk, sub_add_cancel]

omit [Fintype X] [DecidableEq X] in
private theorem torusGraphBondMatrix_right_apply (Oh Ov : TV → Matrix X X ℂ)
    (η : (v : TV) → IncidentEdge TG v → X) (v : TV) :
    torusGraphBondMatrix Oh Ov (torusRightEdge v)
      (graphSiteBondEndpointEquiv η (torusRightEdge v)).1
      (graphSiteBondEndpointEquiv η (torusRightEdge v)).2 =
      Oh v (η (v.1 + 1, v.2) (torusLeftLeg (v.1 + 1, v.2)))
        (η v (torusRightLeg v)) := by
  rw [torusGraphBondMatrix_right]
  by_cases hv : v < (v.1 + 1, v.2)
  · simp [graphSiteBondEndpointEquiv, torusRightEdge,
      Edge.ofAdj_of_lt _ hv, torusRightLeg, torusLeftLeg, torusLeftEdge,
      edgeRightIncident, edgeLeftIncident]
  · have hr : (v.1 + 1, v.2) < v :=
      lt_of_le_of_ne (le_of_not_gt hv) (torusGraph_adj_right v.1 v.2).ne.symm
    simp [graphSiteBondEndpointEquiv, torusRightEdge,
      Edge.ofAdj_of_gt _ hr, torusRightLeg, torusLeftLeg, torusLeftEdge,
      edgeRightIncident, edgeLeftIncident, ne_of_lt hr]

omit [Fintype X] [DecidableEq X] in
private theorem torusGraphBondMatrix_up_apply (Oh Ov : TV → Matrix X X ℂ)
    (η : (v : TV) → IncidentEdge TG v → X) (v : TV) :
    torusGraphBondMatrix Oh Ov (torusUpEdge v)
      (graphSiteBondEndpointEquiv η (torusUpEdge v)).1
      (graphSiteBondEndpointEquiv η (torusUpEdge v)).2 =
      Ov v (η v (torusTopLeg v))
        (η (v.1, v.2 + 1) (torusDownLeg (v.1, v.2 + 1))) := by
  rw [torusGraphBondMatrix_up]
  by_cases hv : v < (v.1, v.2 + 1)
  · simp [graphSiteBondEndpointEquiv, torusUpEdge,
      Edge.ofAdj_of_lt _ hv, torusTopLeg, torusDownLeg, torusDownEdge,
      edgeRightIncident, edgeLeftIncident]
  · have hr : (v.1, v.2 + 1) < v :=
      lt_of_le_of_ne (le_of_not_gt hv) (torusGraph_adj_up v.1 v.2).ne.symm
    simp [graphSiteBondEndpointEquiv, torusUpEdge,
      Edge.ofAdj_of_gt _ hr, torusTopLeg, torusDownLeg, torusDownEdge,
      edgeRightIncident, edgeLeftIncident, ne_of_lt hr]

omit [DecidableEq X] in
/-- The native torus network equals its actual ordered-edge inserted graph
contraction, including arbitrary bond matrices and arbitrary virtual alphabets.
Source: SCP10, equation `eq:2d:peps-with-ug-uh`. -/
theorem torusBondNetwork_eq_graphInsertedBondNetwork {d : ℕ}
    (a : X → X → X → X → Fin d → ℂ)
    (Oh Ov : TV → Matrix X X ℂ) (σ : TV → Fin d) :
    torusBondNetwork (fun v c => a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov =
      graphInsertedBondNetwork (torusGraphBondMatrix Oh Ov) (torusNativeIncidentSite a) σ := by
  classical
  rw [torusBondNetwork_eq_sum_site]
  unfold graphInsertedBondNetwork
  rw [← (graphSiteBondEndpointEquiv (Γ := TG) (X := X)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  let E := Equiv.piCongrRight (fun v : TV => torusNativeIncidentCoordinatesEquiv (X := X) v)
  rw [← E.sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  · rw [← torusEdgeEquiv.prod_comp, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    change _ = torusGraphBondMatrix Oh Ov (torusRightEdge v)
      (graphSiteBondEndpointEquiv η (torusRightEdge v)).1
      (graphSiteBondEndpointEquiv η (torusRightEdge v)).2 *
      torusGraphBondMatrix Oh Ov (torusUpEdge v)
      (graphSiteBondEndpointEquiv η (torusUpEdge v)).1
      (graphSiteBondEndpointEquiv η (torusUpEdge v)).2
    rw [torusGraphBondMatrix_right_apply, torusGraphBondMatrix_up_apply]
    rfl

end TNLean.PEPS
