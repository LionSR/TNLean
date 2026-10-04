/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularWeightedGaugeTransport
import TNLean.PEPS.TorusSweptStringDeformation
import TNLean.PEPS.RegularTorusEntropy

/-!
# The literal native charge–flux string-deformation figure

The charge diagonal lies on the horizontal edge joining the two central
middle-row sites. The swept gauge contains both sites, so its action on the
diagonal is independent of the ordered orientation of this edge, including
at a periodic seam. The actual finite bond contraction changes from the
straight flux string to its swept presentation, with character coefficient
χ(p t) replaced by χ(p k⁻¹ t).

Source: SCP10, arXiv:1001.3807, lines 2560–2581 and
`figs5/chargeon-braiding-virtuallevel`.

**Scope restriction (native gauge presentation):** The periods are at least
five and four. These are literal string-deformation equalities on the original
physical spins. They do not identify a sequence of physical crossing operations
or its reunion measurement with a braid; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (4 < width)] [Fact (3 < height)]
local instance chargeStringWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance chargeStringHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance chargeStringWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance chargeStringHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The literal central charge edge in the three-row deformation figure.
Source: SCP10, lines 2569–2581. -/
def torusSweptStringChargeEdge (v : X) : Edge Γₜ :=
  Edge.ofAdj (torusGraph_adj_right (v.1 + 1) (v.2 + 1))

/-- Both endpoints of the charge diagonal are actually swept; native edge
sorting therefore does not alter its inverse-flux factor.
Source: SCP10, lines 2569–2581. -/
theorem torusSweptStringChargeEdge_tail_mem (v : X) (second : Bool) :
    (torusSweptStringChargeEdge v).1.1 ∈ torusSweptStringVertices v second := by
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right (v.1 + 1) (v.2 + 1)) with
    ⟨ht, _⟩ | ⟨ht, _⟩
  · rw [torusSweptStringChargeEdge, ht]
    cases second <;> simp [torusSweptStringVertices]
  · rw [torusSweptStringChargeEdge, ht]
    cases second <;> simp [torusSweptStringVertices, add_assoc] <;> norm_num

/-- The actual diagonal-weighted original-spin contraction obeys the literal
charge–flux deformation figure, including translated positions and seams.
The character is retained and its single-edge parameter is right-multiplied
by the inverse flux. Source: SCP10, lines 2560–2581. -/
theorem IsGIsometric.graphInsertedBondNetwork_torusChargeStringDeformation {d : ℕ}
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : X) (second : Bool) (k : G) (χ : G → ℂ) (p : G) (σ : X → Fin d) :
    graphInsertedBondNetwork
      (fun e => leftRegularMatrix G (torusSweptStringInitialOperators v k 1 e) *
        Matrix.diagonal (fun t => if e = torusSweptStringChargeEdge v then χ (p * t)
          else 1))
      (torusIncidentSite (width := width) (height := height) a) σ =
    graphInsertedBondNetwork
      (fun e => leftRegularMatrix G (torusSweptStringOperators v second k 1 e) *
        Matrix.diagonal (fun t => if e = torusSweptStringChargeEdge v
          then χ ((p * k⁻¹) * t) else 1))
      (torusIncidentSite (width := width) (height := height) a) σ := by
  classical
  have hinv : ∀ x w η s,
      torusIncidentSite (width := width) (height := height) a w (fun e => x * η e) s =
      torusIncidentSite (width := width) (height := height) a w η s := by
    intro x w η s
    exact (ha.isGIsometric_torusIncidentSite w).toIsGInjective.regularSiteMap_translation
      x η s
  have h := graphInsertedBondNetwork_diagonal_vertexGauge
    (torusIncidentSite (width := width) (height := height) a) hinv
    (regularSweptPatchGauge (torusSweptStringVertices v second) k)
    (torusSweptStringInitialOperators v k 1)
    (fun e t => if e = torusSweptStringChargeEdge v then χ (p * t) else 1) σ
  rw [← regularSweptPatchOperators_eq_vertexGauge] at h
  convert h using 1
  congr 1
  funext e
  congr 1
  funext t
  by_cases he : e = torusSweptStringChargeEdge v
  · subst e
    simp only [ite_true, regularSweptPatchGauge,
      ite_eq_left (torusSweptStringChargeEdge_tail_mem v second), mul_assoc]
  · simp only [ite_eq_right he]

end TNLean.PEPS
