/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusNoncentralFluxDensity

/-!
# Vacuum flux density from the finite zero-crossing graph

Retain a physical bond when the signed native crossing count of the actual
dual path is zero. This graph is computed from the path, independently of
the insertion group or element. If the observed incident counts vanish and
one complementary component of this graph contains every complementary
boundary endpoint, the existing noncentral contraction proves the actual
native vacuum normalized density. Both cuts are derived nonzero.

Source: SCP10, arXiv:1001.3807v3, Theorem 6.9 and Lemma 6.14,
lines 1935–1990 and 2199–2214, under the stated finite graph conditions.
The observed graph and its complement are connected with nonempty boundary.
No simple connectedness or envelope is required. This is a sufficient
criterion, not a characterization of all equal-density observations.
See `docs/paper-gaps/scp10_zero_crossing_density.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance zeroCrossingWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance zeroCrossingHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
local instance zeroCrossingQuiver : Quiver X := torusDualQuiver width height

/-- The finite physical graph retaining precisely native bonds with zero
signed crossing count. Periodic seams use the same native base coordinates;
the definition is independent of any flux group or insertion element. -/
def torusDualZeroCrossingGraph {a b : X} (p : TorusDualPath a b) : SimpleGraph X where
  Adj v w := (Γₜ).Adj v w ∧
    ((w = (v.1 + 1, v.2) ∧ (torusDualPathCrossings p).1 v = 0) ∨
      (v = (w.1 + 1, w.2) ∧ (torusDualPathCrossings p).1 w = 0) ∨
      (w = (v.1, v.2 + 1) ∧ (torusDualPathCrossings p).2 v = 0) ∨
      (v = (w.1, w.2 + 1) ∧ (torusDualPathCrossings p).2 w = 0))
  symm := ⟨by
    intro v w h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨fun _ h => (SimpleGraph.ne_of_adj _ h.1) rfl⟩

variable {G : Type*} [Group G]

private theorem positive_transport {a b : X} (p : TorusDualPath a b) (g : G)
    (v : X) :
    ((torusDualPathCrossings p).1 v = 0 →
      ∀ h : (Γₜ).Adj v (v.1 + 1, v.2),
        regularDirectedTransport (v := v) (w := (v.1 + 1, v.2))
          (torusGraphRegularLabels (torusDualFluxLabels g p).1
            (torusDualFluxLabels g p).2) h = 1) ∧
    ((torusDualPathCrossings p).2 v = 0 →
      ∀ h : (Γₜ).Adj v (v.1, v.2 + 1),
        regularDirectedTransport (v := v) (w := (v.1, v.2 + 1))
          (torusGraphRegularLabels (torusDualFluxLabels g p).1
            (torusDualFluxLabels g p).2) h = 1) := by
  constructor
  · intro hz h
    change torusNativeRightTransport
      (torusGraphRegularLabels (torusDualFluxLabels g p).1 (torusDualFluxLabels g p).2) v = 1
    rw [torusNativeRightTransport_torusGraphRegularLabels]
    simp only [torusDualFluxLabels, torusFluxPowerLabels, hz, zpow_zero]
  · intro hz h
    change torusNativeUpTransport
      (torusGraphRegularLabels (torusDualFluxLabels g p).1 (torusDualFluxLabels g p).2) v = 1
    rw [torusNativeUpTransport_torusGraphRegularLabels]
    simp only [torusDualFluxLabels, torusFluxPowerLabels, hz, zpow_zero, inv_one]

/-- Every edge of the computed zero-crossing graph has identity actual
directed flux transport, for arbitrary groups and insertion elements. -/
theorem torusDualFlux_transport_eq_one_of_zero_crossing_edge
    {a b : X} (p : TorusDualPath a b) (g : G) {v w : X}
    (h : (torusDualZeroCrossingGraph p).Adj v w) :
    regularDirectedTransport (v := v) (w := w)
      (torusGraphRegularLabels (torusDualFluxLabels g p).1
        (torusDualFluxLabels g p).2) h.1 = 1 := by
  rcases h with ⟨hΓ, h⟩
  rcases h with ⟨rfl, hz⟩ | ⟨rfl, hz⟩ | ⟨rfl, hz⟩ | ⟨rfl, hz⟩
  · exact (positive_transport p g v).1 hz hΓ
  · apply (regularDirectedTransport_symm (v := w) (w := (w.1 + 1, w.2))
      (torusGraphRegularLabels (torusDualFluxLabels g p).1
        (torusDualFluxLabels g p).2) hΓ.symm).trans
    simp only [(positive_transport p g w).1 hz hΓ.symm, inv_one]
  · exact (positive_transport p g v).2 hz hΓ
  · apply (regularDirectedTransport_symm (v := w) (w := (w.1, w.2 + 1))
      (torusGraphRegularLabels (torusDualFluxLabels g p).1
        (torusDualFluxLabels g p).2) hΓ.symm).trans
    simp only [(positive_transport p g w).2 hz hΓ.symm, inv_one]

private theorem incident_ofAdj (R : Finset X) {v w : X} (h : (Γₜ).Adj v w) :
    IsRegionIncidentEdge R (Edge.ofAdj h) ↔ v ∈ R ∨ w ∈ R := by
  rcases Edge.ofAdj_endpoints h with h | h
  · simp only [IsRegionIncidentEdge, h.1, h.2]
  · simp only [IsRegionIncidentEdge, h.1, h.2, or_comm]

private theorem incident_labels_one (R : Finset X) {a b : X} (p : TorusDualPath a b)
    (hz : ∀ v : X,
      ((v ∈ R ∨ (v.1 + 1, v.2) ∈ R) → (torusDualPathCrossings p).1 v = 0) ∧
      ((v ∈ R ∨ (v.1, v.2 + 1) ∈ R) → (torusDualPathCrossings p).2 v = 0))
    (g : G) (f : Edge (Γₜ)) (hf : IsRegionIncidentEdge R f) :
    torusGraphRegularLabels (torusDualFluxLabels g p).1 (torusDualFluxLabels g p).2 f = 1 := by
  obtain ⟨z, rfl⟩ := torusEdgeEquiv.surjective f
  rcases z with v | v
  · change torusGraphRegularLabels (torusDualFluxLabels g p).1
      (torusDualFluxLabels g p).2 (torusRightEdge v) = 1
    have hi := (incident_ofAdj R (torusGraph_adj_right v.1 v.2)).mp hf
    have he := (hz v).1 hi
    unfold torusGraphRegularLabels
    rw [show torusEdgeEquiv.symm (torusRightEdge v) = Sum.inl v from
      torusEdgeEquiv.symm_apply_apply (Sum.inl v)]
    simp only [torusDualFluxLabels, torusFluxPowerLabels, he, zpow_zero, inv_one, ite_self]
  · change torusGraphRegularLabels (torusDualFluxLabels g p).1
      (torusDualFluxLabels g p).2 (torusUpEdge v) = 1
    have hi := (incident_ofAdj R (torusGraph_adj_up v.1 v.2)).mp hf
    have he := (hz v).2 hi
    unfold torusGraphRegularLabels
    rw [show torusEdgeEquiv.symm (torusUpEdge v) = Sum.inr v from
      torusEdgeEquiv.symm_apply_apply (Sum.inr v)]
    simp only [torusDualFluxLabels, torusFluxPowerLabels, he, zpow_zero, inv_one, ite_self]

private theorem graph_labels_one :
    torusGraphRegularLabels (1 : X → G) 1 = fun _ => 1 := by
  funext f
  unfold torusGraphRegularLabels
  cases he : torusEdgeEquiv.symm f <;> simp

variable [Fintype G] [DecidableEq G] {d : ℕ}

/-- A finite, group-independent graph criterion for actual native vacuum
normalized density. The observed graph and complement are connected, the
boundary is nonempty, incident signed counts vanish, and one component of
the computed complementary zero-crossing graph contains all boundary ends.
No topology, supplied gauge, Gram identity or nonzero cut is assumed.
Source: SCP10, Theorem 6.9 and Lemma 6.14 under these graph conditions. -/
theorem IsGIsometric.torusFlux_normalized_density_eq_vacuum_of_zero_crossing_connectivity
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hS : ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Connected)
    (hB : Nonempty {e : Edge (Γₜ) // IsRegionBoundaryEdge R e})
    (g : G) {a b : X} (p : TorusDualPath a b)
    (hz : ∀ v : X,
      ((v ∈ R ∨ (v.1 + 1, v.2) ∈ R) → (torusDualPathCrossings p).1 v = 0) ∧
      ((v ∈ R ∨ (v.1, v.2 + 1) ∈ R) → (torusDualPathCrossings p).2 v = 0))
    (hc : ∃ o : {v : X // v ∈ Finset.univ \ R},
      ∀ v : {v : X // v ∈ Finset.univ \ R}, (∃ w ∈ R, (Γₜ).Adj v.1 w) →
        ((torusDualZeroCrossingGraph p).induce
          ((Finset.univ \ R : Finset X) : Set X)).Reachable o v) :
    let M := torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R
    let M₀ := torusBondRegularPhysicalCutMatrix A 1 R
    M ≠ 0 ∧ M₀ ≠ 0 ∧
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
        (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  obtain ⟨o, ho⟩ := hc
  let U := (torusDualZeroCrossingGraph p).induce
    ((Finset.univ \ R : Finset X) : Set X)
  have hU : U ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X) :=
    fun _ _ h => h.1
  have hd := regularPhysicalCutMatrix_normalized_reduced_eq_of_untwisted_boundary_component
    (torusIncidentSite A) (fun v => hA.isGIsometric_torusIncidentSite v) R hR hS hB U hU o
    (torusGraphRegularLabels (torusDualFluxLabels g p).1 (torusDualFluxLabels g p).2)
    (fun {_ _} h => torusDualFlux_transport_eq_one_of_zero_crossing_edge p g h)
    ho (incident_labels_one R p hz g)
  have hvac : torusBondRegularPhysicalCutMatrix A 1 R =
      regularPhysicalCutMatrix (torusIncidentSite A) R := by
    rw [torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix]
    change regularPhysicalCutMatrix (regularTwistedSite (torusIncidentSite A)
      (torusGraphRegularLabels (1 : X → G) 1)) R = _
    rw [graph_labels_one, regularTwistedSite_one]
  rw [torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix A
    (torusDualFluxLabels g p) R, hvac]
  exact hd

end TNLean.PEPS
