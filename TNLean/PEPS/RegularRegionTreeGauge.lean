/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionCoordinates
import TNLean.PEPS.RegularTwistedRegion

/-!
# Removing regular bond operators on a spanning tree

Choose a spanning tree and a root in a finite region. Its bond operators determine
a unique vertex gauge equal to the identity at the root. The transformed operator
on an internal edge is `k_head⁻¹ * u * k_tail`; it is the identity on every tree
edge. The remaining edges retain their residual operators. Crossing labels are
transported by the gauge at their region endpoint, including the bond operator
when that endpoint is the head.

These reversible group-coordinate identities accompany the accessible virtual
systems and blocking argument of Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, local source lines 1765–1920. They do not assume a factorization
of a twisted region contraction or assert a parent-Hamiltonian theorem.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]

private def ambientTreeEdge (R : Finset V) (T : SimpleGraph {v : V // v ∈ R})
    (hT : T ≤ Γ.induce (R : Set V)) (e : Edge T) : Edge Γ :=
  ⟨(e.1.1.1, e.1.2.1), e.2.1, hT e.2.2⟩

/-- The root-normalized vertex gauge determined by the operators on a chosen
spanning tree. Source: SCP10, reversible regular blocking, lines 1765–1920. -/
noncomputable def regularRegionTreeGauge (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) : RootedGroupLabels (G := G) o :=
  (rootedTreeGradientEquiv T htree o).symm (fun e => u (ambientTreeEdge R T hT e))

/-- The chosen gauge is the identity at the root. -/
@[simp]
theorem regularRegionTreeGauge_root (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) : (regularRegionTreeGauge R T hT htree o u).1 o = 1 :=
  (regularRegionTreeGauge R T hT htree o u).2

/-- The gradient of the normalized gauge reproduces each native internal tree
operator. Source: SCP10, controlled regular-coordinate changes, lines 1765–1920. -/
theorem regularRegionTreeGauge_gradient (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R})
    (he : T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩) :
    (regularRegionTreeGauge R T hT htree o u).1 ⟨e.1.1.2, e.2.2⟩ *
        ((regularRegionTreeGauge R T hT htree o u).1 ⟨e.1.1.1, e.2.1⟩)⁻¹ = u e.1 := by
  have h := congrFun ((rootedTreeGradientEquiv T htree o).apply_symm_apply
    (fun f => u (ambientTreeEdge R T hT f)))
      ⟨(⟨e.1.1.1, e.2.1⟩, ⟨e.1.1.2, e.2.2⟩), e.1.2.1, he⟩
  exact h

/-- The residual operator on an internal edge after applying the vertex gauge.
The ambient orientation is from its smaller to its larger endpoint. -/
def regularRegionGaugeResidual (R : Finset V) (k : {v : V // v ∈ R} → G)
    (u : Edge Γ → G) : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G :=
  fun e => (k ⟨e.1.1.2, e.2.2⟩)⁻¹ * u e.1 * k ⟨e.1.1.1, e.2.1⟩

omit [Fintype G] in
/-- The transformed head label is the residual operator applied to the
transformed tail reference. This is an identity of native edge labels. -/
theorem regularRegionGaugeResidual_transport (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) (η : G) :
    regularRegionGaugeResidual R k u e * ((k ⟨e.1.1.1, e.2.1⟩)⁻¹ * η) =
      (k ⟨e.1.1.2, e.2.2⟩)⁻¹ * (u e.1 * η) := by
  simp only [regularRegionGaugeResidual]
  group

/-- The normalized tree gauge removes every operator on the chosen tree.
Source: SCP10, regular blocking and controlled coordinate changes, lines 1765–1920. -/
theorem regularRegionGaugeResidual_eq_one_of_tree (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R})
    (he : T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩) :
    regularRegionGaugeResidual R (regularRegionTreeGauge R T hT htree o u).1 u e = 1 := by
  unfold regularRegionGaugeResidual
  rw [← regularRegionTreeGauge_gradient R T hT htree o u e he]
  group

/-- The remaining native operators, indexed only by the internal edges outside
the spanning tree. No flatness of these cycle residuals is assumed. -/
noncomputable def regularRegionTreeCycleResidual (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (u : Edge Γ → G) :
    {e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
      ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G :=
  fun e => regularRegionGaugeResidual R (regularRegionTreeGauge R T hT htree o u).1 u e.1

/-- Reversible transport of the internal reference labels by the gauge at their
smaller endpoints. -/
def regularRegionGaugeInternalLabels (R : Finset V) (k : {v : V // v ∈ R} → G) :
    ({e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G) ≃
      ({e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G) :=
  Equiv.piCongrRight fun e => Equiv.mulLeft (k ⟨e.1.1.1, e.2.1⟩)⁻¹

omit [Fintype G] in
/-- The transformed reference on an internal edge. -/
@[simp]
theorem regularRegionGaugeInternalLabels_apply (R : Finset V)
    (k : {v : V // v ∈ R} → G)
    (η : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G)
    (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) :
    regularRegionGaugeInternalLabels R k η e = (k ⟨e.1.1.1, e.2.1⟩)⁻¹ * η e := rfl

/-- Reversible left translation of each physical half-edge by the inverse of
the gauge at its vertex. -/
def regularRegionGaugePhysicalLabels (R : Finset V) (k : {v : V // v ∈ R} → G) :
    ((v : {v : V // v ∈ R}) → IncidentEdge Γ v.1 → G) ≃
      ((v : {v : V // v ∈ R}) → IncidentEdge Γ v.1 → G) :=
  Equiv.piCongrRight fun v => Equiv.piCongrRight fun _ => Equiv.mulLeft (k v)⁻¹

omit [Fintype G] in
/-- The gauge acts simultaneously on all physical half-edges at a vertex. -/
@[simp]
theorem regularRegionGaugePhysicalLabels_apply (R : Finset V)
    (k : {v : V // v ∈ R} → G)
    (α : (v : {v : V // v ∈ R}) → IncidentEdge Γ v.1 → G)
    (v : {v : V // v ∈ R}) (e : IncidentEdge Γ v.1) :
    regularRegionGaugePhysicalLabels R k α v e = (k v)⁻¹ * α v e := rfl

/-- Reversible transport of crossing labels to the region endpoint. The bond
operator is included precisely when that endpoint is the larger endpoint.
Source: SCP10, accessible virtual systems and disentangling, lines 1765–1920. -/
def regularRegionBoundaryTransport (R : Finset V) (k : {v : V // v ∈ R} → G)
    (u : Edge Γ → G) :
    ({e : Edge Γ // IsRegionBoundaryEdge R e} → G) ≃
      ({e : Edge Γ // IsRegionBoundaryEdge R e} → G) :=
  Equiv.piCongrRight fun e => Equiv.mulLeft
    (if h : e.1.1.1 ∈ R then (k ⟨e.1.1.1, h⟩)⁻¹ else
      (k ⟨e.1.1.2, by
        rcases e.2 with ht | hh
        · exact False.elim (h ht.1)
        · exact hh.2⟩)⁻¹ * u e.1)

omit [Fintype G] in
/-- A crossing label at the smaller endpoint acquires only the vertex gauge. -/
theorem regularRegionBoundaryTransport_tail (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (e : Edge Γ) (ht : e.1.1 ∈ R) (hh : e.1.2 ∉ R) :
    regularRegionBoundaryTransport R k u θ ⟨e, Or.inl ⟨ht, hh⟩⟩ =
      (k ⟨e.1.1, ht⟩)⁻¹ * θ ⟨e, Or.inl ⟨ht, hh⟩⟩ := by
  simp [regularRegionBoundaryTransport, ht]

omit [Fintype G] in
/-- A crossing label at the larger endpoint acquires its bond operator before
the inverse vertex gauge. -/
theorem regularRegionBoundaryTransport_head (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (e : Edge Γ) (ht : e.1.1 ∉ R) (hh : e.1.2 ∈ R) :
    regularRegionBoundaryTransport R k u θ ⟨e, Or.inr ⟨ht, hh⟩⟩ =
      (k ⟨e.1.2, hh⟩)⁻¹ * (u e * θ ⟨e, Or.inr ⟨ht, hh⟩⟩) := by
  simp [regularRegionBoundaryTransport, ht, mul_assoc]

omit [Fintype G] in
/-- A vertex gauge transforms native twisted half-edge labels into the labels
of the gauged bond operators. Tail references transform by the inverse tail
gauge, and physical half-edges by the inverse gauge at their vertex.
Source: SCP10, controlled regular-coordinate changes, lines 1765–1920. -/
theorem regularTwistedLabels_gauge (u : Edge Γ → G) (k : V → G) (v : V)
    (η : IncidentEdge Γ v → G) :
    regularTwistedLabels (fun e => (k e.1.2)⁻¹ * u e * k e.1.1) v
        (fun f => (k f.1.1.1)⁻¹ * η f) =
      fun f => (k v)⁻¹ * regularTwistedLabels u v η f := by
  funext f
  by_cases hh : v = f.1.1.2
  · simp only [regularTwistedLabels, ite_eq_left hh]
    rw [congrArg k hh]
    group
  · have ht : f.1.1.1 = v := f.2.resolve_right (fun h => hh h.symm)
    simp only [regularTwistedLabels, ite_eq_right hh, ht]

end TNLean.PEPS
