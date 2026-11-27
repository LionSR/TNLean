/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Region.RegionKernelDescent

/-!
# Middle physical indices for edge-blocked PEPS

This file gives the middle tensor in the edge-centered three-site decomposition
its own physical index. For an edge $e=(u,v)$, the middle physical
configuration is the family of physical indices on $V\setminus\{u,v\}$.

The middle tensor is the blocked-region tensor of $V\setminus\{u,v\}$, up to
an identification of the open indices and the factor $\dim A_e$ from the free
sum over the index on $e$, which meets no middle vertex. Its injectivity is
therefore the arbitrary-region theorem at that region, with no second
kernel-descent argument.

## Main results

* `TNLean.PEPS.regionBlockedWeight_edgeMiddleRegionBoundaryConfig` — blocking
  $V\setminus\{u,v\}$ gives $\dim A_e$ times the edge-middle tensor.
* `TNLean.PEPS.edgeMiddleTensorInjective_of_isVertexInjective` — the edge-middle
  tensor of a vertex-injective PEPS with positive bonds is injective.
* `TNLean.PEPS.IsVertexInjective.edgeBlockedThreeSiteInjective` — every edge
  blocking of such a PEPS is an injective three-site chain.

## References

- [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, Section 3, `eq:block_to_mps`](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 981--1009.
- `Papers/1804.04964/paper_normal.tex`, lines 1322--1404.
-/

open ManyBody (Edge)

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Physical configurations on the middle block $V\setminus\{u,v\}$ in the
edge-centered three-site decomposition at the edge $e=(u,v)$.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
abbrev EdgeMiddlePhysicalConfig (e : Edge G) : Type _ :=
  (v : {v : V // v ∈ edgeMiddleVertices e}) → Fin d

/-- Restrict a global physical configuration to the middle block of the
edge-centered three-site decomposition.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
def edgeMiddlePhysicalConfigOf (e : Edge G) (σ : V → Fin d) :
    EdgeMiddlePhysicalConfig (G := G) (d := d) e :=
  fun v => σ v.1

/-- The blocked middle tensor with the distinguished edge left open, written
with its own middle physical index.

The endpoint residual data are fixed, while the matrix index on the
distinguished edge is absent from the middle region. This is the middle block
of the edge-centered three-site chain in arXiv:1804.04964, Section 3. -/
noncomputable def edgeOpenMiddleWeightOn (A : Tensor G d) (e : Edge G)
    (τ : EdgeMiddlePhysicalConfig (G := G) (d := d) e)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    ℂ :=
  ∑ ζ : EdgeOpenMiddleConfig (G := G) A e leftResidual rightResidual,
    ∏ v : {v : V // v ∈ edgeMiddleVertices e},
      A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ.1 v.2 ie)
        (τ v)

/-- The ordinary blocked middle tensor, written with its own middle physical
index. -/
noncomputable def edgeMiddleWeightOn (A : Tensor G d) (e : Edge G)
    (τ : EdgeMiddlePhysicalConfig (G := G) (d := d) e)
    (β : EdgeBoundaryConfig (G := G) A e) : ℂ :=
  ∑ η : EdgeMiddleConfig (G := G) A e β,
    ∏ v : {v : V // v ∈ edgeMiddleVertices e},
      A.component v.1 (fun ie => η.1 ie.1) (τ v)

/-- The full-configuration form of the open middle tensor is the
middle-indexed tensor evaluated on the restricted physical configuration. -/
theorem edgeOpenMiddleWeight_eq_on (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    edgeOpenMiddleWeight (G := G) A e σ leftResidual rightResidual =
      edgeOpenMiddleWeightOn (G := G) A e
        (edgeMiddlePhysicalConfigOf (G := G) (d := d) e σ)
        leftResidual rightResidual :=
  rfl

/-- The full-configuration form of the ordinary middle tensor is the
middle-indexed tensor evaluated on the restricted physical configuration. -/
theorem edgeMiddleWeight_eq_on (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (β : EdgeBoundaryConfig (G := G) A e) :
    edgeMiddleWeight (G := G) A e σ β =
      edgeMiddleWeightOn (G := G) A e
        (edgeMiddlePhysicalConfigOf (G := G) (d := d) e σ) β := by
  classical
  rw [edgeMiddleWeight, edgeMiddleWeightOn]
  refine Finset.sum_congr rfl ?_
  intro η _
  rw [Finset.prod_subtype (F := inferInstance) (s := edgeMiddleVertices e)
    (p := fun v => v ∈ edgeMiddleVertices e) (h := by intro v; rfl)]
  rfl

/-- The ordinary blocked middle tensor is the open middle tensor after restoring
the fixed distinguished-edge index and reindexing the finite sum.

This is the coefficient-level reindexing behind the identity specialization of
an edge insertion, with the physical index already restricted to the middle
block. -/
theorem edgeMiddleWeightOn_eq_edgeOpenMiddleWeightOn (A : Tensor G d) (e : Edge G)
    (τ : EdgeMiddlePhysicalConfig (G := G) (d := d) e)
    (β : EdgeBoundaryConfig (G := G) A e) :
    edgeMiddleWeightOn (G := G) A e τ β =
      edgeOpenMiddleWeightOn (G := G) A e τ β.leftResidual β.rightResidual := by
  classical
  rw [edgeMiddleWeightOn, edgeOpenMiddleWeightOn]
  let φ := edgeMiddleConfigEquivOpenMiddleConfig (G := G) A e β
  calc
    (∑ η : EdgeMiddleConfig (G := G) A e β,
        ∏ v : {v : V // v ∈ edgeMiddleVertices e},
          A.component v.1 (fun ie => η.1 ie.1) (τ v))
        = ∑ ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual,
            ∏ v : {v : V // v ∈ edgeMiddleVertices e},
              A.component v.1 (fun ie => (φ.symm ζ).1 ie.1) (τ v) := by
          refine Fintype.sum_equiv φ
            (fun η : EdgeMiddleConfig (G := G) A e β =>
              ∏ v : {v : V // v ∈ edgeMiddleVertices e},
                A.component v.1 (fun ie => η.1 ie.1) (τ v))
            (fun ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual =>
              ∏ v : {v : V // v ∈ edgeMiddleVertices e},
                A.component v.1 (fun ie => (φ.symm ζ).1 ie.1) (τ v)) ?_
          intro η
          simp [φ]
    _ = ∑ ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual,
          ∏ v : {v : V // v ∈ edgeMiddleVertices e},
            A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ.1 v.2 ie)
              (τ v) := by
        refine Finset.sum_congr rfl ?_
        intro ζ _
        refine Fintype.prod_congr _ _ ?_
        intro v
        apply congrArg (fun cfg => A.component v.1 cfg (τ v))
        funext ie
        have hne := edge_ne_of_middle_incident (G := G) e v.2 ie
        simpa [φ, edgeComplementValue, edgeMiddleConfigEquivOpenMiddleConfig] using
          edgeOpenMiddleConfigToMiddleConfig_apply_ne (G := G) A e β ζ ⟨ie.1, hne⟩

/-- The middle tensor in the edge-blocked three-site chain, indexed by the two
residual boundary configurations adjacent to the endpoints.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
noncomputable def edgeMiddleTensorFamily (A : Tensor G d) (e : Edge G) :
    ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e) ×
        ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e) →
      EdgeMiddlePhysicalConfig (G := G) (d := d) e → ℂ :=
  fun ρ τ => edgeOpenMiddleWeightOn (G := G) A e τ ρ.1 ρ.2

/-- Injectivity of the middle tensor in the edge-blocked three-site chain.

This is the middle-block part of the paper's assertion that the tensor network
obtained after `eq:block_to_mps` is an injective three-site MPS.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
def EdgeMiddleTensorInjective (A : Tensor G d) (e : Edge G) : Prop :=
  LinearIndependent ℂ (edgeMiddleTensorFamily (G := G) A e)

/-- Boundary labels of the middle tensor in the edge-blocked three-site chain.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
abbrev EdgeMiddleBoundaryLabel (A : Tensor G d) (e : Edge G) : Type _ :=
  ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e) ×
    ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)

/-- Injectivity of the three-site chain obtained by blocking around a
chosen edge $e=(u,v)$.

The first and last assertions are the injectivity of the endpoint tensors. The
middle assertion is the injectivity of the tensor obtained by blocking all
vertices except the two endpoints. This is the formal statement targeted by the
assertion after `eq:block_to_mps` in arXiv:1804.04964, Section 3,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
structure EdgeBlockedThreeSiteInjective (A : Tensor G d) (e : Edge G) : Prop where
  left_injective : Function.Injective (localTensorMap A e.1.1)
  middle_injective : EdgeMiddleTensorInjective (G := G) A e
  right_injective : Function.Injective (localTensorMap A e.1.2)

/-- Vertex injectivity supplies the two endpoint injectivity assertions in the
edge-blocked three-site chain.

The middle assertion, linear independence of the middle tensor family over the
residual boundary configurations, is
`edgeMiddleTensorInjective_of_isVertexInjective` below. -/
theorem IsVertexInjective.edgeBlockedEndpointTensorMaps_injective {A : Tensor G d}
    (hA : IsVertexInjective A) (e : Edge G) :
    Function.Injective (localTensorMap A e.1.1) ∧
      Function.Injective (localTensorMap A e.1.2) :=
  ⟨hA.localTensorMap_injective e.1.1, hA.localTensorMap_injective e.1.2⟩

/-- Once the middle block is injective, vertex injectivity gives the full
edge-blocked three-site injectivity statement.

The middle hypothesis is the injectivity of the tensor obtained by blocking the
vertices away from the chosen edge; it is supplied by
`edgeMiddleTensorInjective_of_isVertexInjective` below. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective_of_middle {A : Tensor G d}
    (hA : IsVertexInjective A) (e : Edge G)
    (hMiddle : EdgeMiddleTensorInjective (G := G) A e) :
    EdgeBlockedThreeSiteInjective (G := G) A e :=
  ⟨hA.localTensorMap_injective e.1.1, hMiddle, hA.localTensorMap_injective e.1.2⟩

/-- If every edge-middle tensor is injective, then vertex injectivity gives an
injective edge-blocked three-site chain at every edge.

This is the middle-tensor version of the assertion following `eq:block_to_mps`.
Under positive bond dimensions the middle-tensor hypotheses are supplied by
`edgeMiddleTensorInjective_of_isVertexInjective` below.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective_all_of_middle {A : Tensor G d}
    (hA : IsVertexInjective A)
    (hMiddle : ∀ e : Edge G, EdgeMiddleTensorInjective (G := G) A e) :
    ∀ e : Edge G, EdgeBlockedThreeSiteInjective (G := G) A e :=
  fun e => hA.edgeBlockedThreeSiteInjective_of_middle e (hMiddle e)

/-! ### Empty complement obstruction

The two lemmas below prove the part of the zero-dimensional-bond obstruction
that is checked in this file: if `EdgeComplementConfig A e` is empty, then the
middle tensor family is identically zero, and if the boundary-label type is
also nonempty then the middle tensor family is not linearly independent. The
paper-gap note explains how such an empty complement can arise from a
zero-dimensional bond while vertex injectivity may hold vacuously at vertices
incident to that bond. The positive-bond hypothesis in the theorem below
excludes this obstruction. -/

/-- If the complement configuration space is empty, each vector in the
edge-middle tensor family is the zero function. -/
theorem edgeMiddleTensorFamily_eq_zero_of_isEmpty (A : Tensor G d) (e : Edge G)
    [IsEmpty (EdgeComplementConfig (G := G) A e)]
    (ρ : EdgeMiddleBoundaryLabel (G := G) A e) :
    edgeMiddleTensorFamily (G := G) A e ρ = 0 := by
  funext τ
  rw [edgeMiddleTensorFamily, edgeOpenMiddleWeightOn]
  apply Finset.sum_eq_zero
  intro ζ _
  exact (IsEmpty.false ζ.1).elim

/-- If the complement configuration space is empty and the boundary-label type
is nonempty, then the edge-middle tensor family is not linearly independent. -/
theorem not_edgeMiddleTensorInjective_of_isEmpty (A : Tensor G d) (e : Edge G)
    [IsEmpty (EdgeComplementConfig (G := G) A e)]
    [Nonempty (EdgeMiddleBoundaryLabel (G := G) A e)] :
    ¬ EdgeMiddleTensorInjective (G := G) A e := by
  intro h
  exact h.ne_zero (Classical.arbitrary (EdgeMiddleBoundaryLabel (G := G) A e))
    (edgeMiddleTensorFamily_eq_zero_of_isEmpty (G := G) A e _)

/-! ### The middle block as a blocked region

The region $V\setminus\{u,v\}$ has as boundary edges exactly the edges other
than $e=(u,v)$ that meet $u$ or $v$, so its boundary configurations carry the
two residual endpoint labels of the edge-middle tensor. -/

section EdgeMiddleRegion

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge incident to both endpoints of `e` is `e` itself. -/
theorem eq_of_incident_both (e f : Edge G)
    (h1 : f.1.1 = e.1.1 ∨ f.1.2 = e.1.1) (h2 : f.1.1 = e.1.2 ∨ f.1.2 = e.1.2) : f = e := by
  have hflt := f.2.1
  have helt := e.2.1
  apply Subtype.ext
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.symm.trans h2) (ne_of_lt helt)
  · exact Prod.ext h1 h2
  · exfalso
    rw [h2, h1] at hflt
    exact absurd hflt (not_lt.mpr helt.le)
  · exact absurd (h1.symm.trans h2) (ne_of_lt helt)

omit [DecidableRel G.Adj] in
/-- An edge crossing the boundary of $V\setminus\{u,v\}$ is not $e=(u,v)$. -/
theorem ne_of_isRegionBoundaryEdge_edgeMiddleVertices (e : Edge G) {f : Edge G}
    (hf : ManyBody.IsRegionBoundaryEdge (G := G) (edgeMiddleVertices e) f) : f ≠ e := by
  rintro rfl
  simp [ManyBody.IsRegionBoundaryEdge] at hf

omit [DecidableRel G.Adj] in
/-- An edge crossing the boundary of $V\setminus\{u,v\}$ that avoids $u$ meets $v$. -/
theorem incident_right_of_isRegionBoundaryEdge_edgeMiddleVertices (e : Edge G) {f : Edge G}
    (hf : ManyBody.IsRegionBoundaryEdge (G := G) (edgeMiddleVertices e) f)
    (hL : ¬ (f.1.1 = e.1.1 ∨ f.1.2 = e.1.1)) : f.1.1 = e.1.2 ∨ f.1.2 = e.1.2 := by
  simp only [ManyBody.IsRegionBoundaryEdge, mem_edgeMiddleVertices_iff] at hf
  tauto

omit [DecidableRel G.Adj] in
/-- An edge other than $e=(u,v)$ meeting $u$ or $v$ crosses the boundary of
$V\setminus\{u,v\}$. -/
theorem isRegionBoundaryEdge_edgeMiddleVertices_of_incident (e : Edge G) {f : Edge G}
    (hne : f ≠ e) (h : (f.1.1 = e.1.1 ∨ f.1.2 = e.1.1) ∨ (f.1.1 = e.1.2 ∨ f.1.2 = e.1.2)) :
    ManyBody.IsRegionBoundaryEdge (G := G) (edgeMiddleVertices e) f := by
  have hf : f.1.1 ≠ f.1.2 := ne_of_lt f.2.1
  have he : e.1.1 ≠ e.1.2 := ne_of_lt e.2.1
  have hboth : ¬ ((f.1.1 = e.1.1 ∨ f.1.2 = e.1.1) ∧ (f.1.1 = e.1.2 ∨ f.1.2 = e.1.2)) :=
    fun h' => hne (eq_of_incident_both e f h'.1 h'.2)
  simp only [ManyBody.IsRegionBoundaryEdge, mem_edgeMiddleVertices_iff]
  grind

variable (A : Tensor G d) (e : Edge G)

/-- The boundary configuration of the region $V\setminus\{u,v\}$ attached to a
boundary label of the edge-middle tensor: an edge crossing the boundary carries
the residual index at whichever endpoint of $e=(u,v)$ it meets.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
noncomputable def edgeMiddleRegionBoundaryConfig (ρ : EdgeMiddleBoundaryLabel (G := G) A e) :
    RegionBoundaryConfig (G := G) A (edgeMiddleVertices e) := fun f =>
  if hL : f.1.1.1 = e.1.1 ∨ f.1.1.2 = e.1.1 then
    ρ.1 ⟨⟨f.1, hL⟩, fun hh =>
      ne_of_isRegionBoundaryEdge_edgeMiddleVertices e f.2 (congrArg Subtype.val hh)⟩
  else
    ρ.2 ⟨⟨f.1, incident_right_of_isRegionBoundaryEdge_edgeMiddleVertices e f.2 hL⟩, fun hh =>
      ne_of_isRegionBoundaryEdge_edgeMiddleVertices e f.2 (congrArg Subtype.val hh)⟩

/-- A complement configuration restricts to the region boundary configuration
attached to `ρ` exactly when it carries the residual endpoint labels `ρ`. -/
theorem edgeMiddleRegionBoundaryConfig_eq_iff (ρ : EdgeMiddleBoundaryLabel (G := G) A e)
    (ζ : EdgeComplementConfig (G := G) A e) :
    (fun f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) (edgeMiddleVertices e) f} =>
        ζ ⟨f.1, ne_of_isRegionBoundaryEdge_edgeMiddleVertices e f.2⟩) =
        edgeMiddleRegionBoundaryConfig (G := G) A e ρ ↔
      edgeOpenBoundaryMatches (G := G) A e ρ.1 ρ.2 ζ := by
  constructor
  · intro h
    refine ⟨fun ie => ?_, fun ie => ?_⟩
    · have hb := isRegionBoundaryEdge_edgeMiddleVertices_of_incident e
        (otherLeft_edge_ne (G := G) e ie) (Or.inl ie.1.2)
      have := congrFun h ⟨ie.1.1, hb⟩
      rw [edgeMiddleRegionBoundaryConfig, dite_eq_left ie.1.2] at this
      exact this
    · have hb := isRegionBoundaryEdge_edgeMiddleVertices_of_incident e
        (otherRight_edge_ne (G := G) e ie) (Or.inr ie.1.2)
      have hL : ¬ (ie.1.1.1.1 = e.1.1 ∨ ie.1.1.1.2 = e.1.1) := fun hL =>
        otherRight_edge_ne (G := G) e ie (eq_of_incident_both e ie.1.1 hL ie.1.2)
      have := congrFun h ⟨ie.1.1, hb⟩
      rw [edgeMiddleRegionBoundaryConfig, dite_eq_right hL] at this
      exact this
  · rintro ⟨h1, h2⟩
    funext f
    rw [edgeMiddleRegionBoundaryConfig]
    split_ifs with hL
    · exact h1 ⟨⟨f.1, hL⟩, _⟩
    · exact h2 ⟨⟨f.1, _⟩, _⟩

/-- Distinct boundary labels of the edge-middle tensor give distinct boundary
configurations of $V\setminus\{u,v\}$. -/
theorem edgeMiddleRegionBoundaryConfig_injective :
    Function.Injective (edgeMiddleRegionBoundaryConfig (G := G) A e) := by
  intro ρ ρ' h
  apply Prod.ext
  · funext ie
    have hb := isRegionBoundaryEdge_edgeMiddleVertices_of_incident e
      (otherLeft_edge_ne (G := G) e ie) (Or.inl ie.1.2)
    have := congrFun h ⟨ie.1.1, hb⟩
    rw [edgeMiddleRegionBoundaryConfig, edgeMiddleRegionBoundaryConfig, dite_eq_left ie.1.2,
      dite_eq_left ie.1.2] at this
    exact this
  · funext ie
    have hb := isRegionBoundaryEdge_edgeMiddleVertices_of_incident e
      (otherRight_edge_ne (G := G) e ie) (Or.inr ie.1.2)
    have hL : ¬ (ie.1.1.1.1 = e.1.1 ∨ ie.1.1.1.2 = e.1.1) := fun hL =>
      otherRight_edge_ne (G := G) e ie (eq_of_incident_both e ie.1.1 hL ie.1.2)
    have := congrFun h ⟨ie.1.1, hb⟩
    rw [edgeMiddleRegionBoundaryConfig, edgeMiddleRegionBoundaryConfig, dite_eq_right hL,
      dite_eq_right hL] at this
    exact this

/-- Blocking the region $V\setminus\{u,v\}$ gives the edge-middle tensor times the
dimension of the bond on $e$: the region contraction also sums freely over the
index on $e$, which meets no vertex of the region. -/
theorem regionBlockedWeight_edgeMiddleRegionBoundaryConfig
    (ρ : EdgeMiddleBoundaryLabel (G := G) A e)
    (τ : EdgeMiddlePhysicalConfig (G := G) (d := d) e) :
    regionBlockedWeight (G := G) A (edgeMiddleVertices e)
        (edgeMiddleRegionBoundaryConfig (G := G) A e ρ) τ =
      (A.bondDim e : ℂ) * edgeMiddleTensorFamily (G := G) A e ρ τ := by
  classical
  let E := Equiv.piSplitAt e (fun f : Edge G => Fin (A.bondDim f))
  have hE : ∀ (a : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e)
      (f : Edge G) (hf : f ≠ e), E.symm (a, ζ) f = ζ ⟨f, hf⟩ := by
    intro a ζ f hf
    simp [E, Equiv.piSplitAt, hf]
  let P : EdgeComplementConfig (G := G) A e → ℂ := fun ζ =>
    ∏ v : {v : V // v ∈ edgeMiddleVertices e},
      A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ v.2 ie) (τ v)
  have key : ∀ (a : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e),
      (if regionBoundaryLabel (G := G) A (edgeMiddleVertices e) (E.symm (a, ζ)) =
          edgeMiddleRegionBoundaryConfig (G := G) A e ρ then
        ∏ w : {w : V // w ∈ edgeMiddleVertices e},
          A.component w.1 (fun ie => E.symm (a, ζ) ie.1) (τ w) else 0) =
        if edgeOpenBoundaryMatches (G := G) A e ρ.1 ρ.2 ζ then P ζ else 0 := by
    intro a ζ
    have hlabel : regionBoundaryLabel (G := G) A (edgeMiddleVertices e) (E.symm (a, ζ)) =
        fun f : {f : Edge G //
            ManyBody.IsRegionBoundaryEdge (G := G) (edgeMiddleVertices e) f} =>
          ζ ⟨f.1, ne_of_isRegionBoundaryEdge_edgeMiddleVertices e f.2⟩ := by
      funext f
      exact hE a ζ f.1 _
    have hprod : (∏ w : {w : V // w ∈ edgeMiddleVertices e},
        A.component w.1 (fun ie => E.symm (a, ζ) ie.1) (τ w)) = P ζ := by
      refine Finset.prod_congr rfl fun w _ => ?_
      congr 1
      funext ie
      exact hE a ζ ie.1 (edge_ne_of_middle_incident (G := G) e w.2 ie)
    rw [hlabel, hprod]
    exact if_congr (edgeMiddleRegionBoundaryConfig_eq_iff A e ρ ζ) rfl rfl
  rw [regionBlockedWeight, Finset.sum_filter, ← E.symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [key]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [edgeMiddleTensorFamily, edgeOpenMiddleWeightOn, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun ζ => by simp) P

/-- The middle tensor of the edge-blocked three-site chain is injective: it is the
contraction of the injective tensors over $V\setminus\{u,v\}$, a special case of
the region theorem.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 979--1009; the contraction of
injective tensors is injective, lines 205--250. -/
theorem edgeMiddleTensorInjective_of_isVertexInjective (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    EdgeMiddleTensorInjective (G := G) A e := by
  have hR := (regionBlockedTensorInjective_of_isVertexInjective (G := G) A
    (edgeMiddleVertices e) hA hpos).comp (edgeMiddleRegionBoundaryConfig (G := G) A e)
      (edgeMiddleRegionBoundaryConfig_injective A e)
  have hne : (A.bondDim e : ℂ) ≠ 0 := by exact_mod_cast (hpos e).ne'
  have hfam : edgeMiddleTensorFamily (G := G) A e =
      (fun _ : EdgeMiddleBoundaryLabel (G := G) A e => (Units.mk0 _ hne)⁻¹) •
        (regionBlockedTensorFamily (G := G) A (edgeMiddleVertices e) ∘
          edgeMiddleRegionBoundaryConfig (G := G) A e) := by
    funext ρ τ
    simp [regionBlockedTensorFamily, regionBlockedWeight_edgeMiddleRegionBoundaryConfig,
      Units.smul_def, hne]
  rw [EdgeMiddleTensorInjective, hfam]
  exact hR.units_smul _

end EdgeMiddleRegion

/-- Vertex injectivity is preserved by the edge blocking to a three-site MPS,
for a tensor with positive bond dimensions.

For every edge $e=(u,v)$, the two endpoint tensor maps and the middle tensor
obtained by blocking $V\setminus\{u,v\}$ form an injective three-site chain.

Source: arXiv:1804.04964, Section 3, eq:block_to_mps,
`Papers/1804.04964/paper_normal.tex`, lines 979--1009. The middle-tensor
injectivity is the source fact that a contraction of injective tensors is
injective, with inverse the contraction of the inverses up to the bond
dimension (lines 205--250); the two endpoint injectivities come directly from
vertex injectivity.

**Positive-bond hypothesis (faithfulness fix).** The source works with
injective PEPS, whose virtual bond spaces are nonzero-dimensional. An earlier
statement dropped that assumption. The preceding empty-complement lemmas
show that, when the complement configuration space is empty and the
boundary-label type is nonempty, the middle tensor vanishes and is not
injective. The paper-gap note explains the corresponding zero-dimensional-bond
examples. The hypothesis
\[
  \forall f,\; \dim A_f>0
\]
restores the source assumption. The gap and its restoration are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective {A : Tensor G d}
    (hA : IsVertexInjective A) (hpos : ∀ f : Edge G, 0 < A.bondDim f) (e : Edge G) :
    EdgeBlockedThreeSiteInjective (G := G) A e :=
  hA.edgeBlockedThreeSiteInjective_of_middle e
    (edgeMiddleTensorInjective_of_isVertexInjective (G := G) A e hA hpos)

end PEPS
end TNLean
