import TNLean.PEPS.Blocking
import TNLean.PEPS.InjectiveRegion
import TNLean.PEPS.SingletonRegion

/-!
# Middle physical indices for edge-blocked PEPS

This file gives the middle tensor in the edge-centered three-site decomposition
its own physical index. For an edge $e=(u,v)$, the middle physical
configuration is the family of physical indices on $V\setminus\{u,v\}$.

## References

- [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, Section 3, `eq:block_to_mps`](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 981--1009.
- `Papers/1804.04964/paper_normal.tex`, lines 1322--1404.
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

omit [DecidableRel G.Adj] in
private theorem edge_ne_of_middle_incident_for_physical (e : Edge G) {v : V}
    (hv : v ∈ edgeMiddleVertices e) (ie : IncidentEdge G v) : ie.1 ≠ e := by
  intro hie
  have hvne := (mem_edgeMiddleVertices_iff e v).mp hv
  rcases ie.2 with hleft | hright
  · exact hvne.1 (hleft.symm.trans (congrArg (fun f : Edge G => f.1.1) hie))
  · exact hvne.2 (hright.symm.trans (congrArg (fun f : Edge G => f.1.2) hie))

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
        have hne := edge_ne_of_middle_incident_for_physical (G := G) e v.2 ie
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

/-- A comparison from finite-region injectivity to the middle tensor in the
edge-blocked three-site chain.

The source proof uses that contracting injective tensors over a finite region
gives an injective blocked tensor. This proposition records the part of that
claim needed for the middle region $V\setminus\{u,v\}$ attached to an edge
$e=(u,v)$, without asserting the full contraction theorem.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
structure EdgeMiddleRegionInjectivityComparison
    (κ : RegionInjectivityData V) (A : Tensor G d) : Prop where
  /-- Region injectivity of $V\setminus\{u,v\}$ gives injectivity of the
  corresponding edge-middle tensor family. -/
  middle_tensor_injective :
    ∀ e : Edge G, κ.IsInjective (edgeMiddleVertices e) →
      EdgeMiddleTensorInjective (G := G) A e

/-- Vertex injectivity supplies the two endpoint injectivity assertions in the
edge-blocked three-site chain.

The unformalized content is middle-block injectivity: linear independence of the
middle tensor family over the residual boundary configurations. -/
theorem IsVertexInjective.edgeBlockedEndpointTensorMaps_injective {A : Tensor G d}
    (hA : IsVertexInjective A) (e : Edge G) :
    Function.Injective (localTensorMap A e.1.1) ∧
      Function.Injective (localTensorMap A e.1.2) :=
  ⟨hA.localTensorMap_injective e.1.1, hA.localTensorMap_injective e.1.2⟩

/-- Vertex injectivity supplies the two endpoint injectivity assertions for
the edge-blocked three-site chain at every edge.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem IsVertexInjective.edgeBlockedEndpointTensorMaps_injective_all {A : Tensor G d}
    (hA : IsVertexInjective A) :
    ∀ e : Edge G,
      Function.Injective (localTensorMap A e.1.1) ∧
        Function.Injective (localTensorMap A e.1.2) :=
  fun e => hA.edgeBlockedEndpointTensorMaps_injective e

/-- Once the middle block is injective, vertex injectivity gives the full
edge-blocked three-site injectivity statement.

This isolates the remaining proof obligation in the source argument: injectivity
is preserved when the vertices away from the chosen edge are blocked into the
middle tensor. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective_of_middle {A : Tensor G d}
    (hA : IsVertexInjective A) (e : Edge G)
    (hMiddle : EdgeMiddleTensorInjective (G := G) A e) :
    EdgeBlockedThreeSiteInjective (G := G) A e :=
  ⟨hA.localTensorMap_injective e.1.1, hMiddle, hA.localTensorMap_injective e.1.2⟩

/-- If every edge-middle tensor is injective, then vertex injectivity gives an
injective edge-blocked three-site chain at every edge.

This is the middle-tensor version of the assertion following `eq:block_to_mps`.
The separate comparison theorem below supplies the middle-tensor hypotheses
from finite-region injectivity.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective_all_of_middle {A : Tensor G d}
    (hA : IsVertexInjective A)
    (hMiddle : ∀ e : Edge G, EdgeMiddleTensorInjective (G := G) A e) :
    ∀ e : Edge G, EdgeBlockedThreeSiteInjective (G := G) A e :=
  fun e => hA.edgeBlockedThreeSiteInjective_of_middle e (hMiddle e)

/-- Region injectivity of the edge-middle block, together with the comparison to
the edge-middle tensor family, gives the edge-blocked three-site injectivity
statement.

This is a conditional form of the assertion after `eq:block_to_mps`; the
unconditional paper statement still requires a proof of the finite-region
contraction theorem.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem EdgeMiddleRegionInjectivityComparison.edgeBlockedThreeSiteInjective
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison : EdgeMiddleRegionInjectivityComparison (G := G) (d := d) κ A)
    (hA : IsVertexInjective A) (e : Edge G)
    (hMiddleRegion : κ.IsInjective (edgeMiddleVertices e)) :
    EdgeBlockedThreeSiteInjective (G := G) A e :=
  hA.edgeBlockedThreeSiteInjective_of_middle e
    (hComparison.middle_tensor_injective e hMiddleRegion)

/-- If every edge-middle region is injective after blocking, then every
edge-middle tensor family is injective.

This is the all-edge form of the finite-region comparison isolated from the
assertion following `eq:block_to_mps`.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem EdgeMiddleRegionInjectivityComparison.edgeMiddleTensorInjective_all
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison : EdgeMiddleRegionInjectivityComparison (G := G) (d := d) κ A)
    (hMiddleRegions : ∀ e : Edge G, κ.IsInjective (edgeMiddleVertices e)) :
    ∀ e : Edge G, EdgeMiddleTensorInjective (G := G) A e :=
  fun e => hComparison.middle_tensor_injective e (hMiddleRegions e)

/-- All edge-blocked three-site chains are injective once every edge-middle
region is injective and region injectivity has been compared with the
edge-middle tensor family.

This is the all-edge conditional form of the assertion following
`eq:block_to_mps` in arXiv:1804.04964, Section 3. The remaining source-paper
step is the contraction theorem showing that vertex injectivity gives
injectivity of each finite middle region $V\setminus\{u,v\}$.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem EdgeMiddleRegionInjectivityComparison.edgeBlockedThreeSiteInjective_all
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison : EdgeMiddleRegionInjectivityComparison (G := G) (d := d) κ A)
    (hA : IsVertexInjective A)
    (hMiddleRegions : ∀ e : Edge G, κ.IsInjective (edgeMiddleVertices e)) :
    ∀ e : Edge G, EdgeBlockedThreeSiteInjective (G := G) A e :=
  hA.edgeBlockedThreeSiteInjective_all_of_middle
    (hComparison.edgeMiddleTensorInjective_all hMiddleRegions)

/-- Singleton comparison and finite union closure give the edge-middle tensor
for a chosen edge whose middle region is nonempty.

This is a restricted consequence of the source argument: it handles the case
where $V\setminus\{u,v\}$ is a nonempty finite union of singleton regions.
The remaining comparison from region injectivity to the concrete edge-middle
tensor is still assumed.

**Scope restriction (nonempty middle):** This theorem assumes
`(edgeMiddleVertices e).Nonempty`; see
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps` and Lemma
`lem:injective_union`; `Papers/1804.04964/paper_normal.tex`, lines 981--1009
and 1322--1404. -/
theorem EdgeMiddleRegionInjectivityComparison.edgeMiddleTensorInjective_of_singletons
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison : EdgeMiddleRegionInjectivityComparison (G := G) (d := d) κ A)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hSingleton : SingletonRegionInjectivityComparison (G := G) (d := d) κ A)
    (hA : IsVertexInjective A) (e : Edge G)
    (hMiddle : (edgeMiddleVertices e).Nonempty) :
    EdgeMiddleTensorInjective (G := G) A e :=
  hComparison.middle_tensor_injective e
    (hUnion.finset_injective_of_singletons hSingleton hA hMiddle)

/-- Singleton comparison and finite union closure give the edge-blocked
three-site injectivity statement for an edge whose middle region is nonempty.

**Scope restriction (nonempty middle):** This theorem assumes
`(edgeMiddleVertices e).Nonempty`; see
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps` and Lemma
`lem:injective_union`; `Papers/1804.04964/paper_normal.tex`, lines 981--1009
and 1322--1404. -/
theorem EdgeMiddleRegionInjectivityComparison.edgeBlockedThreeSiteInjective_of_singletons
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison : EdgeMiddleRegionInjectivityComparison (G := G) (d := d) κ A)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hSingleton : SingletonRegionInjectivityComparison (G := G) (d := d) κ A)
    (hA : IsVertexInjective A) (e : Edge G)
    (hMiddle : (edgeMiddleVertices e).Nonempty) :
    EdgeBlockedThreeSiteInjective (G := G) A e :=
  hA.edgeBlockedThreeSiteInjective_of_middle e
    (hComparison.edgeMiddleTensorInjective_of_singletons hUnion hSingleton hA e hMiddle)

/-- Singleton comparison and finite union closure give edge-blocked three-site
injectivity at every edge whose middle region is nonempty.

This is the all-edge form of the preceding restricted consequence.

**Scope restriction (nonempty middle):** This theorem assumes
`∀ e : Edge G, (edgeMiddleVertices e).Nonempty`; see
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps` and Lemma
`lem:injective_union`; `Papers/1804.04964/paper_normal.tex`, lines 981--1009
and 1322--1404. -/
theorem EdgeMiddleRegionInjectivityComparison.edgeBlockedThreeSiteInjective_all_of_singletons
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison : EdgeMiddleRegionInjectivityComparison (G := G) (d := d) κ A)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hSingleton : SingletonRegionInjectivityComparison (G := G) (d := d) κ A)
    (hA : IsVertexInjective A)
    (hMiddle : ∀ e : Edge G, (edgeMiddleVertices e).Nonempty) :
    ∀ e : Edge G, EdgeBlockedThreeSiteInjective (G := G) A e :=
  fun e =>
    hComparison.edgeBlockedThreeSiteInjective_of_singletons
      hUnion hSingleton hA e (hMiddle e)

/-- Vertex injectivity is preserved by the edge blocking to a three-site MPS.

For every edge $e=(u,v)$, the two endpoint tensor maps and the middle tensor
obtained by blocking $V\setminus\{u,v\}$ form an injective three-site chain.

Source: arXiv:1804.04964, Section 3, eq:block_to_mps,
`Papers/1804.04964/paper_normal.tex`, lines 979--1009.

**Proof status:** This declaration states the source assertion. The missing
proof is the finite-region contraction theorem saying that contracting
vertex-injective tensors over the middle region gives an injective blocked
tensor; it is tracked by issue #1366. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective {A : Tensor G d}
    (hA : IsVertexInjective A) (e : Edge G) :
    EdgeBlockedThreeSiteInjective (G := G) A e := by
  sorry

end PEPS
end TNLean
