import TNLean.PEPS.Blocking
import TNLean.PEPS.FiniteKernelDescent
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

## Scope note

The singleton-region consequences below still assume that the middle region
$V\setminus\{u,v\}$ is nonempty. The source comparison and removal plan for
this hypothesis are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations".
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

/-- Boundary labels of the middle tensor in the edge-blocked three-site chain.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
abbrev EdgeMiddleBoundaryLabel (A : Tensor G d) (e : Edge G) : Type _ :=
  ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e) ×
    ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)

/-- Kernel-descent data for the edge-middle tensor.

This structure records the approach to middle-block injectivity: a contraction
of injective tensors is injective (arXiv:1804.04964, Section 3,
`Papers/1804.04964/paper_normal.tex`, lines 205--250). The source proves that
fact in one step from the one-sided inverse; the kernel conditions $K_c(S)$
below are the finite-induction device used to formalize it, not a separate
construction in the source.

For a finitely supported coefficient family $c_{\rho}$, the kernel condition
$K_c(S)$ for a finite vertex set $S$ in the middle region records the zero
relation reached after contracting the tensors in $S$. The initial condition
is, for every middle physical index $\tau$,
\[
    \sum_{\rho} c_{\rho} T^{\rho}_{A,V\setminus\{u,v\}}(\tau)=0,
\]
which is $K_c(V\setminus\{u,v\})$. The deletion condition
$K_c(S)\Rightarrow K_c(S\setminus\{j\})$ applies the one-sided inverse at $j$.
The terminal condition is $K_c(\varnothing)\Rightarrow c=0$.

Source: a contraction of injective tensors is injective, arXiv:1804.04964,
Section 3, `Papers/1804.04964/paper_normal.tex`, lines 205--250; the middle
block is that of `eq:block_to_mps`, lines 981--1009. -/
structure EdgeMiddleKernelDescentData (A : Tensor G d) (e : Edge G) where
  /-- The finite kernel-descent datum attached to a coefficient family $c_{\rho}$.

  Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
  `Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
  kernelDescent :
    (EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ) → FiniteRegionKernelDescent V
  /-- A zero linear relation among the middle tensor vectors gives
  $K_c(V\setminus\{u,v\})$.

  Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
  `Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
  initial_relation :
    ∀ c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ,
      Finsupp.linearCombination ℂ (edgeMiddleTensorFamily (G := G) A e) c = 0 →
        (kernelDescent c).kernelCondition (edgeMiddleVertices e)
  /-- The empty-region condition gives $c=0$.

  Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
  `Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
  terminal_relation :
    ∀ c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ,
      (kernelDescent c).kernelCondition ∅ → c = 0

namespace EdgeMiddleKernelDescentData

/-- Kernel descent for the middle block gives injectivity of the edge-middle
tensor family.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem edgeMiddleTensorInjective {A : Tensor G d} {e : Edge G}
    (hDescent : EdgeMiddleKernelDescentData (G := G) A e) :
    EdgeMiddleTensorInjective (G := G) A e := by
  rw [EdgeMiddleTensorInjective, linearIndependent_iff]
  intro c hc
  exact hDescent.terminal_relation c <|
    (hDescent.kernelDescent c).descend_to_empty (hDescent.initial_relation c hc)

end EdgeMiddleKernelDescentData

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

/-- Kernel descent for the middle block supplies the full edge-blocked
three-site injectivity statement.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective_of_kernelDescent {A : Tensor G d}
    (hA : IsVertexInjective A) (e : Edge G)
    (hDescent : EdgeMiddleKernelDescentData (G := G) A e) :
    EdgeBlockedThreeSiteInjective (G := G) A e :=
  hA.edgeBlockedThreeSiteInjective_of_middle e hDescent.edgeMiddleTensorInjective

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
`(edgeMiddleVertices e).Nonempty`; see the module scope note.

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

/-- Singleton comparison and finite union closure give every edge-middle tensor
when the ambient graph has more than two vertices.

For $2<|V|$, each middle region $V\setminus\{u,v\}$ is nonempty, so the
nonempty-region singleton theorem applies at every edge.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps` and Lemma
`lem:injective_union`; `Papers/1804.04964/paper_normal.tex`, lines 981--1009
and 1322--1404. -/
theorem EdgeMiddleRegionInjectivityComparison.edgeMiddleTensorInjective_all_two_lt_card
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison : EdgeMiddleRegionInjectivityComparison (G := G) (d := d) κ A)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hSingleton : SingletonRegionInjectivityComparison (G := G) (d := d) κ A)
    (hA : IsVertexInjective A)
    (hcard : 2 < Fintype.card V) :
    ∀ e : Edge G, EdgeMiddleTensorInjective (G := G) A e :=
  fun e =>
    hComparison.edgeMiddleTensorInjective_of_singletons hUnion hSingleton hA e
      (edgeMiddleVertices_nonempty_of_two_lt_card e hcard)

/-- Singleton comparison and finite union closure give the edge-blocked
three-site injectivity statement for an edge whose middle region is nonempty.

**Scope restriction (nonempty middle):** This theorem assumes
`(edgeMiddleVertices e).Nonempty`; see the module scope note.

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
`∀ e : Edge G, (edgeMiddleVertices e).Nonempty`; see the module scope note.

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

/-- Singleton comparison and finite union closure give every edge-blocked
three-site injectivity statement when the ambient graph has more than two
vertices.

For $2<|V|$, each edge has a nonempty middle region, and the preceding
nonempty-middle theorem applies uniformly.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps` and Lemma
`lem:injective_union`; `Papers/1804.04964/paper_normal.tex`, lines 981--1009
and 1322--1404. -/
theorem EdgeMiddleRegionInjectivityComparison.edgeBlockedThreeSiteInjective_all_two_lt_card
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison : EdgeMiddleRegionInjectivityComparison (G := G) (d := d) κ A)
    (hUnion : RegionInjectivityUnionClosure κ)
    (hSingleton : SingletonRegionInjectivityComparison (G := G) (d := d) κ A)
    (hA : IsVertexInjective A)
    (hcard : 2 < Fintype.card V) :
    ∀ e : Edge G, EdgeBlockedThreeSiteInjective (G := G) A e :=
  fun e =>
    hComparison.edgeBlockedThreeSiteInjective_of_singletons
      hUnion hSingleton hA e (edgeMiddleVertices_nonempty_of_two_lt_card e hcard)

/-- Vertex injectivity is preserved by the edge blocking to a three-site MPS.

For every edge $e=(u,v)$, the two endpoint tensor maps and the middle tensor
obtained by blocking $V\setminus\{u,v\}$ form an injective three-site chain.

Source: arXiv:1804.04964, Section 3, eq:block_to_mps,
`Papers/1804.04964/paper_normal.tex`, lines 979--1009. The middle-tensor
injectivity is the source fact that a contraction of injective tensors is
injective, with inverse the contraction of the inverses up to the bond
dimension (lines 205--250); the two endpoint injectivities come directly from
vertex injectivity.

**Proof status:** This declaration states the source assertion. The endpoint
maps are injective from vertex injectivity; the open step is the middle-block
contraction fact (lines 205--250). The current formal reductions route that
fact through the finite kernel descent rather than the source's one-step
inverse-of-a-contraction identity, and are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations"; tracked by issue #1366. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective {A : Tensor G d}
    (hA : IsVertexInjective A) (e : Edge G) :
    EdgeBlockedThreeSiteInjective (G := G) A e := by
  sorry

end PEPS
end TNLean
