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

/-- The one-sided inverse of an injective tensor at a single vertex: a
coefficient family on the local virtual configurations at `v` that contracts to
the zero physical vector vanishes.

This is the explicit-summation form of injectivity of the local tensor map at
`v`: if $\sum_\eta R(\eta)\,A_v(\eta,\tau)=0$ for every physical index $\tau$,
then $R=0$. It is the per-vertex one-sided-inverse fact of the source (the
diagram at `Papers/1804.04964/paper_normal.tex` line 203, equivalent to the
existence of the one-sided inverse at lines 205--250), and it is the atomic
deletion engine of the middle-block contraction argument: contracting the open
physical leg of the injective tensor at a vertex `j` removes that vertex from
the blocked product. The remaining infrastructure that feeds this lemma to
prove `EdgeMiddleTensorInjective` (the star-bond split equivalence, the
partial-contraction kernel condition, and the terminal boundary isolation) is
recorded in `docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section
"Remaining mathematical obligations"; tracked by issue #1366. -/
theorem IsVertexInjective.localCoeff_eq_zero_of_contract_zero {A : Tensor G d}
    (hA : IsVertexInjective A) (v : V) (R : LocalVirtualConfig A v → ℂ)
    (hR : ∀ τ : Fin d, ∑ η : LocalVirtualConfig A v, R η • A.component v η τ = 0) :
    R = 0 := by
  have hzero : localTensorMap A v R = 0 := by
    funext τ
    simpa [localTensorMap, Fintype.linearCombination_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hR τ
  have hinj := hA.localTensorMap_injective v
  have h0 : localTensorMap A v R = localTensorMap A v 0 := by rw [hzero, map_zero]
  exact hinj h0


/-! ### Counterexample: the unrestricted target is false

The target `IsVertexInjective.edgeBlockedThreeSiteInjective` is **false** without a
positive-bond-dimension hypothesis. Once the graph has an edge `f ≠ e` carrying bond
dimension `0` while the boundary labels remain inhabited (for example a four-cycle
with the distinguished edge `e`, a middle-to-middle edge of dimension `0`, and
positive boundary bonds), `EdgeComplementConfig A e` is empty, so the entire middle
tensor family is identically zero and is not linearly independent over the nonempty
boundary label type, whereas `IsVertexInjective A` still holds vacuously at the two
vertices on the zero-dimensional edge, whose local virtual configuration type is
empty. The two lemmas below record this obstruction; they are the precise reason the
theorem carries the positive-bond hypothesis restored below. -/

theorem edgeMiddleTensorFamily_eq_zero_of_isEmpty (A : Tensor G d) (e : Edge G)
    [IsEmpty (EdgeComplementConfig (G := G) A e)]
    (ρ : EdgeMiddleBoundaryLabel (G := G) A e) :
    edgeMiddleTensorFamily (G := G) A e ρ = 0 := by
  funext τ
  rw [edgeMiddleTensorFamily, edgeOpenMiddleWeightOn]
  apply Finset.sum_eq_zero
  intro ζ _
  exact (IsEmpty.false ζ.1).elim

theorem not_edgeMiddleTensorInjective_of_isEmpty (A : Tensor G d) (e : Edge G)
    [IsEmpty (EdgeComplementConfig (G := G) A e)]
    [Nonempty (EdgeMiddleBoundaryLabel (G := G) A e)] :
    ¬ EdgeMiddleTensorInjective (G := G) A e := by
  intro h
  exact h.ne_zero (Classical.arbitrary (EdgeMiddleBoundaryLabel (G := G) A e))
    (edgeMiddleTensorFamily_eq_zero_of_isEmpty (G := G) A e _)

/-! ### Star-bond split equivalence at a middle vertex -/

/-- The predicate on complement edges singling out those incident to a middle
vertex `j`. -/
private def IsIncidentTo (e : Edge G) (j : V) (f : {f : Edge G // f ≠ e}) : Prop :=
  f.1.1.1 = j ∨ f.1.1.2 = j

private instance (e : Edge G) (j : V) (f : {f : Edge G // f ≠ e}) :
    Decidable (IsIncidentTo (G := G) e j f) := by
  unfold IsIncidentTo
  infer_instance

/-- For a middle vertex `j` and an incident edge `ie` at `j`, the underlying edge
is a complement edge of `e`. -/
private def middleIncidentToComplement (e : Edge G) {j : V}
    (hj : j ∈ edgeMiddleVertices e) (ie : IncidentEdge G j) :
    {f : Edge G // f ≠ e} :=
  ⟨ie.1, edge_ne_of_middle_incident_for_physical (G := G) e hj ie⟩

/-- The star-bond split equivalence at a middle vertex `j`. -/
noncomputable def edgeComplementConfigSplitAt (A : Tensor G d) (e : Edge G) {j : V}
    (hj : j ∈ edgeMiddleVertices e) :
    EdgeComplementConfig (G := G) A e ≃
      LocalVirtualConfig A j ×
        ((f : {f : {f : Edge G // f ≠ e} // ¬ IsIncidentTo (G := G) e j f}) →
          Fin (A.bondDim f.1.1)) where
  toFun ζ :=
    (fun ie : IncidentEdge G j =>
        ζ (middleIncidentToComplement (G := G) e hj ie),
      fun f => ζ f.1)
  invFun x := fun f =>
    if h : IsIncidentTo (G := G) e j f then
      x.1 ⟨f.1, h⟩
    else
      x.2 ⟨f, h⟩
  left_inv ζ := by
    funext f
    dsimp only
    by_cases h : IsIncidentTo (G := G) e j f
    · rw [dif_pos h]
      rfl
    · rw [dif_neg h]
  right_inv x := by
    apply Prod.ext
    · funext ie
      have h : IsIncidentTo (G := G) e j (middleIncidentToComplement (G := G) e hj ie) :=
        ie.2
      dsimp only
      rw [dif_pos h]
      rfl
    · funext f
      have h : ¬ IsIncidentTo (G := G) e j f.1 := f.2
      dsimp only
      rw [dif_neg h]

@[simp] theorem edgeComplementConfigSplitAt_fst (A : Tensor G d) (e : Edge G) {j : V}
    (hj : j ∈ edgeMiddleVertices e) (ζ : EdgeComplementConfig (G := G) A e)
    (ie : IncidentEdge G j) :
    (edgeComplementConfigSplitAt (G := G) A e hj ζ).1 ie =
      edgeComplementValue (G := G) A e ζ hj ie :=
  rfl

@[simp] theorem edgeComplementValue_edgeComplementConfigSplitAt_symm
    (A : Tensor G d) (e : Edge G) {j : V} (hj : j ∈ edgeMiddleVertices e)
    (η : LocalVirtualConfig A j)
    (r : (f : {f : {f : Edge G // f ≠ e} // ¬ IsIncidentTo (G := G) e j f}) →
      Fin (A.bondDim f.1.1))
    (ie : IncidentEdge G j) :
    edgeComplementValue (G := G) A e
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) hj ie = η ie := by
  have h : IsIncidentTo (G := G) e j (middleIncidentToComplement (G := G) e hj ie) :=
    ie.2
  show (edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)
      (middleIncidentToComplement (G := G) e hj ie) = η ie
  rw [edgeComplementConfigSplitAt]
  dsimp only [Equiv.coe_fn_symm_mk]
  rw [dif_pos h]
  rfl

/-! ### Kernel-descent construction for the middle block -/

omit [Fintype V] [DecidableRel G.Adj] in
private theorem otherLeft_edge_ne' (e : Edge G)
    (ie : OtherIncidentEdge (G := G) e.1.1 (edgeLeftIncident (G := G) e)) :
    ie.1.1 ≠ e := fun hie => ie.2 (Subtype.ext hie)

omit [Fintype V] [DecidableRel G.Adj] in
private theorem otherRight_edge_ne' (e : Edge G)
    (ie : OtherIncidentEdge (G := G) e.1.2 (edgeRightIncident (G := G) e)) :
    ie.1.1 ≠ e := fun hie => ie.2 (Subtype.ext hie)

/-- The boundary label read off a complement configuration: its residual data at
the two endpoints. -/
noncomputable def boundaryLabelOfComplement (A : Tensor G d) (e : Edge G)
    (ζ : EdgeComplementConfig (G := G) A e) : EdgeMiddleBoundaryLabel (G := G) A e :=
  (fun ie => ζ ⟨ie.1.1, otherLeft_edge_ne' (G := G) e ie⟩,
   fun ie => ζ ⟨ie.1.1, otherRight_edge_ne' (G := G) e ie⟩)

/-- The weight of a complement configuration under the coefficient family `c`. -/
noncomputable def complementWeight (A : Tensor G d) (e : Edge G)
    (c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ)
    (ζ : EdgeComplementConfig (G := G) A e) : ℂ :=
  c (boundaryLabelOfComplement (G := G) A e ζ)

/-- The exposed-agreement indicator at stage `S`: `1` if `ζ` agrees with `ζ₀` on
every edge that touches no vertex of `S`, and `0` otherwise. -/
noncomputable def exposedIndicator (A : Tensor G d) (e : Edge G) (S : Finset V)
    (ζ ζ₀ : EdgeComplementConfig (G := G) A e) : ℂ :=
  if (∀ f : {f : Edge G // f ≠ e}, f.1.1.1 ∉ S → f.1.1.2 ∉ S → ζ f = ζ₀ f) then 1 else 0

/-- The kernel condition at stage `S` for the coefficient family `c`. -/
noncomputable def edgeMiddleKernelCondition (A : Tensor G d) (e : Edge G)
    (c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ) (S : Finset V) : Prop :=
  ∀ (ζ₀ : EdgeComplementConfig (G := G) A e) (τ : V → Fin d),
    ∑ ζ : EdgeComplementConfig (G := G) A e,
      exposedIndicator (G := G) A e S ζ ζ₀ *
        complementWeight (G := G) A e c ζ *
        ∏ v ∈ S, (if h : v ∈ edgeMiddleVertices e then
            A.component v (fun ie => edgeComplementValue (G := G) A e ζ h ie) (τ v)
          else 1) = 0

/-! ### Kernel-condition descent: the erase-vertex step -/

variable (A : Tensor G d) (e : Edge G)

/-- The extra-agreement indicator on the `j`-incident edges newly exposed when `j`
is removed from `S`. -/
noncomputable def extraIndicator (S : Finset V) (j : V)
    (ζ ζ₀ : EdgeComplementConfig (G := G) A e) : ℂ :=
  if (∀ f : {f : Edge G // f ≠ e}, (f.1.1.1 = j ∨ f.1.1.2 = j) →
      f.1.1.1 ∉ S.erase j → f.1.1.2 ∉ S.erase j → ζ f = ζ₀ f) then 1 else 0

/-- Removing `j` from `S` factors the exposed indicator into the `S`-indicator and
the extra-agreement indicator on the `j`-incident edges. -/
theorem exposedIndicator_erase (S : Finset V) (j : V)
    (ζ ζ₀ : EdgeComplementConfig (G := G) A e) :
    exposedIndicator (G := G) A e (S.erase j) ζ ζ₀ =
      exposedIndicator (G := G) A e S ζ ζ₀ * extraIndicator (G := G) A e S j ζ ζ₀ := by
  classical
  unfold exposedIndicator extraIndicator
  by_cases hAll : ∀ f : {f : Edge G // f ≠ e},
      f.1.1.1 ∉ S.erase j → f.1.1.2 ∉ S.erase j → ζ f = ζ₀ f
  · -- erase condition holds; both S-cond and extra-cond hold
    rw [if_pos hAll]
    have hS : ∀ f : {f : Edge G // f ≠ e}, f.1.1.1 ∉ S → f.1.1.2 ∉ S → ζ f = ζ₀ f := by
      intro f hf1 hf2
      exact hAll f (fun h => hf1 (Finset.mem_of_mem_erase h)) (fun h => hf2 (Finset.mem_of_mem_erase h))
    have hE : ∀ f : {f : Edge G // f ≠ e}, (f.1.1.1 = j ∨ f.1.1.2 = j) →
        f.1.1.1 ∉ S.erase j → f.1.1.2 ∉ S.erase j → ζ f = ζ₀ f := by
      intro f _ hf1 hf2
      exact hAll f hf1 hf2
    rw [if_pos hS, if_pos hE, one_mul]
  · rw [if_neg hAll]
    -- erase condition fails: need product = 0, i.e. one of S-cond or extra-cond fails
    by_cases hS : ∀ f : {f : Edge G // f ≠ e}, f.1.1.1 ∉ S → f.1.1.2 ∉ S → ζ f = ζ₀ f
    · -- S-cond holds; then extra-cond must fail (else erase holds)
      rw [if_pos hS, one_mul, if_neg]
      intro hE
      apply hAll
      intro f hf1 hf2
      -- f.1.1.1 ∉ S.erase j and f.1.1.2 ∉ S.erase j
      by_cases hj1 : f.1.1.1 = j
      · exact hE f (Or.inl hj1) hf1 hf2
      · by_cases hj2 : f.1.1.2 = j
        · exact hE f (Or.inr hj2) hf1 hf2
        · -- neither endpoint is j; so ∉ S.erase j ↔ ∉ S
          have h1 : f.1.1.1 ∉ S := fun h => hf1 (Finset.mem_erase.mpr ⟨hj1, h⟩)
          have h2 : f.1.1.2 ∉ S := fun h => hf2 (Finset.mem_erase.mpr ⟨hj2, h⟩)
          exact hS f h1 h2
    · rw [if_neg hS, zero_mul]

/-- The extra indicator on a split configuration depends only on the local
configuration `η` at `j`. -/
noncomputable def extraIndicatorη (S : Finset V) {j : V}
    (η : LocalVirtualConfig A j)
    (ζ₀ : EdgeComplementConfig (G := G) A e) : ℂ :=
  if (∀ f : {f : Edge G // f ≠ e}, (h : f.1.1.1 = j ∨ f.1.1.2 = j) →
      f.1.1.1 ∉ S.erase j → f.1.1.2 ∉ S.erase j →
        η ⟨f.1, h⟩ = ζ₀ f) then 1 else 0

theorem extraIndicator_split (S : Finset V) {j : V}
    (hj : j ∈ edgeMiddleVertices e) (η : LocalVirtualConfig A j)
    (r : (f : {f : {f : Edge G // f ≠ e} // ¬ IsIncidentTo (G := G) e j f}) →
      Fin (A.bondDim f.1.1))
    (ζ₀ : EdgeComplementConfig (G := G) A e) :
    extraIndicator (G := G) A e S j
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) ζ₀ =
      extraIndicatorη (G := G) A e S η ζ₀ := by
  classical
  unfold extraIndicator extraIndicatorη
  have hval : ∀ (f : {f : Edge G // f ≠ e}) (hinc : f.1.1.1 = j ∨ f.1.1.2 = j),
      (edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r) f = η ⟨f.1, hinc⟩ := by
    intro f hinc
    have hIs : IsIncidentTo (G := G) e j f := hinc
    rw [edgeComplementConfigSplitAt]
    dsimp only [Equiv.coe_fn_symm_mk]
    rw [dif_pos hIs]
  congr 1
  apply propext
  constructor
  · intro h f hinc hf1 hf2
    rw [← hval f hinc]
    exact h f hinc hf1 hf2
  · intro h f hinc hf1 hf2
    rw [hval f hinc]
    exact h f hinc hf1 hf2

/-- Abbreviation: the guarded local factor at `v` in the kernel condition. -/
noncomputable def kFactor (v : V)
    (ζ : EdgeComplementConfig (G := G) A e) (τ : V → Fin d) : ℂ :=
  if h : v ∈ edgeMiddleVertices e then
    A.component v (fun ie => edgeComplementValue (G := G) A e ζ h ie) (τ v)
  else 1

/-- On a split configuration, the guarded local factor at `j` is the tensor at
`j` evaluated on the local virtual configuration `η`. -/
theorem kFactor_split_mid {j : V} (hj : j ∈ edgeMiddleVertices e)
    (η : LocalVirtualConfig A j)
    (r : (f : {f : {f : Edge G // f ≠ e} // ¬ IsIncidentTo (G := G) e j f}) →
      Fin (A.bondDim f.1.1))
    (τ : V → Fin d) :
    kFactor (G := G) A e j ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) τ =
      A.component j η (τ j) := by
  classical
  unfold kFactor
  rw [dif_pos hj]
  congr 1
  funext ie
  exact edgeComplementValue_edgeComplementConfigSplitAt_symm (G := G) A e hj η r ie

/-- The marginal coefficient family at `j` obtained from the kernel condition at
`S` by summing over the non-`j` star coordinates. -/
noncomputable def kMarginal
    (c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ) (S : Finset V) {j : V}
    (hj : j ∈ edgeMiddleVertices e) (ζ₀ : EdgeComplementConfig (G := G) A e)
    (τ : V → Fin d) (η : LocalVirtualConfig A j) : ℂ :=
  ∑ r : (f : {f : {f : Edge G // f ≠ e} // ¬ IsIncidentTo (G := G) e j f}) →
        Fin (A.bondDim f.1.1),
    exposedIndicator (G := G) A e S
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) ζ₀ *
      complementWeight (G := G) A e c
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) *
      ∏ v ∈ S.erase j, kFactor (G := G) A e v
          ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) τ

/-- The marginal coefficient family vanishes, by injectivity at `j` and the
kernel condition at `S`. -/
theorem kMarginal_eq_zero (hA : IsVertexInjective A)
    (c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ) (S : Finset V) {j : V}
    (hj : j ∈ edgeMiddleVertices e) (hjS : j ∈ S)
    (hK : edgeMiddleKernelCondition (G := G) A e c S)
    (ζ₀ : EdgeComplementConfig (G := G) A e) (τ : V → Fin d) :
    kMarginal (G := G) A e c S hj ζ₀ τ = 0 := by
  classical
  apply hA.localCoeff_eq_zero_of_contract_zero j
  intro τj'
  -- evaluate via K(S) with physical config (Function.update τ j τj')
  have hKS := hK ζ₀ (Function.update τ j τj')
  -- reindex the K(S) sum by the split equiv into ∑_η ∑_r
  rw [← Equiv.sum_comp (edgeComplementConfigSplitAt (G := G) A e hj).symm,
      Fintype.sum_prod_type] at hKS
  rw [← hKS]
  refine Finset.sum_congr rfl ?_
  intro η _
  unfold kMarginal
  rw [smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro r _
  have hAj : A.component j η τj' =
      kFactor (G := G) A e j ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r))
        (Function.update τ j τj') := by
    rw [kFactor_split_mid (G := G) A e hj η r (Function.update τ j τj')]
    rw [Function.update_self]
  have hProdErase : ∀ x : EdgeComplementConfig (G := G) A e,
      (∏ v ∈ S.erase j, kFactor (G := G) A e v x τ) =
        ∏ v ∈ S.erase j, kFactor (G := G) A e v x (Function.update τ j τj') := by
    intro x
    refine Finset.prod_congr rfl ?_
    intro v hv
    have hvj : v ≠ j := Finset.ne_of_mem_erase hv
    unfold kFactor
    by_cases hvm : v ∈ edgeMiddleVertices e
    · rw [dif_pos hvm, dif_pos hvm, Function.update_of_ne hvj]
    · rw [dif_neg hvm, dif_neg hvm]
  rw [hProdErase, hAj]
  rw [show (exposedIndicator (G := G) A e S
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) ζ₀ *
      complementWeight (G := G) A e c
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) *
      ∏ v ∈ S.erase j, kFactor (G := G) A e v
          ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) (Function.update τ j τj')) *
      kFactor (G := G) A e j
          ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) (Function.update τ j τj') =
      exposedIndicator (G := G) A e S
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) ζ₀ *
      complementWeight (G := G) A e c
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) *
      ((∏ v ∈ S.erase j, kFactor (G := G) A e v
          ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) (Function.update τ j τj')) *
        kFactor (G := G) A e j
          ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) (Function.update τ j τj'))
      by ring]
  rw [Finset.prod_erase_mul S _ hjS]
  rfl

/-- The kernel condition descends when a middle vertex `j ∈ S` is removed. -/
theorem edgeMiddleKernelCondition_erase (hA : IsVertexInjective A)
    (c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ) (S : Finset V) {j : V}
    (hj : j ∈ edgeMiddleVertices e) (hjS : j ∈ S)
    (hK : edgeMiddleKernelCondition (G := G) A e c S) :
    edgeMiddleKernelCondition (G := G) A e c (S.erase j) := by
  classical
  intro ζ₀ τ
  -- reindex the sum over ζ by the split equiv into ∑_η ∑_r
  rw [← Equiv.sum_comp (edgeComplementConfigSplitAt (G := G) A e hj).symm,
      Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro η _
  -- inner sum over r equals extraIndicatorη η * kMarginal η = 0
  have hMarg := kMarginal_eq_zero (G := G) A e hA c S hj hjS hK ζ₀ τ
  have hpull :
      (∑ r, exposedIndicator (G := G) A e (S.erase j)
            ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) ζ₀ *
          complementWeight (G := G) A e c
            ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) *
          ∏ v ∈ S.erase j, kFactor (G := G) A e v
            ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) τ) =
      extraIndicatorη (G := G) A e S η ζ₀ *
        kMarginal (G := G) A e c S hj ζ₀ τ η := by
    unfold kMarginal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [exposedIndicator_erase (G := G) A e S j,
      extraIndicator_split (G := G) A e S hj η r]
    ring
  show (∑ r, exposedIndicator (G := G) A e (S.erase j)
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) ζ₀ *
      complementWeight (G := G) A e c
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) *
      ∏ v ∈ S.erase j, kFactor (G := G) A e v
        ((edgeComplementConfigSplitAt (G := G) A e hj).symm (η, r)) τ) = 0
  rw [hpull, congrFun hMarg η, Pi.zero_apply, mul_zero]

/-! ### Surjectivity of the boundary label and the terminal relation -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge incident to both endpoints of `e` is `e` itself. -/
theorem incidentBoth_eq_edge (f : Edge G)
    (h1 : f.1.1 = e.1.1 ∨ f.1.2 = e.1.1) (h2 : f.1.1 = e.1.2 ∨ f.1.2 = e.1.2) : f = e := by
  have hflt := f.2.1; have helt := e.2.1
  apply Subtype.ext
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.symm.trans h2) (ne_of_lt helt)
  · exact Prod.ext h1 h2
  · exfalso; rw [h2, h1] at hflt; exact absurd hflt (not_lt.mpr helt.le)
  · exact absurd (h1.symm.trans h2) (ne_of_lt helt)

/-- A complement configuration witnessing a given boundary label, using positive
bond dimensions to fill the interior coordinates. -/
noncomputable def boundaryWitness (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (ρ : EdgeMiddleBoundaryLabel (G := G) A e) : EdgeComplementConfig (G := G) A e :=
  fun f =>
    if hL : f.1.1.1 = e.1.1 ∨ f.1.1.2 = e.1.1 then
      ρ.1 ⟨⟨f.1, hL⟩, fun hh => f.2 (congrArg Subtype.val hh)⟩
    else if hR : f.1.1.1 = e.1.2 ∨ f.1.1.2 = e.1.2 then
      ρ.2 ⟨⟨f.1, hR⟩, fun hh => f.2 (congrArg Subtype.val hh)⟩
    else
      ⟨0, hpos f.1⟩

omit [Fintype V] in
/-- The boundary label of the witness configuration is the given label. -/
theorem boundaryLabelOfComplement_boundaryWitness (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (ρ : EdgeMiddleBoundaryLabel (G := G) A e) :
    boundaryLabelOfComplement (G := G) A e
        (boundaryWitness (G := G) A e hpos ρ) = ρ := by
  apply Prod.ext
  · funext ie
    show boundaryWitness (G := G) A e hpos ρ ⟨ie.1.1, otherLeft_edge_ne' (G := G) e ie⟩ = ρ.1 ie
    have hL : ie.1.1.1.1 = e.1.1 ∨ ie.1.1.1.2 = e.1.1 := ie.1.2
    rw [boundaryWitness, dif_pos hL]
  · funext ie
    show boundaryWitness (G := G) A e hpos ρ ⟨ie.1.1, otherRight_edge_ne' (G := G) e ie⟩ = ρ.2 ie
    have hR : ie.1.1.1.1 = e.1.2 ∨ ie.1.1.1.2 = e.1.2 := ie.1.2
    have hnotL : ¬ (ie.1.1.1.1 = e.1.1 ∨ ie.1.1.1.2 = e.1.1) := by
      intro hL
      exact (otherRight_edge_ne' (G := G) e ie) (incidentBoth_eq_edge (G := G) e ie.1.1 hL hR)
    rw [boundaryWitness, dif_neg hnotL, dif_pos hR]

/-- The kernel condition at the empty region forces the coefficient family to
vanish. -/
theorem edgeMiddleKernelCondition_empty_eq_zero (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ)
    (hK : edgeMiddleKernelCondition (G := G) A e c ∅) :
    c = 0 := by
  classical
  -- positive bonds and vertex injectivity at the left endpoint give a physical index
  obtain ⟨τ0⟩ : Nonempty (Fin d) := by
    have hne : Nonempty (LocalVirtualConfig A e.1.1) := ⟨fun ie => ⟨0, hpos ie.1⟩⟩
    obtain ⟨η₀⟩ := hne
    have hnz : A.component e.1.1 η₀ ≠ 0 := (hA e.1.1).ne_zero η₀
    by_contra hc
    rw [not_nonempty_iff] at hc
    exact hnz (Subsingleton.elim _ _)
  ext ρ
  -- choose ζ₀ = boundaryWitness ρ, and the constant physical config τ0
  have hKρ := hK (boundaryWitness (G := G) A e hpos ρ) (fun _ => τ0)
  -- the empty-region sum collapses to c (bl ζ₀) = c ρ
  rw [show (∑ ζ : EdgeComplementConfig (G := G) A e,
        exposedIndicator (G := G) A e ∅ ζ (boundaryWitness (G := G) A e hpos ρ) *
          complementWeight (G := G) A e c ζ *
          ∏ v ∈ (∅ : Finset V), (if h : v ∈ edgeMiddleVertices e then
              A.component v (fun ie => edgeComplementValue (G := G) A e ζ h ie) ((fun _ => τ0) v)
            else 1)) =
      ∑ ζ : EdgeComplementConfig (G := G) A e,
        exposedIndicator (G := G) A e ∅ ζ (boundaryWitness (G := G) A e hpos ρ) *
          complementWeight (G := G) A e c ζ from by
    refine Finset.sum_congr rfl ?_
    intro ζ _
    rw [Finset.prod_empty, mul_one]] at hKρ
  -- exposedIndicator at ∅ is [ζ = ζ₀]
  have hExp : ∀ ζ : EdgeComplementConfig (G := G) A e,
      exposedIndicator (G := G) A e ∅ ζ (boundaryWitness (G := G) A e hpos ρ) =
        if ζ = boundaryWitness (G := G) A e hpos ρ then 1 else 0 := by
    intro ζ
    unfold exposedIndicator
    congr 1
    apply propext
    constructor
    · intro h
      funext f
      exact h f (by simp) (by simp)
    · intro h _ _ _
      rw [h]
  simp_rw [hExp, ite_mul, one_mul, zero_mul] at hKρ
  rw [Finset.sum_ite_eq' Finset.univ (boundaryWitness (G := G) A e hpos ρ)
      (fun ζ => complementWeight (G := G) A e c ζ)] at hKρ
  simp only [Finset.mem_univ, if_true] at hKρ
  -- hKρ : complementWeight c (boundaryWitness ρ) = 0
  rw [complementWeight, boundaryLabelOfComplement_boundaryWitness (G := G) A e hpos ρ] at hKρ
  simpa using hKρ

/-! ### The initial relation -/

omit [Fintype V] in
/-- A complement configuration matches the residual data of `ρ` exactly when its
boundary label is `ρ`. -/
theorem edgeOpenBoundaryMatches_iff_boundaryLabel
    (ρ : EdgeMiddleBoundaryLabel (G := G) A e) (ζ : EdgeComplementConfig (G := G) A e) :
    edgeOpenBoundaryMatches (G := G) A e ρ.1 ρ.2 ζ ↔
      boundaryLabelOfComplement (G := G) A e ζ = ρ := by
  unfold edgeOpenBoundaryMatches boundaryLabelOfComplement
  constructor
  · intro ⟨h1, h2⟩
    apply Prod.ext
    · funext ie; exact h1 ie
    · funext ie; exact h2 ie
  · intro h
    refine ⟨fun ie => ?_, fun ie => ?_⟩
    · exact congrFun (congrArg Prod.fst h) ie
    · exact congrFun (congrArg Prod.snd h) ie

/-- The middle tensor family expanded as a fibered sum over complement
configurations with a given boundary label. -/
theorem edgeMiddleTensorFamily_eq_fiber_sum
    (ρ : EdgeMiddleBoundaryLabel (G := G) A e) (τ : V → Fin d) :
    edgeMiddleTensorFamily (G := G) A e ρ
        (edgeMiddlePhysicalConfigOf (G := G) (d := d) e τ) =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : EdgeComplementConfig (G := G) A e =>
            boundaryLabelOfComplement (G := G) A e ζ = ρ),
        ∏ v : {v : V // v ∈ edgeMiddleVertices e},
          A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ v.2 ie)
            (τ v.1) := by
  classical
  rw [edgeMiddleTensorFamily, edgeOpenMiddleWeightOn]
  -- sum over subtype EdgeOpenMiddleConfig = sum over filtered univ
  rw [← Finset.sum_subtype
      (s := Finset.univ.filter
        (fun ζ : EdgeComplementConfig (G := G) A e =>
          boundaryLabelOfComplement (G := G) A e ζ = ρ))
      (p := fun ζ => edgeOpenBoundaryMatches (G := G) A e ρ.1 ρ.2 ζ)
      (by
        intro ζ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [edgeOpenBoundaryMatches_iff_boundaryLabel (G := G) A e ρ ζ])
      (fun ζ => ∏ v : {v : V // v ∈ edgeMiddleVertices e},
        A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ v.2 ie)
          (edgeMiddlePhysicalConfigOf (G := G) (d := d) e τ v))]
  rfl

/-- At the full middle region, the exposed indicator is identically `1`: no
complement edge has both endpoints outside the middle region. -/
theorem exposedIndicator_edgeMiddleVertices
    (ζ ζ₀ : EdgeComplementConfig (G := G) A e) :
    exposedIndicator (G := G) A e (edgeMiddleVertices e) ζ ζ₀ = 1 := by
  classical
  unfold exposedIndicator
  rw [if_pos]
  intro f hf1 hf2
  -- both endpoints of f are outside midV, so both are in {e.1.1, e.1.2}; with f ≠ e impossible
  rw [mem_edgeMiddleVertices_iff, not_and_or, not_not, not_not] at hf1 hf2
  -- hf1 : f.1.1.1 = e.1.1 ∨ f.1.1.1 = e.1.2 ; hf2 : f.1.1.2 = e.1.1 ∨ f.1.1.2 = e.1.2
  have d1 : f.1.1.1 = e.1.1 ∨ f.1.1.1 = e.1.2 := hf1
  have d2 : f.1.1.2 = e.1.1 ∨ f.1.1.2 = e.1.2 := hf2
  refine absurd (incidentBoth_eq_edge (G := G) e f.1 ?_ ?_) f.2
  · rcases d1 with h | h
    · exact Or.inl h
    · rcases d2 with h2 | h2
      · exact Or.inr h2
      · exact (f.1.2.1.ne (h.trans h2.symm)).elim
  · rcases d2 with h | h
    · rcases d1 with h1 | h1
      · exact (f.1.2.1.ne (h1.trans h.symm)).elim
      · exact Or.inl h1
    · exact Or.inr h

/-- The kernel-condition product at a middle vertex set equals the subtype
product used in the middle tensor family. -/
theorem kProd_eq_family_prod (ζ : EdgeComplementConfig (G := G) A e) (τ : V → Fin d) :
    (∏ v ∈ edgeMiddleVertices e, (if h : v ∈ edgeMiddleVertices e then
        A.component v (fun ie => edgeComplementValue (G := G) A e ζ h ie) (τ v)
      else 1)) =
      ∏ v : {v : V // v ∈ edgeMiddleVertices e},
        A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ v.2 ie) (τ v.1) := by
  classical
  rw [Finset.prod_subtype (F := inferInstance) (s := edgeMiddleVertices e)
    (p := fun v => v ∈ edgeMiddleVertices e) (h := by intro v; rfl)
    (f := fun v => if h : v ∈ edgeMiddleVertices e then
        A.component v (fun ie => edgeComplementValue (G := G) A e ζ h ie) (τ v)
      else 1)]
  refine Finset.prod_congr rfl ?_
  intro v _
  rw [dif_pos v.2]

/-- A vanishing linear combination of the middle tensor family gives the kernel
condition at the full middle region. -/
theorem initial_kernelCondition
    (c : EdgeMiddleBoundaryLabel (G := G) A e →₀ ℂ)
    (hc : Finsupp.linearCombination ℂ (edgeMiddleTensorFamily (G := G) A e) c = 0) :
    edgeMiddleKernelCondition (G := G) A e c (edgeMiddleVertices e) := by
  classical
  intro ζ₀ τ
  -- exposed indicator is 1; collapse the product to the subtype form
  have hstep : (∑ ζ : EdgeComplementConfig (G := G) A e,
        exposedIndicator (G := G) A e (edgeMiddleVertices e) ζ ζ₀ *
          complementWeight (G := G) A e c ζ *
          ∏ v ∈ edgeMiddleVertices e, (if h : v ∈ edgeMiddleVertices e then
              A.component v (fun ie => edgeComplementValue (G := G) A e ζ h ie) (τ v)
            else 1)) =
      ∑ ζ : EdgeComplementConfig (G := G) A e,
        complementWeight (G := G) A e c ζ *
          ∏ v : {v : V // v ∈ edgeMiddleVertices e},
            A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ v.2 ie) (τ v.1) := by
    refine Finset.sum_congr rfl ?_
    intro ζ _
    rw [exposedIndicator_edgeMiddleVertices (G := G) A e ζ ζ₀, one_mul,
      kProd_eq_family_prod (G := G) A e ζ τ]
  rw [hstep]
  -- fiber over the boundary label and recognize the family
  rw [← Finset.sum_fiberwise Finset.univ
      (fun ζ : EdgeComplementConfig (G := G) A e => boundaryLabelOfComplement (G := G) A e ζ)
      (fun ζ => complementWeight (G := G) A e c ζ *
        ∏ v : {v : V // v ∈ edgeMiddleVertices e},
          A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ v.2 ie) (τ v.1))]
  -- each fiber's c factor is constant = c ρ; pull out and recognize family
  have hfib : ∀ ρ : EdgeMiddleBoundaryLabel (G := G) A e,
      (∑ ζ ∈ Finset.univ.filter
          (fun ζ : EdgeComplementConfig (G := G) A e =>
            boundaryLabelOfComplement (G := G) A e ζ = ρ),
        complementWeight (G := G) A e c ζ *
          ∏ v : {v : V // v ∈ edgeMiddleVertices e},
            A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ v.2 ie) (τ v.1)) =
        c ρ * edgeMiddleTensorFamily (G := G) A e ρ
          (edgeMiddlePhysicalConfigOf (G := G) (d := d) e τ) := by
    intro ρ
    rw [edgeMiddleTensorFamily_eq_fiber_sum (G := G) A e ρ τ, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ζ hζ
    rw [Finset.mem_filter] at hζ
    rw [complementWeight, hζ.2]
  simp_rw [hfib]
  -- ∑ ρ c ρ * family ρ τ' = (linearCombination family c) τ' = 0
  have hval : (∑ ρ : EdgeMiddleBoundaryLabel (G := G) A e,
        c ρ * edgeMiddleTensorFamily (G := G) A e ρ
          (edgeMiddlePhysicalConfigOf (G := G) (d := d) e τ)) =
      (Finsupp.linearCombination ℂ (edgeMiddleTensorFamily (G := G) A e) c)
        (edgeMiddlePhysicalConfigOf (G := G) (d := d) e τ) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    · intro i; simp
  rw [hval, hc]
  rfl

/-! ### Assembly of the kernel-descent data and the edge-blocked injectivity theorem -/

/-- The kernel-descent data for the edge-middle block, built from vertex
injectivity and positive bond dimensions. -/
noncomputable def edgeMiddleKernelDescentData (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    EdgeMiddleKernelDescentData (G := G) A e where
  kernelDescent c :=
    { kernelCondition := fun S =>
        edgeMiddleKernelCondition (G := G) A e c (S ∩ edgeMiddleVertices e)
      erase_vertex := by
        intro S j hjS hK
        rw [Finset.erase_inter]
        by_cases hjm : j ∈ edgeMiddleVertices e
        · exact edgeMiddleKernelCondition_erase (G := G) A e hA c
            (S ∩ edgeMiddleVertices e) hjm
            (Finset.mem_inter.mpr ⟨hjS, hjm⟩) hK
        · rw [Finset.erase_eq_of_notMem (fun h => hjm (Finset.mem_inter.mp h).2)]
          exact hK }
  initial_relation c hc := by
    show edgeMiddleKernelCondition (G := G) A e c
      (edgeMiddleVertices e ∩ edgeMiddleVertices e)
    rw [Finset.inter_self]
    exact initial_kernelCondition (G := G) A e c hc
  terminal_relation c hK := by
    have hK' : edgeMiddleKernelCondition (G := G) A e c ∅ := by
      have heq : (∅ : Finset V) ∩ edgeMiddleVertices e = ∅ := Finset.empty_inter _
      have hK2 : edgeMiddleKernelCondition (G := G) A e c
          ((∅ : Finset V) ∩ edgeMiddleVertices e) := hK
      rwa [heq] at hK2
    exact edgeMiddleKernelCondition_empty_eq_zero (G := G) A e hA hpos c hK'

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
Lean statement dropped that assumption, which makes the claim false: the checked
counterexample `not_edgeMiddleTensorInjective_of_isEmpty` above exhibits a
zero-dimensional complement bond on which the middle tensor vanishes while
vertex injectivity survives vacuously. The hypothesis `hpos` (every bond
dimension positive) restores the source assumption. The gap and its restoration
are recorded in `docs/paper-gaps/peps_injective_ft_section3_route.tex`.

The middle-block injectivity is obtained from the finite kernel descent
`edgeMiddleKernelDescentData`: the initial relation
`initial_kernelCondition` turns a vanishing linear combination of the middle
tensor family into the kernel condition at the full middle region; the descent
step `edgeMiddleKernelCondition_erase` applies the per-vertex one-sided inverse
`IsVertexInjective.localCoeff_eq_zero_of_contract_zero` after the star-bond
split `edgeComplementConfigSplitAt`; and the terminal step
`edgeMiddleKernelCondition_empty_eq_zero` isolates each boundary coefficient by
surjectivity of `boundaryLabelOfComplement`, which uses `hpos` to fill the
interior virtual indices of the witness configuration. -/
theorem IsVertexInjective.edgeBlockedThreeSiteInjective {A : Tensor G d}
    (hA : IsVertexInjective A) (hpos : ∀ f : Edge G, 0 < A.bondDim f) (e : Edge G) :
    EdgeBlockedThreeSiteInjective (G := G) A e :=
  hA.edgeBlockedThreeSiteInjective_of_kernelDescent e
    (edgeMiddleKernelDescentData (G := G) A e hA hpos)

end PEPS
end TNLean
