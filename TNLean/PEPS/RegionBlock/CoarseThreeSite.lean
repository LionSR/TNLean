import TNLean.PEPS.RegionBlock.ThreeBlockTransfer
import TNLean.PEPS.EdgeMiddlePhysical.Basic

/-!
# The coarse three-site tensor for the normal PEPS theorem

The normal PEPS proof blocks a neighbourhood of each edge into three injective
regions and then applies the injective three-site comparison to that blocking.
The injective comparison machinery (`TNLean.PEPS.InsertionAlgebra`,
`TNLean.PEPS.InsertionRealization`, `TNLean.PEPS.EdgeMiddlePhysical`) operates
on a single-vertex three-site chain: its endpoint injectivity is
`Function.Injective (localTensorMap A v)`, single-vertex linear independence.
A normal tensor need not be vertex injective, so the comparison cannot be run on
the original tensor at the edge endpoints.

The source argument never uses the single vertex. After blocking, the three
sites of the chain are the **blocks**: the red region around one endpoint, the
blue region around the other, and the complement. The "component family" of each
super-site is the blocked-region weight family, which is injective by the normal
blocking hypothesis. This file builds the blocked chain as an honest `Tensor` on
a three-vertex complete graph, so that the proven single-vertex three-site
comparison applies verbatim to the super-sites.

The three coarse vertices are `r`, `b`, `c`. The coarse edges are `r-b` (the
original distinguished edge), `r-c` (the red-to-complement crossing bonds bundled
into one), and `b-c` (the blue-to-complement crossing bonds bundled into one).
The coarse physical dimension is the uniform padded dimension `d ^ (card V)`,
large enough to carry every region's physical configuration through a fixed
surjection.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1449--1500 (the blocking) and lines 254--583 (the injective
  three-site comparison applied to the blocked chain)](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The coarse three-vertex graph

The coarse graph is the complete graph on `Fin 3`. Its vertices are `0` (red
super-site `r`), `1` (blue super-site `b`), and `2` (complement super-site `c`).
Its three edges are `0-1`, `0-2`, and `1-2`. -/

/-- The coarse three-vertex graph: the complete graph on `Fin 3`. -/
abbrev coarseGraph : SimpleGraph (Fin 3) := ⊤

instance : DecidableRel (coarseGraph).Adj := fun a b => by
  unfold coarseGraph; simp only [SimpleGraph.top_adj]; infer_instance

/-- The coarse `r-b` edge `0-1`: the image of the original distinguished edge. -/
def coarseEdgeRB : Edge coarseGraph :=
  ⟨(0, 1), by constructor <;> simp [coarseGraph]⟩

/-- The coarse `r-c` edge `0-2`: the bundled red-to-complement crossing bonds. -/
def coarseEdgeRC : Edge coarseGraph :=
  ⟨(0, 2), by constructor <;> simp [coarseGraph]⟩

/-- The coarse `b-c` edge `1-2`: the bundled blue-to-complement crossing bonds. -/
def coarseEdgeBC : Edge coarseGraph :=
  ⟨(1, 2), by constructor <;> simp [coarseGraph]⟩

/-! ### Restriction of a physical configuration to a region

The coarse physical dimension `d ^ card V` is large enough to carry every region's
physical configuration. A global physical configuration `V → Fin d` is decoded from
a coarse physical index and then restricted to a region; the restriction is
surjective onto every region's physical configurations (under `0 < d`), which is the
property that makes the coarse component family linearly independent whenever the
blocked-region family is. -/

/-- The coarse uniform physical dimension `d ^ card V`. The fixed bijection
`Fin coarseDim ≃ (V → Fin d)` decodes a coarse physical index into a global physical
configuration. -/
abbrev coarseDim (V : Type*) [Fintype V] (d : ℕ) : ℕ := d ^ Fintype.card V

/-- The decoding bijection between coarse physical indices and global physical
configurations. -/
noncomputable def coarseDecodeEquiv (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    Fin (coarseDim V d) ≃ (V → Fin d) :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_fun, Fintype.card_fin])).symm

/-- Decode a coarse physical index into a global physical configuration. -/
noncomputable def coarseDecode (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    Fin (coarseDim V d) → (V → Fin d) :=
  coarseDecodeEquiv V d

/-- The fixed surjection from coarse physical indices to a region's physical
configurations: decode to a global configuration, then restrict to the region.

Surjectivity (under `0 < d`) is `coarseProj_surjective`; it is the property behind
the linear independence of the coarse component family. -/
noncomputable def coarseProj (R : Finset V) :
    Fin (coarseDim V d) → RegionPhysicalConfig (V := V) (d := d) R :=
  fun p w => coarseDecode V d p w.1

omit [LinearOrder V] in
/-- The decoding bijection is bijective, hence surjective. -/
theorem coarseDecode_surjective : Function.Surjective (coarseDecode V d) :=
  (coarseDecodeEquiv V d).surjective

omit [LinearOrder V] in
/-- Under `0 < d`, the restriction of a global physical configuration to a region is
surjective, so the coarse projection onto a region's physical configurations is
surjective. -/
theorem coarseProj_surjective (hd : 0 < d) (R : Finset V) :
    Function.Surjective (coarseProj (V := V) (d := d) R) := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro τ
  obtain ⟨σ, hσ⟩ :=
    coarseDecode_surjective (V := V) (d := d)
      (fun v => if hv : v ∈ R then τ ⟨v, hv⟩ else Classical.arbitrary _)
  refine ⟨σ, ?_⟩
  funext w
  simp only [coarseProj, hσ, w.2, dif_pos]

/-! ### The coarse blocking frame

A coarse blocking frame records the geometric identification of the three coarse
super-sites with the three blocked regions of a one-edge blocking. The coarse
vertex `r=0` carries the red block, `b=1` the blue block, `c=2` the complement
block. For each coarse vertex, an equivalence identifies the coarse virtual legs
incident to that vertex with the region's boundary configuration. The frame
abstracts the combinatorics "the boundary edges of the red region are the
distinguished edge together with the red-to-complement crossings", isolating the
edge-set geometry from the tensor construction and injectivity transport.

The blocked-region injectivities (`red_injective`, `blue_injective`,
`complement_injective`) are the normal blocking hypothesis: the super-site
component families are injective **by hypothesis**, with no single-vertex
injectivity. -/

/-- **A coarse blocking frame** for a tensor `A` at a distinguished edge.

The three regions are blocked-tensor injective (the normal blocking hypothesis),
positive physical dimension, and for each coarse vertex an equivalence between the
coarse virtual legs incident to that vertex and the region's boundary
configurations. The bond dimensions of the coarse graph are recorded so that the
per-vertex leg space matches the region boundary configuration.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
structure CoarseBlockingFrame (A : Tensor G d) where
  /-- The red block (around the left endpoint). -/
  red : Finset V
  /-- The blue block (around the right endpoint). -/
  blue : Finset V
  /-- The complement block. -/
  complement : Finset V
  /-- The red block is blocked-tensor injective. -/
  red_injective : RegionBlockedTensorInjective (G := G) A red
  /-- The blue block is blocked-tensor injective. -/
  blue_injective : RegionBlockedTensorInjective (G := G) A blue
  /-- The complement block is blocked-tensor injective. -/
  complement_injective : RegionBlockedTensorInjective (G := G) A complement
  /-- The physical dimension is positive. -/
  pos_dim : 0 < d
  /-- The coarse bond dimensions on the three coarse edges. -/
  coarseBondDim : Edge coarseGraph → ℕ
  /-- The coarse bond dimensions are positive. -/
  pos_coarseBondDim : ∀ f : Edge coarseGraph, 0 < coarseBondDim f
  /-- The coarse virtual legs at `r=0` identify with the red boundary configurations. -/
  legEquivRed :
    ((ie : IncidentEdge coarseGraph 0) → Fin (coarseBondDim ie.1)) ≃
      RegionBoundaryConfig (G := G) A red
  /-- The coarse virtual legs at `b=1` identify with the blue boundary configurations. -/
  legEquivBlue :
    ((ie : IncidentEdge coarseGraph 1) → Fin (coarseBondDim ie.1)) ≃
      RegionBoundaryConfig (G := G) A blue
  /-- The coarse virtual legs at `c=2` identify with the complement boundary
  configurations. -/
  legEquivComplement :
    ((ie : IncidentEdge coarseGraph 2) → Fin (coarseBondDim ie.1)) ≃
      RegionBoundaryConfig (G := G) A complement

namespace CoarseBlockingFrame

variable {A : Tensor G d} (F : CoarseBlockingFrame (G := G) (d := d) A)

/-- The region attached to a coarse vertex: red at `0`, blue at `1`, complement at
`2` (and red as a harmless default elsewhere, never used on `Fin 3`). -/
def regionOf : Fin 3 → Finset V
  | 0 => F.red
  | 1 => F.blue
  | 2 => F.complement

omit [DecidableEq V] in
@[simp] theorem regionOf_zero : F.regionOf 0 = F.red := rfl
omit [DecidableEq V] in
@[simp] theorem regionOf_one : F.regionOf 1 = F.blue := rfl
omit [DecidableEq V] in
@[simp] theorem regionOf_two : F.regionOf 2 = F.complement := rfl

omit [DecidableEq V] in
/-- The blocked-tensor injectivity of the region attached to a coarse vertex. -/
theorem regionOf_injective : ∀ v : Fin 3,
    RegionBlockedTensorInjective (G := G) A (F.regionOf v)
  | 0 => F.red_injective
  | 1 => F.blue_injective
  | 2 => F.complement_injective

/-- The leg-to-boundary equivalence attached to a coarse vertex. -/
def legEquiv : ∀ v : Fin 3,
    ((ie : IncidentEdge coarseGraph v) → Fin (F.coarseBondDim ie.1)) ≃
      RegionBoundaryConfig (G := G) A (F.regionOf v)
  | 0 => F.legEquivRed
  | 1 => F.legEquivBlue
  | 2 => F.legEquivComplement

/-! ### The coarse tensor

The coarse tensor on the three-vertex complete graph. Its component at coarse
vertex `v` is the blocked-region weight of the region attached to `v`, with the
coarse virtual legs identified with the region boundary configuration through
`legEquiv v` and the coarse physical index decoded and restricted to the region
through `coarseProj`. -/

/-- **The coarse three-site tensor.** A `Tensor` on the complete three-vertex graph
whose super-site at coarse vertex `v` is the blocked-region weight of the region
attached to `v`. The endpoint super-sites carry the red and blue blocked weights;
the middle super-site carries the complement blocked weight.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def coarseTensor : Tensor coarseGraph (coarseDim V d) where
  bondDim := F.coarseBondDim
  component v legs p :=
    regionBlockedWeight (G := G) A (F.regionOf v) (F.legEquiv v legs)
      (coarseProj (F.regionOf v) p)

@[simp] theorem coarseTensor_bondDim :
    (F.coarseTensor).bondDim = F.coarseBondDim := rfl

@[simp] theorem coarseTensor_component (v : Fin 3)
    (legs : (ie : IncidentEdge coarseGraph v) → Fin (F.coarseBondDim ie.1))
    (p : Fin (coarseDim V d)) :
    (F.coarseTensor).component v legs p =
      regionBlockedWeight (G := G) A (F.regionOf v) (F.legEquiv v legs)
        (coarseProj (F.regionOf v) p) :=
  rfl

/-! ### Vertex injectivity of the coarse tensor

Each coarse super-site component family is linearly independent. The transport is
purely formal: the coarse family is the blocked-region tensor family of the region
attached to the vertex, reindexed by the leg equivalence and postcomposed with the
pullback along the surjection `coarseProj`. Reindexing by an equivalence preserves
linear independence, and the pullback along a surjection is an injective linear map,
so it preserves linear independence by `LinearIndependent.map'`.

No single-vertex injectivity of `A` is used: the input is the **blocked-region**
injectivity `RegionBlockedTensorInjective A (regionOf v)`, the normal blocking
hypothesis. -/

/-- The coarse component family at vertex `v`, as a family of vectors. -/
theorem coarseTensor_component_eq (v : Fin 3) :
    (F.coarseTensor).component v =
      (LinearMap.funLeft ℂ ℂ (coarseProj (F.regionOf v))) ∘
        ((regionBlockedTensorFamily (G := G) A (F.regionOf v)) ∘ F.legEquiv v) := by
  funext legs
  funext p
  simp only [coarseTensor_component, Function.comp_apply, LinearMap.funLeft_apply,
    regionBlockedTensorFamily]

/-- **Vertex injectivity of the coarse tensor.** The component family at every
coarse super-site is linearly independent, inherited from the blocked-region
injectivity of the region attached to that vertex.

This is the endpoint and middle injectivity input for the coarse three-site chain,
supplied by the normal blocking hypothesis with no single-vertex injectivity.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem coarseTensor_isVertexInjective : IsVertexInjective (F.coarseTensor) := by
  intro v
  rw [coarseTensor_component_eq]
  refine LinearIndependent.map' ?_ (LinearMap.funLeft ℂ ℂ (coarseProj (F.regionOf v))) ?_
  · exact (linearIndependent_equiv' (F.legEquiv v) rfl).mpr (F.regionOf_injective v)
  · rw [LinearMap.ker_eq_bot]
    exact LinearMap.funLeft_injective_of_surjective ℂ ℂ _
      (coarseProj_surjective F.pos_dim (F.regionOf v))

/-- **The coarse three-site chain is injective at the `r-b` edge.** The endpoint
super-sites (red and blue blocks) and the middle super-site (complement block) are
all injective, so the edge-blocked three-site injectivity hypothesis holds for the
coarse tensor at its `r-b` edge. This is the input to the proven injective
three-site comparison, supplied entirely from the normal blocking hypothesis with
no single-vertex injectivity of the original tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, the three-site chain after
`eq:block_to_mps`, lines 1449--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem coarseTensor_edgeBlockedThreeSiteInjective :
    EdgeBlockedThreeSiteInjective (G := coarseGraph) (F.coarseTensor) coarseEdgeRB :=
  F.coarseTensor_isVertexInjective.edgeBlockedThreeSiteInjective
    F.pos_coarseBondDim coarseEdgeRB

end CoarseBlockingFrame

/-! ### The coarse edge-inserted coefficient transfer

Two coarse tensors blocked around the same edge (frames `F` for `A`, `F'` for `B`)
that share the same coarse bond dimensions and generate the same coarse state admit
the proven injective three-site comparison verbatim. The comparison
`exists_edgeInsertedCoeff_eq` runs on the coarse `r-b` edge, whose bond space is the
single coarse bond dimension `coarseBondDim coarseEdgeRB`. The output is the bond
gauge on the coarse `r-b` bond: for every matrix inserted on that bond of the first
coarse tensor there is a matrix on the second coarse tensor giving the same
coarse edge-inserted coefficient at every coarse physical configuration.

This is the entire content the proven edge machinery supplies; the descent to the
original `IsBondLocalTransferKernel` on the original edge `e` is the bridge
identity recorded in `docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/

/-- **The coarse edge-inserted coefficient transfer.** For two coarse frames over
`A` and `B` with the same coarse bond dimensions and the same coarse state, the
proven injective three-site comparison on the coarse `r-b` edge gives, for every
matrix inserted on the coarse `r-b` bond of the first coarse tensor, a matrix on the
second coarse tensor with equal coarse edge-inserted coefficients at every coarse
physical configuration.

No single-vertex injectivity of `A` or `B` is used: the two edge-blocked three-site
injectivities are `coarseTensor_edgeBlockedThreeSiteInjective`, both from the
blocked-region injectivities of the frames.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--583 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem coarse_exists_edgeInsertedCoeff_eq {A B : Tensor G d}
    (F : CoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoarseBlockingFrame (G := G) (d := d) B)
    (hsame : SameState (F.coarseTensor) (F'.coarseTensor))
    (M : Matrix (Fin (F.coarseBondDim coarseEdgeRB))
        (Fin (F.coarseBondDim coarseEdgeRB)) ℂ) :
    ∃ N : Matrix (Fin (F'.coarseBondDim coarseEdgeRB))
        (Fin (F'.coarseBondDim coarseEdgeRB)) ℂ,
      ∀ σ : Fin 3 → Fin (coarseDim V d),
        edgeInsertedCoeff (G := coarseGraph) (F.coarseTensor) coarseEdgeRB σ M =
          edgeInsertedCoeff (G := coarseGraph) (F'.coarseTensor) coarseEdgeRB σ N :=
  exists_edgeInsertedCoeff_eq (G := coarseGraph) (F.coarseTensor) (F'.coarseTensor)
    coarseEdgeRB F.coarseTensor_edgeBlockedThreeSiteInjective
    F'.coarseTensor_edgeBlockedThreeSiteInjective hsame F'.pos_coarseBondDim M

end PEPS
end TNLean
