import TNLean.PEPS.VertexComplement.Basic

/-!
# Blocked-region tensor for an arbitrary PEPS region

For an arbitrary finite vertex region `R`, this file gives the blocked tensor of
`R`: the contraction of all tensors at vertices `w ∈ R`, with the edges crossing
the boundary of `R` left open, and the physical legs on `R`.

This generalizes the vertex-complement block `V\{v}` of
`TNLean.PEPS.VertexComplement`. There the open boundary is the star of the
erased vertex `v`, which for the region `R = V\{v}` is exactly the family of
edges crossing the boundary of `R`: an edge crosses the boundary of `V\{v}`
precisely when it is incident to `v`. The open boundary of a general region is
the family of edges with exactly one endpoint in `R`.

The blocked-region tensor is the second injective block of the
one-region-versus-complement comparison of arXiv:1804.04964, Section 3: a
contraction of injective tensors over any finite region is injective.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, lines 205--250 and 1205--1210](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 205--250 (a contraction of
  injective tensors is injective) and 1205--1210 (one region against its
  complement).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Boundary edges of a region

An edge crosses the boundary of `R` when exactly one of its endpoints lies in
`R`. These crossing edges carry the open virtual legs of the blocked tensor. -/

/-- An edge crosses the boundary of the region `R` when exactly one of its
endpoints lies in `R`. -/
def IsRegionBoundaryEdge (R : Finset V) (f : Edge G) : Prop :=
  (f.1.1 ∈ R ∧ f.1.2 ∉ R) ∨ (f.1.1 ∉ R ∧ f.1.2 ∈ R)

instance (R : Finset V) (f : Edge G) : Decidable (IsRegionBoundaryEdge (G := G) R f) := by
  unfold IsRegionBoundaryEdge; infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- A boundary edge of `R` has at least one endpoint in `R`. -/
theorem isRegionBoundaryEdge_touches (R : Finset V) {f : Edge G}
    (hf : IsRegionBoundaryEdge (G := G) R f) : f.1.1 ∈ R ∨ f.1.2 ∈ R := by
  rcases hf with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2

/-! ### Region configurations

The open virtual legs live on the crossing edges; the physical legs live on the
vertices of `R`. -/

/-- An assignment of virtual indices to the edges crossing the boundary of `R`.

These are the open legs of the blocked tensor: an edge crosses the boundary of
`R` precisely when exactly one of its endpoints lies in `R`. -/
abbrev RegionBoundaryConfig (A : Tensor G d) (R : Finset V) : Type _ :=
  (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) → Fin (A.bondDim f.1)

instance instFintypeRegionBoundaryConfig (A : Tensor G d) (R : Finset V) :
    Fintype (RegionBoundaryConfig (G := G) A R) :=
  inferInstance

/-- Physical configurations on the region `R`: one physical index per vertex of
`R`. -/
abbrev RegionPhysicalConfig (R : Finset V) : Type _ :=
  (w : {w : V // w ∈ R}) → Fin d

instance instFintypeRegionPhysicalConfig (R : Finset V) :
    Fintype (RegionPhysicalConfig (V := V) (d := d) R) :=
  inferInstance

/-- The boundary configuration read off a global virtual configuration: the
labels on the edges crossing the boundary of `R`. -/
def regionBoundaryLabel (A : Tensor G d) (R : Finset V) (ζ : VirtualConfig A) :
    RegionBoundaryConfig (G := G) A R :=
  fun f => ζ f.1

omit [Fintype V] in
@[simp] theorem regionBoundaryLabel_apply (A : Tensor G d) (R : Finset V)
    (ζ : VirtualConfig A) (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryLabel (G := G) A R ζ f = ζ f.1 := rfl

/-- The blocked-region weight: the sum over all global virtual configurations
restricting to `bdry` on the crossing edges, of the product of all tensors at
vertices `w ∈ R`.

This is the contraction of `A` over `R` with the boundary-crossing edges left
open. It is the general-region analogue of `vertexComplementWeight`. -/
noncomputable def regionBlockedWeight (A : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) : ℂ :=
  ∑ ζ ∈ Finset.univ.filter
      (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = bdry),
    ∏ w : {w : V // w ∈ R},
      A.component w.1 (fun ie => ζ ie.1) (τ w)

/-- The blocked-region tensor family, indexed by the boundary configuration on
the crossing edges with physical legs on `R`. -/
noncomputable def regionBlockedTensorFamily (A : Tensor G d) (R : Finset V) :
    RegionBoundaryConfig (G := G) A R →
      RegionPhysicalConfig (V := V) (d := d) R → ℂ :=
  fun bdry τ => regionBlockedWeight (G := G) A R bdry τ

/-- Injectivity of the blocked-region tensor family. -/
def RegionBlockedTensorInjective (A : Tensor G d) (R : Finset V) : Prop :=
  LinearIndependent ℂ (regionBlockedTensorFamily (G := G) A R)

end PEPS
end TNLean
