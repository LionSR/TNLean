/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.KernelDescent

/-!
# Vertex-complement injectivity as a region specialization

The complement of one vertex is a finite region. Its boundary edges are exactly
the edges incident to the omitted vertex, and its physical vertices are exactly
the vertices distinct from the omitted vertex. The equivalences below identify
the boundary and physical configurations under these two descriptions.

The vertex-complement tensor is consequently the blocked-region tensor of
$V\setminus\{v\}$. Its linear independence follows from the arbitrary-region
theorem, with no second kernel-descent argument.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 979--981 and 1207--1210.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

omit [DecidableRel G.Adj] in
/-- The boundary edges of $V\setminus\{v\}$ are precisely the edges incident to
$v$. -/
theorem isRegionBoundaryEdge_vertexComplementVertices_iff (v : V) (f : Edge G) :
    IsRegionBoundaryEdge (G := G) (vertexComplementVertices (V := V) v) f ↔
      IsIncidentEdge (G := G) v f := by
  rw [IsRegionBoundaryEdge, IsIncidentEdge]
  simp only [mem_vertexComplementVertices_iff, not_not]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · refine Or.inr ⟨h, ?_⟩
      intro h'
      exact (ne_of_lt f.2.1) (h.trans h'.symm)
    · refine Or.inl ⟨?_, h⟩
      intro h'
      exact (ne_of_lt f.2.1) (h'.trans h.symm)

/-- Boundary edges of the complement of `v`, identified with edges incident to
`v`. -/
def vertexComplementBoundaryEdgeEquiv (v : V) :
    {f : Edge G // IsRegionBoundaryEdge (G := G)
      (vertexComplementVertices (V := V) v) f} ≃ IncidentEdge G v :=
  Equiv.subtypeEquivRight fun f =>
    isRegionBoundaryEdge_vertexComplementVertices_iff (G := G) v f

/-- Boundary configurations of the complement of `v`, identified with local
virtual configurations at `v`. -/
noncomputable def vertexComplementBoundaryConfigEquiv (A : Tensor G d) (v : V) :
    RegionBoundaryConfig (G := G) A (vertexComplementVertices (V := V) v) ≃
      LocalVirtualConfig A v :=
  Equiv.piCongrLeft (fun ie : IncidentEdge G v => Fin (A.bondDim ie.1))
    (vertexComplementBoundaryEdgeEquiv (G := G) v)

/-- The vertices of the complement of `v`, identified with vertices distinct
from `v`. -/
def vertexComplementVertexEquiv (v : V) :
    {w : V // w ∈ vertexComplementVertices (V := V) v} ≃ {w : V // w ≠ v} :=
  Equiv.subtypeEquivRight fun w => mem_vertexComplementVertices_iff (V := V) v w

/-- Physical configurations of the complement region, identified with physical
configurations on the vertices distinct from `v`. -/
noncomputable def vertexComplementPhysicalConfigEquiv (v : V) :
    RegionPhysicalConfig (V := V) (d := d) (vertexComplementVertices (V := V) v) ≃
      VertexComplementPhysicalConfig (V := V) (d := d) v :=
  Equiv.piCongrLeft (fun _ : {w : V // w ≠ v} => Fin d) (vertexComplementVertexEquiv v)

@[simp]
theorem vertexComplementBoundaryConfigEquiv_regionBoundaryLabel
    (A : Tensor G d) (v : V) (ζ : VirtualConfig A) :
    vertexComplementBoundaryConfigEquiv (G := G) A v
        (regionBoundaryLabel (G := G) A (vertexComplementVertices (V := V) v) ζ) =
      vertexStarLabel (G := G) A v ζ := by
  funext ie
  rfl

/-- Blocking the complement of one vertex gives the vertex-complement tensor
after identifying its open virtual and physical indices. -/
theorem regionBlockedWeight_vertexComplement (A : Tensor G d) (v : V)
    (bdry : RegionBoundaryConfig (G := G) A (vertexComplementVertices (V := V) v))
    (τ : RegionPhysicalConfig (V := V) (d := d)
      (vertexComplementVertices (V := V) v)) :
    regionBlockedWeight (G := G) A (vertexComplementVertices (V := V) v) bdry τ =
      vertexComplementWeight (G := G) A v
        (vertexComplementBoundaryConfigEquiv (G := G) A v bdry)
        (vertexComplementPhysicalConfigEquiv (d := d) v τ) := by
  classical
  unfold regionBlockedWeight vertexComplementWeight
  refine Finset.sum_congr ?_ ?_
  · ext ζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← vertexComplementBoundaryConfigEquiv_regionBoundaryLabel A v, h]
    · intro h
      apply (vertexComplementBoundaryConfigEquiv (G := G) A v).injective
      simpa using h
  · intro ζ _
    apply Fintype.prod_equiv (vertexComplementVertexEquiv v)
    intro w
    rfl

/-- The vertex-complement tensor family is linearly independent: a contraction
of injective tensors over $V\setminus\{v\}$ is injective.

**Positive-bond hypothesis (faithfulness fix).** The source works with injective
PEPS, whose virtual bond spaces are nonzero-dimensional. Without the positivity
assumption the complement tensor can vanish when an interior virtual space is
empty, breaking linear independence. The hypothesis `∀ f, 0 < A.bondDim f`
restores the source assumption; the gap is recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3. Lines 979--981 state that contracting
injective tensors gives an injective tensor; lines 1207--1210 select one tensor
and block all remaining tensors into the second injective tensor
(`Papers/1804.04964/paper_normal.tex`). -/
theorem vertexComplementTensorInjective_of_isVertexInjective
    (A : Tensor G d) (v : V) (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    VertexComplementTensorInjective (G := G) A v := by
  let R := vertexComplementVertices (V := V) v
  let Ψ := vertexComplementBoundaryConfigEquiv (G := G) A v
  let Φ := vertexComplementPhysicalConfigEquiv (V := V) (d := d) v
  have hR : LinearIndependent ℂ (regionBlockedTensorFamily (G := G) A R) :=
    regionBlockedTensorInjective_of_isVertexInjective (G := G) A R hA hpos
  have hfam : (LinearEquiv.funCongrLeft ℂ ℂ Φ) ∘
      (vertexComplementTensorFamily (G := G) A v ∘ Ψ) =
        regionBlockedTensorFamily (G := G) A R := by
    funext bdry
    funext τ
    exact (regionBlockedWeight_vertexComplement A v bdry τ).symm
  have hcomp : LinearIndependent ℂ ((LinearEquiv.funCongrLeft ℂ ℂ Φ) ∘
      (vertexComplementTensorFamily (G := G) A v ∘ Ψ)) := by
    rw [hfam]
    exact hR
  have hΨ : LinearIndependent ℂ (vertexComplementTensorFamily (G := G) A v ∘ Ψ) :=
    LinearIndependent.of_comp _ hcomp
  exact (linearIndependent_equiv Ψ).mp hΨ

end PEPS
end TNLean
