import TNLean.PEPS.Blocking
import TNLean.PEPS.FiniteKernelDescent
import TNLean.PEPS.TwoInjectiveComparison

/-!
# Vertex-complement region tensor for PEPS

This file gives the complement region $V\setminus\{v\}$ its own blocked tensor,
opened along the star of the selected vertex $v$. For a vertex $v$, the star
boundary is the family of edges incident to $v$, and the complement tensor is the
contraction of all tensors at vertices $w\ne v$ with the star bonds left open and
its own physical index on $V\setminus\{v\}$.

This is the analogue of `EdgeMiddlePhysical.Basic` with the vertex star
`IncidentEdge G v` as the open boundary instead of the two endpoint residual
stars of an edge. It is the second injective block in the one-vertex-versus-
complement comparison of arXiv:1804.04964, Section 3.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, lines 1205--1210](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 205--250 (a contraction of
  injective tensors is injective) and 1205--1210 (one vertex against its
  complement).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Complement vertices and configurations -/

/-- The vertices other than `v`, as a finite set. -/
def vertexComplementVertices (v : V) : Finset V :=
  Finset.univ.erase v

omit [DecidableRel G.Adj] in
@[simp] theorem mem_vertexComplementVertices_iff (v w : V) :
    w ∈ vertexComplementVertices (V := V) v ↔ w ≠ v := by
  simp [vertexComplementVertices]

omit [DecidableRel G.Adj] in
@[simp] theorem notMem_vertexComplementVertices_self (v : V) :
    v ∉ vertexComplementVertices (V := V) v := by
  simp [vertexComplementVertices]

omit [DecidableRel G.Adj] in
/-- A complement vertex of `v` is distinct from `v`. -/
theorem complementVertex_ne (v : V) {w : V} (hw : w ∈ vertexComplementVertices (V := V) v) :
    w ≠ v := (mem_vertexComplementVertices_iff (V := V) v w).mp hw

/-- The predicate singling out edges incident to the selected vertex `v`. -/
def IsStarEdge (v : V) (f : Edge G) : Prop :=
  f.1.1 = v ∨ f.1.2 = v

instance (v : V) (f : Edge G) : Decidable (IsStarEdge (G := G) v f) := by
  unfold IsStarEdge; infer_instance

/-- Internal complement edges: edges with neither endpoint equal to `v`. -/
abbrev VertexComplementInternalEdge (v : V) : Type _ :=
  {f : Edge G // ¬ IsStarEdge (G := G) v f}

instance instFintypeVertexComplementInternalEdge (v : V) :
    Fintype (VertexComplementInternalEdge (G := G) v) :=
  inferInstance

/-- Virtual configurations on the internal complement edges of `v`. -/
abbrev VertexComplementConfig (A : Tensor G d) (v : V) : Type _ :=
  (f : VertexComplementInternalEdge (G := G) v) → Fin (A.bondDim f.1)

instance instFintypeVertexComplementConfig (A : Tensor G d) (v : V) :
    Fintype (VertexComplementConfig (G := G) A v) :=
  inferInstance

/-! ### Reading a complement-vertex local configuration -/

/-- The value of a star configuration together with an internal configuration on
an edge incident to a complement vertex `w`.

If the incident edge `ie` is a star edge of `v`, the value is read from
`starCfg`; otherwise it is read from the internal configuration `r`. This is the
vertex-star analogue of `edgeComplementValue`. -/
noncomputable def vertexComplementValue (A : Tensor G d) (v : V)
    (starCfg : LocalVirtualConfig A v) (r : VertexComplementConfig (G := G) A v)
    {w : V} (_hw : w ≠ v) (ie : IncidentEdge G w) :
    Fin (A.bondDim ie.1) :=
  if h : IsStarEdge (G := G) v ie.1 then
    starCfg ⟨ie.1, h⟩
  else
    r ⟨ie.1, h⟩

/-! ### The vertex-complement tensor family -/

/-- Physical configurations on the complement region $V\setminus\{v\}$. -/
abbrev VertexComplementPhysicalConfig (v : V) : Type _ :=
  (w : {w : V // w ≠ v}) → Fin d

instance instFintypeVertexComplementPhysicalConfig (v : V) :
    Fintype (VertexComplementPhysicalConfig (V := V) (d := d) v) :=
  inferInstance

/-- The complement tensor weight: the product of all tensors at vertices `w \ne v`,
with the star bonds fixed by `starCfg` and the internal bonds summed.

This is the contraction of `A` over `V\{v}` with the v-star left open, the
vertex-star analogue of `edgeOpenMiddleWeightOn`. -/
noncomputable def vertexComplementWeight (A : Tensor G d) (v : V)
    (starCfg : LocalVirtualConfig A v)
    (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) : ℂ :=
  ∑ r : VertexComplementConfig (G := G) A v,
    ∏ w : {w : V // w ≠ v},
      A.component w.1
        (fun ie => vertexComplementValue (G := G) A v starCfg r w.2 ie) (τ w)

/-- The vertex-complement tensor family, indexed by the v-star boundary
configuration with physical leg on the complement region. -/
noncomputable def vertexComplementTensorFamily (A : Tensor G d) (v : V) :
    LocalVirtualConfig A v →
      VertexComplementPhysicalConfig (V := V) (d := d) v → ℂ :=
  fun starCfg τ => vertexComplementWeight (G := G) A v starCfg τ

/-- Injectivity of the vertex-complement tensor family. -/
def VertexComplementTensorInjective (A : Tensor G d) (v : V) : Prop :=
  LinearIndependent ℂ (vertexComplementTensorFamily (G := G) A v)

end PEPS
end TNLean
