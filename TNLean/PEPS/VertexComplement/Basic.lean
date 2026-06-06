import TNLean.PEPS.Blocking
import TNLean.PEPS.FiniteKernelDescent

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

/-! ### Complement vertices -/

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

/-! ### The vertex-complement tensor family

The complement region $V\setminus\{v\}$ is contracted over a global virtual
configuration, with the v-star left open. The boundary label is the v-star
configuration read off such a global configuration, and the physical leg lives
on $V\setminus\{v\}$. -/

/-- The v-star configuration read off a global virtual configuration: the local
virtual configuration at `v`. -/
def vertexStarLabel (A : Tensor G d) (v : V) (ζ : VirtualConfig A) :
    LocalVirtualConfig A v :=
  fun ie => ζ ie.1

omit [Fintype V] in
@[simp] theorem vertexStarLabel_apply (A : Tensor G d) (v : V) (ζ : VirtualConfig A)
    (ie : IncidentEdge G v) : vertexStarLabel (G := G) A v ζ ie = ζ ie.1 := rfl

/-- Physical configurations on the complement region $V\setminus\{v\}$. -/
abbrev VertexComplementPhysicalConfig (v : V) : Type _ :=
  (w : {w : V // w ≠ v}) → Fin d

instance instFintypeVertexComplementPhysicalConfig (v : V) :
    Fintype (VertexComplementPhysicalConfig (V := V) (d := d) v) :=
  inferInstance

/-- The complement tensor weight: the sum over all global virtual configurations
restricting to `starCfg` on the v-star, of the product of all tensors at
vertices `w \ne v`.

This is the contraction of `A` over `V\{v}` with the v-star left open, the
vertex-star analogue of `edgeOpenMiddleWeightOn`. -/
noncomputable def vertexComplementWeight (A : Tensor G d) (v : V)
    (starCfg : LocalVirtualConfig A v)
    (τ : VertexComplementPhysicalConfig (V := V) (d := d) v) : ℂ :=
  ∑ ζ ∈ Finset.univ.filter
      (fun ζ : VirtualConfig A => vertexStarLabel (G := G) A v ζ = starCfg),
    ∏ w : {w : V // w ≠ v},
      A.component w.1 (fun ie => ζ ie.1) (τ w)

/-- The vertex-complement tensor family, indexed by the v-star boundary
configuration with physical leg on the complement region. -/
noncomputable def vertexComplementTensorFamily (A : Tensor G d) (v : V) :
    LocalVirtualConfig A v →
      VertexComplementPhysicalConfig (V := V) (d := d) v → ℂ :=
  fun starCfg τ => vertexComplementWeight (G := G) A v starCfg τ

/-- Injectivity of the vertex-complement tensor family. -/
def VertexComplementTensorInjective (A : Tensor G d) (v : V) : Prop :=
  LinearIndependent ℂ (vertexComplementTensorFamily (G := G) A v)

/-- The one-sided inverse of an injective tensor at a single vertex: a
coefficient family on the local virtual configurations at `v` that contracts to
the zero physical vector vanishes.

This is the explicit-summation form of injectivity of the local tensor map at
`v`. It is the per-vertex one-sided-inverse fact of the source (the diagram at
`Papers/1804.04964/paper_normal.tex` line 203, equivalent to the existence of
the one-sided inverse at lines 205--250). -/
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

end PEPS
end TNLean
