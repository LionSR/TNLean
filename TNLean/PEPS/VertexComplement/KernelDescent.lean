import TNLean.PEPS.VertexComplement.Basic

/-!
# Kernel descent for the vertex-complement block

This file proves that the vertex-complement tensor family of
`VertexComplement.Basic` is linearly independent, by the finite kernel-descent
device of `EdgeMiddlePhysical.KernelDescent` adapted to the vertex star
`IncidentEdge G v` as the open boundary.

The contraction region is $V\setminus\{v\}$. Deleting one complement vertex
$j\ne v$ at a time uses the one-sided inverse at $j$
(`IsVertexInjective.localCoeff_eq_zero_of_contract_zero`); the terminal empty
region forces every boundary coefficient to vanish, using positive bond
dimensions to fill the interior virtual indices.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, lines 205--250 and 1205--1210](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Star-bond split equivalence at a complement vertex -/

/-- The predicate on edges singling out those incident to a complement vertex
`j`. -/
def IsIncidentEdge (j : V) (f : Edge G) : Prop :=
  f.1.1 = j ∨ f.1.2 = j

instance (j : V) (f : Edge G) : Decidable (IsIncidentEdge (G := G) j f) := by
  unfold IsIncidentEdge; infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- For a vertex `j` and an incident edge `ie` at `j`, the underlying edge is
incident to `j`. -/
theorem isIncidentEdge_of_incident (j : V) (ie : IncidentEdge G j) :
    IsIncidentEdge (G := G) j ie.1 := ie.2

/-- The split equivalence at a complement vertex `j`: a global virtual
configuration is the local configuration at `j` together with the configuration
on the edges not incident to `j`. -/
noncomputable def vertexConfigSplitAt (A : Tensor G d) (j : V) :
    VirtualConfig A ≃
      LocalVirtualConfig A j ×
        ((f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1)) where
  toFun ζ :=
    (fun ie : IncidentEdge G j => ζ ie.1, fun f => ζ f.1)
  invFun x := fun f =>
    if h : IsIncidentEdge (G := G) j f then
      x.1 ⟨f, h⟩
    else
      x.2 ⟨f, h⟩
  left_inv ζ := by
    funext f
    dsimp only
    by_cases h : IsIncidentEdge (G := G) j f
    · rw [dif_pos h]
    · rw [dif_neg h]
  right_inv x := by
    apply Prod.ext
    · funext ie
      have h : IsIncidentEdge (G := G) j ie.1 := ie.2
      dsimp only
      rw [dif_pos h]
    · funext f
      have h : ¬ IsIncidentEdge (G := G) j f.1 := f.2
      dsimp only
      rw [dif_neg h]

omit [Fintype V] in
@[simp] theorem vertexConfigSplitAt_fst (A : Tensor G d) (j : V) (ζ : VirtualConfig A)
    (ie : IncidentEdge G j) :
    (vertexConfigSplitAt (G := G) A j ζ).1 ie = ζ ie.1 := rfl

omit [Fintype V] in
@[simp] theorem vertexConfigSplitAt_symm_apply_incident (A : Tensor G d) (j : V)
    (η : LocalVirtualConfig A j)
    (r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1))
    (ie : IncidentEdge G j) :
    (vertexConfigSplitAt (G := G) A j).symm (η, r) ie.1 = η ie := by
  have h : IsIncidentEdge (G := G) j ie.1 := ie.2
  change (if hh : IsIncidentEdge (G := G) j ie.1 then η ⟨ie.1, hh⟩ else r ⟨ie.1, hh⟩) = η ie
  rw [dif_pos h]

/-! ### Kernel condition -/

/-- The exposed-agreement indicator at stage `S`: `1` if `ζ` agrees with `ζ₀` on
every edge that touches no vertex of `S`, and `0` otherwise. -/
noncomputable def vcExposedIndicator (A : Tensor G d) (S : Finset V)
    (ζ ζ₀ : VirtualConfig A) : ℂ :=
  if (∀ f : Edge G, f.1.1 ∉ S → f.1.2 ∉ S → ζ f = ζ₀ f) then 1 else 0

/-- The guarded local factor at `w` in the kernel condition: the tensor at `w`
contracted along the global configuration when `w \ne v`, and `1` at `v`. -/
noncomputable def vcFactor (A : Tensor G d) (v : V) (w : V)
    (ζ : VirtualConfig A) (τ : V → Fin d) : ℂ :=
  if w ≠ v then A.component w (fun ie => ζ ie.1) (τ w) else 1

/-- The kernel condition at stage `S` for the coefficient family `c`. -/
noncomputable def vertexComplementKernelCondition (A : Tensor G d) (v : V)
    (c : LocalVirtualConfig A v →₀ ℂ) (S : Finset V) : Prop :=
  ∀ (ζ₀ : VirtualConfig A) (τ : V → Fin d),
    ∑ ζ : VirtualConfig A,
      vcExposedIndicator (G := G) A S ζ ζ₀ *
        c (vertexStarLabel (G := G) A v ζ) *
        ∏ w ∈ S, vcFactor (G := G) A v w ζ τ = 0

end PEPS
end TNLean
