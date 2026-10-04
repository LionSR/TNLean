/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.InjectiveVertexCoordinates
import TNLean.PEPS.ParentHamiltonian.VirtualBondGroundSpace

/-!
# Endpoint-pair coordinates for virtual PEPS bonds

The independent virtual labels at all vertices are equivalent to two labels
on each edge, one at each endpoint. The equivalence retains the original
graph and the dimension of every bond. It identifies consistency of the
endpoint labels with the diagonal condition on every virtual pair.

Source: CPGSV21, arXiv:2011.12127, Section IV.C.1,
the product of virtual entangled pairs, lines 2017–2044.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

namespace TNLean.PEPS

open scoped BigOperators

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Independent virtual configurations on all vertex tensor domains.
Source: CPGSV21, Section IV.C.1, lines 2017–2028. -/
abbrev VertexVirtualConfig (A : Tensor Γ d) := (v : V) → LocalVirtualConfig A v

/-- The two endpoint labels of every virtual graph edge.
Source: the virtual-pair coordinates of CPGSV21, Section IV.C.1,
lines 2017–2028. -/
abbrev EdgePairVirtualConfig (A : Tensor Γ d) :=
  (e : Edge Γ) → Fin (A.bondDim e) × Fin (A.bondDim e)

omit [Fintype V] in
private theorem vertexVirtualConfig_apply_eq_of_vertex_eq (A : Tensor Γ d)
    (α : VertexVirtualConfig A) {u v : V} (h : u = v) (e : Edge Γ)
    (hu : e.1.1 = u ∨ e.1.2 = u) (hv : e.1.1 = v ∨ e.1.2 = v) :
    α u ⟨e, hu⟩ = α v ⟨e, hv⟩ := by
  subst v
  rfl

/-- Reorganize the independent vertex labels as independent edge pairs.
No positivity or injectivity assumption is required.
Source: the virtual-pair product of CPGSV21, lines 2017–2028. -/
def vertexVirtualConfigEquivEdgePair (A : Tensor Γ d) :
    VertexVirtualConfig A ≃ EdgePairVirtualConfig A where
  toFun α e := (α e.1.1 ⟨e, Or.inl rfl⟩, α e.1.2 ⟨e, Or.inr rfl⟩)
  invFun ζ v ie := if ie.1.1.1 = v then (ζ ie.1).1 else (ζ ie.1).2
  left_inv α := by
    funext v ie
    rcases ie.2 with h | h
    · simp only [ite_eq_left h]
      exact vertexVirtualConfig_apply_eq_of_vertex_eq A α h ie.1 (Or.inl rfl) ie.2
    · have hn : ie.1.1.1 ≠ v := fun hv =>
        (ne_of_lt ie.1.2.1) (hv.trans h.symm)
      simp only [ite_eq_right hn]
      exact vertexVirtualConfig_apply_eq_of_vertex_eq A α h ie.1 (Or.inr rfl) ie.2
  right_inv ζ := by
    funext e
    apply Prod.ext
    · simp only [ite_true]
    · simp only [ite_eq_right (ne_of_lt e.2.1)]

/-- Full-region vertex coordinates differ from global vertex coordinates
only by the redundant membership proof in the full region.
Source: CPGSV21, the global virtual-pair product, lines 2017–2028. -/
def fullRegionVertexConfigEquiv (A : Tensor Γ d) :
    RegionVertexVirtualConfig A Finset.univ ≃ VertexVirtualConfig A where
  toFun α v := α ⟨v, Finset.mem_univ v⟩
  invFun α w := α w.1
  left_inv α := by funext w; rfl
  right_inv α := rfl

/-- The full-region independent virtual coordinates are the actual edge-pair
coordinates of the graph. Source: CPGSV21, lines 2017–2028. -/
def fullRegionVertexConfigEquivEdgePair (A : Tensor Γ d) :
    RegionVertexVirtualConfig A Finset.univ ≃ EdgePairVirtualConfig A :=
  (fullRegionVertexConfigEquiv A).trans (vertexVirtualConfigEquivEdgePair A)

/-- Every edge receives the same virtual label at its two endpoints.
Source: the Bell-pair constraint in CPGSV21, lines 2017–2028. -/
def IsVertexVirtualConsistent (A : Tensor Γ d) (α : VertexVirtualConfig A) : Prop :=
  ∀ e : Edge Γ, α e.1.1 ⟨e, Or.inl rfl⟩ = α e.1.2 ⟨e, Or.inr rfl⟩

omit [Fintype V] in
/-- Endpoint consistency is exactly the diagonal condition on edge pairs.
Source: the virtual Bell-pair constraint in CPGSV21, lines 2017–2028. -/
theorem isVertexVirtualConsistent_iff_edgePair_diagonal (A : Tensor Γ d)
    (α : VertexVirtualConfig A) :
    IsVertexVirtualConsistent A α ↔
      ∀ e, ((vertexVirtualConfigEquivEdgePair A α) e).1 =
        ((vertexVirtualConfigEquivEdgePair A α) e).2 := Iff.rfl

/-- A consistent assignment of bond labels gives its endpoint labels at
every vertex. Source: the contracted virtual pairs in CPGSV21, lines 2017–2028. -/
def vertexVirtualConfigOfBonds (A : Tensor Γ d) (η : VirtualConfig A) :
    VertexVirtualConfig A := fun _ e => η e.1

omit [Fintype V] in
/-- A common bond assignment becomes diagonal in edge-pair coordinates.
Source: the Bell-pair coordinates in CPGSV21, lines 2017–2028. -/
@[simp]
theorem vertexVirtualConfigEquivEdgePair_ofBonds (A : Tensor Γ d) (η : VirtualConfig A) :
    vertexVirtualConfigEquivEdgePair A (vertexVirtualConfigOfBonds A η) =
      virtualBondDiagonalConfig A.bondDim η := rfl

omit [Fintype V] in
/-- Consistent endpoint configurations are precisely those obtained from
one virtual label on each bond. Source: the Bell-pair contraction in
CPGSV21, lines 2017–2028. -/
theorem isVertexVirtualConsistent_iff_exists_bonds (A : Tensor Γ d)
    (α : VertexVirtualConfig A) :
    IsVertexVirtualConsistent A α ↔ ∃ η : VirtualConfig A, α = vertexVirtualConfigOfBonds A η := by
  constructor
  · intro hα
    let η : VirtualConfig A := fun e => ((vertexVirtualConfigEquivEdgePair A α) e).1
    refine ⟨η, (vertexVirtualConfigEquivEdgePair A).injective ?_⟩
    funext e
    exact Prod.ext rfl (hα e).symm
  · rintro ⟨η, rfl⟩
    exact fun _ => rfl

/-- Incident labels of the full region are precisely the global bond labels.
Source: the fully contracted virtual pairs in CPGSV21, lines 2017–2028. -/
def fullRegionIncidentConfigEquivBonds (A : Tensor Γ d) :
    RegionIncidentConfig A Finset.univ ≃ VirtualConfig A where
  toFun η e := η ⟨e, Or.inl (Finset.mem_univ e.1.1)⟩
  invFun η e := η e.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full-region incident labels induce the same endpoint configuration
as their global bond assignment. Source: the Bell-pair contraction in
CPGSV21, lines 2017–2028. -/
theorem fullRegionVertexConfigEquiv_incident (A : Tensor Γ d)
    (η : RegionIncidentConfig A Finset.univ) :
    fullRegionVertexConfigEquiv A (regionIncidentVertexConfig A Finset.univ η) =
      vertexVirtualConfigOfBonds A (fullRegionIncidentConfigEquivBonds A η) := rfl

private theorem virtualBondProduct_eq_sum_diagonal {E : Type*} [Fintype E] [DecidableEq E]
    (D : E → ℕ) (ζ : VirtualBondConfig D) :
    virtualBondProduct D ζ =
      ∑ η : (e : E) → Fin (D e), if ζ = virtualBondDiagonalConfig D η then 1 else 0 := by
  classical
  by_cases hDiag : ∀ e, (ζ e).1 = (ζ e).2
  · let η₀ : (e : E) → Fin (D e) := fun e => (ζ e).1
    have hEq (η : (e : E) → Fin (D e)) :
        ζ = virtualBondDiagonalConfig D η ↔ η = η₀ := by
      constructor
      · intro h
        funext e
        exact (congrArg Prod.fst (congrFun h e)).symm
      · rintro rfl
        funext e
        exact Prod.ext rfl (hDiag e).symm
    simp [hEq, virtualBondProduct, virtualBondBell, hDiag]
  · obtain ⟨e, he⟩ := not_forall.mp hDiag
    have hProduct : virtualBondProduct D ζ = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp only [virtualBondBell, ite_eq_right he]
    have hNe (η : (e : E) → Fin (D e)) : ζ ≠ virtualBondDiagonalConfig D η := by
      intro h
      apply he
      have hp := congrFun h e
      exact (congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm
    simp [hProduct, hNe]

/-- The actual full-region virtual contraction is the product Bell vector
in endpoint-pair coordinates. No injectivity or positivity assumption is
used. Source: the independent virtual-bond product in CPGSV21,
lines 2017–2028. -/
theorem regionVirtualBondWeight_univ_apply (A : Tensor Γ d)
    (μ : RegionBoundaryConfig A Finset.univ) (α : RegionVertexVirtualConfig A Finset.univ) :
    regionVirtualBondWeight A Finset.univ μ α =
      virtualBondProduct A.bondDim (fullRegionVertexConfigEquivEdgePair A α) := by
  classical
  have hBoundary (η : RegionIncidentConfig A Finset.univ) :
      regionIncidentBoundaryLabel A Finset.univ η = μ := by
    funext e
    exact False.elim (by simpa [IsRegionBoundaryEdge] using e.2)
  simp only [regionVirtualBondWeight, hBoundary, ite_true, Finset.sum_apply, Pi.single_apply]
  rw [virtualBondProduct_eq_sum_diagonal]
  refine Fintype.sum_equiv (fullRegionIncidentConfigEquivBonds A) _ _ ?_
  intro η
  congr 1
  apply propext
  have hCoordinates :
      fullRegionVertexConfigEquivEdgePair A (regionIncidentVertexConfig A Finset.univ η) =
        virtualBondDiagonalConfig A.bondDim (fullRegionIncidentConfigEquivBonds A η) := by
    simp only [fullRegionVertexConfigEquivEdgePair, Equiv.trans_apply,
      fullRegionVertexConfigEquiv_incident, vertexVirtualConfigEquivEdgePair_ofBonds]
  constructor
  · rintro rfl
    exact hCoordinates
  · intro h
    exact (fullRegionVertexConfigEquivEdgePair A).injective (h.trans hCoordinates.symm)

/-- Reorganize full-region virtual coefficient vectors by their two edge
endpoint coordinates. Source: the virtual-pair product of CPGSV21,
lines 2017–2028. -/
def fullRegionVertexVectorEquivEdgePair (A : Tensor Γ d) :
    (RegionVertexVirtualConfig A Finset.univ → ℂ) ≃ₗ[ℂ] (EdgePairVirtualConfig A → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (fullRegionVertexConfigEquivEdgePair A).symm

/-- In edge-pair coordinates, the full-region virtual vector is exactly
the product of Bell vectors. Source: CPGSV21, lines 2017–2028. -/
theorem fullRegionVertexVectorEquivEdgePair_virtualBondWeight (A : Tensor Γ d)
    (μ : RegionBoundaryConfig A Finset.univ) :
    fullRegionVertexVectorEquivEdgePair A (regionVirtualBondWeight A Finset.univ μ) =
      virtualBondProduct A.bondDim := by
  funext ζ
  change regionVirtualBondWeight A Finset.univ μ
    ((fullRegionVertexConfigEquivEdgePair A).symm ζ) = virtualBondProduct A.bondDim ζ
  rw [regionVirtualBondWeight_univ_apply, Equiv.apply_symm_apply]

end TNLean.PEPS
