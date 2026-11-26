/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Tensor.Region.VertexComplement
import TNLean.PEPS.Graph.Region.InjectiveRegion
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

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

The file also records the boundary configuration of a region read on its complement
(`regionComplementBoundaryConfig`), the blocked weight of the full vertex set
(`regionBlockedWeight_univ`), the blocked weights of a tensor with reindexed bond
dimensions (`regionBlockedWeight_reindexTensor`), and the blocked-region tensor map
(`regionBlockedTensorMap`).

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, lines 205--250 and 1205--1210](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 205--250 (a contraction of
  injective tensors is injective) and 1205--1210 (one region against its
  complement).
-/

open ManyBody (Edge)

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Region configurations

The open virtual legs live on the crossing edges; the physical legs live on the
vertices of `R`. -/

/-- An assignment of virtual indices to the edges crossing the boundary of `R`.

These are the open legs of the blocked tensor: an edge crosses the boundary of
`R` precisely when exactly one of its endpoints lies in `R`. -/
abbrev RegionBoundaryConfig (A : Tensor G d) (R : Finset V) : Type _ :=
  (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f}) → Fin (A.bondDim f.1)

instance instFintypeRegionBoundaryConfig (A : Tensor G d) (R : Finset V) :
    Fintype (RegionBoundaryConfig (G := G) A R) :=
  inferInstance

/-- Physical configurations on the region `R`: one physical index per vertex of
`R`. -/
abbrev RegionPhysicalConfig (R : Finset V) : Type _ :=
  (w : {w : V // w ∈ R}) → Fin d

omit [Fintype V] in
/-- The vertex product over `R` reads a virtual configuration only through edges incident to
`R`: two configurations agreeing on every `R`-incident edge give the same product. -/
theorem regionProd_subtype_congr {A : Tensor G d} (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) {ζ ζ' : VirtualConfig A}
    (h : ∀ e : Edge G, ManyBody.IsRegionIncidentEdge (G := G) R e → ζ e = ζ' e) :
    (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ' ie.1) (σ w) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  refine h ie.1 ?_
  rcases ie.2 with hie | hie
  · exact Or.inl (by rw [hie]; exact w.2)
  · exact Or.inr (by rw [hie]; exact w.2)

/-- The boundary configuration read off a global virtual configuration: the
labels on the edges crossing the boundary of `R`. -/
def regionBoundaryLabel (A : Tensor G d) (R : Finset V) (ζ : VirtualConfig A) :
    RegionBoundaryConfig (G := G) A R :=
  fun f => ζ f.1

omit [Fintype V] in
@[simp] theorem regionBoundaryLabel_apply (A : Tensor G d) (R : Finset V)
    (ζ : VirtualConfig A) (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f}) :
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

variable {A : Tensor G d}

/-! ### Transporting region configurations along a region-set equality

When two regions are equal as finite sets, their boundary and physical configuration types
coincide. The transport equivalences carry a configuration across the equality, and the blocked
weight transports with them. -/

/-- The transport equivalence of boundary configurations along a region-set equality: relabel
the boundary edges by the predicate equivalence, leaving the assignment unchanged. -/
def regionBoundaryConfigCongr {S R : Finset V} (h : S = R) :
    RegionBoundaryConfig (G := G) A S ≃ RegionBoundaryConfig (G := G) A R :=
  Equiv.piCongrLeft' _
    (Equiv.subtypeEquivRight (ManyBody.isRegionBoundaryEdge_congr (G := G) h))

omit [Fintype V] in
/-- The transported configuration reads the same value as the original on a boundary edge. -/
theorem regionBoundaryConfigCongr_apply {S R : Finset V} (h : S = R)
    (bcfg : RegionBoundaryConfig (G := G) A S)
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryConfigCongr (A := A) h bcfg f =
      bcfg ⟨f.1, (ManyBody.isRegionBoundaryEdge_congr (G := G) h f.1).mpr f.2⟩ := by
  rfl

/-- The transport equivalence of physical configurations along a region-set equality: relabel
the vertex index along the equality of regions. -/
def regionPhysicalConfigCongr {S R : Finset V} (h : S = R) :
    RegionPhysicalConfig (V := V) (d := d) S ≃ RegionPhysicalConfig (V := V) (d := d) R :=
  Equiv.piCongrLeft' _ (Equiv.subtypeEquivRight (fun _ => by rw [h]))

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] in
/-- The transported physical configuration reads the same value as the original on a vertex. -/
theorem regionPhysicalConfigCongr_apply {S R : Finset V} (h : S = R)
    (τ : RegionPhysicalConfig (V := V) (d := d) S) (w : {w : V // w ∈ R}) :
    regionPhysicalConfigCongr (d := d) h τ w = τ ⟨w.1, by rw [h]; exact w.2⟩ := rfl

/-- The blocked-region weight transports along a region-set equality: for equal regions the
weight of a configuration agrees with the weight of its transported boundary and physical
configurations. -/
theorem regionBlockedWeight_congr {S R : Finset V} (h : S = R)
    (bdry : RegionBoundaryConfig (G := G) A S)
    (τ : RegionPhysicalConfig (V := V) (d := d) S) :
    regionBlockedWeight (G := G) A S bdry τ =
      regionBlockedWeight (G := G) A R
        (regionBoundaryConfigCongr (A := A) h bdry)
        (regionPhysicalConfigCongr (d := d) h τ) := by
  subst h
  rfl

/-! ### Boundary configurations of a region read on its complement -/

section ComplementBoundaryConfig

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The boundary configuration on the complement `univ \ R`, obtained from a
boundary configuration on `R` by reading each crossing edge under the
boundary-edge identification. -/
def regionComplementBoundaryConfig (A : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R) :
    RegionBoundaryConfig (G := G) A (Finset.univ \ R) :=
  fun f => bdry ((regionBoundaryEdgeComplEquiv (G := G) R).symm f)

/-- The complement boundary configuration reads the boundary edge `f` of `R`,
viewed on the complement as `regionBoundaryEdgeToCompl R f`, off the original
boundary value at `f`. -/
theorem regionComplementBoundaryConfig_apply_toCompl (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
    (bdry : RegionBoundaryConfig (G := G) A R) :
    regionComplementBoundaryConfig (G := G) A R bdry (regionBoundaryEdgeToCompl (G := G) R f) =
      bdry f := by
  rw [regionComplementBoundaryConfig]
  congr 1

end ComplementBoundaryConfig

/-! ### Blocked weights of a tensor with reindexed bond dimensions -/

section ReindexTensor

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The blocked-region weight transports along a bond-dimension reindex: the
weight of the reindexed tensor at a boundary configuration is the weight of the
original tensor at the cast boundary configuration. -/
theorem regionBlockedWeight_reindexTensor (B : Tensor G d) {bd : Edge G → ℕ}
    (h : bd = B.bondDim) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) (reindexTensor (G := G) B h) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedWeight (G := G) (reindexTensor (G := G) B h) R bdry τ =
      regionBlockedWeight (G := G) B R
        (fun f => Fin.cast (congr_fun h f.1) (bdry f)) τ := by
  classical
  rw [regionBlockedWeight, regionBlockedWeight]
  -- Reindex the constrained virtual-configuration sum by casting every bond.
  let φ : VirtualConfig (reindexTensor (G := G) B h) ≃ VirtualConfig B :=
    Equiv.piCongrRight fun e =>
      finCongr (by simpa [reindexTensor_bondDim] using congr_fun h e)
  refine Finset.sum_nbij' φ φ.symm ?_ ?_ ?_ ?_ ?_
  · -- Forward map lands in the complement filter.
    intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    funext f
    have hf : regionBoundaryLabel (G := G) (reindexTensor (G := G) B h) R ζ f = bdry f :=
      congrFun hζ f
    rw [regionBoundaryLabel_apply] at hf ⊢
    change Fin.cast (by simpa [reindexTensor_bondDim] using congr_fun h f.1) (ζ f.1) =
      Fin.cast (by simpa [reindexTensor_bondDim] using congr_fun h f.1) (bdry f)
    rw [hf]
  · -- Backward map lands in the original filter.
    intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    funext f
    have hf : regionBoundaryLabel (G := G) B R ζ f = Fin.cast (congr_fun h f.1) (bdry f) :=
      congrFun hζ f
    rw [regionBoundaryLabel_apply] at hf ⊢
    apply Fin.eq_of_val_eq
    change (((finCongr (by simpa [reindexTensor_bondDim] using congr_fun h f.1)).symm
      (ζ f.1) : Fin ((reindexTensor (G := G) B h).bondDim f.1)) : ℕ) = (bdry f : ℕ)
    rw [finCongr_symm_apply_coe]
    exact (congrArg Fin.val hf).trans (Fin.val_cast _ _)
  · -- Left inverse.
    intro ζ _
    exact φ.left_inv ζ
  · -- Right inverse.
    intro ζ _
    exact φ.right_inv ζ
  · -- Matching summand: products of casts agree.
    intro ζ _
    refine Finset.prod_congr rfl fun w _ => ?_
    rfl

end ReindexTensor

/-! ### The blocked-region tensor map -/

section BlockedTensorMap

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The blocked-region tensor map: the linear combination of the blocked-region
weight family of `R`, sending a boundary-configuration coefficient to the region
physical function it produces.

This is the region analogue of `edgeMiddleTensorMap`. Its injectivity is exactly
the blocked-tensor injectivity of `R`. -/
noncomputable def regionBlockedTensorMap (A : Tensor G d) (R : Finset V) :
    (RegionBoundaryConfig (G := G) A R → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (V := V) (d := d) R → ℂ) :=
  Fintype.linearCombination ℂ (regionBlockedTensorFamily (G := G) A R)

/-- The blocked-region tensor map is injective when the region is blocked-tensor
injective. This is the region analogue of
`edgeMiddleTensorMap_injective_of_injective`. -/
theorem regionBlockedTensorMap_injective_of_injective (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R) :
    Function.Injective (regionBlockedTensorMap (G := G) A R) :=
  hR.fintypeLinearCombination_injective

/-- The blocked-region tensor map, expanded as the boundary-configuration sum of
the blocked-region weights. -/
theorem regionBlockedTensorMap_apply (A : Tensor G d) (R : Finset V)
    (c : RegionBoundaryConfig (G := G) A R → ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedTensorMap (G := G) A R c τ =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        c μ • regionBlockedWeight (G := G) A R μ τ := by
  rw [regionBlockedTensorMap, Fintype.linearCombination_apply, Finset.sum_apply]
  rfl

end BlockedTensorMap

/-! ### The blocked weight of the full vertex set -/

section FullRegion

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The blocked weight of the full vertex set is the closed state coefficient:
there are no boundary edges, and the vertex product runs over all vertices.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex` (the degenerate end of the one-site
comparison pair). -/
theorem regionBlockedWeight_univ (A : Tensor G d)
    (μ : RegionBoundaryConfig (G := G) A (Finset.univ : Finset V))
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ : Finset V)) :
    regionBlockedWeight (G := G) A Finset.univ μ τ =
      stateCoeff A (fun v => τ ⟨v, Finset.mem_univ v⟩) := by
  classical
  have hbdry :
      IsEmpty {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) (Finset.univ :
        Finset V) f} := by
    refine ⟨fun f => ?_⟩
    rcases f.2 with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2 (Finset.mem_univ _)
    · exact h1 (Finset.mem_univ _)
  unfold regionBlockedWeight stateCoeff
  have hfilter : (Finset.univ.filter
      (fun ζ : VirtualConfig A =>
        regionBoundaryLabel (G := G) A Finset.univ ζ = μ)) = Finset.univ :=
    Finset.filter_true_of_mem (fun ζ _ => funext fun f => hbdry.elim f)
  rw [hfilter]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  exact Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun v => Finset.mem_univ v))
    _ _ (fun w => rfl)

end FullRegion

end PEPS
end TNLean
