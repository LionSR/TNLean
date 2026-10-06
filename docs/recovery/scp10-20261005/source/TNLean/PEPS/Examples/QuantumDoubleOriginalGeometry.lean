/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.ToricCodePlaquetteGeometry

/-!
# Arrow-sensitive quantum-double terms on the original spin lattice

SCP10, arXiv:1001.3807v3, Section 7.2, lines 2858–2923 and Figure
`fig:ex:kitaev-lattice`: tile interiors are the clockwise A faces used by
(7.10); the intervening A faces have the opposite geometric orientation.
The four-spin order and the outgoing/incoming B incidences below are defined
on actual fine physical sites, independently of any transported operator.
The group-independent face geometry and its bijective indexing are reused.

**Scope restriction (native even torus):** fine periods are 2w,2h with w,h≥3.
See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "E" => Edge (torusGraph width height)
local notation "tile" => kitaevPeriodicTilingEquiv (width := width) (height := height)
variable {G : Type*} [Group G]

/-- The source's ordered four-spin product: clockwise inside a tile and
oppositely oriented around an intervening A face, following its arrows. -/
def quantumDoubleOriginalAHolonomy (j : V ⊕ V) (σ : F → G) : G :=
  match j with
  | .inl v => σ (tile (v, 0)) * σ (tile (v, 1)) *
      σ (tile (v, 2)) * σ (tile (v, 3))
  | .inr v => σ (tile ((v.1, v.2 + 1), 1)) * σ (tile (v, 0)) *
      σ (tile ((v.1 + 1, v.2), 3)) * σ (tile ((v.1 + 1, v.2 + 1), 2))

/-- The two physical arrows pointing away from a B face. These spins receive Lᵤ. -/
def quantumDoubleOriginalBOutgoing (e : E) : Finset F :=
  match torusEdgeEquiv.symm e with
  | .inl v => {tile (v, 1), tile ((v.1 + 1, v.2), 3)}
  | .inr v => {tile (v, 0), tile ((v.1, v.2 + 1), 2)}

/-- The two physical arrows pointing towards a B face. These spins receive Rᵤ. -/
def quantumDoubleOriginalBIncoming (e : E) : Finset F :=
  match torusEdgeEquiv.symm e with
  | .inl v => {tile (v, 0), tile ((v.1 + 1, v.2), 2)}
  | .inr v => {tile (v, 3), tile ((v.1, v.2 + 1), 1)}

@[simp]
theorem quantumDoubleOriginalBOutgoing_right (v : V) :
    quantumDoubleOriginalBOutgoing (torusRightEdge v) =
      {tile (v, 1), tile ((v.1 + 1, v.2), 3)} := by
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (.inl v)) with
    | .inl w => _ | .inr w => _) = _
  rw [Equiv.symm_apply_apply]

@[simp]
theorem quantumDoubleOriginalBOutgoing_up (v : V) :
    quantumDoubleOriginalBOutgoing (torusUpEdge v) =
      {tile (v, 0), tile ((v.1, v.2 + 1), 2)} := by
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (.inr v)) with
    | .inl w => _ | .inr w => _) = _
  rw [Equiv.symm_apply_apply]

@[simp]
theorem quantumDoubleOriginalBIncoming_right (v : V) :
    quantumDoubleOriginalBIncoming (torusRightEdge v) =
      {tile (v, 0), tile ((v.1 + 1, v.2), 2)} := by
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (.inl v)) with
    | .inl w => _ | .inr w => _) = _
  rw [Equiv.symm_apply_apply]

@[simp]
theorem quantumDoubleOriginalBIncoming_up (v : V) :
    quantumDoubleOriginalBIncoming (torusUpEdge v) =
      {tile (v, 3), tile ((v.1, v.2 + 1), 1)} := by
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (.inr v)) with
    | .inl w => _ | .inr w => _) = _
  rw [Equiv.symm_apply_apply]

/-- All four B spins occur exactly once, with the source's two L and two R arrows. -/
theorem quantumDoubleOriginalB_incidence (e : E) :
    Disjoint (quantumDoubleOriginalBOutgoing e) (quantumDoubleOriginalBIncoming e) ∧
      quantumDoubleOriginalBOutgoing e ∪ quantumDoubleOriginalBIncoming e =
        toricCodeBRegion e := by
  obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e <;>
    simp [quantumDoubleOriginalBOutgoing, quantumDoubleOriginalBIncoming,
      toricCodeBRegion, (tile).injective.eq_iff, Finset.disjoint_left,
      Finset.ext_iff] <;> aesop

/-- The literal source B action on original spins, with all other spins as
spectators. Its definition uses only Lᵤ(g)=ug and Rᵤ(g)=gu⁻¹ on the indicated face. -/
def quantumDoubleOriginalBAction (e : E) (u : G) (σ : F → G) : F → G := fun p =>
  if p ∈ quantumDoubleOriginalBOutgoing e then u * σ p
  else if p ∈ quantumDoubleOriginalBIncoming e then σ p * u⁻¹
  else σ p

/-- Spins outside the literal four-site B face are unchanged. -/
theorem quantumDoubleOriginalBAction_spectator (e : E) (u : G) (σ : F → G)
    (p : F) (hp : p ∉ toricCodeBRegion e) :
    quantumDoubleOriginalBAction e u σ p = σ p := by
  have h := (quantumDoubleOriginalB_incidence e).2
  have ho : p ∉ quantumDoubleOriginalBOutgoing e := by
    intro hc
    exact hp (h ▸ Finset.mem_union_left _ hc)
  have hi : p ∉ quantumDoubleOriginalBIncoming e := by
    intro hc
    exact hp (h ▸ Finset.mem_union_right _ hc)
  simp [quantumDoubleOriginalBAction, ho, hi]

@[simp]
theorem quantumDoubleOriginalBAction_one (e : E) (σ : F → G) :
    quantumDoubleOriginalBAction e 1 σ = σ := by
  funext p
  simp [quantumDoubleOriginalBAction]

theorem quantumDoubleOriginalBAction_mul (e : E) (u v : G) (σ : F → G) :
    quantumDoubleOriginalBAction e (u * v) σ =
      quantumDoubleOriginalBAction e u (quantumDoubleOriginalBAction e v σ) := by
  funext p
  simp only [quantumDoubleOriginalBAction]
  split_ifs <;> simp [mul_assoc, mul_inv_rev]

/-- The independently specified original four-spin action is a permutation
representation of G on the entire fine-lattice configuration space. -/
def quantumDoubleOriginalBPermutation (e : E) : G →* Equiv.Perm (F → G) where
  toFun u :=
    { toFun := quantumDoubleOriginalBAction e u
      invFun := quantumDoubleOriginalBAction e u⁻¹
      left_inv σ := by rw [← quantumDoubleOriginalBAction_mul, inv_mul_cancel]; simp
      right_inv σ := by rw [← quantumDoubleOriginalBAction_mul, mul_inv_cancel]; simp }
  map_one' := by apply Equiv.ext; exact quantumDoubleOriginalBAction_one e
  map_mul' u v := by apply Equiv.ext; exact quantumDoubleOriginalBAction_mul e u v

variable [Fintype G] [DecidableEq G]
local notation "block" => quantumDoublePhysicalBlockingEquiv
  (G := G) (width := width) (height := height)

omit [Fact (2 < width)] [Fact (2 < height)] [Fintype G] [DecidableEq G] in
/-- Equality of the original ordered A product with the actual K local/hole
product. No reordering of noncommuting spin values is permitted. -/
theorem quantumDoubleOriginalAHolonomy_block (j : V ⊕ V) (σ : F → G) :
    quantumDoubleOriginalAHolonomy j σ =
      match j with
      | .inl v => quantumDoubleKHolonomy (block σ v)
      | .inr v => quantumDoubleKLatticePlaquetteHolonomy (block σ) v := by
  cases j <;> rfl

omit [Fintype G] [DecidableEq G] in
/-- Physical regrouping intertwines the independently defined four-spin L/R
operation with the actual shared K-bond color change. This holds for every
finite group, every spin configuration, and both periodic seams. -/
theorem quantumDoubleOriginalBAction_block (e : E) (u : G) (σ : F → G) :
    block (quantumDoubleOriginalBAction e u σ) =
      quantumDoubleKLatticeBondPermutation e u (block σ) := by
  obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e
  · change block (quantumDoubleOriginalBAction (torusRightEdge v) u σ) =
      quantumDoubleKLatticeBondPermutation (torusRightEdge v) u (block σ)
    funext w
    simp only [quantumDoublePhysicalBlockingEquiv, finFourArrowEquiv_apply]
    simp only [quantumDoubleKLatticeBondPermutation, MonoidHom.coe_comp,
      Function.comp_apply, quantumDoubleKLatticeGaugePermutation, MonoidHom.coe_mk,
      OneHom.coe_mk, Equiv.coe_fn_mk, quantumDoubleKLatticeGauge,
      MonoidHom.mulSingle_apply]
    simp only [Pi.mulSingle_apply, torusDownEdge, torusLeftEdge,
      Ne.symm (torusRightEdge_ne_torusUpEdge _ _), torusRightEdge_injective.eq_iff]
    have hs : (w.1 - 1, w.2) = v ↔ w = (v.1 + 1, v.2) := by
      simp [Prod.ext_iff, sub_eq_iff_eq_add]
    simp [hs, quantumDoubleOriginalBAction, quantumDoubleOriginalBOutgoing_right,
      quantumDoubleOriginalBIncoming_right, (tile).injective.eq_iff, ite_mul,
      apply_ite Inv.inv, mul_ite]
  · change block (quantumDoubleOriginalBAction (torusUpEdge v) u σ) =
      quantumDoubleKLatticeBondPermutation (torusUpEdge v) u (block σ)
    funext w
    simp only [quantumDoublePhysicalBlockingEquiv, finFourArrowEquiv_apply]
    simp only [quantumDoubleKLatticeBondPermutation, MonoidHom.coe_comp,
      Function.comp_apply, quantumDoubleKLatticeGaugePermutation, MonoidHom.coe_mk,
      OneHom.coe_mk, Equiv.coe_fn_mk, quantumDoubleKLatticeGauge,
      MonoidHom.mulSingle_apply]
    simp only [Pi.mulSingle_apply, torusDownEdge, torusLeftEdge,
      torusRightEdge_ne_torusUpEdge, torusUpEdge_injective.eq_iff]
    have hs : (w.1, w.2 - 1) = v ↔ w = (v.1, v.2 + 1) := by
      simp [Prod.ext_iff, sub_eq_iff_eq_add]
    simp [hs, quantumDoubleOriginalBAction, quantumDoubleOriginalBOutgoing_up,
      quantumDoubleOriginalBIncoming_up, (tile).injective.eq_iff, ite_mul,
      apply_ite Inv.inv, mul_ite]

end TNLean.PEPS
