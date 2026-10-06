/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.ToricCodePauliOperators
import TNLean.PEPS.Examples.QuantumDoubleLatticeGauge
import TNLean.PEPS.QuantumDoubleNativeGlobalBlocking

/-!
# Original-lattice toric-code plaquettes

The fine lattice is the torus with periods 2w and 2h. The disjoint 2×2
tiles use the clockwise corner order upper-right, lower-right, lower-left,
upper-left. A plaquettes occur inside a tile and in the four-tile holes;
B plaquettes lie across each horizontal or vertical tile boundary.
These are sets of four original physical sites, not operators on virtual legs.

Source: SCP10, arXiv:1001.3807v3, Section 7.1, lines 2636–2667 and
Figure `fig:ex:kitaev-lattice`. The native edge enumeration used here has
coarse periods at least three, hence fine periods at least six.

**Scope restriction (native even torus):** the full comparison uses fine
periods 2w,2h with w,h≥3. Small periodic lattices are not classified here.
See `docs/paper-gaps/scp10_toric_code_projector_normalization.tex`.
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
local notation "block" => quantumDoublePhysicalBlockingEquiv
  (G := ToricCodeGroup) (width := width) (height := height)

/-- The four original physical sites of either an interior A plaquette or
an A plaquette between four tiles. The two copies label the two placements. -/
def toricCodeARegion (j : V ⊕ V) : Finset F :=
  match j with
  | .inl v => {tile (v, 0), tile (v, 1), tile (v, 2), tile (v, 3)}
  | .inr v => {tile ((v.1, v.2 + 1), 1), tile (v, 0),
      tile ((v.1 + 1, v.2), 3), tile ((v.1 + 1, v.2 + 1), 2)}

/-- The four original physical sites surrounding a B plaquette across a tile
boundary. Every native edge specifies one such horizontal or vertical placement. -/
def toricCodeBRegion (e : E) : Finset F :=
  match torusEdgeEquiv.symm e with
  | .inl v => {tile (v, 0), tile (v, 1),
      tile ((v.1 + 1, v.2), 2), tile ((v.1 + 1, v.2), 3)}
  | .inr v => {tile (v, 0), tile (v, 3),
      tile ((v.1, v.2 + 1), 1), tile ((v.1, v.2 + 1), 2)}

@[simp]
theorem toricCodeBRegion_right (v : V) :
    toricCodeBRegion (torusRightEdge v) =
      {tile (v, 0), tile (v, 1), tile ((v.1 + 1, v.2), 2),
        tile ((v.1 + 1, v.2), 3)} := by
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (.inl v)) with
    | .inl w => _ | .inr w => _) = _
  rw [Equiv.symm_apply_apply]

@[simp]
theorem toricCodeBRegion_up (v : V) :
    toricCodeBRegion (torusUpEdge v) =
      {tile (v, 0), tile (v, 3), tile ((v.1, v.2 + 1), 1),
        tile ((v.1, v.2 + 1), 2)} := by
  change (match torusEdgeEquiv.symm (torusEdgeEquiv (.inr v)) with
    | .inl w => _ | .inr w => _) = _
  rw [Equiv.symm_apply_apply]

/-- All A supports contain four distinct physical qubits, including at a seam. -/
@[simp]
theorem card_toricCodeARegion (j : V ⊕ V) : (toricCodeARegion j).card = 4 := by
  cases j <;> simp [toricCodeARegion, (tile).injective.eq_iff]

/-- All B supports contain four distinct physical qubits, including at a seam. -/
@[simp]
theorem card_toricCodeBRegion (e : E) : (toricCodeBRegion e).card = 4 := by
  obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e
  · change (toricCodeBRegion (torusRightEdge v)).card = 4
    simp [(tile).injective.eq_iff]
  · change (toricCodeBRegion (torusUpEdge v)).card = 4
    simp [(tile).injective.eq_iff]

/-- The four corners of a literal unit square with the given lower-left
physical site, including wraparound on the fine torus. -/
def toricCodeFinePlaquette (p : F) : Finset F :=
  {(p.1 + 1, p.2 + 1), (p.1 + 1, p.2), p, (p.1, p.2 + 1)}

omit [Fact (2 < width)] [Fact (2 < height)] in
private theorem finePlaquette_tile (p : V × Fin 4) :
    toricCodeFinePlaquette (tile p) =
      {tile (kitaevTiledUp (kitaevTiledRight p)), tile (kitaevTiledRight p),
        tile p, tile (kitaevTiledUp p)} := by
  simp only [kitaevPeriodicTilingEquiv_up, kitaevPeriodicTilingEquiv_right]
  rfl

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- An interior A support is a literal unit square of the original lattice. -/
theorem toricCodeARegion_inner_eq_square (v : V) :
    toricCodeARegion (.inl v) = toricCodeFinePlaquette (tile (v, 2)) := by
  rw [finePlaquette_tile]
  rfl

omit [Fact (2 < width)] [Fact (2 < height)] in
/-- A hole A support is the unit square whose lower-left site is the tile's
upper-right corner. -/
theorem toricCodeARegion_hole_eq_square (v : V) :
    toricCodeARegion (.inr v) = toricCodeFinePlaquette (tile (v, 0)) := by
  rw [finePlaquette_tile]
  ext p
  simp [toricCodeARegion, kitaevTiledRight, kitaevTiledUp]
  tauto

/-- A horizontal B support is the unit square crossing a horizontal tile boundary. -/
theorem toricCodeBRegion_right_eq_square (v : V) :
    toricCodeBRegion (torusRightEdge v) = toricCodeFinePlaquette (tile (v, 1)) := by
  rw [finePlaquette_tile, toricCodeBRegion_right]
  ext p
  simp [kitaevTiledRight, kitaevTiledUp]
  tauto

/-- A vertical B support is the unit square crossing a vertical tile boundary. -/
theorem toricCodeBRegion_up_eq_square (v : V) :
    toricCodeBRegion (torusUpEdge v) = toricCodeFinePlaquette (tile (v, 3)) := by
  rw [finePlaquette_tile, toricCodeBRegion_up]
  ext p
  simp [kitaevTiledRight, kitaevTiledUp]
  tauto

/-- Every original unit square is one of the listed A or B plaquettes.
The four cases are the four possible lower-left corners in a 2×2 tile. -/
theorem toricCodePlaquette_coverage (p : F) :
    (∃ j, toricCodeARegion j = toricCodeFinePlaquette p) ∨
      ∃ e, toricCodeBRegion e = toricCodeFinePlaquette p := by
  obtain ⟨⟨v, i⟩, rfl⟩ := (tile).surjective p
  fin_cases i
  · exact .inl ⟨.inr v, toricCodeARegion_hole_eq_square v⟩
  · exact .inr ⟨torusRightEdge v, toricCodeBRegion_right_eq_square v⟩
  · exact .inl ⟨.inl v, toricCodeARegion_inner_eq_square v⟩
  · exact .inr ⟨torusUpEdge v, toricCodeBRegion_up_eq_square v⟩

/-- Match every tile-corner lower-left position with exactly one A or B face.
This bijection proves that the Hamiltonian index counts each original face once. -/
def toricCodePlaquetteTileIndex : (V × Fin 4) ≃ ((V ⊕ V) ⊕ E) where
  toFun p := ![.inl (.inr p.1), .inr (torusEdgeEquiv (.inl p.1)),
    .inl (.inl p.1), .inr (torusEdgeEquiv (.inr p.1))] p.2
  invFun j := match j with
    | .inl (.inl v) => (v, 2)
    | .inl (.inr v) => (v, 0)
    | .inr e => match torusEdgeEquiv.symm e with
      | .inl v => (v, 1)
      | .inr v => (v, 3)
  left_inv p := by
    rcases p with ⟨v, i⟩
    fin_cases i <;> simp
  right_inv j := by
    rcases j with (v | v) | e
    · rfl
    · rfl
    · obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e <;> simp

/-- The A/B index is in bijection with all original physical lower-left
corners, hence with the entire fine-lattice face set. -/
def toricCodePlaquetteIndexEquiv : ((V ⊕ V) ⊕ E) ≃ F :=
  toricCodePlaquetteTileIndex.symm.trans tile

/-- The face attached to each Hamiltonian index is its actual unit square. -/
theorem toricCodePlaquetteIndexEquiv_region (j : (V ⊕ V) ⊕ E) :
    (match j with | .inl k => toricCodeARegion k | .inr e => toricCodeBRegion e) =
      toricCodeFinePlaquette (toricCodePlaquetteIndexEquiv j) := by
  rcases j with (v | v) | e
  · exact toricCodeARegion_inner_eq_square v
  · exact toricCodeARegion_hole_eq_square v
  · obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e
    · simp only [toricCodePlaquetteIndexEquiv, Equiv.trans_apply,
        toricCodePlaquetteTileIndex, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply]
      exact toricCodeBRegion_right_eq_square v
    · simp only [toricCodePlaquetteIndexEquiv, Equiv.trans_apply,
        toricCodePlaquetteTileIndex, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply]
      exact toricCodeBRegion_up_eq_square v

/-- The parity of an original A plaquette is exactly the corresponding
clockwise local or hole holonomy after physical regrouping. -/
theorem toricCodeARegion_product (j : V ⊕ V) (σ : F → ToricCodeGroup) :
    (∏ p ∈ toricCodeARegion j, σ p) =
      match j with
      | .inl v => quantumDoubleKHolonomy (block σ v)
      | .inr v => quantumDoubleKLatticePlaquetteHolonomy (block σ) v := by
  cases j <;>
    simp [toricCodeARegion, (tile).injective.eq_iff, quantumDoublePhysicalBlockingEquiv,
      quantumDoubleKHolonomy, quantumDoubleKLatticePlaquetteHolonomy, mul_assoc]

/-- Original four-spin B flips become the actual single-bond color change
of K, after regrouping physical sites. This compares independently defined
physical actions on all spin configurations. -/
theorem toricCodeBRegion_flip_block (e : E) (σ : F → ToricCodeGroup) :
    block (toricCodeFlipSites (toricCodeBRegion e) σ) =
      quantumDoubleKLatticeBondPermutation e toricCodeBitOne (block σ) := by
  obtain ⟨v | v, rfl⟩ := torusEdgeEquiv.surjective e
  · change block (toricCodeFlipSites (toricCodeBRegion (torusRightEdge v)) σ) =
      quantumDoubleKLatticeBondPermutation (torusRightEdge v) toricCodeBitOne (block σ)
    funext w
    simp only [quantumDoublePhysicalBlockingEquiv, finFourArrowEquiv_apply,
      toricCodeFlipSites, Equiv.coe_fn_mk, toricCodeBRegion_right,
      Finset.mem_insert, Finset.mem_singleton, (tile).injective.eq_iff,
      Prod.mk.injEq]
    simp only [quantumDoubleKLatticeBondPermutation, MonoidHom.coe_comp,
      Function.comp_apply, quantumDoubleKLatticeGaugePermutation, MonoidHom.coe_mk,
      OneHom.coe_mk, Equiv.coe_fn_mk, quantumDoubleKLatticeGauge,
      MonoidHom.mulSingle_apply]
    simp only [Pi.mulSingle_apply, torusDownEdge, torusLeftEdge,
      Ne.symm (torusRightEdge_ne_torusUpEdge _ _),
      torusRightEdge_injective.eq_iff, toricCodeGroup_inv]
    have hs : (w.1 - 1, w.2) = v ↔ w = (v.1 + 1, v.2) := by
      simp [Prod.ext_iff, sub_eq_iff_eq_add]
    simp [hs, ite_mul, mul_ite, mul_comm]
  · change block (toricCodeFlipSites (toricCodeBRegion (torusUpEdge v)) σ) =
      quantumDoubleKLatticeBondPermutation (torusUpEdge v) toricCodeBitOne (block σ)
    funext w
    simp only [quantumDoublePhysicalBlockingEquiv, finFourArrowEquiv_apply,
      toricCodeFlipSites, Equiv.coe_fn_mk, toricCodeBRegion_up,
      Finset.mem_insert, Finset.mem_singleton, (tile).injective.eq_iff,
      Prod.mk.injEq]
    simp only [quantumDoubleKLatticeBondPermutation, MonoidHom.coe_comp,
      Function.comp_apply, quantumDoubleKLatticeGaugePermutation, MonoidHom.coe_mk,
      OneHom.coe_mk, Equiv.coe_fn_mk, quantumDoubleKLatticeGauge,
      MonoidHom.mulSingle_apply]
    simp only [Pi.mulSingle_apply, torusDownEdge, torusLeftEdge,
      torusRightEdge_ne_torusUpEdge,
      torusUpEdge_injective.eq_iff, toricCodeGroup_inv]
    have hs : (w.1, w.2 - 1) = v ↔ w = (v.1, v.2 + 1) := by
      simp [Prod.ext_iff, sub_eq_iff_eq_add]
    simp [hs, ite_mul, mul_ite, mul_comm]

end TNLean.PEPS
