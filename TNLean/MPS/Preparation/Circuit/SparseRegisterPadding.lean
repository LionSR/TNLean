/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.Circuit.WindowGHZ
import QICLean.Circuit.Protocol.Teleportation.RegisterGates
import QICLean.Circuit.Compile.SwapRouting
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Parity padding for sparse physical registers

Teleportation between two registers uses an even number of scratch sites. In a block of odd
length, rotating its first `r + 1` sites moves the first register one site to the right; the
scratch gap is then even. The inverse rotation restores the physical ancilla sites. Both
rotations have depth bounded solely by the fixed register width. Every operation uses sites
of the original chain, including for a singleton ring.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
* arXiv:2103.13367, Example 1.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators
open Fin.NatCast

namespace MPSPreparation

namespace SparseRegister

variable {d M N r q : ℕ} {ℓ : Fin M → ℕ}

/-- The first `r + 1` sites of a block, containing one scratch site beyond the first register. -/
def prefixEmbedding (hq : r + 1 ≤ q) : Fin (r + 1) ↪ Fin q :=
  ⟨Fin.castLE hq, Fin.castLE_injective hq⟩

/-- Rotate the first `r + 1` sites by the parity of the block length. -/
noncomputable def padding (hq : r + 1 ≤ q) : Equiv.Perm (Fin q) :=
  ((finRotate (r + 1)) ^ (q % 2)).viaEmbedding (prefixEmbedding hq)

private theorem padding_prefix (hq : r + 1 ≤ q) (i : Fin (r + 1)) :
    padding hq (prefixEmbedding hq i) = prefixEmbedding hq ((finRotate (r + 1) ^ (q % 2)) i) :=
  Equiv.Perm.viaEmbedding_apply _ _ _

/-- The first register is shifted by zero or one sites, according to parity. -/
theorem padding_first (hq : r + 1 ≤ q) (i : Fin r) :
    padding hq ⟨i, by omega⟩ = ⟨q % 2 + i, by have := Nat.mod_lt q (by omega : 0 < 2); omega⟩ := by
  change padding hq (prefixEmbedding hq i.castSucc) = _
  rw [padding_prefix]
  apply Fin.ext
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · simp [h, prefixEmbedding]
  · simp only [h, pow_one, prefixEmbedding, Function.Embedding.coeFn_mk, Fin.val_castLE,
      finRotate_val, Fin.val_castSucc]
    rw [ite_eq_right (by have := i.isLt; omega)]
    omega

/-- The padding rotation fixes every site beyond its constant-size prefix. -/
theorem padding_of_ge (hq : r + 1 ≤ q) (i : Fin q) (hi : r + 1 ≤ i.val) :
    padding hq i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  simp only [prefixEmbedding, Function.Embedding.coeFn_mk, Fin.val_castLE] at this
  have := j.isLt
  omega

/-- One fixed-size prefix circuit implements each padding rotation, uniformly in block length:
the rotation of the first `r + 1` sites is a product of at most `2 (r + 1)²` gates on neighbouring
sites. -/
theorem exists_isGateProduct_padding :
    ∃ K : ℕ, ∀ q (hq : r + 1 ≤ q),
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph q)) K
          (ManyBody.sitePermOp (α := Fin d) (padding hq)) ∧
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph q)) K
          (ManyBody.sitePermOp (α := Fin d) (padding hq).symm) := by
  classical
  refine ⟨2 * (r + 1) ^ 2, fun q hq => ?_⟩
  have hπ : ∀ σ : Equiv.Perm (Fin (r + 1)),
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph q)) (2 * (r + 1) ^ 2)
        (ManyBody.sitePermOp (α := Fin d) (σ.viaEmbedding (prefixEmbedding hq))) := by
    intro σ
    rw [← ManyBody.placeAlong_sitePermOp]
    refine IsGateProduct.place_pathGraph (ManyBody.windowEquiv (prefixEmbedding hq))
      (fun p p' h => ?_) (isGateProduct_sitePermOp σ)
    rw [ManyBody.coe_windowEquiv, ManyBody.coe_windowEquiv]
    simpa [prefixEmbedding] using h
  refine ⟨hπ _, ?_⟩
  have hsymm : (padding hq).symm =
      ((finRotate (r + 1) ^ (q % 2))⁻¹).viaEmbedding (prefixEmbedding hq) := by
    rw [← Equiv.Perm.viaEmbeddingHom_apply, map_inv, Equiv.Perm.viaEmbeddingHom_apply]
    rfl
  rw [hsymm]
  exact hπ _

/-- The padding rotations act independently inside the blocks. -/
noncomputable def paddingAll (hN : ∑ k, ℓ k = N) (hq : ∀ k, r + 1 ≤ ℓ k) :
    Equiv.Perm (Fin N) :=
  (blockSigmaEquiv hN).symm.trans
    ((Equiv.sigmaCongrRight fun k => padding (hq k)).trans (blockSigmaEquiv hN))

@[simp] theorem paddingAll_blockSite (hN : ∑ k, ℓ k = N) (hq : ∀ k, r + 1 ≤ ℓ k)
    (k : Fin M) (i : Fin (ℓ k)) :
    paddingAll hN hq (blockSite hN k i) = blockSite hN k (padding (hq k) i) := by
  change (blockSigmaEquiv hN) ((Equiv.sigmaCongrRight fun k => padding (hq k))
    ((blockSigmaEquiv hN).symm ((blockSigmaEquiv hN) ⟨k, i⟩))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem paddingAll_symm_blockSite (hN : ∑ k, ℓ k = N) (hq : ∀ k, r + 1 ≤ ℓ k)
    (k : Fin M) (i : Fin (ℓ k)) :
    (paddingAll hN hq).symm (blockSite hN k i) = blockSite hN k ((padding (hq k)).symm i) := by
  apply (paddingAll hN hq).injective
  simp

/-- A block layer of site permutations is the corresponding permutation of physical sites. -/
private theorem blockLayerOp_padding (hN : ∑ k, ℓ k = N) (hq : ∀ k, r + 1 ≤ ℓ k)
    (inverse : Bool) :
    blockLayerOp hN (fun k => ManyBody.sitePermOp (α := Fin d)
      (if inverse then (padding (hq k)).symm else padding (hq k))) =
      ManyBody.sitePermOp (α := Fin d)
        (if inverse then (paddingAll hN hq).symm else paddingAll hN hq) := by
  apply Matrix.mulVec_injective
  funext v
  rw [blockLayerOp_mulVec_eq_comp hN
    (f := fun k x => x ∘ ⇑(show Equiv.Perm (Fin (ℓ k)) from
      if inverse then (padding (hq k)).symm else padding (hq k)))
    (fun _ v => ManyBody.sitePermOp_mulVec _ v), ManyBody.sitePermOp_mulVec]
  funext x
  simp only [Function.comp_apply]
  congr 1
  funext i
  obtain ⟨k, j, rfl⟩ := exists_blockSite hN i
  rw [layerCfg_apply (blockSite_injective hN) (fun _ _ h => disjoint_range_blockSite hN h)]
  cases inverse <;> simp

/-- Both padding layers have the same bound, independent of block lengths and block count. -/
theorem exists_isUnitaryCircuitOn_paddingAll :
    ∃ K : ℕ, ∀ {M N : ℕ} [NeZero N] {ℓ : Fin M → ℕ}
      (hN : ∑ k, ℓ k = N) (hq : ∀ k, r + 1 ≤ ℓ k),
      IsUnitaryCircuitOn (Geometry.ring N) Finset.univ K
          (ManyBody.sitePermOp (α := Fin d) (paddingAll hN hq)) ∧
        IsUnitaryCircuitOn (Geometry.ring N) Finset.univ K
          (ManyBody.sitePermOp (α := Fin d) (paddingAll hN hq).symm) := by
  obtain ⟨K, hK⟩ := exists_isGateProduct_padding (d := d) (r := r)
  refine ⟨K, fun {M N} _ {ℓ} hN hq => ?_⟩
  constructor
  · have he := blockLayerOp_padding (d := d) hN hq false
    simp only [Bool.false_eq_true, ↓reduceIte] at he
    rw [← he]
    exact isUnitaryCircuitOn_blockLayerOp hN fun k => (hK (ℓ k) (hq k)).1
  · have he := blockLayerOp_padding (d := d) hN hq true
    simp only [↓reduceIte] at he
    rw [← he]
    exact isUnitaryCircuitOn_blockLayerOp hN fun k => (hK (ℓ k) (hq k)).2

/-- The original ancilla and register at the two ends of a block. -/
def ends (hq : r + r ≤ q) (t : Fin (r + r)) : Fin q :=
  ⟨if t.val < r then t.val else q - (r + r) + t.val, by split_ifs <;> omega⟩

theorem ends_injective (hq : r + r ≤ q) : Function.Injective (ends hq) := by
  intro t u h
  have := congrArg Fin.val h
  dsimp [ends] at this
  apply Fin.ext
  split_ifs at this <;> omega

section Shift

variable [NeZero d]

/-- The shift on the ends of a block is exactly the controlled subtraction used in the GHZ
protocol, with every central scratch site fixed. -/
theorem ends_shift_mulVec (hq : r + r ≤ q) (v : Cfg d q → ℂ) :
    ManyBody.placeAlong (X := fun _ ↦ Fin d) ⟨ends hq, ends_injective hq⟩
        ((tailShift r).permMatrix ℂ) *ᵥ v = v ∘ blockShift r q := by
  rw [placeAlong_mulVec_eq_comp (ends_injective hq) (fun _ => Matrix.permMatrix_mulVec _)]
  congr 1
  funext x p
  have hdisj : ∀ k k' : Unit, k ≠ k' → Disjoint (Set.range (ends hq)) (Set.range (ends hq)) :=
    fun k k' h => (h (Subsingleton.elim _ _)).elim
  by_cases hp : p.val < r
  · have he : ends hq ⟨p.val, by omega⟩ = p := by ext; simp [ends, hp]
    have he' : ends hq ⟨r + p.val, by omega⟩ =
        (⟨q - r + p.val, by omega⟩ : Fin q) := by
      ext
      simp only [ends]
      split_ifs <;> omega
    conv_lhs => rw [← he, layerCfg_apply (fun _ => ends_injective hq) hdisj (k := ())]
    simp only [tailShift, Equiv.coe_fn_mk, Function.comp_apply, dite_eq_left hp,
      he, he', blockShift]
  · by_cases ht : q - r ≤ p.val
    · have he : ends hq ⟨r + (p.val - (q - r)), by omega⟩ = p := by
        ext; simp only [ends]; split_ifs <;> omega
      rw [← he, layerCfg_apply (fun _ => ends_injective hq) hdisj (k := ())]
      simp only [tailShift, Equiv.coe_fn_mk, Function.comp_apply]
      rw [he]
      simp only [dite_eq_right (show ¬r + (p.val - (q - r)) < r by omega),
        blockShift, dite_eq_right hp]
    · rw [layerCfg_apply_of_forall_ne _ (fun (_ : Unit) t he => ?_), blockShift,
        dite_eq_right hp]
      have h := congrArg Fin.val he
      dsimp [ends] at h
      split_ifs at h <;> omega

end Shift

section Gate

variable [NeZero d] [NeZero N] (hN : ∑ k, ℓ k = N) (hr : 2 ≤ r)
  (hℓ : ∀ k, 3 * r ≤ ℓ k)

include hℓ in
private theorem twice_hops (k : Fin M) :
    2 * ((ℓ k - 2 * r) / 2) + 2 * r + ℓ k % 2 = ℓ k := by
  have := hℓ k
  omega

/-- The end-to-end subtraction, after shifting the first register in odd blocks. -/
noncomputable def gate (k : Fin M) : RegisterGate d N r where
  a := blockSite hN k ⟨ℓ k % 2, by have := hℓ k; have := Nat.mod_lt (ℓ k) (by omega : 0 < 2); omega⟩
  L := (ℓ k - 2 * r) / 2
  le := by
    have hsum : ℓ k ≤ N := by
      rw [← hN]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have := twice_hops hℓ k
    omega
  X := (tailShift r).permMatrix ℂ

private theorem gate_add (k : Fin M) {j : ℕ} (hj : j < 2 * (gate (d := d) hN hr hℓ k).L + 2 * r) :
    (gate (d := d) hN hr hℓ k).a + (j : Fin N) =
      blockSite hN k ⟨ℓ k % 2 + j, by
        have := twice_hops hℓ k
        change j < 2 * ((ℓ k - 2 * r) / 2) + 2 * r at hj
        omega⟩ := by
  have hp := twice_hops hℓ k
  have hlt := blockOffset_add_lt hN k (⟨ℓ k % 2 + j, by
    change j < 2 * ((ℓ k - 2 * r) / 2) + 2 * r at hj
    omega⟩)
  apply Fin.ext
  simp only [gate, blockSite_val, Fin.val_add, Fin.val_natCast]
  rw [Nat.add_mod_mod, Nat.mod_eq_of_lt (by simpa [Nat.add_assoc] using hlt)]
  omega

/-- Every teleportation stretch lies entirely within its block. -/
theorem gate_span_subset (k : Fin M) :
    (gate (d := d) hN hr hℓ k).span ⊆ Finset.univ.image (blockSite hN k) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := (gate (d := d) hN hr hℓ k).mem_span.mp hi
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (gate_add hN hr hℓ k hj).symm⟩

/-- All padded register gates can be teleported in parallel. -/
theorem pairwise_gates :
    (List.ofFn (gate (d := d) hN hr hℓ)).Pairwise fun g g' => Disjoint g.span g'.span := by
  rw [List.pairwise_ofFn]
  intro k k' hkk'
  exact (Finset.disjoint_coe.mp (by simpa using disjoint_range_blockSite hN (ne_of_lt hkk'))).mono
    (gate_span_subset hN hr hℓ k) (gate_span_subset hN hr hℓ k')

/-- The padded register sites are the images of the original two end registers. -/
theorem gate_sites (k : Fin M) (t : Fin (r + r)) :
    (gate (d := d) hN hr hℓ k).sites t =
      paddingAll (r := r) hN (fun j => by have := hℓ j; omega)
        (blockSite hN k (ends (by have := hℓ k; omega) t)) := by
  rw [RegisterGate.sites, gate_add hN hr hℓ k ((gate (d := d) hN hr hℓ k).offset_lt t),
    paddingAll_blockSite]
  apply congrArg (blockSite hN k)
  by_cases ht : t.val < r
  · rw [show ends (by have := hℓ k; omega) t =
        (⟨t.val, by have := hℓ k; omega⟩ : Fin (ℓ k)) by ext; simp [ends, ht],
      padding_first _ (⟨t.val, ht⟩ : Fin r)]
    apply Fin.ext
    simp [RegisterGate.offset, ht]
  · rw [padding_of_ge _ _ (by dsimp [ends]; rw [ite_eq_right ht]; have := hℓ k; omega)]
    apply Fin.ext
    have := twice_hops hℓ k
    simp only [RegisterGate.offset, ite_eq_right ht, ends, gate]
    omega

/-- Every site strictly between the padded registers is an original central scratch site and
is fixed by the padding permutation. -/
theorem gate_interior (k : Fin M) {i : Fin N} (hi : i ∈ (gate (d := d) hN hr hℓ k).interior) :
    (∃ p : Fin (ℓ k), r ≤ p.val ∧ p.val < ℓ k - r ∧ i = blockSite hN k p) ∧
      paddingAll (r := r) hN (fun j => by have := hℓ j; omega) i = i := by
  obtain ⟨j, hj, hj', rfl⟩ := (gate (d := d) hN hr hℓ k).mem_zone.mp hi
  have hp := twice_hops hℓ k
  change j < r + 2 * ((ℓ k - 2 * r) / 2) at hj'
  rw [gate_add hN hr hℓ k (by dsimp [gate]; omega)]
  refine ⟨⟨_, ?_, ?_, rfl⟩, ?_⟩
  · change r ≤ ℓ k % 2 + j
    omega
  · change ℓ k % 2 + j < ℓ k - r
    omega
  rw [paddingAll_blockSite]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one (ℓ k) with he | he
  · simp [padding, he, ← Equiv.Perm.viaEmbeddingHom_apply]
  · apply padding_of_ge
    simp only [he]
    omega

/-- Conjugating the product of the teleported register gates by the two padding layers gives
exactly the original block-shift layer. This is an operator identity on all states. -/
theorem padding_conj_gates :
    ManyBody.sitePermOp (α := Fin d)
        (paddingAll (r := r) hN (fun j => by have := hℓ j; omega)).symm *
        ((List.ofFn (gate (d := d) hN hr hℓ)).map RegisterGate.op).prod *
        ManyBody.sitePermOp (α := Fin d)
          (paddingAll (r := r) hN (fun j => by have := hℓ j; omega)) =
      blockLayerOp hN (fun k => ManyBody.placeAlong (X := fun _ ↦ Fin d)
        ⟨ends (by have := hℓ k; omega), ends_injective _⟩ ((tailShift r).permMatrix ℂ)) := by
  classical
  let π := paddingAll (r := r) hN (fun j => by have := hℓ j; omega)
  have hPQ : ManyBody.sitePermOp (α := Fin d) π * ManyBody.sitePermOp π.symm = 1 := by
    rw [ManyBody.sitePermOp_mul]
    change ManyBody.sitePermOp (π * π⁻¹) = 1
    rw [mul_inv_cancel, ManyBody.sitePermOp_one]
  have hQP : ManyBody.sitePermOp (α := Fin d) π.symm * ManyBody.sitePermOp π = 1 := by
    rw [ManyBody.sitePermOp_mul]
    change ManyBody.sitePermOp (π⁻¹ * π) = 1
    rw [inv_mul_cancel, ManyBody.sitePermOp_one]
  rw [List.mul_prod_mul_of_mul_eq_one hPQ hQP, List.map_map, List.map_ofFn]
  have heq : ∀ k, ManyBody.sitePermOp (α := Fin d) π.symm * (gate (d := d) hN hr hℓ k).op *
        ManyBody.sitePermOp π =
      ManyBody.placeAlong (X := fun _ ↦ Fin d) ⟨blockSite hN k, blockSite_injective hN k⟩
        (ManyBody.placeAlong (X := fun _ ↦ Fin d)
          ⟨ends (by have := hℓ k; omega), ends_injective _⟩ ((tailShift r).permMatrix ℂ)) := by
    intro k
    have hconj := ManyBody.sitePermOp_mul_placeAlong_mul_conjTranspose (α := Fin d)
      (gate (d := d) hN hr hℓ k).sitesEmb π.symm (gate (d := d) hN hr hℓ k).X
    rw [ManyBody.conjTranspose_sitePermOp, Equiv.Perm.inv_def, Equiv.symm_symm] at hconj
    rw [RegisterGate.op, hconj, ManyBody.placeAlong_placeAlong]
    have hw : (gate (d := d) hN hr hℓ k).sitesEmb.trans π.symm.toEmbedding =
        (⟨ends (by have := hℓ k; omega), ends_injective _⟩ : Fin (r + r) ↪ Fin (ℓ k)).trans
          ⟨blockSite hN k, blockSite_injective hN k⟩ := by
      ext t
      simp [RegisterGate.sitesEmb, gate_sites, π]
    rw [hw]
    rfl
  simp_rw [Function.comp_def, heq]
  let f := fun k : Fin M => ManyBody.placeAlong (X := fun _ ↦ Fin d)
    ⟨blockSite hN k, blockSite_injective hN k⟩ (ManyBody.placeAlong (X := fun _ ↦ Fin d)
      ⟨ends (by have := hℓ k; omega), ends_injective _⟩ ((tailShift r).permMatrix ℂ))
  have hl : (List.ofFn (fun k : Fin M => k)).toFinset = Finset.univ := by ext; simp
  have hc : (↑(List.ofFn (fun k : Fin M => k)).toFinset : Set (Fin M)).Pairwise
      (Function.onFun Commute f) := by
    rw [hl]
    exact pairwise_commute_blockSite hN _
  have hprod := Finset.noncommProd_toFinset (List.ofFn (fun k : Fin M => k)) f hc
    (List.nodup_ofFn.mpr Function.injective_id)
  simpa only [hl, List.map_ofFn, Function.comp_def, f, blockLayerOp] using hprod.symm

end Gate

end SparseRegister

end MPSPreparation
