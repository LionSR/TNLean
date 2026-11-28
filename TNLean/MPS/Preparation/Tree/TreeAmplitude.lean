/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.PlacedConfiguration
import TNLean.MPS.Tensor.VaryingBond.Staircase
import TNLean.MPS.Preparation.Tree.BinaryMERA

/-!
# Amplitudes of binary trees of isometries

A tool for reading the tree-RG circuit of arXiv:2307.01696, eq. (16), as a product of placed
unitaries: the tree, one layer at a time. The map `binaryTreeMatrix k W V` of a binary tree of
isometries, with the finest layer `W` and the coarser layers `V`, is written as a sum over the
outputs of the coarser layers (`MPSTensor.binaryTreeMatrix_apply_succ`): the amplitude of
`2^{k+2}` leaves, grouped into `2^{k+1}` neighbouring pairs `e`, is
`∑_τ ∏_p W(e_p, τ_p) ⋅ (tree of the coarser layers)(τ)`, with `τ` the outputs of the coarser
layers grouped into pairs in their turn. The amplitudes of a layer of placed matrices are
`QuantumCircuit.list_prod_placeAlong_placeCfg`.

## Main definitions

* `MPSTensor.pairsEquiv` — a family of letters of the two-site blocked alphabet as a family of
  twice as many letters.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16).
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSTensor

/-! ### Pairs of letters -/

/-- A family of `2^j` letters of the two-site blocked alphabet read as `2^{j+1}` letters: the
letters `2p` and `2p + 1` are the two sites of the letter `p`. -/
noncomputable def unpair {j : ℕ} {β : Type*} (e : Fin (2 ^ j) → Fin 2 → β) :
    Fin (2 ^ (j + 1)) → β :=
  fun u => (e ⟨u.val / 2, by
    have := u.isLt; have : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j; omega⟩)
    ⟨u.val % 2, Nat.mod_lt _ two_pos⟩

theorem two_mul_add_lt_two_pow {j : ℕ} (p : Fin (2 ^ j)) (i : Fin 2) :
    2 * p.val + i.val < 2 ^ (j + 1) := by
  have := p.isLt; have := i.isLt; rw [pow_succ]; omega

theorem unpair_apply {j : ℕ} {β : Type*} (e : Fin (2 ^ j) → Fin 2 → β) (p : Fin (2 ^ j))
    (i : Fin 2) : unpair e ⟨2 * p.val + i.val, two_mul_add_lt_two_pow p i⟩ = e p i := by
  have h1 : (2 * p.val + i.val) / 2 = p.val := by omega
  have h2 : (2 * p.val + i.val) % 2 = i.val := by omega
  simp only [unpair, h1, h2]

theorem unpair_injective {j : ℕ} {β : Type*} :
    Function.Injective (unpair (j := j) (β := β)) := by
  intro e e' h
  funext p i
  have := congrFun h ⟨2 * p.val + i.val, two_mul_add_lt_two_pow p i⟩
  rwa [unpair_apply, unpair_apply] at this

theorem unpair_surjective {j : ℕ} {β : Type*} :
    Function.Surjective (unpair (j := j) (β := β)) := by
  intro σ
  refine ⟨fun p => fun i => σ ⟨2 * p.val + i.val,
    two_mul_add_lt_two_pow p i⟩, ?_⟩
  funext u
  simp only [unpair]
  congr 1
  ext
  simp only
  omega

theorem unpair_bijective {j : ℕ} {β : Type*} :
    Function.Bijective (unpair (j := j) (β := β)) :=
  ⟨unpair_injective, unpair_surjective⟩

/-! ### Regrouped blocks -/

/-- The letters of the pairs of a regrouped block are the pairs of letters of the block. -/
theorem pairRegroupEquiv_eq (α : Type) (j : ℕ) (e : Fin (2 ^ (j + 1)) → Fin 2 → α)
    (σ : Fin (2 ^ (j + 2)) → α)
    (hσ : ∀ t i, σ ⟨2 * t.val + i.val, by
      have := t.isLt; have := i.isLt; have : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      omega⟩ = e t i) :
    pairRegroupEquiv α j σ = e := by
  rw [pairRegroupEquiv, Equiv.trans_apply, Equiv.symm_apply_eq]
  funext x
  obtain ⟨⟨t, u⟩, rfl⟩ := finProdFinEquiv.surjective x
  rw [Kraus.blockConfigEquiv_apply, Equiv.symm_apply_apply, ← hσ t u]
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, finCongr_symm,
    finCongr_apply]
  congr 1
  ext
  simp only [Fin.val_cast, finProdFinEquiv_apply_val]
  ring

/-! ### The tree, one layer at a time -/

/-- The amplitude of a binary tree of `j + 1` layers, with the finest layer `W` and the coarser
layers `V 0, V 1, …` from fine to coarse, at the outputs `e` of the `2^j` isometries of its
finest layer: a sum over the outputs `e'` of the coarser layers.

arXiv:2307.01696, eq. (16): the layers `(V⁽¹⁾)^{⊗2^{k}} (V⁽²⁾)^{⊗2^{k-1}} ⋯` of the tree. -/
noncomputable def treeAmp {χ : ℕ} :
    (j : ℕ) → {α : Type} → Matrix (Fin 2 → α) (Fin χ) ℂ →
      (ℕ → Matrix (Fin 2 → Fin χ) (Fin χ) ℂ) →
      (Fin (2 ^ j) → Fin 2 → α) → Fin χ → ℂ
  | 0, _, W, _, e, x => W (e 0) x
  | j + 1, _, W, V, e, x => ∑ e' : Fin (2 ^ j) → Fin 2 → Fin χ,
      (∏ p, W (e p) (unpair e' p)) * treeAmp j (V 0) (fun m => V (m + 1)) e' x

/-- **The tree, one layer at a time.** The map of a binary tree of isometries at the leaves
grouped into the pairs `e` is the amplitude `treeAmp`. -/
theorem binaryTreeMatrix_apply_unpair {χ : ℕ} (j : ℕ) {α : Type}
    (W : Matrix (Fin 2 → α) (Fin χ) ℂ)
    (V : ℕ → Matrix (Fin 2 → Fin χ) (Fin χ) ℂ)
    (e : Fin (2 ^ j) → Fin 2 → α) (x : Fin χ) :
    binaryTreeMatrix j W (fun l : Fin j => V l) (unpair e) x = treeAmp j W V e x := by
  induction j generalizing α V with
  | zero =>
    change W (unpair e) x = W (e 0) x
    congr 1
    funext u
    have hu : u.val / 2 = 0 := by have := u.isLt; omega
    have hu' : u.val % 2 = u.val := Nat.mod_eq_of_lt u.isLt
    simp only [unpair, hu, hu']
    rfl
  | succ j ih =>
    change ((blockKron (2 ^ (j + 1)) W * binaryTreeMatrix j (V 0) (fun l : Fin j => V (l + 1)))
      (pairRegroupEquiv α j (unpair e)) x) = _
    rw [Matrix.mul_apply, treeAmp]
    symm
    refine Fintype.sum_bijective unpair unpair_bijective _ _ fun e' => ?_
    rw [ih (V 0) (fun m => V (m + 1)) e']
    congr 1
    rw [blockKron_apply, pairRegroupEquiv_eq α j e (unpair e) fun t i => unpair_apply e t i]

end MPSTensor

namespace MPSPreparation

end MPSPreparation
