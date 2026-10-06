/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.EmbeddedProduct
import TNLean.MPS.Preparation.Staircase
import TNLean.MPS.Preparation.BinaryMERA

/-!
# Amplitudes of binary trees of isometries

A tool for reading the tree-RG circuit of arXiv:2307.01696, eq. (16), as a product of placed
unitaries: the tree, one layer at a time. The map `binaryTreeMatrix k W V` of a binary tree of
isometries, with the finest layer `W` and the coarser layers `V`, is written as a sum over the
outputs of the coarser layers (`MPSTensor.binaryTreeMatrix_apply_succ`): the amplitude of
`2^{k+2}` leaves, grouped into `2^{k+1}` neighbouring pairs `e`, is
`∑_τ ∏_p W(e_p, τ_p) ⋅ (tree of the coarser layers)(τ)`, with `τ` the outputs of the coarser
layers grouped into pairs in their turn. The amplitudes of a layer of placed matrices are
`QuantumCircuit.list_prod_embedOp_placeCfg`.

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
noncomputable def unpair {j β : ℕ} (e : Fin (2 ^ j) → Fin (blockPhysDim β 2)) :
    Fin (2 ^ (j + 1)) → Fin β :=
  fun u => decodeBlock β 2 (e ⟨u.val / 2, by
    have := u.isLt; have : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j; omega⟩)
    ⟨u.val % 2, Nat.mod_lt _ two_pos⟩

theorem two_mul_add_lt_two_pow {j : ℕ} (p : Fin (2 ^ j)) (i : Fin 2) :
    2 * p.val + i.val < 2 ^ (j + 1) := by
  have := p.isLt; have := i.isLt; rw [pow_succ]; omega

theorem unpair_apply {j β : ℕ} (e : Fin (2 ^ j) → Fin (blockPhysDim β 2)) (p : Fin (2 ^ j))
    (i : Fin 2) : unpair e ⟨2 * p.val + i.val, two_mul_add_lt_two_pow p i⟩ =
      decodeBlock β 2 (e p) i := by
  have h1 : (2 * p.val + i.val) / 2 = p.val := by omega
  have h2 : (2 * p.val + i.val) % 2 = i.val := by omega
  simp only [unpair, h1, h2]

theorem unpair_injective {j β : ℕ} : Function.Injective (unpair (j := j) (β := β)) := by
  intro e e' h
  funext p
  apply (decodeBlockEquiv β 2).injective
  funext i
  have := congrFun h ⟨2 * p.val + i.val, two_mul_add_lt_two_pow p i⟩
  rwa [unpair_apply, unpair_apply] at this

theorem unpair_surjective {j β : ℕ} : Function.Surjective (unpair (j := j) (β := β)) := by
  intro σ
  refine ⟨fun p => (decodeBlockEquiv β 2).symm fun i => σ ⟨2 * p.val + i.val,
    two_mul_add_lt_two_pow p i⟩, ?_⟩
  funext u
  simp only [unpair, decodeBlock_decodeBlockEquiv_symm]
  congr 1
  ext
  simp only
  omega

theorem unpair_bijective {j β : ℕ} : Function.Bijective (unpair (j := j) (β := β)) :=
  ⟨unpair_injective, unpair_surjective⟩

/-! ### Decoding blocked indices -/

theorem decodeBlock_blockIndexOfList (d L : ℕ) (w : List (Fin d)) (h : w.length = L)
    (i : Fin L) : decodeBlock d L (blockIndexOfList d L w h) i = w.get (Fin.cast h.symm i) := by
  unfold blockIndexOfList
  simp [decodeBlock, Kraus.decodeBlock]

theorem decodeBlock_finCongr (d : ℕ) {L₁ L₂ : ℕ} (h : L₁ = L₂) (I : Fin (blockPhysDim d L₁))
    (i : Fin L₂) :
    decodeBlock d L₂ (finCongr (congrArg (blockPhysDim d) h) I) i =
      decodeBlock d L₁ I (Fin.cast h.symm i) := by
  subst h
  rfl

/-- The letters of the pairs of a regrouped block are the pairs of letters of the block. -/
theorem decodeBlock_pairRegroupEquiv (n j : ℕ) (e : Fin (2 ^ (j + 1)) → Fin (blockPhysDim n 2))
    (σ : Fin (2 ^ (j + 2)) → Fin n)
    (hσ : ∀ t i, σ ⟨2 * t.val + i.val, by
      have := t.isLt; have := i.isLt; have : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
      omega⟩ = decodeBlock n 2 (e t) i) :
    decodeBlock (blockPhysDim n 2) (2 ^ (j + 1))
        (pairRegroupEquiv n j ((decodeBlockEquiv n (2 ^ (j + 2))).symm σ)) = e := by
  funext t
  apply (decodeBlockEquiv n 2).injective
  funext u
  rw [decodeBlockEquiv_apply, decodeBlockEquiv_apply]
  simp only [pairRegroupEquiv, Equiv.trans_apply, directIteratedBlockEquiv_apply,
    directToIteratedBlockIndex, decodeBlock_blockIndexOfList, List.get_ofFn, blockWordChunk]
  rw [decodeBlock_finCongr, decodeBlock_decodeBlockEquiv_symm, ← hσ t u]
  · congr 1
  · ring

/-! ### The tree, one layer at a time -/

/-- The amplitude of a binary tree of `j + 1` layers, with the finest layer `W` and the coarser
layers `V 0, V 1, …` from fine to coarse, at the outputs `e` of the `2^j` isometries of its
finest layer: a sum over the outputs `e'` of the coarser layers.

arXiv:2307.01696, eq. (16): the layers `(V⁽¹⁾)^{⊗2^{k}} (V⁽²⁾)^{⊗2^{k-1}} ⋯` of the tree. -/
noncomputable def treeAmp {χ : ℕ} :
    (j : ℕ) → {n : ℕ} → Matrix (Fin (blockPhysDim n 2)) (Fin χ) ℂ →
      (ℕ → Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ) →
      (Fin (2 ^ j) → Fin (blockPhysDim n 2)) → Fin χ → ℂ
  | 0, _, W, _, e, x => W (e 0) x
  | j + 1, _, W, V, e, x => ∑ e' : Fin (2 ^ j) → Fin (blockPhysDim χ 2),
      (∏ p, W (e p) (unpair e' p)) * treeAmp j (V 0) (fun m => V (m + 1)) e' x

/-- **The tree, one layer at a time.** The map of a binary tree of isometries at the leaves
grouped into the pairs `e` is the amplitude `treeAmp`. -/
theorem binaryTreeMatrix_apply_unpair {χ : ℕ} (j : ℕ) {n : ℕ}
    (W : Matrix (Fin (blockPhysDim n 2)) (Fin χ) ℂ)
    (V : ℕ → Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ)
    (e : Fin (2 ^ j) → Fin (blockPhysDim n 2)) (x : Fin χ) :
    binaryTreeMatrix j W (fun l : Fin j => V l)
        ((decodeBlockEquiv n (2 ^ (j + 1))).symm (unpair e)) x = treeAmp j W V e x := by
  induction j generalizing n V with
  | zero =>
    change W _ x = W (e 0) x
    congr 1
    apply (decodeBlockEquiv n (2 ^ (0 + 1))).injective
    rw [Equiv.apply_symm_apply]
    change _ = decodeBlock n 2 (e 0)
    funext u
    have hu : u.val / 2 = 0 := by have := u.isLt; omega
    have hu' : u.val % 2 = u.val := Nat.mod_eq_of_lt u.isLt
    simp only [unpair, hu, hu']
    rfl
  | succ j ih =>
    change ((blockKron (2 ^ (j + 1)) W * binaryTreeMatrix j (V 0) (fun l : Fin j => V (l + 1)))
      (pairRegroupEquiv n j _) x) = _
    rw [Matrix.mul_apply, treeAmp]
    symm
    refine Fintype.sum_bijective (fun e' => (decodeBlockEquiv χ (2 ^ (j + 1))).symm (unpair e'))
      ((decodeBlockEquiv χ (2 ^ (j + 1))).symm.bijective.comp unpair_bijective) _ _
      fun e' => ?_
    rw [ih (V 0) (fun m => V (m + 1)) e']
    congr 1
    symm
    simp only [blockKron]
    rw [decodeBlock_pairRegroupEquiv n j e (unpair e) fun t i => unpair_apply e t i,
      decodeBlock_decodeBlockEquiv_symm]

end MPSTensor

namespace MPSPreparation

end MPSPreparation
