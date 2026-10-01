/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.EmbeddedProduct
import TNLean.MPS.Preparation.Staircase
import TNLean.MPS.Preparation.TreeMERA

/-!
# Amplitudes of binary trees of isometries and of layers of placed matrices

Two tools for reading the tree-RG circuit of arXiv:2307.01696, eq. (16), as a product of placed
unitaries.

* **The tree, one layer at a time.** The map `binaryTreeMatrix k W V` of a binary tree of
  isometries, with the finest layer `W` and the coarser layers `V`, is written as a sum over the
  outputs of the coarser layers (`MPSTensor.binaryTreeMatrix_apply_succ`): the amplitude of
  `2^{k+2}` leaves, grouped into `2^{k+1}` neighbouring pairs `e`, is
  `∑_τ ∏_p W(e_p, τ_p) ⋅ (tree of the coarser layers)(τ)`, with `τ` the outputs of the coarser
  layers grouped into pairs in their turn.
* **A layer of placed matrices.** If matrices `Y_p` on pairwise disjoint windows `W_p` act on
  the inputs `ι_p(c)` as matrices `V_p` with injective outputs `o_p(e)`, then the product of the
  placed matrices maps the configuration carrying `ι_p(c_p)` on the window `p` and `0` elsewhere to
  `∑_e ∏_p V_p(e_p, c_p) |o_p(e_p) on the windows, 0 elsewhere⟩`
  (`MPSPreparation.list_prod_embedOp_placeCfg`).

## Main definitions

* `MPSTensor.pairsEquiv` — a family of letters of the two-site blocked alphabet as a family of
  twice as many letters.
* `MPSPreparation.placeCfg` — the configuration carrying given contents on given windows and `0`
  elsewhere.

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

/-! ### Configurations placed on windows -/

section Place

variable {d m n : ℕ} [NeZero d] {ι : Type*}

/-- The configuration carrying `c p` on the window `W p` and `0` at the other sites. -/
noncomputable def placeCfg (W : ι → Fin m → Fin n) (c : ι → Cfg d m) : Cfg d n :=
  Function.extend (fun pt : ι × Fin m => W pt.1 pt.2) (fun pt => c pt.1 pt.2) fun _ => 0

variable {W : ι → Fin m → Fin n} (hW : Function.Injective fun pt : ι × Fin m => W pt.1 pt.2)
include hW

theorem placeCfg_apply (c : ι → Cfg d m) (p : ι) (t : Fin m) : placeCfg W c (W p t) = c p t :=
  hW.extend_apply _ _ (p, t)

theorem placeCfg_comp (c : ι → Cfg d m) (p : ι) : placeCfg W c ∘ W p = c p :=
  funext (placeCfg_apply hW c p)

omit hW in
theorem placeCfg_apply_of_notMem (c : ι → Cfg d m) {y : Fin n} (hy : ∀ p t, W p t ≠ y) :
    placeCfg W c y = 0 :=
  Function.extend_apply' _ _ _ fun ⟨pt, h⟩ => hy pt.1 pt.2 h

/-- A configuration with `0` off the windows is the placed configuration of its contents. -/
theorem eq_placeCfg {z : Cfg d n} (hz : ∀ y, (∀ p t, W p t ≠ y) → z y = 0) :
    z = placeCfg W fun p => z ∘ W p := by
  funext y
  by_cases hy : ∃ p t, W p t = y
  · obtain ⟨p, t, rfl⟩ := hy
    rw [placeCfg_apply hW]; rfl
  · simp only [not_exists] at hy
    rw [placeCfg_apply_of_notMem _ hy, hz y hy]

theorem placeCfg_injective : Function.Injective (placeCfg (d := d) W) := by
  intro c c' h
  funext p
  rw [← placeCfg_comp hW c p, ← placeCfg_comp hW c' p, h]

theorem injective_window (p : ι) : Function.Injective (W p) := fun t t' h =>
  (Prod.ext_iff.mp (hW (a₁ := (p, t)) (a₂ := (p, t')) h)).2

theorem disjoint_range_window {p p' : ι} (hpp : p ≠ p') :
    Disjoint (Set.range (W p)) (Set.range (W p')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, rfl⟩ ⟨t', ht⟩
  exact hpp (Prod.ext_iff.mp (hW (a₁ := (p', t')) (a₂ := (p, t)) ht)).1.symm

end Place

/-! ### A layer of placed matrices -/

/-- **A layer of placed matrices on placed inputs.** Let `Y p` be matrices on the pairwise
disjoint windows `W p` acting on the inputs `ι' p c` as the matrices `V p` with injective outputs
`o p b`: `Y p (z, ι' p c) = V p (b, c)` if `z = o p b` and `0` otherwise. Then the product of
the placed `Y p` applied to the configuration carrying `ι' p (c p)` on the windows and `0`
elsewhere has the amplitude `∏_p V p (e p) (c p)` at the configuration carrying `o p (e p)` on
the windows and `0` elsewhere, and `0` at every other configuration. -/
theorem list_prod_embedOp_placeCfg {d m n P : ℕ} [NeZero d] {W : Fin P → Fin m → Fin n}
    (hW : Function.Injective fun pt : Fin P × Fin m => W pt.1 pt.2)
    (Y : Fin P → Matrix (Cfg d m) (Cfg d m) ℂ) {α β : Type*}
    (ι' : Fin P → α → Cfg d m) (o : Fin P → β → Cfg d m) (ho : ∀ p, Function.Injective (o p))
    (V : Fin P → β → α → ℂ)
    (hY : ∀ p c z, Y p z (ι' p c) = Function.extend (o p) (fun b => V p b c) 0 z)
    (c : Fin P → α) (y : Cfg d n) :
    ((List.finRange P).map fun p => embedOp (W p) (Y p)).prod y
        (placeCfg W fun p => ι' p (c p)) =
      Function.extend (fun e : Fin P → β => placeCfg W fun p => o p (e p))
        (fun e => ∏ p, V p (e p) (c p)) 0 y := by
  classical
  have hWp := injective_window hW
  have hcomm : ((List.finRange P).toFinset : Set (Fin P)).Pairwise
      (Function.onFun Commute fun p => embedOp (W p) (Y p)) := fun p _ p' _ h =>
    commute_embedOp_of_disjoint (hWp p) (hWp p') (disjoint_range_window hW h) _ _
  rw [← Finset.noncommProd_toFinset (List.finRange P) _ hcomm (List.nodup_finRange P),
    noncommProd_embedOp_apply W hWp Y _ (fun p _ p' _ h => disjoint_range_window hW h)]
  simp only [List.toFinset_finRange, Finset.mem_univ, true_implies, placeCfg_comp hW, hY]
  have hinj : Function.Injective fun e : Fin P → β => placeCfg (d := d) W fun p => o p (e p) :=
    fun e e' h => funext fun p => ho p (congrFun (placeCfg_injective hW h) p)
  by_cases hy : ∃ e : Fin P → β, (placeCfg W fun p => o p (e p)) = y
  · obtain ⟨e, rfl⟩ := hy
    have hag : ∀ i, (∀ p j, W p j ≠ i) →
        (placeCfg W fun p => o p (e p)) i = (placeCfg W fun p => ι' p (c p)) i := fun i hi => by
      rw [placeCfg_apply_of_notMem _ hi, placeCfg_apply_of_notMem _ hi]
    rw [hinj.extend_apply, ite_eq_left hag]
    exact Finset.prod_congr rfl fun p _ => by
      rw [placeCfg_comp hW, (ho p).extend_apply]
  · rw [Function.extend_apply' _ _ _ hy, Pi.zero_apply]
    split_ifs with hag
    · by_contra hne
      apply hy
      have hall : ∀ p, ∃ b, o p b = y ∘ W p := by
        intro p
        by_contra hp
        simp only [not_exists] at hp
        exact hne (Finset.prod_eq_zero (Finset.mem_univ p) (by
          rw [Function.extend_apply' _ _ _ fun ⟨b, hb⟩ => hp b hb, Pi.zero_apply]))
      choose e he using hall
      refine ⟨e, ?_⟩
      rw [eq_placeCfg hW (z := y) fun i hi => by
        rw [hag i hi, placeCfg_apply_of_notMem _ hi]]
      simp only [he]
    · rfl

/-- **Columns along a product.** If the column of `M` at `x₀` is `f` placed by an injective `R`,
and `G` maps every `R a` to the column `g a` placed by an injective `R'`, then the column of
`G M` at `x₀` is `b ↦ ∑_a g a b f a` placed by `R'`. -/
theorem _root_.Matrix.mul_apply_extend {H α β : Type*} [Fintype H] [Fintype α]
    (G M : Matrix H H ℂ) (x₀ : H) {R : α → H} (hR : Function.Injective R) (f : α → ℂ)
    (hM : ∀ y, M y x₀ = Function.extend R f 0 y) {R' : β → H} (hR' : Function.Injective R')
    (g : α → β → ℂ) (hG : ∀ a y, G y (R a) = Function.extend R' (g a) 0 y) (y : H) :
    (G * M) y x₀ = Function.extend R' (fun b => ∑ a, g a b * f a) 0 y := by
  classical
  rw [Matrix.mul_apply]
  simp_rw [hM]
  rw [sum_extend_zero hR f (fun z v => G y z * v) fun _ => mul_zero _]
  simp_rw [hG]
  by_cases hy : ∃ b, R' b = y
  · obtain ⟨b, rfl⟩ := hy
    simp only [hR'.extend_apply]
  · simp only [Function.extend_apply' _ _ _ hy, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

end MPSPreparation
