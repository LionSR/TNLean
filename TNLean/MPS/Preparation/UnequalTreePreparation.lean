/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.UnequalRegisterTreeState

/-!
# The state of blocks of unequal lengths with measurements in depth `O(log q)`

The paragraph "Tree-RG circuit with measurements" of arXiv:2307.01696 applies the tree-RG
circuit of eq. (16) to every block with measurements, every isometry in constant time. The
Supplemental Material, proof of Theorem 1, cuts a chain of any length into blocks "all of the
same size, `q_N`, except for the last one, which may be larger". This file prepares the state
`(⊗ₖ V_k) ⊗ₖ |ω⟩` of eq. (10) for blocks of unequal lengths with measurements: for blocks of
lengths between `2^{h+2} s` and `2^{h+1} c` the depth is at most `C (h + 1)`, with `C` depending
only on `d`, `s` and `c`
(`MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_blockIsometryState`).

## The protocol

Let the blocked tensors of `A` over `m ≥ s` sites be injective, `s ≥ 2`. Every block of `ℓ` sites
is cut into `2^{h+1}` leaves of even widths, as equal as possible
(`MPSPreparation.balancedWidths`); when `ℓ` is odd the last leaf has one more site. A register of
`s` sites carries `ℂ^{D²}`, and a leg of a pair is written on the first `s - 1` sites of a register,
its last site in `|0⟩`. The protocol

1. prepares the pairs `|ω⟩` across the boundaries of the blocks by a local circuit, as in
   eq. (12), in one round without measurements;
2. applies the depths `0, …, h` of the trees of all the blocks with measurement rounds
   (`MPSPreparation.exists_rounds_blockLayerOp_treeLevelsOp`);
3. applies the leaves of all the blocks by a local circuit, in one round without measurements.

When `ℓ` is odd, the right leg of the pair of a block ends on the last site of the block, which
carries `|0⟩` and lies outside the last register of the root, so the registers of every node are
an even number of sites apart. After every sequence of outcomes the output is a scalar multiple of
`(⊗ₖ V_k) ⊗ₖ |ω⟩` (`MPSPreparation.treeBlockOp_apply`).

## Main definitions

* `MPSPreparation.balancedWidths` — the widths of the leaves of a block.

## Main results

* `MPSPreparation.isTreeLayout_balancedWidths`.
* `MPSPreparation.exists_isPreparedWithMeasurementRoundsInDepth_blockIsometryState`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eqs. (10)–(12) and (16), the paragraph
  "Tree-RG circuit with measurements", and Supplemental Material, proof of Theorem 1.
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

open TeleportHop

/-! ### Leaves of a block of any length -/

/-- The widths of `m` leaves cutting a block of `L` sites: even, as equal as possible, and of
total `2 ⌊L/2⌋`. -/
def balancedWidths (m L : ℕ) (i : ℕ) : ℕ := 2 * (L / 2 / m) + if i < L / 2 % m then 2 else 0

theorem leafOffset_balancedWidths (m L : ℕ) :
    ∀ t, leafOffset (balancedWidths m L) t = 2 * (L / 2 / m) * t + 2 * min t (L / 2 % m)
  | 0 => by simp [leafOffset]
  | t + 1 => by
    rw [leafOffset_succ, leafOffset_balancedWidths m L t, balancedWidths]
    split_ifs with ht
    · rw [min_eq_left (by omega), min_eq_left (by omega)]; ring
    · rw [min_eq_right (by omega), min_eq_right (by omega)]; ring

theorem leafOffset_balancedWidths_self {m : ℕ} (hm : 0 < m) (L : ℕ) :
    leafOffset (balancedWidths m L) m = 2 * (L / 2) := by
  rw [leafOffset_balancedWidths, min_eq_right (Nat.mod_lt _ hm).le]
  have := Nat.div_add_mod (L / 2) m
  linarith

/-- **The leaves of a block of any length.** A block of `L ≥ 2^{h+2} s` sites carries a tree
layout with `2^{h+1}` leaves of even widths at least `2s`. -/
theorem isTreeLayout_balancedWidths {h s L : ℕ} (hL : 2 ^ (h + 2) * s ≤ L) :
    IsTreeLayout h s L (balancedWidths (2 ^ (h + 1)) L) where
  two_mul_le i _ := by
    have : s ≤ L / 2 / 2 ^ (h + 1) := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.le_div_iff_mul_le two_pos]
      calc s * 2 ^ (h + 1) * 2 = 2 ^ (h + 2) * s := by ring
        _ ≤ L := hL
    unfold balancedWidths
    split_ifs <;> omega
  even i _ := by
    unfold balancedWidths
    split_ifs
    · exact ⟨L / 2 / 2 ^ (h + 1) + 1, by ring⟩
    · exact ⟨L / 2 / 2 ^ (h + 1), by ring⟩
  le := by rw [leafOffset_balancedWidths_self (Nat.two_pow_pos _)]; omega

theorem le_leafOffset_balancedWidths_add_one (h L : ℕ) :
    L ≤ leafOffset (balancedWidths (2 ^ (h + 1)) L) (2 ^ (h + 1)) + 1 := by
  rw [leafOffset_balancedWidths_self (Nat.two_pow_pos _)]; omega

/-- The leaves of a block of at most `2^{h+1} c` sites have at most `c + 3` sites. -/
theorem leafLen_balancedWidths_le {h L c : ℕ} (hL : L ≤ 2 ^ (h + 1) * c) (p : ℕ) :
    leafLen h L (balancedWidths (2 ^ (h + 1)) L) p ≤ c + 3 := by
  have hq : 2 * (L / 2 / 2 ^ (h + 1)) ≤ c := by
    have h1 := Nat.div_mul_le_self (L / 2) (2 ^ (h + 1))
    have h2 : L / 2 ≤ 2 ^ h * c := by
      have : L ≤ 2 * (2 ^ h * c) := by rw [pow_succ] at hL; linarith
      omega
    have h3 : 2 * (L / 2 / 2 ^ (h + 1)) * 2 ^ h ≤ c * 2 ^ h := by
      calc 2 * (L / 2 / 2 ^ (h + 1)) * 2 ^ h = L / 2 / 2 ^ (h + 1) * 2 ^ (h + 1) := by ring
        _ ≤ L / 2 := h1
        _ ≤ 2 ^ h * c := h2
        _ = c * 2 ^ h := by ring
    exact Nat.le_of_mul_le_mul_right h3 (Nat.two_pow_pos h)
  have hw : balancedWidths (2 ^ (h + 1)) L p ≤ c + 2 := by
    unfold balancedWidths; split_ifs <;> omega
  rw [leafLen_eq]
  split_ifs with hlast
  · have h1 := leafOffset_balancedWidths_self (Nat.two_pow_pos (h + 1)) L
    have h3 := leafOffset_succ (w := balancedWidths (2 ^ (h + 1)) L) p
    rw [hlast] at h3
    omega
  · exact hw.trans (by omega)

/-! ### The input of a block on the registers of its root -/

section Root

variable {d s D h n : ℕ} [NeZero d] [NeZero s] {w : ℕ → ℕ}

/-- The input of a block, `|l, 0 ⋯ 0, r⟩`, lies on the two registers of the root of its tree when
the legs end with a site in `|0⟩` and the leaves leave at most one site. -/
theorem blockInputCfg_eq_placeCfg (hT : IsTreeLayout h s n w)
    (hn : n ≤ leafOffset w (2 ^ (h + 1)) + 1) {dig : Fin D → Cfg d s}
    (hdig : ∀ l, dig l ⟨s - 1, by have := NeZero.pos s; omega⟩ = 0) (l r : Fin D) :
    blockInputCfg (NeZero.pos d) n dig l r =
      placeCfg (fun p : Fin (2 ^ 0) => nodeWindow hT 0 p)
        fun _ => blockInputCfg (NeZero.pos d) n dig l r ∘ nodeWindow hT 0 0 := by
  have hW := nodeWindow_injective₂ hT (Nat.zero_le (h + 1))
  have hstart : nodeStart h w 0 0 = 0 := by simp [nodeStart, leafOffset]
  have hstop : nodeStop h w 0 0 = leafOffset w (2 ^ (h + 1)) := by
    simp [nodeStop, nodeLeaves]
  have hroot := nodeStart_add_le hT (Nat.zero_le _) (Nat.two_pow_pos 0)
  rw [hstart, hstop] at hroot
  have hle := hT.le
  refine (eq_placeCfg (W := fun p : Fin (2 ^ 0) => nodeWindow hT 0 p) hW
    (z := blockInputCfg (NeZero.pos d) n dig l r) fun y hy => ?_).trans ?_
  · -- `y` is off the two registers of the root
    have hy' : ∀ t : Fin (s + s), (nodeWindow hT 0 0 t).val ≠ y.val := fun t ht =>
      hy 0 t (Fin.ext ht)
    have hval : ∀ t : Fin (s + s), (nodeWindow hT 0 0 t).val =
        if t.val < s then t.val else leafOffset w (2 ^ (h + 1)) - (s + s) + t.val := fun t => by
      rw [nodeWindow_val hT (Nat.zero_le _) (Nat.two_pow_pos 0)]
      simp only [nodeOffset, hstart, hstop, zero_add]
    have hys : s ≤ y.val := by
      by_contra hc
      exact hy' ⟨y.val, by omega⟩ (by rw [hval]; simp only; split_ifs <;> omega)
    have hyn : y.val + s < leafOffset w (2 ^ (h + 1)) ∨ leafOffset w (2 ^ (h + 1)) ≤ y.val := by
      by_contra hc
      push Not at hc
      exact hy' ⟨y.val - (leafOffset w (2 ^ (h + 1)) - (s + s)), by omega⟩
        (by rw [hval]; simp only; split_ifs <;> omega)
    simp only [blockInputCfg, show ¬ y.val < s by omega, ↓reduceDIte]
    split_ifs with hy2
    · have hyl : y.val = n - 1 := by have := y.isLt; omega
      have hidx : y.val - (n - s) = s - 1 := by omega
      convert hdig r using 2
      exact Fin.ext hidx
    · rfl
  · congr 1
    funext p
    rw [show p = 0 from Fin.ext (by have := p.isLt; simp at this; omega)]
    congr 2

end Root

/-! ### The preparation -/

/-- `D² ≤ d^s` with `s ≥ 2` gives `D ≤ d^{s-1}`: a leg fits in `s - 1` sites. -/
theorem le_pow_sub_one_of_mul_self_le {d D s : ℕ} (hs : 2 ≤ s) (hd : 0 < d)
    (h : D * D ≤ d ^ s) : D ≤ d ^ (s - 1) := by
  by_contra hc
  push Not at hc
  have h1 : d ≤ d ^ (s - 1) := Nat.le_self_pow (by omega) d
  have h2 : d ^ s = d * d ^ (s - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h3 : (d ^ (s - 1) + 1) * (d ^ (s - 1) + 1) ≤ D * D := Nat.mul_le_mul hc hc
  nlinarith

/-- **The state of blocks of unequal lengths with measurements in depth `O(h)`**
(arXiv:2307.01696, paragraph "Tree-RG circuit with measurements", with eqs. (10)–(12) and (16),
for the blocks of unequal lengths of the Supplemental Material, proof of Theorem 1). For every
`d ≥ 1`, `s ≥ 2` and `c` there is `C`, depending only on `d`, `s` and `c`, with the following
property. Let `A` be a tensor whose blocked tensors over `m ≥ s` sites are injective, and `ω` a
unit vector on the pair space. For every `h` and every cutting of a ring of `N` sites into
`M ≥ 1` blocks of lengths `2^{h+2} s ≤ ℓ_k ≤ 2^{h+1} c`, the state `(⊗ₖ V_k) ⊗ₖ |ω⟩` is prepared
with measurement rounds in depth at most `C (h + 1)`: the pairs and the leaves of the trees by
local circuits, and the depths `0, …, h` of the trees one at a time with measurements. No outcome
is post-selected. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_blockIsometryState (d s c : ℕ) [NeZero d]
    (hs : 2 ≤ s) :
    ∃ C : ℕ, ∀ {D : ℕ} (A : MPSTensor d D), (∀ m, s ≤ m → Kraus.IsInjective (blockTensor A m)) →
      ∀ (ω : Fin D × Fin D → ℂ), ∑ p, star (ω p) * ω p = 1 →
      ∀ (h : ℕ) {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ b, ℓ b = N),
        (∀ b, 2 ^ (h + 2) * s ≤ ℓ b) → (∀ b, ℓ b ≤ 2 ^ (h + 1) * c) →
          IsPreparedWithMeasurementRoundsInDepth (C * (h + 1))
            fun x => blockIsometryState A ω hN x := by
  classical
  have hd : 0 < d := NeZero.pos d
  have : NeZero s := ⟨by omega⟩
  obtain ⟨K, hK⟩ := exists_isPairProduct (n := s + s) hd (by omega)
  -- the unitaries of the leaves, on at most `c + 3` sites
  have hleaf : ∀ n : Fin (c + 4), ∃ K' : ℕ, 2 ≤ n.val →
      ∀ X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ), IsPairProduct d n K' X := fun n => by
    by_cases hn : 2 ≤ n.val
    · obtain ⟨K', hK'⟩ := exists_isPairProduct hd hn
      exact ⟨K', fun _ => hK'⟩
    · exact ⟨0, fun h' => absurd h' hn⟩
  choose Kl hKl using hleaf
  refine ⟨2 * K + 4 * s + ∑ n, Kl n + 6, fun {D} A hinj ω hω h M _ ℓ N _ hN hℓ₁ hℓ₂ => ?_⟩
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact absurd hω (by simp)
  -- the legs on the first `s - 1` sites of a register, and `ℂ^{D²}` on a register
  have hDD := mul_self_le_pow_of_isInjective_blockTensor (hinj s le_rfl)
  obtain ⟨dig₀⟩ : Nonempty (Fin D ↪ Cfg d (s - 1)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using le_pow_sub_one_of_mul_self_le hs hd hDD)
  obtain ⟨enc⟩ : Nonempty (Fin (D * D) ↪ Cfg d s) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hDD)
  let dig : Fin D → Cfg d s := fun l i => if hi : i.val < s - 1 then dig₀ l ⟨i.val, hi⟩ else 0
  have hdig : Function.Injective dig := fun l l' he => dig₀.injective (funext fun i => by
    have := congrFun he ⟨i.val, by omega⟩
    simpa [dig, show i.val < s - 1 from i.isLt] using this)
  have hdig0 : ∀ l, dig l ⟨s - 1, by omega⟩ = 0 := fun l => by simp [dig]
  -- the trees of the blocks
  have hT : ∀ b, IsTreeLayout h s (ℓ b) (balancedWidths (2 ^ (h + 1)) (ℓ b)) := fun b =>
    isTreeLayout_balancedWidths (hℓ₁ b)
  have hr : ∀ b, s + s ≤ ℓ b := fun b => by
    have := hℓ₁ b
    have : 4 ≤ 2 ^ (h + 2) := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ (h + 2) := Nat.pow_le_pow_right two_pos (by omega)
    nlinarith
  set ι₀ : ∀ b, Fin (D * D) → Cfg d (s + s) := fun b x =>
    blockInputCfg hd (ℓ b) dig (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 ∘
      nodeWindow (hT b) 0 0 with hι₀def
  have hroot : ∀ b l r, blockInputCfg hd (ℓ b) dig l r =
      placeCfg (fun p : Fin (2 ^ 0) => nodeWindow (hT b) 0 p)
        fun _ => ι₀ b (finProdFinEquiv (l, r)) := fun b l r => by
    rw [blockInputCfg_eq_placeCfg (hT b) (le_leafOffset_balancedWidths_add_one h (ℓ b)) hdig0]
    simp only [hι₀def, Equiv.symm_apply_apply]
  have hι₀ : ∀ b, Function.Injective (ι₀ b) := fun b x x' he => by
    obtain ⟨⟨l, r⟩, rfl⟩ := finProdFinEquiv.surjective x
    obtain ⟨⟨l', r'⟩, rfl⟩ := finProdFinEquiv.surjective x'
    have := blockInputCfg_injective hd (hr b) hdig (l := l) (r := r) (l' := l') (r' := r')
      (by rw [hroot b l r, hroot b l' r', he])
    rw [this.1, this.2]
  set X : Fin M → ℕ → ℕ → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ := fun b =>
    treeNodeGate (h := h) (n := ℓ b) (w := balancedWidths (2 ^ (h + 1)) (ℓ b)) A (ι₀ b) enc
  set U := fun b => treeLeafGate (hT b) A (ι₀ b) enc
  -- the pairs
  obtain ⟨W, hWu, hW⟩ := exists_pairUnitary hd hdig ω hω
  obtain ⟨Ls, hLs, -, hLsW⟩ := isCircuitOn_pairLayerOp hN hr fun _ => hK W hWu
  -- the depths `0, …, h` of the trees
  obtain ⟨Rs, hRs, hRsE⟩ := exists_rounds_blockLayerOp_treeLevelsOp (hN := hN) (hT := hT)
    (X := X) (K := K)
    fun b j p => hK _ (treeNodeGate_mem_unitary A (ι₀ b) enc j p)
  -- the leaves
  obtain ⟨Ll, hLl, -, hLlU⟩ := isCircuitOn_blockLayerOp_treeLeafOp (hN := hN) (hT := hT) U
    (K := ∑ n, Kl n) fun b p => by
      have h1 := two_mul_le_leafLen (hT b) p.isLt
      have h2 := leafLen_balancedWidths_le (hℓ₂ b) p.val
      exact (hKl ⟨_, (by omega : leafLen h (ℓ b) _ p < c + 4)⟩ (by simp only; omega) _
        (treeLeafGate_mem_unitary (hT b) A (ι₀ b) enc p)).mono
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  set v₀ : Fin N → Fin d → ℂ := fun _ => Pi.single ⟨0, hd⟩ 1
  have hv₀ : productVector v₀ ≠ 0 := fun h0 => by
    have := congrFun h0 fun _ => ⟨0, hd⟩
    rw [productVector_single_zero_apply hd] at this
    simp at this
  have h₀ : MeasurementRound.IsRoundsImplementationOn [round Ls [] valid_nil] {productVector v₀}
      (pairLayerOp hN hr fun _ => W) := by
    have := (isImplementationOn_round (d := d) Ls (valid_nil (N := N))).isRoundsImplementationOn
    rw [chainPerm_nil, Matrix.one_mul, ← hLsW] at this
    exact this.mono fun v _ => fun _ _ _ h => h.elim
  have hleafR : MeasurementRound.IsRoundsImplementationOn [round Ll [] valid_nil] Set.univ
      (blockLayerOp hN fun b => treeLeafOp (hT b) (U b)) := by
    have := (isImplementationOn_round (d := d) Ll (valid_nil (N := N))).isRoundsImplementationOn
    rw [chainPerm_nil, Matrix.one_mul, ← hLlU] at this
    exact this.mono fun v _ => fun _ _ _ h => h.elim
  have hall := (h₀.append hRsE fun v hv => by
    rw [Set.mem_singleton_iff] at hv
    subst hv
    refine (isZeroOn_pairLayerOp_mulVec_productVector hN hr _).mono ?_
    rintro x ⟨b, y, hy1, hy2, rfl⟩
    exact ⟨b, y, hy1, by have := (hT b).le; simp only at hy2; omega, rfl⟩).append hleafR
      fun _ _ => trivial
  have hprep := hall.isPreparedWithMeasurementRoundsInDepth hv₀ rfl
  have hdepth : ((([round Ls [] valid_nil] ++ Rs) ++ [round Ll [] valid_nil]).map
      MeasurementRound.depth).sum ≤ (2 * K + 4 * s + ∑ n, Kl n + 6) * (h + 1) := by
    simp only [List.map_append, List.sum_append, hRs, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, depth_round, hLs, hLl]
    nlinarith
  have hψ : (fun x => blockIsometryState A ω hN x) =
      ((blockLayerOp hN fun b => treeLeafOp (hT b) (U b)) *
        ((blockLayerOp hN fun b => treeLevelsOp (hT b) (X b) 0 (h + 1)) *
          pairLayerOp hN hr fun _ => W)) *ᵥ productVector v₀ := by
    funext x
    rw [← Matrix.mul_assoc, ← blockLayerOp_mul]
    exact blockIsometryState_eq_mulVec hd hN hr hdig A ω (U := fun b => treeBlockOp (hT b) A (ι₀ b)
      enc) (fun b l r τ => by
        rw [hroot, treeBlockOp_apply (hT b) hinj (hι₀ b) enc.injective]
        rfl) hW x
  rw [hψ]
  exact hprep.mono hdepth

end MPSPreparation
