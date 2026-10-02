/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.PolarMerge
import TNLean.MPS.Preparation.RegisterTreeState
import TNLean.MPS.Preparation.UnequalRegisterTree

/-!
# The tree of a block of any length implements the isometry of the block

The tree-RG circuit of arXiv:2307.01696, eq. (16), writes the isometry `V` of `B_q = V P` as a
binary tree of isometries. On a block of `n` sites cut into leaves of unequal widths
(`MPSPreparation.IsTreeLayout`), the node `p` of depth `j` covers `ℓ_{j,p}` sites
(`MPSPreparation.nodeLen`), and its isometry is the isometry
`W : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` joining its two halves, `V_{ℓ₁+ℓ₂} = (V_{ℓ₁} ⊗ V_{ℓ₂}) W`
(`MPSPreparation.cfgPolarIso_split`); a leaf of `ℓ` sites carries `V_ℓ` itself. The halves of a
node may have different lengths, so the isometries differ from node to node.

With registers carrying `ℂ^{D²}` through an injective `enc`, every isometry extends to a unitary
on the two registers of its node (`MPSPreparation.treeNodeGate`) or on the sites of its leaf
(`MPSPreparation.treeLeafGate`). The tree of these unitaries on the block satisfies

  `⟨τ| T |ι₀ x⟩ = ⟨τ| V_n |x⟩`

for every configuration `τ` of the block, where the input `ι₀ x` is placed on the two registers
of the root (`MPSPreparation.treeBlockOp_apply`).

The proof follows the tree from the leaves: after the leaves and the depths `h, …, j`, the
amplitude of the configuration `τ` on the inputs `x p` of the nodes of depth `j` is the product of
the isometries `V_{ℓ_{j,p}}` of these nodes (`MPSPreparation.treeLevelsOp_apply_nodeCfg`).

## Main definitions

* `MPSPreparation.treeNodeGate`, `MPSPreparation.treeLeafGate`, `MPSPreparation.treeBlockOp`.

## Main results

* `MPSPreparation.treeBlockOp_apply`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eqs. (11) and (16), and paragraph "Tree-RG
  circuit with measurements".
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

section State

variable {d s D h n : ℕ} {w : ℕ → ℕ}

private theorem append_inj {u v u' v' : Cfg d s} (he : Fin.append u v = Fin.append u' v') :
    u = u' ∧ v = v' := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · have := congrFun he (Fin.castAdd s i)
    rwa [Fin.append_left, Fin.append_left] at this
  · have := congrFun he (Fin.natAdd s i)
    rwa [Fin.append_right, Fin.append_right] at this

private theorem append_apply_lt (u v : Cfg d s) (t : Fin (s + s)) (ht : t.val < s) :
    Fin.append u v t = u ⟨t.val, ht⟩ :=
  Fin.append_left u v ⟨t.val, ht⟩

private theorem append_apply_ge (u v : Cfg d s) (t : Fin (s + s)) (ht : s ≤ t.val) :
    Fin.append u v t = v ⟨t.val - s, by omega⟩ := by
  calc Fin.append u v t = Fin.append u v (Fin.natAdd s ⟨t.val - s, by omega⟩) := by
        congr 1; ext; simp only [Fin.val_natAdd]; omega
    _ = _ := Fin.append_right u v _

/-! ### Inputs and configurations -/

variable [NeZero d] [NeZero s]

/-- The input of the unitary of the node `p` of depth `j`: at the root the input `ι₀ x`, below it
the register `enc x` in the first register of an even node and in the last register of an odd
one, the other register in `|0⟩`.

arXiv:2307.01696, eqs. (11) and (16): every isometry of eq. (16) takes one register `ℂ^{D²}`. -/
def treeInput (ι₀ : Fin (D * D) → Cfg d (s + s)) (enc : Fin (D * D) → Cfg d s) (j p : ℕ)
    (x : Fin (D * D)) : Cfg d (s + s) :=
  if j = 0 then ι₀ x else if p % 2 = 0 then Fin.append (enc x) 0 else Fin.append 0 (enc x)

omit [NeZero s] in
theorem treeInput_injective {ι₀ : Fin (D * D) → Cfg d (s + s)} {enc : Fin (D * D) → Cfg d s}
    (hι₀ : Function.Injective ι₀) (henc : Function.Injective enc) (j p : ℕ) :
    Function.Injective (treeInput ι₀ enc j p) := by
  intro x x' he
  unfold treeInput at he
  split_ifs at he
  · exact hι₀ he
  · exact henc (append_inj he).1
  · exact henc (append_inj he).2

variable (hT : IsTreeLayout h s n w)

/-- The configuration of a block carrying the inputs `x p` of the nodes of depth `j` on their
registers and `|0⟩` elsewhere. -/
noncomputable def nodeCfg (ι₀ : Fin (D * D) → Cfg d (s + s)) (enc : Fin (D * D) → Cfg d s)
    (j : ℕ) (x : Fin (2 ^ j) → Fin (D * D)) : Cfg d n :=
  placeCfg (fun p : Fin (2 ^ j) => nodeWindow hT j p) fun p => treeInput ι₀ enc j p (x p)

/-- The configuration of the sites of the node `p` of depth `j`. -/
def segCfg (j p : ℕ) (τ : Cfg d n) : Cfg d (nodeLen h n w j p) :=
  fun i => τ ⟨(nodeStart h w j p + i.val) % n, Nat.mod_lt _ hT.pos⟩

/-- The two registers of the leaf `p`, as sites of the leaf. -/
def leafRegWindow (p : Fin (2 ^ (h + 1))) (t : Fin (s + s)) : Fin (leafLen h n w p) :=
  ⟨(if t.val < s then t.val else w p - (s + s) + t.val) % leafLen h n w p,
    Nat.mod_lt _ (by have := two_mul_le_leafLen hT p.isLt; have := NeZero.pos s; omega)⟩

theorem leafRegWindow_val (p : Fin (2 ^ (h + 1))) (t : Fin (s + s)) :
    (leafRegWindow hT p t).val = if t.val < s then t.val else w p - (s + s) + t.val := by
  refine Nat.mod_eq_of_lt ?_
  have h1 := two_mul_le_leafLen hT p.isLt
  have h2 := hT.two_mul_le p p.isLt
  have h3 : w p ≤ leafLen h n w p := by
    have := leafOffset_add_leafLen hT p.isLt
    have := leafOffset_mono (w := w) (show p.val + 1 ≤ 2 ^ (h + 1) from p.isLt)
    have := hT.le
    rw [leafLen_eq, leafOffset_succ] at *
    split_ifs <;> omega
  have := t.isLt
  split_ifs <;> omega

theorem leafRegWindow_injective₂ (p : Fin (2 ^ (h + 1))) :
    Function.Injective fun pt : Fin 1 × Fin (s + s) => leafRegWindow hT p pt.2 := by
  rintro ⟨u, t⟩ ⟨u', t'⟩ he
  simp only at he
  have he' := congrArg Fin.val he
  simp only [leafRegWindow_val] at he'
  have := hT.two_mul_le p p.isLt
  refine Prod.ext (Subsingleton.elim _ _) (Fin.ext ?_)
  change t.val = t'.val
  have := t.isLt; have := t'.isLt
  split_ifs at he' <;> omega

/-- The input of the leaf `p`: the input of depth `h + 1` on its two registers. -/
noncomputable def leafInput (ι₀ : Fin (D * D) → Cfg d (s + s)) (enc : Fin (D * D) → Cfg d s)
    (p : Fin (2 ^ (h + 1))) (x : Fin (D * D)) : Cfg d (leafLen h n w p) :=
  placeCfg (fun _ : Fin 1 => leafRegWindow hT p) fun _ => treeInput ι₀ enc (h + 1) p x

theorem leafInput_injective {ι₀ : Fin (D * D) → Cfg d (s + s)} {enc : Fin (D * D) → Cfg d s}
    (hι₀ : Function.Injective ι₀) (henc : Function.Injective enc) (p : Fin (2 ^ (h + 1))) :
    Function.Injective (leafInput hT ι₀ enc p) := fun _ _ he =>
  treeInput_injective hι₀ henc (h + 1) p
    (congrFun (placeCfg_injective (leafRegWindow_injective₂ hT p) he) 0)

/-! ### The gates -/

variable (A : MPSTensor d D) (ι₀ : Fin (D * D) → Cfg d (s + s)) (enc : Fin (D * D) → Cfg d s)

/-- The unitary of the node `p` of depth `j`: the extension of the isometry
`W : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` joining its two halves from its input to its two registers.

arXiv:2307.01696, eq. (16) and paragraph "Tree-RG circuit with measurements". -/
noncomputable def treeNodeGate (j p : ℕ) : Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ :=
  extUnitary (mergeIso A (nodeLen h n w (j + 1) (2 * p)) (nodeLen h n w (j + 1) (2 * p + 1)))
    (treeInput ι₀ enc j p) (coarseOutput enc)

/-- The unitary of the leaf `p`: the extension of the isometry `V_ℓ` of its `ℓ` sites from its
input to all the configurations of the leaf.

arXiv:2307.01696, eq. (16), the finest isometries of the tree. -/
noncomputable def treeLeafGate (p : Fin (2 ^ (h + 1))) :
    Matrix (Cfg d (leafLen h n w p)) (Cfg d (leafLen h n w p)) ℂ :=
  extUnitary (cfgPolarIso A (leafLen h n w p)) (leafInput hT ι₀ enc p) id

/-- The tree of a block: the depths `0, …, h`, the root applied first, then the leaves.

arXiv:2307.01696, eq. (16). -/
noncomputable def treeBlockOp : Matrix (Cfg d n) (Cfg d n) ℂ :=
  treeLeafOp hT (treeLeafGate hT A ι₀ enc) *
    treeLevelsOp hT (treeNodeGate (h := h) (n := n) (w := w) A ι₀ enc) 0 (h + 1)

omit [NeZero s] in
theorem treeNodeGate_mem_unitary (j p : ℕ) :
    treeNodeGate (h := h) (n := n) (w := w) A ι₀ enc j p ∈
      unitary (Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) :=
  extUnitary_mem_unitary _ _ _

theorem treeLeafGate_mem_unitary (p : Fin (2 ^ (h + 1))) :
    treeLeafGate hT A ι₀ enc p ∈
      unitary (Matrix (Cfg d (leafLen h n w p)) (Cfg d (leafLen h n w p)) ℂ) :=
  extUnitary_mem_unitary _ _ _

/-! ### Lengths of the nodes -/

omit [NeZero d] [NeZero s] in
theorem nodeLen_two_mul_add (hT : IsTreeLayout h s n w) {j p : ℕ} (hj : j ≤ h)
    (hp : p < 2 ^ j) :
    nodeLen h n w (j + 1) (2 * p) + nodeLen h n w (j + 1) (2 * p + 1) = nodeLen h n w j p := by
  have hp1 : 2 * p < 2 ^ (j + 1) := by rw [pow_succ]; omega
  have hp2 : 2 * p + 1 < 2 ^ (j + 1) := by rw [pow_succ]; omega
  have a1 := nodeStart_add_le hT (by omega : j + 1 ≤ h + 1) hp1
  have a2 := nodeStart_add_le hT (by omega : j + 1 ≤ h + 1) hp2
  have a3 := nodeStop_le_n hT (by omega : j + 1 ≤ h + 1) hp2
  have e1 := nodeStart_two_mul (w := w) hj p
  have e2 := nodeStop_two_mul_add_one (w := w) hj p
  have e3 := nodeStop_two_mul (h := h) (w := w) j p
  have hlast : (2 * p + 1 + 1 = 2 ^ (j + 1)) ↔ (p + 1 = 2 ^ j) := by rw [pow_succ]; omega
  simp only [nodeLen, show ¬ (2 * p + 1 = 2 ^ (j + 1)) by rw [pow_succ]; omega, ↓reduceIte]
  by_cases hl : p + 1 = 2 ^ j
  · simp only [hlast.mpr hl, hl, ↓reduceIte]; omega
  · simp only [show ¬ (2 * p + 1 + 1 = 2 ^ (j + 1)) from fun h' => hl (hlast.mp h'), hl,
      ↓reduceIte]
    omega

omit [NeZero d] [NeZero s] in
theorem two_mul_le_nodeLen (hT : IsTreeLayout h s n w) {j p : ℕ} (hj : j ≤ h + 1)
    (hp : p < 2 ^ j) : s + s ≤ nodeLen h n w j p := by
  have a1 := nodeStart_add_le hT hj hp
  have a2 := nodeStop_le_n hT hj hp
  unfold nodeLen
  split_ifs <;> omega

/-! ### The configurations of consecutive depths -/

/-- The registers of the nodes of depth `j` carrying the outputs `e` of their unitaries are the
inputs of the nodes of depth `j + 1`: the output registers of a node are the input registers of
its two halves. -/
theorem placeCfg_coarseOutput_eq_nodeCfg {j : ℕ} (hj : j ≤ h)
    (e : Fin (2 ^ j) → Fin (blockPhysDim (D * D) 2)) :
    placeCfg (fun p : Fin (2 ^ j) => nodeWindow hT j p) (fun p => coarseOutput enc (e p)) =
      nodeCfg hT ι₀ enc (j + 1) (unpair e) := by
  have hW := nodeWindow_injective₂ hT (by omega : j ≤ h + 1)
  have hW' := nodeWindow_injective₂ hT (by omega : j + 1 ≤ h + 1)
  funext y
  -- the value at a register of depth `j + 1`
  have key : ∀ (p' : Fin (2 ^ (j + 1))) (t : Fin (s + s)),
      placeCfg (fun p : Fin (2 ^ j) => nodeWindow hT j p) (fun p => coarseOutput enc (e p))
        (nodeWindow hT (j + 1) p' t) = treeInput ι₀ enc (j + 1) p' (unpair e p') t := by
    intro p' t
    obtain ⟨q, hqv⟩ : ∃ q : Fin (2 ^ j), q.val = p'.val / 2 := ⟨⟨p'.val / 2, by
      have := p'.isLt; have : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j; omega⟩, rfl⟩
    have hq := q.isLt
    have hun : ∀ i : Fin 2, p'.val = 2 * q.val + i.val → unpair e p' = decodeBlock _ 2 (e q) i :=
      fun i hi => by
        rw [show p' = ⟨2 * q.val + i.val, two_mul_add_lt_two_pow q i⟩ from Fin.ext hi,
          unpair_apply]
    have hst := nodeStart_add_le hT (by omega : j ≤ h + 1) hq
    have hp1 : 2 * q.val < 2 ^ (j + 1) := by rw [pow_succ]; omega
    have hp2 : 2 * q.val + 1 < 2 ^ (j + 1) := by rw [pow_succ]; omega
    have c1 := nodeStart_add_le hT (by omega : j + 1 ≤ h + 1) hp1
    have c2 := nodeStart_add_le hT (by omega : j + 1 ≤ h + 1) hp2
    have e1 := nodeStart_two_mul (w := w) hj q.val
    have e2 := nodeStop_two_mul_add_one (w := w) hj q.val
    have e3 := nodeStop_two_mul (h := h) (w := w) j q.val
    -- the registers of depth `j + 1` that are not registers of depth `j` lie strictly inside the
    -- node `q` of depth `j`
    have hinner : ∀ (m : Fin (2 ^ j)) (t' : Fin (s + s)),
        nodeStart h w j q + s ≤ (nodeWindow hT (j + 1) p' t).val →
        (nodeWindow hT (j + 1) p' t).val + s < nodeStop h w j q →
        nodeWindow hT j m t' ≠ nodeWindow hT (j + 1) p' t := by
      intro m t' h1 h2 he
      have := congrArg Fin.val he
      rw [nodeWindow_val hT (by omega) m.isLt] at this
      rcases nodeOffset_notMem_interior hT (by omega : j ≤ h + 1) m.isLt hq t' with h' | h' <;>
        omega
    have hv := nodeWindow_val hT (by omega : j + 1 ≤ h + 1) p'.isLt t
    have := t.isLt
    rcases Nat.mod_two_eq_zero_or_one p'.val with hpar | hpar
    · have hp' : p'.val = 2 * q.val := by omega
      rw [hun 0 (by simp [hp'])]
      simp only [treeInput, show j + 1 ≠ 0 by omega, hpar, ↓reduceIte]
      by_cases ht : t.val < s
      · have hwin : nodeWindow hT (j + 1) p' t = nodeWindow hT j q t := Fin.ext (by
          rw [hv, nodeWindow_val hT (by omega) hq]
          simp only [nodeOffset, ht, ↓reduceIte, hp', e1])
        rw [hwin, placeCfg_apply hW, coarseOutput, append_apply_lt _ _ _ ht,
          append_apply_lt _ _ _ ht]
      · rw [placeCfg_apply_of_notMem _ fun m t' => hinner m t' (by
            rw [hv]; simp only [nodeOffset, ht, ↓reduceIte, hp']; omega) (by
            rw [hv]; simp only [nodeOffset, ht, ↓reduceIte, hp']; omega),
          append_apply_ge _ _ _ (by omega)]
        rfl
    · have hp' : p'.val = 2 * q.val + 1 := by omega
      rw [hun 1 (by simp [hp'])]
      simp only [treeInput, show j + 1 ≠ 0 by omega, hpar, one_ne_zero, ↓reduceIte]
      by_cases ht : t.val < s
      · rw [placeCfg_apply_of_notMem _ fun m t' => hinner m t' (by
            rw [hv]; simp only [nodeOffset, ht, ↓reduceIte, hp']; omega) (by
            rw [hv]; simp only [nodeOffset, ht, ↓reduceIte, hp']; omega),
          append_apply_lt _ _ _ ht]
        rfl
      · have hwin : nodeWindow hT (j + 1) p' t = nodeWindow hT j q t := Fin.ext (by
          rw [hv, nodeWindow_val hT (by omega) hq]
          simp only [nodeOffset, ht, ↓reduceIte, hp', e2])
        rw [hwin, placeCfg_apply hW, coarseOutput, append_apply_ge _ _ _ (by omega),
          append_apply_ge _ _ _ (by omega)]
  by_cases hy : ∃ (p' : Fin (2 ^ (j + 1))) (t : Fin (s + s)), nodeWindow hT (j + 1) p' t = y
  · obtain ⟨p', t, rfl⟩ := hy
    rw [key, nodeCfg, placeCfg_apply hW']
  · simp only [not_exists] at hy
    rw [nodeCfg, placeCfg_apply_of_notMem _ hy]
    refine placeCfg_apply_of_notMem _ fun p t he => ?_
    obtain ⟨m, hm, hme⟩ := exists_nodeOffset_eq (h := h) (w := w) (Nat.le_succ j)
      (by omega : j + 1 ≤ h + 1) p.isLt t
    refine hy ⟨m, hm⟩ t (he ▸ Fin.ext ?_)
    rw [nodeWindow_val hT (by omega) hm, nodeWindow_val hT (by omega) p.isLt, hme]

/-- The configuration of depth `h + 1` read on the sites of the leaf `p` is the input of the
leaf. -/
theorem nodeCfg_comp_leafWindow (x : Fin (2 ^ (h + 1)) → Fin (D * D)) (p : Fin (2 ^ (h + 1))) :
    nodeCfg hT ι₀ enc (h + 1) x ∘ leafWindow hT p = leafInput hT ι₀ enc p (x p) := by
  have hW := nodeWindow_injective₂ hT (le_refl (h + 1))
  have hL := leafRegWindow_injective₂ hT p
  have hleaf : ∀ t : Fin (s + s), leafWindow hT p (leafRegWindow hT p t) =
      nodeWindow hT (h + 1) p t := fun t => Fin.ext (by
    rw [leafWindow_val hT p.isLt, leafRegWindow_val, nodeWindow_val hT le_rfl p.isLt]
    simp only [nodeOffset, nodeStart, nodeStop, nodeLeaves, Nat.sub_self, pow_zero, mul_one,
      leafOffset_succ]
    have := hT.two_mul_le p p.isLt
    split_ifs <;> omega)
  funext i
  by_cases hi : ∃ t, leafRegWindow hT p t = i
  · obtain ⟨t, rfl⟩ := hi
    rw [Function.comp_apply, hleaf, nodeCfg, placeCfg_apply hW, leafInput,
      placeCfg_apply hL (fun _ => treeInput ι₀ enc (h + 1) p (x p)) 0 t]
  · simp only [not_exists] at hi
    rw [leafInput, placeCfg_apply_of_notMem _ fun _ t => hi t, Function.comp_apply, nodeCfg]
    refine placeCfg_apply_of_notMem _ fun p' t he => ?_
    have he' := congrArg Fin.val he
    rw [nodeWindow_val hT le_rfl p'.isLt, leafWindow_val hT p.isLt] at he'
    simp only [nodeOffset, nodeStart, nodeStop, nodeLeaves, Nat.sub_self, pow_zero, mul_one,
      leafOffset_succ] at he'
    have hw' := hT.two_mul_le p' p'.isLt
    have hi' := i.isLt
    have := t.isLt
    by_cases hpp : p' = p
    · subst hpp
      refine hi t (Fin.ext ?_)
      rw [leafRegWindow_val]
      split_ifs at he' ⊢ <;> omega
    · have hlen := leafLen_eq (h := h) (n := n) (w := w) p.val
      rcases Nat.lt_or_gt_of_ne (fun h' => hpp (Fin.ext h')) with hlt | hlt
      · have := leafOffset_mono (w := w) (show p'.val + 1 ≤ p.val by omega)
        rw [leafOffset_succ] at this
        split_ifs at he' <;> omega
      · have := leafOffset_mono (w := w) (show p.val + 1 ≤ p'.val by omega)
        rw [leafOffset_succ] at this
        have hlp : leafLen h n w p = w p := by rw [hlen]; split_ifs <;> omega
        split_ifs at he' <;> omega

/-! ### The amplitudes, from the leaves -/

variable {A ι₀ enc}

private theorem unpair_two_mul {j β : ℕ} (e : Fin (2 ^ j) → Fin (blockPhysDim β 2))
    (p : Fin (2 ^ j)) (hp : 2 * p.val < 2 ^ (j + 1)) :
    unpair e ⟨2 * p.val, hp⟩ = decodeBlock β 2 (e p) 0 :=
  unpair_apply e p 0

private theorem unpair_two_mul_add_one {j β : ℕ} (e : Fin (2 ^ j) → Fin (blockPhysDim β 2))
    (p : Fin (2 ^ j)) (hp : 2 * p.val + 1 < 2 ^ (j + 1)) :
    unpair e ⟨2 * p.val + 1, hp⟩ = decodeBlock β 2 (e p) 1 :=
  unpair_apply e p 1

private theorem prod_fin_two_pow_succ {j : ℕ} (f : Fin (2 ^ (j + 1)) → ℂ) :
    ∏ p', f p' = ∏ p : Fin (2 ^ j),
      f ⟨2 * p.val, by have := p.isLt; rw [pow_succ]; omega⟩ *
        f ⟨2 * p.val + 1, by have := p.isLt; rw [pow_succ]; omega⟩ := by
  let e : Fin (2 ^ j) × Fin 2 ≃ Fin (2 ^ (j + 1)) :=
    finProdFinEquiv.trans (finCongr (pow_succ 2 j).symm)
  rw [← e.prod_comp, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Fin.prod_univ_two]
  congr 1 <;> congr 1 <;> ext <;> simp [e, finProdFinEquiv, Nat.add_comm]

/-- The leaves applied to the inputs of depth `h + 1` give the product of the isometries of the
leaves. -/
theorem treeLeafOp_apply_nodeCfg (hinj : ∀ m, s ≤ m → Kraus.IsInjective (blockTensor A m))
    (hι₀ : Function.Injective ι₀) (henc : Function.Injective enc)
    (x : Fin (2 ^ (h + 1)) → Fin (D * D)) (τ : Cfg d n) :
    treeLeafOp hT (treeLeafGate hT A ι₀ enc) τ (nodeCfg hT ι₀ enc (h + 1) x) =
      ∏ p : Fin (2 ^ (h + 1)), cfgPolarIso A (leafLen h n w p) (τ ∘ leafWindow hT p) (x p) := by
  classical
  have hcomm : ((List.finRange (2 ^ (h + 1))).toFinset : Set (Fin (2 ^ (h + 1)))).Pairwise
      (Function.onFun Commute fun p : Fin (2 ^ (h + 1)) =>
        embedOp (leafWindow hT p) (treeLeafGate hT A ι₀ enc p)) := fun p _ p' _ hne =>
    commute_embedOp_of_disjoint (leafWindow_injective hT p.isLt) (leafWindow_injective hT p'.isLt)
      (disjoint_range_leafWindow hT p.isLt p'.isLt fun h' => hne (Fin.ext h')) _ _
  rw [treeLeafOp, ← Finset.noncommProd_toFinset (List.finRange _) _ hcomm
    (List.nodup_finRange _), noncommProd_embedOp_apply (fun p : Fin (2 ^ (h + 1)) =>
      leafWindow hT p) (fun p => leafWindow_injective hT p.isLt) _ _
      (fun p _ p' _ hne => disjoint_range_leafWindow hT p.isLt p'.isLt fun h' => hne (Fin.ext h'))]
  have hcond : ∀ i : Fin n, (∀ k ∈ (List.finRange (2 ^ (h + 1))).toFinset,
      ∀ j : Fin (leafLen h n w k), leafWindow hT k j ≠ i) → τ i = nodeCfg hT ι₀ enc (h + 1) x i :=
    fun i hi => absurd hi (by
      obtain ⟨p, hp, i', hi'⟩ := exists_leafWindow_eq hT i
      simp only [List.toFinset_finRange, Finset.mem_univ, true_implies, not_forall, not_not]
      exact ⟨⟨p, hp⟩, i', hi'⟩)
  rw [ite_eq_left hcond]
  simp only [List.toFinset_finRange]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [nodeCfg_comp_leafWindow, treeLeafGate,
    extUnitary_apply (isIsometry_cfgPolarIso A (hinj _ (by
      have := two_mul_le_leafLen hT p.isLt; omega))) (leafInput_injective hT hι₀ henc p)
      Function.injective_id]
  exact Function.injective_id.extend_apply _ _ _

omit [NeZero d] [NeZero s] in
private theorem cfgPolarIso_congr {L L' : ℕ} (hL : L = L') (τ : Cfg d L) (τ' : Cfg d L')
    (hτ : ∀ i : Fin L, τ i = τ' (Fin.cast hL i)) (x : Fin (D * D)) :
    cfgPolarIso A L τ x = cfgPolarIso A L' τ' x := by
  subst hL
  congr 1
  funext i
  exact hτ i

/-- **The tree from the leaves.** After the leaves and the depths `h, …, j`, the amplitude of
the configuration `τ` on the inputs `x p` of the nodes of depth `j` is the product of the
isometries `V_{ℓ_{j,p}}` of the nodes.

arXiv:2307.01696, eq. (16), with `V_{ℓ₁+ℓ₂} = (V_{ℓ₁} ⊗ V_{ℓ₂}) W` at every node. -/
theorem treeLevelsOp_apply_nodeCfg (hinj : ∀ m, s ≤ m → Kraus.IsInjective (blockTensor A m))
    (hι₀ : Function.Injective ι₀) (henc : Function.Injective enc) :
    ∀ k j, j + k = h + 1 → ∀ (x : Fin (2 ^ j) → Fin (D * D)) (τ : Cfg d n),
      (treeLeafOp hT (treeLeafGate hT A ι₀ enc) *
          treeLevelsOp hT (treeNodeGate (h := h) (n := n) (w := w) A ι₀ enc) j k) τ
        (nodeCfg hT ι₀ enc j x) =
      ∏ p : Fin (2 ^ j), cfgPolarIso A (nodeLen h n w j p) (segCfg hT j p τ) (x p)
  | 0, j, hj, x, τ => by
    obtain rfl : j = h + 1 := by omega
    rw [treeLevelsOp, Matrix.mul_one, treeLeafOp_apply_nodeCfg hT hinj hι₀ henc]
    refine Finset.prod_congr rfl fun p _ => cfgPolarIso_congr rfl _ _ (fun i => ?_) _
    simp only [Function.comp_apply, segCfg, Fin.cast_eq_self]
    congr 1
    refine Fin.ext ?_
    rw [leafWindow_val hT p.isLt]
    simp only [nodeStart, nodeLeaves, Nat.sub_self, pow_zero, mul_one]
    exact (Nat.mod_eq_of_lt (by
      have := leafOffset_add_leafLen hT p.isLt; have := i.isLt; omega)).symm
  | k + 1, j, hj, x, τ => by
    have hjh : j ≤ h := by omega
    have ih := treeLevelsOp_apply_nodeCfg hinj hι₀ henc k (j + 1) (by omega)
    rw [treeLevelsOp_succ', ← Matrix.mul_assoc, Matrix.mul_apply]
    -- the unitaries of depth `j`
    have hlayer : ∀ c : Cfg d n, treeLevelOp hT (treeNodeGate A ι₀ enc) j c
        (nodeCfg hT ι₀ enc j x) =
        Function.extend (fun e : Fin (2 ^ j) → Fin (blockPhysDim (D * D) 2) =>
          placeCfg (fun p : Fin (2 ^ j) => nodeWindow hT j p) fun p => coarseOutput enc (e p))
          (fun e => ∏ p : Fin (2 ^ j), mergeIso A (nodeLen h n w (j + 1) (2 * p))
            (nodeLen h n w (j + 1) (2 * p + 1)) (e p) (x p)) 0 c := fun c =>
      list_prod_embedOp_placeCfg (nodeWindow_injective₂ hT (by omega)) _
        (fun p => treeInput ι₀ enc j p) (fun _ => coarseOutput enc)
        (fun _ => coarseOutput_injective henc) _ (fun p c z => by
          refine extUnitary_apply (isIsometry_mergeIso A (hinj _ ?_))
            (treeInput_injective hι₀ henc j p) (coarseOutput_injective henc) c z
          rw [nodeLen_two_mul_add hT hjh p.isLt]
          have := two_mul_le_nodeLen hT (by omega : j ≤ h + 1) p.isLt
          omega) x c
    simp_rw [hlayer]
    have hinjo : Function.Injective fun e : Fin (2 ^ j) → Fin (blockPhysDim (D * D) 2) =>
        placeCfg (d := d) (fun p : Fin (2 ^ j) => nodeWindow hT j p)
          fun p => coarseOutput enc (e p) := fun e e' he =>
      funext fun p => coarseOutput_injective henc
        (congrFun (placeCfg_injective (nodeWindow_injective₂ hT (by omega)) he) p)
    rw [sum_extend_zero hinjo _ (fun c v => (treeLeafOp hT (treeLeafGate hT A ι₀ enc) *
      treeLevelsOp hT (treeNodeGate A ι₀ enc) (j + 1) k) τ c * v) fun _ => mul_zero _]
    simp_rw [placeCfg_coarseOutput_eq_nodeCfg hT ι₀ enc hjh, ih]
    -- regroup the nodes of depth `j + 1` along their parents
    simp_rw [prod_fin_two_pow_succ, ← Finset.prod_mul_distrib, unpair_two_mul,
      unpair_two_mul_add_one]
    rw [← Fintype.prod_sum (fun (p : Fin (2 ^ j)) (b : Fin (blockPhysDim (D * D) 2)) =>
      cfgPolarIso A (nodeLen h n w (j + 1) (2 * p)) (segCfg hT (j + 1) (2 * p) τ)
          (decodeBlock (D * D) 2 b 0) *
        cfgPolarIso A (nodeLen h n w (j + 1) (2 * p + 1)) (segCfg hT (j + 1) (2 * p + 1) τ)
          (decodeBlock (D * D) 2 b 1) *
        mergeIso A (nodeLen h n w (j + 1) (2 * p)) (nodeLen h n w (j + 1) (2 * p + 1)) b (x p))]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hp1 : 2 * p.val < 2 ^ (j + 1) := by have := p.isLt; rw [pow_succ]; omega
    have hp2 : 2 * p.val + 1 < 2 ^ (j + 1) := by have := p.isLt; rw [pow_succ]; omega
    have hn₁ := two_mul_le_nodeLen hT (by omega : j + 1 ≤ h + 1) hp1
    have hn₂ := two_mul_le_nodeLen hT (by omega : j + 1 ≤ h + 1) hp2
    rw [cfgPolarIso_split A (nodeLen_two_mul_add hT hjh p.isLt) (hinj _ (by omega))
      (hinj _ (by omega))]
    refine Finset.sum_congr rfl fun e _ => ?_
    have e1 := nodeStart_two_mul (w := w) hjh p.val
    have e3 := nodeStop_two_mul (h := h) (w := w) j p.val
    have c1 := nodeStart_add_le hT (by omega : j + 1 ≤ h + 1) hp1
    have hn1 : nodeLen h n w (j + 1) (2 * p) =
        nodeStart h w (j + 1) (2 * p + 1) - nodeStart h w j p := by
      simp only [nodeLen, show ¬ (2 * p.val + 1 = 2 ^ (j + 1)) by rw [pow_succ]; omega,
        ↓reduceIte, e1, e3]
    refine congrArg₂ _ (congrArg₂ _ (congrArg (fun z => cfgPolarIso A _ z _) (funext fun i => ?_))
      (congrArg (fun z => cfgPolarIso A _ z _) (funext fun i => ?_))) rfl
    · simp only [segCfg]
      congr 1
      exact Fin.ext (by simp only [e1])
    · simp only [segCfg]
      congr 1
      refine Fin.ext ?_
      simp only
      rw [hn1]
      congr 1
      omega

/-- **The tree of a block of any length implements its isometry** (arXiv:2307.01696, eqs. (11)
and (16)). Let the blocked tensors of `A` over `m ≥ s` sites be injective, let `enc` place
`ℂ^{D²}` on a register injectively, and let `ι₀` place the input injectively on the two registers
of the root. On a block of `n` sites cut into leaves by a tree layout, the tree of the unitaries
`treeNodeGate` and `treeLeafGate` satisfies `⟨τ| T |ι₀ x⟩ = ⟨τ| V_n |x⟩` for every configuration
`τ` of the block, with `B_n = V_n P_n` the polar decomposition of `A` blocked over `n` sites. -/
theorem treeBlockOp_apply (hinj : ∀ m, s ≤ m → Kraus.IsInjective (blockTensor A m))
    (hι₀ : Function.Injective ι₀) (henc : Function.Injective enc) (x : Fin (D * D))
    (τ : Cfg d n) :
    treeBlockOp hT A ι₀ enc τ (placeCfg (fun p : Fin (2 ^ 0) => nodeWindow hT 0 p) fun _ => ι₀ x) =
      cfgPolarIso A n τ x := by
  have h0 := treeLevelsOp_apply_nodeCfg hT hinj hι₀ henc (h + 1) 0 (by omega) (fun _ => x) τ
  have hcfg : nodeCfg hT ι₀ enc 0 (fun _ => x) =
      placeCfg (fun p : Fin (2 ^ 0) => nodeWindow hT 0 p) fun _ => ι₀ x := by
    simp only [nodeCfg, treeInput, ↓reduceIte]
  rw [treeBlockOp, ← hcfg, h0, Finset.prod_eq_single (0 : Fin (2 ^ 0))
    (fun b _ hb => absurd (Fin.ext (by have := b.isLt; simp at this; omega)) hb) (by simp)]
  have hlen : nodeLen h n w 0 (0 : Fin (2 ^ 0)) = n := by
    simp [nodeLen, nodeStart, leafOffset]
  refine cfgPolarIso_congr hlen _ _ (fun i => ?_) x
  simp only [segCfg]
  congr 1
  refine Fin.ext ?_
  simp only [Fin.val_cast]
  have hi : i.val < n := by have := i.isLt; omega
  simp [nodeStart, leafOffset, Nat.mod_eq_of_lt hi]

end State

end MPSPreparation
