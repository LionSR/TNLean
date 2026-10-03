/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RegisterTree
import TNLean.MPS.Preparation.TreeAmplitude

/-!
# The tree of registers implements the isometry of a block

The tree-RG circuit of arXiv:2307.01696, eq. (16), writes the isometry `V` of the blocked tensor
`B_q = V P` of a block of `q = s 2^{k+1}` sites as a binary tree of isometries. Group the sites
into `2^{k+1}` registers of `s` sites, put `B = A` blocked over `s` sites, and assume that the
two-site blocked tensor of `B` is injective. Then the isometries of the tree are
`V⁽¹⁾ : ℂ^{D²} → ℂ^{d^s} ⊗ ℂ^{d^s}` and `V⁽ʲ⁾ : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}`
(`MPSTensor.treeLayers`). With registers carrying `ℂ^{D²}` through an injective `enc` and the
legs `ℂ^D` of the input pair through an injective `dig`, every isometry of the tree extends to a
unitary on its two registers (`MPSPreparation.regTreeGate`), and the tree of these unitaries on
the block (`MPSPreparation.regTreeOp`) satisfies

  `⟨σ| T |dig l, 0 ⋯ 0, dig r⟩ = ⟨σ| V |l, r⟩`

for every configuration `σ` of the block (`MPSPreparation.regTreeOp_apply_blockInputCfg`). So
`T` is a unitary implementing `V` on the inputs of eq. (11), as the block unitaries of the
preparation must.

The proof follows the tree from the root: after the depths `0, …, j` the registers of the
`2^{j+1}` sub-blocks of depth `j + 1` carry the outputs of the isometries of the depths
`0, …, j`, with the amplitude of the tree of the corresponding coarse layers
(`MPSTensor.treeAmp`); the finest depth writes the configuration of the block.

## Main definitions

* `MPSPreparation.extUnitary` — a unitary extending an isometry from placed inputs to placed
  outputs.
* `MPSPreparation.regTreeGate` — the unitaries of the tree-RG circuit on the registers.

## Main results

* `MPSPreparation.regTreeOp_apply_blockInputCfg`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eqs. (11) and (16).
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

/-! ### Unitaries extending isometries -/

section Extend

variable {H α β : Type*} [Fintype H] [DecidableEq H] [DecidableEq α] [Fintype β]

/-- An isometry `V`, read from the inputs `ι c` to the outputs `o b` of a finite-dimensional
space, extends to a unitary. -/
theorem exists_unitary_apply_eq_extend {V : Matrix β α ℂ} (hV : V.IsIsometry) {ι : α → H}
    (hι : Function.Injective ι) {o : β → H} (ho : Function.Injective o) :
    ∃ U ∈ unitary (Matrix H H ℂ), ∀ c z, U z (ι c) = Function.extend o (fun b => V b c) 0 z := by
  classical
  let V' : Matrix H α ℂ := Matrix.of fun z c => Function.extend o (fun b => V b c) 0 z
  have hV' : V'.IsIsometry := by
    ext c c'
    rw [Matrix.mul_apply]
    simp only [conjTranspose_apply, V', of_apply]
    rw [sum_extend_zero ho (fun b => V b c')
      (fun z v => star (Function.extend o (fun b => V b c) 0 z) * v) fun _ => mul_zero _]
    simp only [ho.extend_apply]
    have := congrFun (congrFun hV c) c'
    rwa [Matrix.mul_apply] at this
  obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV' ⟨ι, hι⟩
  exact ⟨U, hU, fun c z => hUV z c⟩

/-- A unitary extending the isometry `V` from the inputs `ι c` to the outputs `o b` (the identity
if `V` is not an isometry or `ι`, `o` are not injective). -/
noncomputable def extUnitary (V : Matrix β α ℂ) (ι : α → H) (o : β → H) : Matrix H H ℂ := by
  classical
  exact if h : V.IsIsometry ∧ Function.Injective ι ∧ Function.Injective o then
    (exists_unitary_apply_eq_extend h.1 h.2.1 h.2.2).choose else 1

theorem extUnitary_mem_unitary (V : Matrix β α ℂ) (ι : α → H) (o : β → H) :
    extUnitary V ι o ∈ unitary (Matrix H H ℂ) := by
  classical
  unfold extUnitary
  split_ifs with h
  · exact (exists_unitary_apply_eq_extend h.1 h.2.1 h.2.2).choose_spec.1
  · exact Submonoid.one_mem _

theorem extUnitary_apply {V : Matrix β α ℂ} (hV : V.IsIsometry) {ι : α → H}
    (hι : Function.Injective ι) {o : β → H} (ho : Function.Injective o) (c : α) (z : H) :
    extUnitary V ι o z (ι c) = Function.extend o (fun b => V b c) 0 z := by
  classical
  unfold extUnitary
  rw [dite_eq_left_of_eq_true (eq_true ⟨hV, hι, ho⟩)]
  exact (exists_unitary_apply_eq_extend hV hι ho).choose_spec.2 c z

end Extend

/-! ### Two registers side by side -/

section Append

variable {d s : ℕ}

private theorem append_apply_of_lt (u v : Cfg d s) (t : Fin (s + s)) (h : t.val < s) :
    Fin.append u v t = u ⟨t.val, h⟩ :=
  Fin.append_left u v ⟨t.val, h⟩

private theorem append_apply_of_le (u v : Cfg d s) (t : Fin (s + s)) (h : s ≤ t.val) :
    Fin.append u v t = v ⟨t.val - s, by omega⟩ := by
  calc Fin.append u v t = Fin.append u v (Fin.natAdd s ⟨t.val - s, by omega⟩) := by
        congr 1; ext; simp only [Fin.val_natAdd]; omega
    _ = _ := Fin.append_right u v _

private theorem append_injective {u v u' v' : Cfg d s} (h : Fin.append u v = Fin.append u' v') :
    u = u' ∧ v = v' := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · have := congrFun h (Fin.castAdd s i)
    rwa [Fin.append_left, Fin.append_left] at this
  · have := congrFun h (Fin.natAdd s i)
    rwa [Fin.append_right, Fin.append_right] at this

end Append

/-! ### The windows of consecutive depths -/

section Windows

variable {s k : ℕ}

theorem regSpan_eq_two_mul {j : ℕ} (hj : j + 1 ≤ k) : regSpan k j = 2 * regSpan k (j + 1) := by
  rw [regSpan, regSpan, show k + 1 - j = (k + 1 - (j + 1)) + 1 by omega, pow_succ, mul_comm]

variable [NeZero s]

/-- The first register of the sub-block `p` of depth `j` is the first register of its first
half. -/
theorem regWindow_two_mul {j : ℕ} (hj : j + 1 ≤ k) {p : ℕ} (hp : p < 2 ^ j) (t : Fin (s + s))
    (ht : t.val < s) : regWindow k (j + 1) (2 * p) t = regWindow k j p t := by
  have hp' : 2 * p < 2 ^ (j + 1) := by rw [pow_succ]; omega
  apply Fin.ext
  rw [regWindow_val hj hp' t, regWindow_val (by omega) hp t, regSpan_eq_two_mul hj]
  simp only [regOffset, ht, ↓reduceIte]
  ring

/-- The last register of the sub-block `p` of depth `j` is the last register of its second
half. -/
theorem regWindow_two_mul_add_one {j : ℕ} (hj : j + 1 ≤ k) {p : ℕ} (hp : p < 2 ^ j)
    (t : Fin (s + s)) (ht : s ≤ t.val) :
    regWindow k (j + 1) (2 * p + 1) t = regWindow k j p t := by
  have hp' : 2 * p + 1 < 2 ^ (j + 1) := by rw [pow_succ]; omega
  apply Fin.ext
  rw [regWindow_val hj hp' t, regWindow_val (by omega) hp t, regSpan_eq_two_mul hj]
  have hB := two_le_regSpan (k := k) (j := j + 1) hj
  obtain ⟨c, hc⟩ : ∃ c, regSpan k (j + 1) = c + 2 := ⟨_, (Nat.sub_add_cancel hB).symm⟩
  simp only [regOffset, not_lt.mpr ht, ↓reduceIte, regSpan_eq_two_mul hj, hc]
  rw [show 2 * (c + 2) - 2 = 2 * c + 2 by omega, Nat.add_sub_cancel]
  ring

/-- The last register of the first half of a sub-block of depth `j` is strictly between the two
registers of the sub-block. -/
theorem regWindow_two_mul_notMem {j : ℕ} (hj : j + 1 ≤ k) {p : ℕ} (hp : p < 2 ^ j)
    (t : Fin (s + s)) (ht : s ≤ t.val) (p' : Fin (2 ^ j)) (t' : Fin (s + s)) :
    regWindow k j p' t' ≠ regWindow k (j + 1) (2 * p) t := by
  have hp' : 2 * p < 2 ^ (j + 1) := by rw [pow_succ]; omega
  intro h
  have h' := congrArg Fin.val h
  rw [regWindow_val (by omega) p'.isLt, regWindow_val hj hp' t] at h'
  have hB := two_le_regSpan (k := k) (j := j + 1) hj
  have := mul_sub_two_add_two_mul (s := s) hB
  have h2 : s * (2 * p * regSpan k (j + 1)) + regOffset k s (j + 1) t =
      s * (p * regSpan k j) + (t.val + s * (regSpan k (j + 1) - 2)) := by
    simp only [regOffset, not_lt.mpr ht, ↓reduceIte, regSpan_eq_two_mul hj]
    ring
  have hlt := t.isLt
  refine regWindow_val_ne_of_interior (by omega) t' (by omega) ?_ (h'.trans h2)
  rw [regSpan_eq_two_mul hj]
  have : s * (2 * regSpan k (j + 1)) = 2 * (s * regSpan k (j + 1)) := by ring
  omega

/-- The first register of the second half of a sub-block of depth `j` is strictly between the
two registers of the sub-block. -/
theorem regWindow_two_mul_add_one_notMem {j : ℕ} (hj : j + 1 ≤ k) {p : ℕ} (hp : p < 2 ^ j)
    (t : Fin (s + s)) (ht : t.val < s) (p' : Fin (2 ^ j)) (t' : Fin (s + s)) :
    regWindow k j p' t' ≠ regWindow k (j + 1) (2 * p + 1) t := by
  have hp' : 2 * p + 1 < 2 ^ (j + 1) := by rw [pow_succ]; omega
  intro h
  have h' := congrArg Fin.val h
  rw [regWindow_val (by omega) p'.isLt, regWindow_val hj hp' t] at h'
  have hB := two_le_regSpan (k := k) (j := j + 1) hj
  have h2 : s * ((2 * p + 1) * regSpan k (j + 1)) + regOffset k s (j + 1) t =
      s * (p * regSpan k j) + (s * regSpan k (j + 1) + t.val) := by
    simp only [regOffset, ht, ↓reduceIte, regSpan_eq_two_mul hj]
    ring
  have hsB : 2 * s ≤ s * regSpan k (j + 1) := by
    rw [mul_comm 2 s]; exact Nat.mul_le_mul_left s hB
  refine regWindow_val_ne_of_interior (by omega) t' (by omega) ?_ (h'.trans h2)
  rw [regSpan_eq_two_mul hj]
  have : s * (2 * regSpan k (j + 1)) = 2 * (s * regSpan k (j + 1)) := by ring
  omega

/-- The windows of the finest depth cover the block. -/
theorem exists_regWindow_eq (y : Fin (s * 2 ^ (k + 1))) :
    ∃ (p : Fin (2 ^ k)) (t : Fin (s + s)), regWindow k k p t = y := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hq : s * 2 ^ (k + 1) = (s + s) * 2 ^ k := by rw [pow_succ]; ring
  have hy : y.val < (s + s) * 2 ^ k := by rw [← hq]; exact y.isLt
  have hp : y.val / (s + s) < 2 ^ k := by rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
  refine ⟨⟨y.val / (s + s), hp⟩, ⟨y.val % (s + s), Nat.mod_lt _ (by omega)⟩, ?_⟩
  apply Fin.ext
  rw [regWindow_val le_rfl hp]
  have h2 : regSpan k k = 2 := by simp [regSpan]
  have ho : regOffset k s k ⟨y.val % (s + s), Nat.mod_lt _ (by omega)⟩ = y.val % (s + s) := by
    unfold regOffset; rw [h2]; split_ifs <;> simp
  rw [ho, h2]
  have := Nat.div_add_mod y.val (s + s)
  linarith

end Windows

/-! ### Blocked indices -/

section Blocked

variable {d D : ℕ}

/-- Blocking a blocked tensor reads the polar isometry of the directly blocked tensor through the
grouping of its sites. -/
theorem polarIsoMatrix_blockTensor_blockTensor (A : MPSTensor d D) (m n : ℕ)
    (I : Fin (blockPhysDim (blockPhysDim d m) n)) (x : Fin (D * D)) :
    polarIsoMatrix (blockTensor (blockTensor A m) n) I x =
      polarIsoMatrix (blockTensor A (m * n)) (iteratedBlockIndex d m n I) x := by
  have h : blockTensor (blockTensor A m) n =
      fun I => blockTensor A (m * n) ((directIteratedBlockEquiv d m n).symm I) := by
    funext I
    rw [directIteratedBlockEquiv_symm_apply, blockTensor_blockTensor_apply]
  rw [h, polarIsoMatrix_comp_equiv]
  rfl

/-- The blocked index of `n` blocks of `m` sites, each carrying the word `σ u`, is the blocked
index of the concatenated word `τ`. -/
theorem iteratedBlockIndex_decodeBlockEquiv_symm {m n : ℕ} (σ : Fin n → Fin (blockPhysDim d m))
    (τ : Fin (m * n) → Fin d)
    (h : ∀ (u : Fin n) (r : Fin m), τ ⟨m * u.val + r.val, by
      have := u.isLt; have := r.isLt
      calc m * u.val + r.val < m * (u.val + 1) := by rw [Nat.mul_succ]; omega
        _ ≤ m * n := Nat.mul_le_mul_left m (by omega)⟩ = decodeBlock d m (σ u) r) :
    iteratedBlockIndex d m n ((decodeBlockEquiv (blockPhysDim d m) n).symm σ) =
      (decodeBlockEquiv d (m * n)).symm τ := by
  apply wordOfBlock_injective
  rw [wordOfBlock_iteratedBlockIndex]
  change ((List.ofFn (decodeBlock _ n ((decodeBlockEquiv _ n).symm σ))).map
    (Kraus.wordOfBlock d m)).flatten = List.ofFn (decodeBlock d (m * n) _)
  rw [decodeBlock_decodeBlockEquiv_symm, decodeBlock_decodeBlockEquiv_symm, List.map_ofFn,
    List.ofFn_mul']
  congr 1
  refine congrArg List.ofFn (funext fun u => ?_)
  simp only [Function.comp_apply, Kraus.wordOfBlock]
  exact congrArg List.ofFn (funext fun r => (h u r).symm)

end Blocked

/-! ### The gates of the tree-RG circuit -/

section Gates

variable {d s D : ℕ} [NeZero d] (dig : Fin D → Cfg d s) (enc : Fin (D * D) → Cfg d s)

/-- The input of the unitary of the sub-block `p` of depth `j`: at the root the input legs
`dig l` and `dig r` of the pair `x = (l, r)`, below it the register `enc x` in the first
register of an even sub-block and in the last register of an odd one, the other register in
`|0⟩`.

arXiv:2307.01696, eqs. (11) and (16): the input of `V` is `|l⟩_L |0⟩_C |r⟩_R`, and every isometry
`V⁽ʲ⁾` of eq. (16) takes one register `ℂ^{D²}`. -/
def regInput (j p : ℕ) (x : Fin (D * D)) : Cfg d (s + s) :=
  if j = 0 then Fin.append (dig (finProdFinEquiv.symm x).1) (dig (finProdFinEquiv.symm x).2)
  else if p % 2 = 0 then Fin.append (enc x) 0 else Fin.append 0 (enc x)

/-- The two registers written by an isometry `ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}`. -/
noncomputable def coarseOutput (e : Fin (blockPhysDim (D * D) 2)) : Cfg d (s + s) :=
  Fin.append (enc (decodeBlock _ 2 e 0)) (enc (decodeBlock _ 2 e 1))

/-- The two registers of the finest layer, read as `2s` sites. -/
noncomputable def fineOutput (e : Fin (blockPhysDim (blockPhysDim d s) 2)) : Cfg d (s + s) :=
  Fin.append (decodeBlock d s (decodeBlock _ 2 e 0)) (decodeBlock d s (decodeBlock _ 2 e 1))

variable {dig enc}

theorem regInput_injective (hdig : Function.Injective dig) (henc : Function.Injective enc)
    (j p : ℕ) : Function.Injective (regInput dig enc j p) := by
  intro x x' h
  unfold regInput at h
  split_ifs at h
  · obtain ⟨h1, h2⟩ := append_injective h
    exact finProdFinEquiv.symm.injective (Prod.ext (hdig h1) (hdig h2))
  · exact henc (append_injective h).1
  · exact henc (append_injective h).2

omit [NeZero d] in
private theorem decodeBlock_two_injective {β : ℕ} {e e' : Fin (blockPhysDim β 2)}
    (h0 : decodeBlock β 2 e 0 = decodeBlock β 2 e' 0)
    (h1 : decodeBlock β 2 e 1 = decodeBlock β 2 e' 1) : e = e' := by
  apply (decodeBlockEquiv β 2).injective
  funext i
  fin_cases i
  · exact h0
  · exact h1

omit [NeZero d] in
theorem coarseOutput_injective (henc : Function.Injective enc) :
    Function.Injective (coarseOutput (s := s) enc) := fun _ _ h =>
  decodeBlock_two_injective (henc (append_injective h).1) (henc (append_injective h).2)

omit [NeZero d] in
theorem fineOutput_bijective : Function.Bijective (fineOutput (d := d) (s := s)) := by
  refine ⟨fun e e' h => decodeBlock_two_injective ((decodeBlockEquiv d s).injective
    (append_injective h).1) ((decodeBlockEquiv d s).injective (append_injective h).2),
    fun z => ?_⟩
  refine ⟨(decodeBlockEquiv _ 2).symm ![(decodeBlockEquiv d s).symm fun i => z (Fin.castAdd s i),
    (decodeBlockEquiv d s).symm fun i => z (Fin.natAdd s i)], ?_⟩
  funext t
  refine Fin.addCases (fun i => ?_) (fun i => ?_) t
  · simp only [fineOutput, Fin.append_left, decodeBlock_decodeBlockEquiv_symm,
      Matrix.cons_val_zero]
  · simp only [fineOutput, Fin.append_right, decodeBlock_decodeBlockEquiv_symm,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]

variable (dig enc) (B : MPSTensor (blockPhysDim d s) D)

/-- The coarse layer `V⁽ᵐ⁺²⁾ : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` of the tree-RG circuit of `B`, the
isometric factor of the two-site blocked tensor of `T_{m+1}` (`MPSTensor.treeLayers`).

arXiv:2307.01696, eq. (16). -/
noncomputable def regLayer (m : ℕ) : Matrix (Fin (blockPhysDim (D * D) 2)) (Fin (D * D)) ℂ :=
  polarIsoMatrix (blockTensor
    ((pairPosTensor : MPSTensor (D * D) D → MPSTensor (D * D) D)^[m] (pairPosTensor B)) 2)

/-- The unitary of the sub-block `p` of depth `j` of the tree-RG circuit of `B` with `k + 1`
layers: the extension of the layer `V⁽ᵏ⁺¹⁻ʲ⁾` from its input to its output registers.

arXiv:2307.01696, eq. (16) and paragraph "Tree-RG circuit with measurements". -/
noncomputable def regTreeGate (k j p : ℕ) : Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ :=
  if j < k then extUnitary (regLayer B (k - 1 - j)) (regInput dig enc j p) (coarseOutput enc)
  else extUnitary (polarIsoMatrix (blockTensor B 2)) (regInput dig enc j p) fineOutput

theorem regTreeGate_mem_unitary (k j p : ℕ) :
    regTreeGate dig enc B k j p ∈ unitary (Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) := by
  unfold regTreeGate
  split_ifs <;> exact extUnitary_mem_unitary _ _ _

variable {dig enc B}

theorem regTreeGate_apply_of_lt (h2 : Kraus.IsInjective (blockTensor B 2))
    (hdig : Function.Injective dig) (henc : Function.Injective enc) {k j : ℕ} (hj : j < k)
    (p : ℕ) (c : Fin (D * D)) (z : Cfg d (s + s)) :
    regTreeGate dig enc B k j p z (regInput dig enc j p c) =
      Function.extend (coarseOutput enc) (fun b => regLayer B (k - 1 - j) b c) 0 z := by
  simp only [regTreeGate, hj, ↓reduceIte]
  exact extUnitary_apply (isIsometry_polarIsoMatrix_of_isInjective
    (isInjective_blockTensor_iterate_pairPosTensor h2 _)) (regInput_injective hdig henc j p)
    (coarseOutput_injective henc) c z

theorem regTreeGate_apply_of_le (h2 : Kraus.IsInjective (blockTensor B 2))
    (hdig : Function.Injective dig) (henc : Function.Injective enc) {k j : ℕ} (hj : k ≤ j)
    (p : ℕ) (c : Fin (D * D)) (z : Cfg d (s + s)) :
    regTreeGate dig enc B k j p z (regInput dig enc j p c) =
      Function.extend fineOutput (fun b => polarIsoMatrix (blockTensor B 2) b c) 0 z := by
  simp only [regTreeGate, show ¬ j < k by omega, ↓reduceIte]
  exact extUnitary_apply (isIsometry_polarIsoMatrix_of_isInjective h2)
    (regInput_injective hdig henc j p) fineOutput_bijective.1 c z

end Gates

/-! ### The configurations of the registers -/

section Configs

variable {d s D : ℕ} [NeZero d] [NeZero s] {dig : Fin D → Cfg d s} {enc : Fin (D * D) → Cfg d s}
  {k : ℕ}

variable (dig enc k) in
/-- The configuration of a block after the depths `0, …, j` of the tree: the registers of the
sub-blocks of depth `j` carry the outputs `e` of their unitaries, the other sites `|0⟩`. -/
noncomputable def regRegisterCfg (j : ℕ) (e : Fin (2 ^ j) → Fin (blockPhysDim (D * D) 2)) :
    Cfg d (s * 2 ^ (k + 1)) :=
  placeCfg (fun p : Fin (2 ^ j) => regWindow k j p) fun p => coarseOutput enc (e p)

variable (k) in
/-- The configuration of a block written by the finest depth from the outputs `e`. -/
noncomputable def regLeafCfg (e : Fin (2 ^ k) → Fin (blockPhysDim (blockPhysDim d s) 2)) :
    Cfg d (s * 2 ^ (k + 1)) :=
  placeCfg (fun p : Fin (2 ^ k) => regWindow k k p) fun p => fineOutput (e p)

theorem regRegisterCfg_injective (henc : Function.Injective enc) {j : ℕ} (hj : j ≤ k) :
    Function.Injective (regRegisterCfg (d := d) (s := s) enc k j) := fun _ _ h =>
  funext fun p => coarseOutput_injective henc
    (congrFun (placeCfg_injective (regWindow_injective₂ hj) h) p)

theorem regLeafCfg_bijective : Function.Bijective (regLeafCfg (d := d) (s := s) k) := by
  have hW := regWindow_injective₂ (s := s) (le_refl k)
  refine ⟨fun e e' h => funext fun p => fineOutput_bijective.1
    (congrFun (placeCfg_injective hW h) p), fun τ => ?_⟩
  refine ⟨fun p => Function.surjInv fineOutput_bijective.2 (τ ∘ regWindow k k p), ?_⟩
  change placeCfg _ _ = τ
  conv_rhs => rw [eq_placeCfg hW (z := τ) fun y hy => absurd (exists_regWindow_eq y) (by
    simp only [not_exists]; exact fun p t h => hy p t h)]
  simp only [Function.surjInv_eq]

/-- The configuration written by the finest depth carries at the site `s u + r` the letter `r`
of the register `u`. -/
theorem regLeafCfg_apply (e : Fin (2 ^ k) → Fin (blockPhysDim (blockPhysDim d s) 2))
    (u : Fin (2 ^ (k + 1))) (r : Fin s) :
    regLeafCfg k e ⟨s * u.val + r.val, by
      have := u.isLt; have := r.isLt
      calc s * u.val + r.val < s * (u.val + 1) := by rw [Nat.mul_succ]; omega
        _ ≤ s * 2 ^ (k + 1) := Nat.mul_le_mul_left s (by omega)⟩ =
      decodeBlock d s (unpair e u) r := by
  have hW := regWindow_injective₂ (s := s) (le_refl k)
  have hu := u.isLt
  have hp : u.val / 2 < 2 ^ k := by have : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k; omega
  have hi := Nat.mod_lt u.val two_pos
  set t : Fin (s + s) := ⟨u.val % 2 * s + r.val, by
    have := r.isLt; rcases Nat.mod_two_eq_zero_or_one u.val with h | h <;> rw [h] <;> omega⟩
  have hsite : regWindow k k (u.val / 2) t = ⟨s * u.val + r.val, by
      calc s * u.val + r.val < s * (u.val + 1) := by rw [Nat.mul_succ]; omega
        _ ≤ s * 2 ^ (k + 1) := Nat.mul_le_mul_left s (by omega)⟩ := by
    apply Fin.ext
    rw [regWindow_val le_rfl hp]
    have h2 : regSpan k k = 2 := by simp [regSpan]
    have ho : regOffset k s k t = t.val := by unfold regOffset; rw [h2]; split_ifs <;> simp
    rw [ho, h2]
    have := Nat.div_add_mod u.val 2
    simp only [t]
    nlinarith
  rw [← hsite, regLeafCfg, show (u.val / 2 : ℕ) = ((⟨u.val / 2, hp⟩ : Fin (2 ^ k)) : ℕ) from rfl,
    placeCfg_apply hW]
  simp only [fineOutput, unpair]
  rcases Nat.mod_two_eq_zero_or_one u.val with h | h
  · rw [append_apply_of_lt _ _ _ (by simp only [t, h]; omega)]
    simp only [t, h, zero_mul, zero_add]
    congr 2
  · rw [append_apply_of_le _ _ _ (by simp only [t, h]; omega)]
    simp only [t, h, one_mul]
    congr 2
    omega

variable (dig enc) in
/-- The configuration after the depths `0, …, j` is the input of the depth `j + 1`: the output
registers of the sub-block `p` of depth `j` are the input registers of its two halves. -/
theorem regRegisterCfg_eq_placeCfg {j : ℕ} (hj : j + 1 ≤ k)
    (e : Fin (2 ^ j) → Fin (blockPhysDim (D * D) 2)) :
    regRegisterCfg (s := s) enc k j e =
      placeCfg (fun p : Fin (2 ^ (j + 1)) => regWindow k (j + 1) p)
        fun p => regInput dig enc (j + 1) p (unpair e p) := by
  have hW := regWindow_injective₂ (s := s) hj
  have hW' := regWindow_injective₂ (s := s) (k := k) (j := j) (by omega)
  have hsub : ∀ (p : Fin (2 ^ j)) (t : Fin (s + s)), ∃ (p' : Fin (2 ^ (j + 1))),
      regWindow k (j + 1) p' t = regWindow k j p t := by
    intro p t
    have h1 : 2 * p.val < 2 ^ (j + 1) := by have := p.isLt; rw [pow_succ]; omega
    have h2 : 2 * p.val + 1 < 2 ^ (j + 1) := by have := p.isLt; rw [pow_succ]; omega
    by_cases ht : t.val < s
    · exact ⟨⟨2 * p.val, h1⟩, regWindow_two_mul hj p.isLt t ht⟩
    · exact ⟨⟨2 * p.val + 1, h2⟩, regWindow_two_mul_add_one hj p.isLt t (by omega)⟩
  conv_lhs => rw [eq_placeCfg hW (z := regRegisterCfg enc k j e) fun y hy =>
    placeCfg_apply_of_notMem _ fun p t h => by
      obtain ⟨p', hp'⟩ := hsub p t
      exact hy p' t (hp'.trans h)]
  congr 1
  funext p' t
  have hp := p'.isLt
  have hq : p'.val / 2 < 2 ^ j := by have : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j; omega
  simp only [Function.comp_apply, regInput, show j + 1 ≠ 0 by omega, ↓reduceIte, unpair]
  rcases Nat.mod_two_eq_zero_or_one p'.val with h | h
  · have hp' : p'.val = 2 * (p'.val / 2) := by omega
    simp only [h, ↓reduceIte]
    by_cases ht : t.val < s
    · rw [show regWindow k (j + 1) p' t = regWindow k j (p'.val / 2) t by
        rw [← regWindow_two_mul hj hq t ht, ← hp']]
      refine (placeCfg_apply hW' (fun p => coarseOutput enc (e p)) ⟨p'.val / 2, hq⟩ t).trans ?_
      rw [coarseOutput, append_apply_of_lt _ _ _ ht, append_apply_of_lt _ _ _ ht]
      rfl
    · rw [regRegisterCfg, placeCfg_apply_of_notMem _ fun p t' h' => by
          rw [show (p'.val : ℕ) = 2 * (p'.val / 2) from hp'] at h'
          exact regWindow_two_mul_notMem hj hq t (by omega) p t' h',
        append_apply_of_le _ _ _ (by omega)]
      rfl
  · have hp' : p'.val = 2 * (p'.val / 2) + 1 := by omega
    simp only [h, one_ne_zero, ↓reduceIte]
    by_cases ht : t.val < s
    · rw [regRegisterCfg, placeCfg_apply_of_notMem _ fun p t' h' => by
          rw [show (p'.val : ℕ) = 2 * (p'.val / 2) + 1 from hp'] at h'
          exact regWindow_two_mul_add_one_notMem hj hq t ht p t' h',
        append_apply_of_lt _ _ _ ht]
      rfl
    · rw [show regWindow k (j + 1) p' t = regWindow k j (p'.val / 2) t by
        rw [← regWindow_two_mul_add_one hj hq t (by omega), ← hp']]
      refine (placeCfg_apply hW' (fun p => coarseOutput enc (e p)) ⟨p'.val / 2, hq⟩ t).trans ?_
      rw [coarseOutput, append_apply_of_le _ _ _ (by omega), append_apply_of_le _ _ _ (by omega)]
      rfl

variable (dig enc) in
/-- The input of the root is the input of the block: `dig l` on its first `s` sites, `dig r` on
its last `s` sites and `|0⟩` elsewhere. -/
theorem placeCfg_regInput_zero (x : Fin (D * D)) :
    placeCfg (fun p : Fin (2 ^ 0) => regWindow k 0 p) (fun p => regInput dig enc 0 p x) =
      blockInputCfg (Nat.pos_of_ne_zero (NeZero.ne d)) (s * 2 ^ (k + 1)) dig
        (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 := by
  have hW := regWindow_injective₂ (s := s) (k := k) (j := 0) (Nat.zero_le k)
  have hq : 2 * s ≤ s * 2 ^ (k + 1) := by
    rw [mul_comm 2 s]; exact Nat.mul_le_mul_left s (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right two_pos (by omega))
  have h0 : regSpan k 0 = 2 ^ (k + 1) := rfl
  have hval : ∀ t : Fin (s + s), (regWindow k 0 0 t).val =
      if t.val < s then t.val else t.val + (s * 2 ^ (k + 1) - 2 * s) := by
    intro t
    rw [regWindow_val (Nat.zero_le k) (Nat.two_pow_pos 0) t]
    simp only [regOffset, h0, zero_mul, mul_zero, zero_add]
    split_ifs
    · rfl
    · congr 1; rw [Nat.mul_sub, mul_comm s 2]
  funext y
  simp only [blockInputCfg]
  by_cases hy : y.val < s
  · simp only [hy, ↓reduceDIte]
    have hy0 : regWindow k 0 ((0 : Fin (2 ^ 0)) : ℕ) ⟨y.val, by omega⟩ = y :=
      Fin.ext (by rw [Fin.val_zero, hval]; simp [hy])
    calc placeCfg _ _ y = placeCfg (fun p : Fin (2 ^ 0) => regWindow k 0 p)
          (fun p => regInput dig enc 0 p x)
          (regWindow k 0 ((0 : Fin (2 ^ 0)) : ℕ) ⟨y.val, by omega⟩) := by rw [hy0]
      _ = _ := placeCfg_apply hW _ 0 _
      _ = _ := by
        simp only [regInput, ↓reduceIte]
        exact append_apply_of_lt _ _ _ hy
  by_cases hy' : s * 2 ^ (k + 1) - s ≤ y.val
  · simp only [hy, hy', ↓reduceDIte]
    have hlt : y.val - (s * 2 ^ (k + 1) - 2 * s) < s + s := by have := y.isLt; omega
    have hy0 : regWindow k 0 ((0 : Fin (2 ^ 0)) : ℕ)
        ⟨y.val - (s * 2 ^ (k + 1) - 2 * s), hlt⟩ = y := Fin.ext (by
      rw [Fin.val_zero, hval]
      simp only [show ¬ y.val - (s * 2 ^ (k + 1) - 2 * s) < s by omega, ↓reduceIte]
      omega)
    calc placeCfg _ _ y = placeCfg (fun p : Fin (2 ^ 0) => regWindow k 0 p)
          (fun p => regInput dig enc 0 p x)
          (regWindow k 0 ((0 : Fin (2 ^ 0)) : ℕ) ⟨_, hlt⟩) := by rw [hy0]
      _ = _ := placeCfg_apply hW _ 0 _
      _ = _ := by
        simp only [regInput, ↓reduceIte]
        rw [append_apply_of_le _ _ _ (by simp only; omega)]
        congr 2
        simp only
        omega
  · simp only [hy, hy', ↓reduceDIte]
    refine placeCfg_apply_of_notMem _ fun p t h => ?_
    have := congrArg Fin.val h
    rw [show (p : ℕ) = 0 by have := p.isLt; simp at this; omega, hval] at this
    split_ifs at this <;> omega

end Configs

/-! ### The tree from the root -/

section Tree

variable {d s D : ℕ} [NeZero d] [NeZero s] {dig : Fin D → Cfg d s} {enc : Fin (D * D) → Cfg d s}
  {B : MPSTensor (blockPhysDim d s) D} {k : ℕ}

private theorem prod_fin_two_pow_zero {M : Type*} [CommMonoid M] (f : Fin (2 ^ 0) → M) :
    ∏ p, f p = f 0 :=
  Finset.prod_eq_single 0 (fun b _ hb => absurd (Fin.ext (by have := b.isLt; simp at this; omega))
    hb) (by simp)

/-- After the depths `0, …, j < k`, the registers of the sub-blocks of depth `j` carry the
outputs `e` with the amplitude of the coarse layers `V⁽ᵏ⁺¹⁻ʲ⁾, …, V⁽ᵏ⁺¹⁾` of the tree. -/
theorem regTreeOp_apply_regRegisterCfg (h2 : Kraus.IsInjective (blockTensor B 2))
    (hdig : Function.Injective dig) (henc : Function.Injective enc) (x : Fin (D * D)) :
    ∀ j, j < k → ∀ y, regTreeOp (regTreeGate dig enc B k) k (j + 1) y
        (placeCfg (fun p : Fin (2 ^ 0) => regWindow k 0 p) fun p => regInput dig enc 0 p x) =
      Function.extend (regRegisterCfg enc k j)
        (fun e => treeAmp j (regLayer B (k - 1 - j)) (fun m => regLayer B (k - j + m)) e x) 0 y
  | 0, hk, y => by
    rw [regTreeOp, regTreeOp, Matrix.mul_one, regLevelOp,
      list_prod_embedOp_placeCfg (regWindow_injective₂ (Nat.zero_le k)) _
        (fun p => regInput dig enc 0 p) (fun _ => coarseOutput enc)
        (fun _ => coarseOutput_injective henc) (fun _ => regLayer B (k - 1 - 0))
        (fun p c z => regTreeGate_apply_of_lt h2 hdig henc hk p c z) (fun _ => x) y]
    congr 1
    funext e
    rw [prod_fin_two_pow_zero, treeAmp]
  | j + 1, hk, y => by
    have ih := regTreeOp_apply_regRegisterCfg h2 hdig henc x j (by omega)
    rw [regTreeOp, Matrix.mul_apply_extend _ _ _ (regRegisterCfg_injective henc (by omega)) _ ih
      (regRegisterCfg_injective henc (by omega))
      (fun e e' => ∏ p, regLayer B (k - 1 - (j + 1)) (e' p) (unpair e p)) ?_ y]
    · congr 1
      funext e'
      have e1 : k - (j + 1) + 0 = k - 1 - j := by omega
      have e2 : ∀ m, k - (j + 1) + (m + 1) = k - j + m := fun m => by omega
      rw [treeAmp]
      simp only [e1, e2]
    · intro e y
      rw [regRegisterCfg_eq_placeCfg dig enc (show j + 1 ≤ k by omega) e, regLevelOp]
      exact list_prod_embedOp_placeCfg (regWindow_injective₂ (by omega)) _
        (fun p => regInput dig enc (j + 1) p) (fun _ => coarseOutput enc)
        (fun _ => coarseOutput_injective henc) (fun _ => regLayer B (k - 1 - (j + 1)))
        (fun p c z => regTreeGate_apply_of_lt h2 hdig henc hk p c z) (unpair e) y

/-- After all the depths the block carries the outputs `e` of the finest layer with the
amplitude of the whole tree. -/
theorem regTreeOp_apply_regLeafCfg (h2 : Kraus.IsInjective (blockTensor B 2))
    (hdig : Function.Injective dig) (henc : Function.Injective enc) (x : Fin (D * D))
    (y : Cfg d (s * 2 ^ (k + 1))) :
    regTreeOp (regTreeGate dig enc B k) k (k + 1) y
        (placeCfg (fun p : Fin (2 ^ 0) => regWindow k 0 p) fun p => regInput dig enc 0 p x) =
      Function.extend (regLeafCfg k)
        (fun e => treeAmp k (polarIsoMatrix (blockTensor B 2)) (regLayer B) e x) 0 y := by
  cases k with
  | zero =>
    rw [regTreeOp, regTreeOp, Matrix.mul_one, regLevelOp,
      list_prod_embedOp_placeCfg (regWindow_injective₂ le_rfl) _
        (fun p => regInput dig enc 0 p) (fun _ => fineOutput) (fun _ => fineOutput_bijective.1)
        (fun _ => polarIsoMatrix (blockTensor B 2))
        (fun p c z => regTreeGate_apply_of_le h2 hdig henc le_rfl p c z) (fun _ => x) y]
    congr 1
    funext e
    rw [prod_fin_two_pow_zero, treeAmp]
  | succ k =>
    have ih := regTreeOp_apply_regRegisterCfg (k := k + 1) h2 hdig henc x k (by omega)
    rw [regTreeOp, Matrix.mul_apply_extend _ _ _ (regRegisterCfg_injective henc (by omega)) _ ih
      regLeafCfg_bijective.1
      (fun e e' => ∏ p, polarIsoMatrix (blockTensor B 2) (e' p) (unpair e p)) ?_ y]
    · congr 1
      funext e'
      have e1 : k + 1 - 1 - k = 0 := by omega
      have e2 : ∀ m, k + 1 - k + m = m + 1 := fun m => by omega
      rw [treeAmp]
      simp only [e1, e2]
    · intro e y
      rw [regRegisterCfg_eq_placeCfg dig enc (show k + 1 ≤ k + 1 from le_rfl) e, regLevelOp]
      exact list_prod_embedOp_placeCfg (regWindow_injective₂ le_rfl) _
        (fun p => regInput dig enc (k + 1) p) (fun _ => fineOutput)
        (fun _ => fineOutput_bijective.1) (fun _ => polarIsoMatrix (blockTensor B 2))
        (fun p c z => regTreeGate_apply_of_le h2 hdig henc le_rfl p c z) (unpair e) y

/-- **The tree of registers implements the isometry of the block** (arXiv:2307.01696,
eqs. (11) and (16)). Let `B` be `A` blocked over `s` sites, with injective two-site blocked
tensor, and let `dig : ℂ^D → (ℂ^d)^{⊗s}` and `enc : ℂ^{D²} → (ℂ^d)^{⊗s}` place the legs and the
registers injectively. On a block of `q = s 2^{k+1}` sites the tree of the unitaries
`regTreeGate` satisfies `⟨σ| T |dig l, 0 ⋯ 0, dig r⟩ = ⟨σ| V |l, r⟩` for every configuration
`σ`, with `B_q = V P` the polar decomposition of `A` blocked over `q` sites. -/
theorem regTreeOp_apply_blockInputCfg (A : MPSTensor d D)
    (h2 : Kraus.IsInjective (blockTensor (blockTensor A s) 2)) (hdig : Function.Injective dig)
    (henc : Function.Injective enc) (l r : Fin D) (τ : Cfg d (s * 2 ^ (k + 1))) :
    regTreeOp (regTreeGate dig enc (blockTensor A s) k) k (k + 1) τ
        (blockInputCfg (Nat.pos_of_ne_zero (NeZero.ne d)) (s * 2 ^ (k + 1)) dig l r) =
      polarIsoMatrix (blockTensor A (s * 2 ^ (k + 1)))
        ((decodeBlockEquiv d (s * 2 ^ (k + 1))).symm τ) (finProdFinEquiv (l, r)) := by
  have hx := placeCfg_regInput_zero dig enc (k := k) (finProdFinEquiv (l, r))
  simp only [Equiv.symm_apply_apply] at hx
  rw [← hx, regTreeOp_apply_regLeafCfg h2 hdig henc]
  obtain ⟨e, rfl⟩ := regLeafCfg_bijective.2 τ
  rw [regLeafCfg_bijective.1.extend_apply, ← binaryTreeMatrix_apply_unpair]
  change binaryTreeMatrix k (polarIsoMatrix (blockTensor (blockTensor A s) 2))
    (treeLayers k (blockTensor A s)) _ _ = _
  rw [binaryTreeMatrix_treeLayers, ← polarIsoMatrix_blockTensor_eq_treeIsoMatrix,
    polarIsoMatrix_blockTensor_blockTensor,
    iteratedBlockIndex_decodeBlockEquiv_symm _ _ fun u r => regLeafCfg_apply e u r]

end Tree

end MPSPreparation
