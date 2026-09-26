/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.ShiftIndex
import TNLean.MPS.MPU.SimpleBlocking

/-!
# Shift MPUs: source ranks and index values at every blocking

**Source.** Cirac, Perez-Garcia, Schuch, Verstraete 2017 (arXiv:1703.09188),
Definition IV.1 and Proposition IV.2, `Papers/1703.09188/paper_v2.tex`
lines 681--704: the index of a tensor is $\frac12(\log_2 r-\log_2\ell)$ at any
simple blocking, independently of the blocking; lines 1980--2001 and
2037--2041: the shift $T^{(N)}$ has index $\log_2 d$, its adjoint has index
$-\log_2 d$, and $U_2=T^\dagger\otimes T$ and $U_3=T\otimes T^\dagger$ have
index zero.
Review: arXiv:2011.12127, Appendix A, "The shift MPU",
`Papers/2011.12127/TN-Review-main.tex` lines 2607--2611, calls the shift the
paradigmatic MPU that cannot be approximated by a short-range time evolution,
citing arXiv:1703.09188.

**Formalized here.** For every $k$, the shift tensors blocked over $k+1$ sites
are simple, and their source ranks are computed exactly: the right shift has
$(r,\ell)=(d^{k+2},d^k)$, the left shift $(d^k,d^{k+2})$, and $U_2$, $U_3$ have
$r=\ell=d^{2k+2}$. Hence the index values $\log_2 d$, $-\log_2 d$, $0$, $0$ hold
at every simple blocking of these tensors, not only at the displayed one. For
$d>1$ the right and left ranks of every blocked shift differ, so its index value
is nonzero. By the source's appendix, line 2308, a depth-two circuit of
nearest-neighbour gates is the standard form of an MPU; its two gate outputs have
the dimensions $\ell$ and $r$, and the rank inequality says that no blocked shift
tensor has equal gate outputs.

The review sentence itself is not formalized. Its content in the source is
Theorem `IndexTh` (iii)--(iv), lines 824--853: the index is robust and equal
indices characterize equivalence, while the identity has index zero. Neither
part is proved here.

**Scope restriction (specified tensors):** The values are for the displayed
shift tensors and their blockings. Definition IV.1 defines the index for a
tensor in canonical form, and the identification of these values with the public
index of any tensor generating the shift needs the canonical form of the shift
and the uniqueness of that form. Documented in
`docs/paper-gaps/mpu_shift_specified_tensor_index_scope.tex`.

## Main results
* `evalWord_rightShiftTensor_ofFn`, `blockTensor_rightShiftTensor_apply`: the
  blocked right shift is a matrix unit or zero.
* `rightRank_blockTensor_rightShiftTensor`, `leftRank_blockTensor_rightShiftTensor`:
  the ranks $d^{k+2}$ and $d^k$.
* `rightRank_mul_leftRank_blockTensor_rightShiftTensor`: $r\ell=d^{2(k+1)}$.
* `sourceIndexValue_blockTensor_rightShiftTensor`,
  `sourceIndexValue_blockTensor_leftShiftTensor`,
  `sourceIndexValue_blockTensor_shiftExampleU₂`,
  `sourceIndexValue_blockTensor_shiftExampleU₃`: index values at every blocking.
* `rightShiftTensor_isMPUSimple`, `leftShiftTensor_isMPUSimple`,
  `blockTensor_rightShiftTensor_isMPUSimple`,
  `blockTensor_leftShiftTensor_isMPUSimple`: simplicity at every blocking.
* `rightRank_blockTensor_rightShiftTensor_ne_leftRank`,
  `sourceIndexValue_blockTensor_rightShiftTensor_ne_zero`: for $d>1$ the ranks
  differ and the index value is nonzero.

## References
- [arXiv:1703.09188](https://arxiv.org/abs/1703.09188) -- Cirac, Perez-Garcia,
  Schuch, Verstraete, *Matrix Product Unitaries: Structure, Symmetries, and
  Topological Invariants*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Perez-Garcia,
  Schuch, Verstraete, *Matrix Product States and Projected Entangled Pair
  States: Concepts, Symmetries, and Theorems*
-/

open scoped Matrix

namespace MPOTensor

variable {d : ℕ}

/-! ### The blocked right shift -/

/-- Word evaluation of the right-shift tensor along two words of length $n+1$:
$$
T^{\sigma_0\tau_0}\cdots T^{\sigma_n\tau_n}
  = [\tau_m=\sigma_{m+1}\ (m<n)]\,|\sigma_0)(\tau_n|.
$$

Source: arXiv:1703.09188, lines 1980--1987 (the tensor of the shift $T^{(N)}$). -/
theorem evalWord_rightShiftTensor_ofFn (n : ℕ) (σ τ : Fin (n + 1) → Fin d) :
    evalWord (rightShiftTensor d) (List.ofFn σ) (List.ofFn τ) =
      if Fin.init τ = Fin.tail σ then Matrix.single (σ 0) (τ (Fin.last n)) 1 else 0 := by
  induction n with
  | zero =>
      have h : Fin.init τ = Fin.tail σ := funext fun m ↦ m.elim0
      simp [h, rightShiftTensor]
  | succ n ih =>
      rw [List.ofFn_succ (f := σ), List.ofFn_succ (f := τ), evalWord_cons,
        ih (fun m ↦ σ m.succ) (fun m ↦ τ m.succ)]
      have hiff : Fin.init τ = Fin.tail σ ↔
          τ 0 = σ 1 ∧ Fin.init (fun m ↦ τ m.succ) = Fin.tail (fun m ↦ σ m.succ) := by
        simp only [funext_iff, Fin.init, Fin.tail, Fin.forall_fin_succ, Fin.castSucc_zero,
          Fin.succ_zero_eq_one, Fin.succ_castSucc]
      by_cases h₀ : τ 0 = σ 1 <;> by_cases h₁ :
          Fin.init (fun m ↦ τ m.succ) = Fin.tail (fun m ↦ σ m.succ) <;>
        simp [hiff, h₀, h₁, rightShiftTensor, Fin.succ_last, Matrix.single_mul_single_same,
          Fin.succ_zero_eq_one]

/-- Entry formula for the right-shift tensor blocked over $k+1$ sites. Writing
$\sigma$ and $\tau$ for the decoded ket and bra words of the blocked indices,
the blocked letter is the matrix unit $|\sigma_0)(\tau_k|$ when
$\tau_m=\sigma_{m+1}$ for every $m<k$, and zero otherwise.

Source: arXiv:1703.09188, lines 1980--1987 (the shift $T^{(N)}$), blocked as in
Proposition IV.2, lines 697--704. -/
theorem blockTensor_rightShiftTensor_apply (k : ℕ)
    (I J : Fin (MPSTensor.blockPhysDim d (k + 1))) :
    blockTensor (rightShiftTensor d) (k + 1) I J =
      if Fin.init (Kraus.decodeBlock d (k + 1) J) = Fin.tail (Kraus.decodeBlock d (k + 1) I)
      then Matrix.single (Kraus.decodeBlock d (k + 1) I 0)
        (Kraus.decodeBlock d (k + 1) J (Fin.last k)) 1
      else 0 :=
  evalWord_rightShiftTensor_ofFn k _ _

/-- The bijection of source-cut indices that carries the first source cut of the
blocked right shift to the identity: a row $(\sigma,\beta)$ goes to the column
$(\sigma_0,\ \sigma_1\cdots\sigma_k\beta)$. -/
private noncomputable def rightShiftCutEquiv (d k : ℕ) :
    Fin (MPSTensor.blockPhysDim d (k + 1)) × Fin d ≃
      Fin d × Fin (MPSTensor.blockPhysDim d (k + 1)) where
  toFun p := (Kraus.decodeBlock d (k + 1) p.1 0,
    (Kraus.decodeBlockEquiv d (k + 1)).symm
      (Fin.snoc (Fin.tail (Kraus.decodeBlock d (k + 1) p.1)) p.2))
  invFun q := ((Kraus.decodeBlockEquiv d (k + 1)).symm
      (Fin.cons q.1 (Fin.init (Kraus.decodeBlock d (k + 1) q.2))),
    Kraus.decodeBlock d (k + 1) q.2 (Fin.last k))
  left_inv p := by
    rcases p with ⟨I, β⟩
    simp only [Kraus.decodeBlock_decodeBlockEquiv_symm, Fin.init_snoc, Fin.snoc_last,
      Fin.cons_self_tail, Prod.mk.injEq, and_true]
    rw [← Kraus.decodeBlockEquiv_apply, Equiv.symm_apply_apply]
  right_inv q := by
    rcases q with ⟨α, J⟩
    simp only [Kraus.decodeBlock_decodeBlockEquiv_symm, Fin.cons_zero, Fin.tail_cons,
      Fin.snoc_init_self, Prod.mk.injEq, true_and]
    rw [← Kraus.decodeBlockEquiv_apply, Equiv.symm_apply_apply]

/-- The first source cut of the blocked right shift is a permutation of the identity.

Source: arXiv:1703.09188, definition `defnrl`, lines 450--477, applied to the
blocked shift tensor. -/
theorem sourceCutM₁_blockTensor_rightShiftTensor (k : ℕ) :
    sourceCutM₁ (blockTensor (rightShiftTensor d) (k + 1)) =
      (1 : Matrix (Fin d × Fin (MPSTensor.blockPhysDim d (k + 1)))
        (Fin d × Fin (MPSTensor.blockPhysDim d (k + 1))) ℂ).submatrix
          (rightShiftCutEquiv d k) (Equiv.refl _) := by
  ext ⟨I, β⟩ ⟨α, J⟩
  have hsnoc : (Kraus.decodeBlockEquiv d (k + 1)).symm
        (Fin.snoc (Fin.tail (Kraus.decodeBlock d (k + 1) I)) β) = J ↔
      Fin.init (Kraus.decodeBlock d (k + 1) J) = Fin.tail (Kraus.decodeBlock d (k + 1) I) ∧
        Kraus.decodeBlock d (k + 1) J (Fin.last k) = β := by
    rw [Equiv.symm_apply_eq, Kraus.decodeBlockEquiv_apply]
    constructor
    · rintro h
      rw [← h, Fin.init_snoc, Fin.snoc_last]
      exact ⟨rfl, rfl⟩
    · rintro ⟨h₁, h₂⟩
      rw [← h₁, ← h₂, Fin.snoc_init_self]
  simp only [sourceCutM₁_apply, blockTensor_rightShiftTensor_apply, Matrix.submatrix_apply,
    Equiv.refl_apply, Matrix.one_apply, rightShiftCutEquiv, Equiv.coe_fn_mk, Prod.mk.injEq,
    hsnoc]
  by_cases h₁ : Fin.init (Kraus.decodeBlock d (k + 1) J) =
      Fin.tail (Kraus.decodeBlock d (k + 1) I) <;>
    by_cases h₂ : Kraus.decodeBlock d (k + 1) J (Fin.last k) = β <;>
    by_cases h₃ : Kraus.decodeBlock d (k + 1) I 0 = α <;>
    simp [h₁, h₂, h₃]

/-- The right source rank of the right shift blocked over $k+1$ sites is $d^{k+2}$.

Source: arXiv:1703.09188, definition `defnrl`, lines 450--477, and the blocked
ranks $r_k$ of Proposition IV.2, lines 697--704. -/
theorem rightRank_blockTensor_rightShiftTensor (k : ℕ) :
    r[blockTensor (rightShiftTensor d) (k + 1)] = d ^ (k + 2) := by
  rw [rightRank, sourceCutM₁_blockTensor_rightShiftTensor, Matrix.rank_submatrix,
    Matrix.rank_one]
  simp [MPSTensor.blockPhysDim, Kraus.blockPhysDim_eq_pow, pow_succ]
  ring

/-- The second source cut of the blocked right shift factors through the
$d^k$ middle words $\sigma_1\cdots\sigma_k=\tau_0\cdots\tau_{k-1}$.

Source: arXiv:1703.09188, definition `defnrl`, lines 450--477, applied to the
blocked shift tensor. -/
theorem sourceCutM₂_blockTensor_rightShiftTensor (k : ℕ) :
    sourceCutM₂ (blockTensor (rightShiftTensor d) (k + 1)) =
      (Matrix.of fun (p : Fin d × Fin (MPSTensor.blockPhysDim d (k + 1)))
          (y : Fin k → Fin d) ↦
        if Kraus.decodeBlock d (k + 1) p.2 0 = p.1 ∧
            Fin.tail (Kraus.decodeBlock d (k + 1) p.2) = y then (1 : ℂ) else 0) *
      Matrix.of fun (y : Fin k → Fin d)
          (q : Fin (MPSTensor.blockPhysDim d (k + 1)) × Fin d) ↦
        if Fin.init (Kraus.decodeBlock d (k + 1) q.1) = y ∧
            Kraus.decodeBlock d (k + 1) q.1 (Fin.last k) = q.2 then (1 : ℂ) else 0 := by
  ext ⟨α, I⟩ ⟨J, β⟩
  rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.tail (Kraus.decodeBlock d (k + 1) I))]
  · simp only [sourceCutM₂_apply, blockTensor_rightShiftTensor_apply, Matrix.of_apply, and_true]
    by_cases h₁ : Fin.init (Kraus.decodeBlock d (k + 1) J) =
        Fin.tail (Kraus.decodeBlock d (k + 1) I) <;>
      by_cases h₂ : Kraus.decodeBlock d (k + 1) J (Fin.last k) = β <;>
      by_cases h₃ : Kraus.decodeBlock d (k + 1) I 0 = α <;>
      simp [h₁, h₂, h₃]
  · intro y hy
    simp [Ne.symm hy]

/-- The left source rank of the right shift blocked over $k+1$ sites is $d^k$.

Source: arXiv:1703.09188, definition `defnrl`, lines 450--477, and the blocked
ranks $\ell_k$ of Proposition IV.2, lines 697--704. -/
theorem leftRank_blockTensor_rightShiftTensor [NeZero d] (k : ℕ) :
    ℓ[blockTensor (rightShiftTensor d) (k + 1)] = d ^ k := by
  classical
  apply le_antisymm
  · rw [leftRank, sourceCutM₂_blockTensor_rightShiftTensor]
    refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans_eq ?_)
    simp
  · let e := (Kraus.decodeBlockEquiv d (k + 1)).symm
    let f : (Fin k → Fin d) → Fin d × Fin (MPSTensor.blockPhysDim d (k + 1)) :=
      fun y ↦ (0, e (Fin.cons 0 y))
    let g : (Fin k → Fin d) → Fin (MPSTensor.blockPhysDim d (k + 1)) × Fin d :=
      fun y ↦ (e (Fin.snoc y 0), 0)
    have hminor : (sourceCutM₂ (blockTensor (rightShiftTensor d) (k + 1))).submatrix f g = 1 := by
      ext y y'
      simp only [Matrix.submatrix_apply, f, g, e, sourceCutM₂_apply,
        blockTensor_rightShiftTensor_apply, Kraus.decodeBlock_decodeBlockEquiv_symm,
        Fin.init_snoc, Fin.tail_cons, Fin.cons_zero, Fin.snoc_last, Matrix.one_apply]
      by_cases h : y' = y
      · subst h; simp
      · simp [h, Ne.symm h]
    have hlower := Matrix.rank_submatrix_le
      (sourceCutM₂ (blockTensor (rightShiftTensor d) (k + 1))) f g
    rw [hminor, Matrix.rank_one] at hlower
    simpa [leftRank] using hlower

/-- The source ranks of every nontrivial blocking of the right shift are positive. -/
lemma sourceRanks_pos_blockTensor_rightShiftTensor [NeZero d] (k : ℕ) :
    0 < r[blockTensor (rightShiftTensor d) (k + 1)] ∧
      0 < ℓ[blockTensor (rightShiftTensor d) (k + 1)] := by
  rw [rightRank_blockTensor_rightShiftTensor, leftRank_blockTensor_rightShiftTensor]
  exact ⟨pow_pos (NeZero.pos d) _, pow_pos (NeZero.pos d) _⟩

/-- The source ranks of the right shift blocked over $k+1$ sites satisfy
$r\ell=d^{2(k+1)}$, the product identity for the blocked physical dimension
$d^{k+1}$.

Source: arXiv:1703.09188, Proposition IV.2, line 703.

**Local fix (rank-product exponent):** Source line 703 prints $d^k$; for the
blocked physical dimension the product is $d^{2k}$. See
`docs/paper-gaps/mpu_blocking_rank_product_exponent.tex`. -/
theorem rightRank_mul_leftRank_blockTensor_rightShiftTensor [NeZero d] (k : ℕ) :
    r[blockTensor (rightShiftTensor d) (k + 1)] *
        ℓ[blockTensor (rightShiftTensor d) (k + 1)] = d ^ (2 * (k + 1)) := by
  rw [rightRank_blockTensor_rightShiftTensor, leftRank_blockTensor_rightShiftTensor,
    ← pow_add]
  congr 1
  ring

/-- Every nontrivial blocking of the right shift has source-index value $\log_2 d$:
$$
\frac12\bigl(\log_2 d^{k+2}-\log_2 d^{k}\bigr)=\log_2 d.
$$

Source: arXiv:1703.09188, Definition IV.1 and Proposition IV.2, lines 681--704,
and the value of $T^{(N)}$ at lines 2037--2041. -/
theorem sourceIndexValue_blockTensor_rightShiftTensor [NeZero d] (k : ℕ) :
    sourceIndexValue (blockTensor (rightShiftTensor d) (k + 1))
        (sourceRanks_pos_blockTensor_rightShiftTensor k).1
        (sourceRanks_pos_blockTensor_rightShiftTensor k).2 =
      Real.logb 2 d := by
  rw [sourceIndexValue, rightRank_blockTensor_rightShiftTensor,
    leftRank_blockTensor_rightShiftTensor, Nat.cast_pow, Nat.cast_pow, Real.logb_pow,
    Real.logb_pow]
  push_cast
  ring

/-! ### The blocked left shift -/

/-- Blocking the left shift is the physical adjoint of blocking the right shift.

Bridge: arXiv:1703.09188, lines 390--405 and 1980--1987. -/
theorem blockTensor_leftShiftTensor (k : ℕ) :
    blockTensor (leftShiftTensor d) k =
      physicalAdjointTensor (blockTensor (rightShiftTensor d) k) := by
  rw [leftShiftTensor, physicalAdjointTensor_blockTensor]

/-- The right source rank of the left shift blocked over $k+1$ sites is $d^k$.

Source: arXiv:1703.09188, definition `defnrl`, lines 450--477, and lines
1196--1207 (adjunction exchanges the two ranks). -/
theorem rightRank_blockTensor_leftShiftTensor [NeZero d] (k : ℕ) :
    r[blockTensor (leftShiftTensor d) (k + 1)] = d ^ k := by
  rw [blockTensor_leftShiftTensor, rightRank_physicalAdjointTensor,
    leftRank_blockTensor_rightShiftTensor]

/-- The left source rank of the left shift blocked over $k+1$ sites is $d^{k+2}$.

Source: arXiv:1703.09188, definition `defnrl`, lines 450--477, and lines
1196--1207 (adjunction exchanges the two ranks). -/
theorem leftRank_blockTensor_leftShiftTensor (k : ℕ) :
    ℓ[blockTensor (leftShiftTensor d) (k + 1)] = d ^ (k + 2) := by
  rw [blockTensor_leftShiftTensor, leftRank_physicalAdjointTensor,
    rightRank_blockTensor_rightShiftTensor]

/-- The source ranks of every nontrivial blocking of the left shift are positive. -/
lemma sourceRanks_pos_blockTensor_leftShiftTensor [NeZero d] (k : ℕ) :
    0 < r[blockTensor (leftShiftTensor d) (k + 1)] ∧
      0 < ℓ[blockTensor (leftShiftTensor d) (k + 1)] := by
  rw [rightRank_blockTensor_leftShiftTensor, leftRank_blockTensor_leftShiftTensor]
  exact ⟨pow_pos (NeZero.pos d) _, pow_pos (NeZero.pos d) _⟩

/-- Every nontrivial blocking of the left shift has source-index value $-\log_2 d$.

Source: arXiv:1703.09188, Definition IV.1 and Proposition IV.2, lines 681--704,
and the value of $T^{(N)\dagger}$ at lines 2037--2041. -/
theorem sourceIndexValue_blockTensor_leftShiftTensor [NeZero d] (k : ℕ) :
    sourceIndexValue (blockTensor (leftShiftTensor d) (k + 1))
        (sourceRanks_pos_blockTensor_leftShiftTensor k).1
        (sourceRanks_pos_blockTensor_leftShiftTensor k).2 =
      -Real.logb 2 d := by
  rw [sourceIndexValue, rightRank_blockTensor_leftShiftTensor,
    leftRank_blockTensor_leftShiftTensor, Nat.cast_pow, Nat.cast_pow, Real.logb_pow,
    Real.logb_pow]
  push_cast
  ring

/-! ### The balanced families $U_2$ and $U_3$ -/

/-- Both source ranks of $U_2=T^\dagger\otimes T$ blocked over $k+1$ sites equal
$d^{2k+2}$.

Source: arXiv:1703.09188, lines 1980--2001 and the proof of Theorem `IndexTh`
(ii), lines 824--847. -/
theorem sourceRanks_blockTensor_shiftExampleU₂ [NeZero d] (k : ℕ) :
    r[blockTensor (shiftExampleU₂ d) (k + 1)] = d ^ (2 * k + 2) ∧
      ℓ[blockTensor (shiftExampleU₂ d) (k + 1)] = d ^ (2 * k + 2) := by
  rw [shiftExampleU₂, blockTensor_tensorProduct, rightRank_reindexPhysical,
    leftRank_reindexPhysical, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_blockTensor_leftShiftTensor, rightRank_blockTensor_rightShiftTensor,
    leftRank_blockTensor_leftShiftTensor, leftRank_blockTensor_rightShiftTensor,
    ← pow_add, ← pow_add]
  constructor <;> congr 1 <;> ring

/-- Both source ranks of $U_3=T\otimes T^\dagger$ blocked over $k+1$ sites equal
$d^{2k+2}$.

Source: arXiv:1703.09188, lines 1980--2001 and the proof of Theorem `IndexTh`
(ii), lines 824--847. -/
theorem sourceRanks_blockTensor_shiftExampleU₃ [NeZero d] (k : ℕ) :
    r[blockTensor (shiftExampleU₃ d) (k + 1)] = d ^ (2 * k + 2) ∧
      ℓ[blockTensor (shiftExampleU₃ d) (k + 1)] = d ^ (2 * k + 2) := by
  rw [shiftExampleU₃, blockTensor_tensorProduct, rightRank_reindexPhysical,
    leftRank_reindexPhysical, rightRank_tensorProduct, leftRank_tensorProduct,
    rightRank_blockTensor_leftShiftTensor, rightRank_blockTensor_rightShiftTensor,
    leftRank_blockTensor_leftShiftTensor, leftRank_blockTensor_rightShiftTensor,
    ← pow_add, ← pow_add]
  constructor <;> congr 1 <;> ring

/-- The source ranks of every nontrivial blocking of $U_2$ are positive. -/
lemma sourceRanks_pos_blockTensor_shiftExampleU₂ [NeZero d] (k : ℕ) :
    0 < r[blockTensor (shiftExampleU₂ d) (k + 1)] ∧
      0 < ℓ[blockTensor (shiftExampleU₂ d) (k + 1)] := by
  rw [(sourceRanks_blockTensor_shiftExampleU₂ k).1, (sourceRanks_blockTensor_shiftExampleU₂ k).2]
  exact ⟨pow_pos (NeZero.pos d) _, pow_pos (NeZero.pos d) _⟩

/-- Every nontrivial blocking of $U_2$ has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2041. -/
theorem sourceIndexValue_blockTensor_shiftExampleU₂ [NeZero d] (k : ℕ) :
    sourceIndexValue (blockTensor (shiftExampleU₂ d) (k + 1))
        (sourceRanks_pos_blockTensor_shiftExampleU₂ k).1
        (sourceRanks_pos_blockTensor_shiftExampleU₂ k).2 = 0 :=
  sourceIndexValue_eq_zero_of_rightRank_eq_leftRank _ _ _
    ((sourceRanks_blockTensor_shiftExampleU₂ k).1.trans
      (sourceRanks_blockTensor_shiftExampleU₂ k).2.symm)

/-- The source ranks of every nontrivial blocking of $U_3$ are positive. -/
lemma sourceRanks_pos_blockTensor_shiftExampleU₃ [NeZero d] (k : ℕ) :
    0 < r[blockTensor (shiftExampleU₃ d) (k + 1)] ∧
      0 < ℓ[blockTensor (shiftExampleU₃ d) (k + 1)] := by
  rw [(sourceRanks_blockTensor_shiftExampleU₃ k).1, (sourceRanks_blockTensor_shiftExampleU₃ k).2]
  exact ⟨pow_pos (NeZero.pos d) _, pow_pos (NeZero.pos d) _⟩

/-- Every nontrivial blocking of $U_3$ has source-index value zero.

Source: arXiv:1703.09188, lines 2037--2041. -/
theorem sourceIndexValue_blockTensor_shiftExampleU₃ [NeZero d] (k : ℕ) :
    sourceIndexValue (blockTensor (shiftExampleU₃ d) (k + 1))
        (sourceRanks_pos_blockTensor_shiftExampleU₃ k).1
        (sourceRanks_pos_blockTensor_shiftExampleU₃ k).2 = 0 :=
  sourceIndexValue_eq_zero_of_rightRank_eq_leftRank _ _ _
    ((sourceRanks_blockTensor_shiftExampleU₃ k).1.trans
      (sourceRanks_blockTensor_shiftExampleU₃ k).2.symm)

/-! ### Simplicity of the shifts at every blocking -/

/-- The right-shift tensor is simple. Its double-layer letters are
$W^{ik}=|\Phi)(ik|$ with $\Phi=\sum_j|jj)$, so the boundary vectors
$a=|00)$ and $b=\Phi$ satisfy both simplicity identities.

Source: arXiv:1703.09188, Definition III.2, lines 363--374, for the tensor at
lines 1980--1987. -/
theorem rightShiftTensor_isMPUSimple (d : ℕ) [NeZero d] :
    IsMPUSimple (rightShiftTensor d) := by
  classical
  let Φ : Fin (d * d) → ℂ := fun x ↦
    if (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm x).2 then 1 else 0
  let e : Fin d → Fin d → Fin (d * d) → ℂ := fun i k ↦ Pi.single (finProdFinEquiv (i, k)) 1
  have hW : ∀ i k, doubleLayerTensor (rightShiftTensor d) i k = Matrix.vecMulVec Φ (e i k) := by
    intro i k
    ext x y
    obtain ⟨⟨x₁, x₂⟩, rfl⟩ := finProdFinEquiv.surjective x
    obtain ⟨⟨y₁, y₂⟩, rfl⟩ := finProdFinEquiv.surjective y
    simp only [doubleLayerTensor_apply, rightShiftTensor, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
      physicalAdjointTensor_apply, Matrix.single_apply, RCLike.star_def,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero,
      finProdFinEquiv_symm_apply, Matrix.vecMulVec_apply, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq, Φ, e]
    rw [Fintype.sum_eq_single x₂ (fun c hc ↦ by simp [hc])]
    split_ifs <;> grind
  have hΦe : ∀ i k, e i k ⬝ᵥ Φ = if i = k then 1 else 0 := by
    intro i k
    simp [e, Φ]
  refine ⟨e 0 0, Φ, fun i j ↦ ?_, fun i j k l ↦ ?_⟩
  · rw [hW, Matrix.vecMulVec_mulVec, hΦe]
    split_ifs <;> simp [hΦe]
  · simp only [hW, Matrix.vecMulVec_mul_vecMulVec, smul_dotProduct, hΦe]
    simp

/-- The left-shift tensor is simple. Its double-layer letters are
$W^{ik}=|ik)(\Phi|$, so the boundary vectors $a=\Phi$ and $b=|00)$ satisfy both
simplicity identities.

Source: arXiv:1703.09188, Definition III.2, lines 363--374, for the adjoint of the
tensor at lines 1980--1987. -/
theorem leftShiftTensor_isMPUSimple (d : ℕ) [NeZero d] :
    IsMPUSimple (leftShiftTensor d) := by
  classical
  let Φ : Fin (d * d) → ℂ := fun x ↦
    if (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm x).2 then 1 else 0
  let e : Fin d → Fin d → Fin (d * d) → ℂ := fun i k ↦ Pi.single (finProdFinEquiv (i, k)) 1
  have hW : ∀ i k, doubleLayerTensor (leftShiftTensor d) i k = Matrix.vecMulVec (e i k) Φ := by
    intro i k
    ext x y
    obtain ⟨⟨x₁, x₂⟩, rfl⟩ := finProdFinEquiv.surjective x
    obtain ⟨⟨y₁, y₂⟩, rfl⟩ := finProdFinEquiv.surjective y
    simp only [leftShiftTensor, doubleLayerTensor_apply,
      physicalAdjointTensor_physicalAdjointTensor, rightShiftTensor, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single_apply,
      physicalAdjointTensor_apply, RCLike.star_def, MonoidWithZeroHom.map_ite_one_zero, mul_ite,
      mul_one, mul_zero, finProdFinEquiv_symm_apply, Matrix.vecMulVec_apply, Pi.single_apply,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat, e, Φ]
    rw [Fintype.sum_eq_single y₂ (fun c hc ↦ by simp [hc])]
    split_ifs <;> grind
  have hΦe : ∀ i k, Φ ⬝ᵥ e i k = if i = k then 1 else 0 := by
    intro i k
    simp [e, Φ]
  refine ⟨Φ, e 0 0, fun i j ↦ ?_, fun i j k l ↦ ?_⟩
  · rw [hW, Matrix.vecMulVec_mulVec]
    simp [hΦe]
  · simp only [hW, Matrix.vecMulVec_mul_vecMulVec, smul_dotProduct, hΦe]
    simp

/-- Every nontrivial blocking of the right shift is simple.

Source: arXiv:1703.09188, Definition III.2, lines 363--374, and the blocked
tensors ${\cal U}_k$ of Definition IV.1, lines 681--686. -/
theorem blockTensor_rightShiftTensor_isMPUSimple (d : ℕ) [NeZero d] (k : ℕ) :
    IsMPUSimple (blockTensor (rightShiftTensor d) (k + 1)) :=
  (rightShiftTensor_isMPUSimple d).blockTensor (k + 1) k.succ_pos

/-- Every nontrivial blocking of the left shift is simple.

Source: arXiv:1703.09188, Definition III.2, lines 363--374, and the blocked
tensors ${\cal U}_k$ of Definition IV.1, lines 681--686. -/
theorem blockTensor_leftShiftTensor_isMPUSimple (d : ℕ) [NeZero d] (k : ℕ) :
    IsMPUSimple (blockTensor (leftShiftTensor d) (k + 1)) :=
  (leftShiftTensor_isMPUSimple d).blockTensor (k + 1) k.succ_pos

/-! ### Rank obstruction -/

/-- For $d>1$, no nontrivial blocking of the right shift has equal source ranks:
$r=d^{k+2}\ne d^k=\ell$.

Source: arXiv:1703.09188, lines 2037--2041 (the shift has nonzero index) and
line 2308 (a depth-two circuit of nearest-neighbour gates is the standard form,
whose two gate outputs have the dimensions $\ell$ and $r$). -/
theorem rightRank_blockTensor_rightShiftTensor_ne_leftRank (hd : 1 < d) (k : ℕ) :
    r[blockTensor (rightShiftTensor d) (k + 1)] ≠
      ℓ[blockTensor (rightShiftTensor d) (k + 1)] := by
  have : NeZero d := ⟨by omega⟩
  rw [rightRank_blockTensor_rightShiftTensor, leftRank_blockTensor_rightShiftTensor]
  intro h
  have := Nat.pow_right_injective hd h
  omega

/-- For $d>1$, the source-index value of every nontrivial blocking of the right
shift is nonzero.

Source: arXiv:1703.09188, lines 2037--2041. -/
theorem sourceIndexValue_blockTensor_rightShiftTensor_ne_zero [NeZero d] (hd : 1 < d)
    (k : ℕ) :
    sourceIndexValue (blockTensor (rightShiftTensor d) (k + 1))
        (sourceRanks_pos_blockTensor_rightShiftTensor k).1
        (sourceRanks_pos_blockTensor_rightShiftTensor k).2 ≠ 0 := by
  rw [sourceIndexValue_blockTensor_rightShiftTensor]
  exact (Real.logb_pos (by norm_num) (by exact_mod_cast hd)).ne'

end MPOTensor
