/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Examples.AKLT
import TNLean.MPS.Symmetry.StringOrder
import TNLean.MPS.Chain.BlockedChainFT

/-!
# String order of the AKLT state under its `Z₂ × Z₂` symmetry

This module exhibits the AKLT state as a witness of the string-order criterion of
Pérez-García, Wolf, Sanz, Verstraete, Cirac (arXiv:0802.0447).  The single-site
AKLT tensor is not injective, only normal (`2`-block injective), so the criterion
is applied to the length-`2` blocked tensor, which is injective.

## Main definitions

* `akltBlocked` : the length-`2` blocked AKLT tensor (physical dimension `9`)
* `akltBlockedZ2Z2Action` : the `Z₂ × Z₂` on-site representation on the blocked
  physical space, the Kronecker squares of the two spin-`1` `π`-rotations

## Main results

* `akltBlocked_isInjective` : the blocked tensor is injective
* `aklt_blocked_isOnSiteSymmetric_Z2Z2` : the blocked tensor is on-site symmetric
  under `Z₂ × Z₂`
* `aklt_hasStringOrder` : the blocked AKLT tensor has string order under every
  element of its `Z₂ × Z₂` symmetry, with the maximally mixed boundary state

## References

* Affleck, Kennedy, Lieb, Tasaki (1987) — original AKLT construction
* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447 (PRL 2008) —
  string order and local symmetry for finitely correlated states
* RMP review (arXiv:2011.12127) Section III.A
-/

open scoped Matrix BigOperators
open Matrix Finset MPSTensor

noncomputable section

namespace MPSTensor

/-! ### The Kronecker-power physical action through blocking

For a physical-index operator `P` on `Fin d`, the blocked operator `blockKron`
acts on the blocked physical index `Fin (blockPhysDim d L)` by the entrywise
product of `P` over the `L` decoded sites.  This is the operator that makes
blocking commute with physical twisting. -/

variable {d D : ℕ}

/-- The Kronecker-power lift of a physical-index operator `P` through length-`L`
blocking: `(blockKron P) I J = ∏ k, P (decode I k) (decode J k)`. -/
noncomputable def blockKron (L : ℕ) (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (blockPhysDim d L)) (Fin (blockPhysDim d L)) ℂ :=
  fun I J => ∏ k : Fin L, P (decodeBlock d L I k) (decodeBlock d L J k)

/-- `decodeBlock` is a bijection of the blocked index onto length-`L` words. -/
noncomputable def decodeBlockEquiv (d L : ℕ) :
    Fin (blockPhysDim d L) ≃ (Fin L → Fin d) :=
  (finCongr (blockPhysDim_eq_pow d L)).trans finFunctionFinEquiv.symm

@[simp] lemma decodeBlockEquiv_apply (d L : ℕ) (I : Fin (blockPhysDim d L)) :
    decodeBlockEquiv d L I = decodeBlock d L I := rfl

@[simp] lemma decodeBlock_decodeBlockEquiv_symm (d L : ℕ) (w : Fin L → Fin d) :
    decodeBlock d L ((decodeBlockEquiv d L).symm w) = w := by
  rw [← decodeBlockEquiv_apply, Equiv.apply_symm_apply]

/-- The Kronecker lift is multiplicative: `blockKron L (P * Q) = blockKron L P *
blockKron L Q`.  Summing over the intermediate blocked index is summing over
length-`L` words, and the product distributes site by site. -/
lemma blockKron_mul (L : ℕ) (P Q : Matrix (Fin d) (Fin d) ℂ) :
    blockKron L (P * Q) = blockKron L P * blockKron L Q := by
  classical
  ext I J
  simp only [blockKron, Matrix.mul_apply]
  -- Sum over the intermediate blocked index = sum over words.
  rw [← Equiv.sum_comp (decodeBlockEquiv d L).symm
    (fun K => (∏ k : Fin L, P (decodeBlock d L I k) (decodeBlock d L K k)) *
      ∏ k : Fin L, Q (decodeBlock d L K k) (decodeBlock d L J k))]
  simp only [decodeBlock_decodeBlockEquiv_symm]
  -- Distribute the product over the sum of words.
  rw [Finset.prod_univ_sum (t := fun _ : Fin L => (Finset.univ : Finset (Fin d)))
    (f := fun (k : Fin L) (a : Fin d) =>
      P (decodeBlock d L I k) a * Q a (decodeBlock d L J k)),
    Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.prod_mul_distrib]

/-- The Kronecker lift of the identity is the identity. -/
lemma blockKron_one (L : ℕ) :
    blockKron L (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  classical
  ext I J
  simp only [blockKron, Matrix.one_apply]
  by_cases hIJ : I = J
  · simp [hIJ]
  · rw [if_neg hIJ]
    -- Some site differs, contributing a zero factor.
    have : ∃ k : Fin L, decodeBlock d L I k ≠ decodeBlock d L J k := by
      by_contra hcon
      rw [not_exists] at hcon
      exact hIJ ((decodeBlockEquiv d L).injective (funext fun k => not_not.1 (hcon k)))
    obtain ⟨k, hk⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ k) (Matrix.one_apply_ne hk)

/-- The Kronecker lift commutes with the conjugate transpose:
`(blockKron L P)ᴴ = blockKron L (Pᴴ)`. -/
lemma blockKron_conjTranspose (L : ℕ) (P : Matrix (Fin d) (Fin d) ℂ) :
    (blockKron L P)ᴴ = blockKron L Pᴴ := by
  ext I J
  simp only [Matrix.conjTranspose_apply, blockKron, star_prod]

/-- The Kronecker power preserves unitarity: if `P * Pᴴ = 1` then
`blockKron L P * (blockKron L P)ᴴ = 1`. -/
lemma blockKron_mul_conjTranspose (L : ℕ) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P * Pᴴ = 1) :
    blockKron L P * (blockKron L P)ᴴ = 1 := by
  rw [blockKron_conjTranspose, ← blockKron_mul, hP, blockKron_one]

/-- The `Z₂ × Z₂` (or any) on-site representation lifted to the blocked physical
space by the Kronecker power of each group element's physical action. -/
noncomputable def blockKronAction {G : Type*} [Monoid G] (L : ℕ)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) :
    G →* Matrix (Fin (blockPhysDim d L)) (Fin (blockPhysDim d L)) ℂ where
  toFun g := blockKron L (U g)
  map_one' := by rw [map_one, blockKron_one]
  map_mul' g h := by rw [map_mul, blockKron_mul]

@[simp] lemma blockKronAction_apply {G : Type*} [Monoid G] (L : ℕ)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    blockKronAction L U g = blockKron L (U g) := rfl

/-! ### Twisting commutes with blocking

The word evaluation of a twisted tensor expands into a sum over words, with the
physical matrix elements distributing as the Kronecker power.  This is the
identity that makes twisting by `blockKronAction` agree with blocking the twisted
tensor. -/

/-- Word evaluation of a twisted tensor expands over the intermediate word: for a
length-`L` index function `b`,
`evalWord (twistedTensor A U g) (List.ofFn b) =
  ∑ v, (∏ k, (U g) (b k) (v k)) • evalWord A (List.ofFn v)`. -/
lemma evalWord_twistedTensor_ofFn {G : Type*} [Monoid G]
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    ∀ {L : ℕ} (b : Fin L → Fin d),
      evalWord (twistedTensor A U g) (List.ofFn b) =
        ∑ v : Fin L → Fin d,
          (∏ k : Fin L, (U g) (b k) (v k)) • evalWord A (List.ofFn v) := by
  classical
  intro L
  induction L with
  | zero =>
    intro b
    simp only [List.ofFn_zero, evalWord_nil]
    rw [Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  | succ L ih =>
    intro b
    rw [List.ofFn_succ, evalWord_cons, twistedTensor, ih (fun i => b i.succ)]
    -- Head sum times tail sum; distribute and reindex over `Fin.cons`.
    rw [Finset.sum_mul]
    -- Reindex the sum over `Fin (L+1) → Fin d` via `Fin.consEquiv`.
    rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => Fin d)).sum_comp]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.smul_mul, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    -- Evaluate the consed word and the product over `Fin (L+1)`.
    have heval : evalWord A (List.ofFn ((Fin.consEquiv fun _ : Fin (L + 1) => Fin d) (a, w)))
        = A a * evalWord A (List.ofFn w) := by
      simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, evalWord_cons,
        Fin.cons_succ]
    rw [heval]
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ,
      Matrix.mul_smul, smul_smul]

/-- Twisting by `blockKronAction` agrees with blocking the twisted tensor:
`twistedTensor (blockTensor A L) (blockKronAction L U) g = blockTensor
(twistedTensor A U g) L`. -/
lemma twistedTensor_blockTensor_comm {G : Type*} [Monoid G]
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) (L : ℕ) :
    twistedTensor (blockTensor A L) (blockKronAction L U) g =
      blockTensor (twistedTensor A U g) L := by
  classical
  funext I
  rw [twistedTensor]
  simp only [blockKronAction_apply, blockKron, blockTensor, wordOfBlock]
  rw [evalWord_twistedTensor_ofFn A U g (decodeBlock d L I)]
  -- Reindex the sum over words by the blocked index.
  rw [← (decodeBlockEquiv d L).sum_comp]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  simp [decodeBlockEquiv_apply]

/-- On-site symmetry transfers to the blocked tensor under the Kronecker-power
action: if `A` is on-site symmetric under `U`, then `blockTensor A L` is on-site
symmetric under `blockKronAction L U`.  Blocking preserves the underlying matrix
product vector family, so no injectivity of `A` is needed. -/
theorem isOnSiteSymmetric_blockTensor {G : Type*} [Monoid G]
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (L : ℕ)
    (hSymm : IsOnSiteSymmetric A U) :
    IsOnSiteSymmetric (blockTensor A L) (blockKronAction L U) := by
  intro g
  rw [twistedTensor_blockTensor_comm]
  exact (hSymm g).blockTensor L

/-! ### The length-`2` blocked AKLT tensor and its string order

The single-site AKLT tensor is not injective, only normal; the string-order
criterion requires injectivity, so it is applied to the length-`2` blocked
tensor.  The on-site `Z₂ × Z₂` symmetry of the single-site tensor lifts to the
blocked tensor through the Kronecker-power action above. -/

section AKLT

open scoped ComplexOrder MatrixOrder

/-- The length-`2` blocked AKLT tensor (physical dimension `9 = 3²`). -/
noncomputable def akltBlocked : MPSTensor (blockPhysDim 3 2) 2 :=
  blockTensor akltTensor 2

/-- The length-`2` blocked AKLT tensor is injective: its matrices span `M₂(ℂ)`.
This is the blocked-tensor form of `aklt_isNBlkInjective_two`. -/
theorem akltBlocked_isInjective : IsInjective akltBlocked :=
  (isNBlkInjective_iff_blockTensor_isInjective akltTensor 2).1 aklt_isNBlkInjective_two

/-- The `Z₂ × Z₂` on-site representation on the blocked AKLT physical space, the
Kronecker square of the two single-site spin-`1` `π`-rotations. -/
noncomputable def akltBlockedZ2Z2Action :
    Multiplicative (ZMod 2 × ZMod 2) →*
      Matrix (Fin (blockPhysDim 3 2)) (Fin (blockPhysDim 3 2)) ℂ :=
  blockKronAction 2 akltZ2Z2Action

/-- The blocked AKLT tensor is on-site symmetric under `Z₂ × Z₂`, with each group
element acting by the Kronecker square of the corresponding spin-`1` `π`-rotation.
The bond gauges are the same anticommuting virtual gauges `σz` and `iσy` as for
the single-site tensor, so the blocked tensor realizes the same non-trivial SPT
phase. -/
theorem aklt_blocked_isOnSiteSymmetric_Z2Z2 :
    IsOnSiteSymmetric akltBlocked akltBlockedZ2Z2Action :=
  isOnSiteSymmetric_blockTensor akltTensor akltZ2Z2Action 2 aklt_isOnSiteSymmetric_Z2Z2

/-! #### Normalization of the blocked AKLT transfer map -/

/-- The single-site AKLT tensor is right-canonical: `∑ Aᵢ Aᵢ† = 1`.  This is the
matrix-identity value of `aklt_transferMap_one`. -/
private theorem aklt_sum_mul_conjTranspose :
    ∑ i : Fin 3, akltTensor i * (akltTensor i)ᴴ = 1 := by
  have h := aklt_transferMap_one
  rw [transferMap_apply] at h
  simpa only [Matrix.mul_one] using h

/-- The single-site AKLT tensor is left-canonical: `∑ Aᵢ† Aᵢ = 1`.  Together with
right-canonicity this makes the channel both trace preserving and unital. -/
private theorem aklt_sum_conjTranspose_mul :
    ∑ i : Fin 3, (akltTensor i)ᴴ * akltTensor i = 1 := by
  rw [Fin.sum_univ_three]
  simp only [akltTensor_conjTranspose]
  ext a b
  simp only [akltTensor, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
    mul_neg, neg_mul, neg_neg, Matrix.one_apply]
  have hdiag : (↑(1 / Real.sqrt 3) : ℂ) * ↑(1 / Real.sqrt 3) +
      (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) * ↑(Real.sqrt 2 / Real.sqrt 3) = 1 := by
    have hr : (1 / Real.sqrt 3) * (1 / Real.sqrt 3) +
        (Real.sqrt 2 / Real.sqrt 3) * (Real.sqrt 2 / Real.sqrt 3) = 1 := by
      rw [div_mul_div_comm, div_mul_div_comm, one_mul,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3),
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, hr,
      Complex.ofReal_one]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_ne_zero, zero_ne_one, if_true, if_false, mul_zero,
      zero_mul, mul_one, add_zero, zero_add, neg_zero, mul_neg, neg_mul, neg_neg] <;>
    first
      | rfl
      | exact hdiag

/-- The blocked AKLT transfer map is unital: `∑ Bᵢ Bᵢ† = 1`.  Right-canonicity of
the single-site letters propagates to length-`2` words. -/
private theorem akltBlocked_transferMap_one : transferMap akltBlocked 1 = 1 := by
  classical
  rw [transferMap_apply]
  simp only [Matrix.mul_one, akltBlocked, blockTensor, wordOfBlock]
  rw [Fintype.sum_equiv (decodeBlockEquiv 3 2)
    (fun I => evalWord akltTensor (List.ofFn (decodeBlock 3 2 I)) *
      (evalWord akltTensor (List.ofFn (decodeBlock 3 2 I)))ᴴ)
    (fun ρ => evalWord akltTensor (List.ofFn ρ) * (evalWord akltTensor (List.ofFn ρ))ᴴ)
    (fun I => by rw [decodeBlockEquiv_apply])]
  exact sum_evalWord_mul_conjTranspose_evalWord akltTensor aklt_sum_mul_conjTranspose 2

/-- The maximally mixed boundary state `Λ = (1/2)·1` is a fixed point of the
blocked adjoint transfer map: `∑ Bᵢ† Λ Bᵢ = Λ`.  Left-canonicity of the
single-site letters propagates to length-`2` words. -/
private theorem akltBlocked_adjoint_fixes_maximallyMixed :
    transferMap (fun i => (akltBlocked i)ᴴ) ((1 / 2 : ℂ) • 1) = (1 / 2 : ℂ) • 1 := by
  classical
  have hleft : ∑ i : Fin (blockPhysDim 3 2),
      (akltBlocked i)ᴴ * akltBlocked i = 1 := by
    simpa only [akltBlocked] using
      leftCanonical_blockTensor akltTensor 2 aklt_sum_conjTranspose_mul
  rw [transferMap_apply]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]
  rw [← Finset.smul_sum, hleft]

/-- The blocked `Z₂ × Z₂` representation is unitary on every group element.  The
single-site representation is unitary (`aklt_isUnitary_Z2Z2`) and the Kronecker
power preserves unitarity. -/
private theorem akltBlockedZ2Z2Action_unitary (g : Multiplicative (ZMod 2 × ZMod 2)) :
    akltBlockedZ2Z2Action g * (akltBlockedZ2Z2Action g)ᴴ = 1 := by
  rw [akltBlockedZ2Z2Action, blockKronAction_apply]
  exact blockKron_mul_conjTranspose 2 (akltZ2Z2Action g) (aklt_isUnitary_Z2Z2 g)

/-- **The AKLT state has string order under its `Z₂ × Z₂` symmetry.**

For every group element `g`, the length-`2` blocked AKLT tensor has string order
with the maximally mixed boundary state `Λ = (1/2)·1`.  The blocked tensor is
injective and on-site symmetric, the maximally mixed state is a positive definite,
trace-one fixed point of the adjoint transfer map, and the transfer map itself is
unital; an injective, on-site symmetric tensor meeting these conditions has string
order for every group element (see `hasStringOrder_of_symmetric_injective`).

Like the cluster state, the AKLT state thus witnesses the string-order criterion of
Pérez-García, Wolf, Sanz, Verstraete, Cirac (arXiv:0802.0447); it carries the same
caveat on the virtual-boundary form of the string order parameter recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`. -/
theorem aklt_hasStringOrder (g : Multiplicative (ZMod 2 × ZMod 2)) :
    HasStringOrder akltBlocked (akltBlockedZ2Z2Action g)
      ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
  hasStringOrder_of_symmetric_injective akltBlocked akltBlocked_isInjective
    akltBlockedZ2Z2Action aklt_blocked_isOnSiteSymmetric_Z2Z2 akltBlockedZ2Z2Action_unitary g
    ((1 / 2 : ℂ) • 1)
    (by
      have h : (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
          (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        ext i j; simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      rw [h]; exact Matrix.PosDef.one.smul (by norm_num))
    (by rw [Matrix.trace_smul, Matrix.trace_one]; norm_num)
    akltBlocked_adjoint_fixes_maximallyMixed akltBlocked_transferMap_one

end AKLT

end MPSTensor

end
