/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.MatrixAction
import TNLean.PEPS.Approximation.PartyLayout

/-!
# Euclidean registers at the front of a layout

This file provides the calculus used to read explicit matrices as allowed monomials of
Theorem 5.2 of the polynomial-PEPS manuscript.  A register `ℂ^α` of a party is a Euclidean
register; one or two Euclidean registers at the front of a layout are identified with `ℂ^α`
(`oneIso`) or with `ℂ^{α × β}` (`twoIso`), and a matrix acts on them through
`EncodedFrame.act`.  A local map built from a matrix on such registers acts, under these
identifications, as the matrix tensored with the identity of the untouched registers
(`eval_localMap`).

It also records which parties a monomial uses: `Word.UsesOnly S` says that every local map
of a word acts at a party of `S` and every pair source joins two parties of `S`, and
`Word.sourceCount` counts its pair sources; `PartyChain.UsesOnly` and
`PartyChain.sourceCount` extend these to monomials with pair effects.

## Main definitions

* `PairEffect.Word.UsesOnly`, `PairEffect.Word.sourceCount`,
  `PairEffect.PartyChain.UsesOnly`, `PairEffect.PartyChain.sourceCount`.
* `PairEffect.oneIso`, `PairEffect.twoIso` : one or two Euclidean registers as a Euclidean
  space.
* `PairEffect.matLocal₂₁`, `PairEffect.matLocal₁₂`, `PairEffect.matLocal₂₂` : local maps given
  by matrices on one or two registers of one party.

## Main results

* `PairEffect.pairHeadIso_eq` : the identification of a front pair register is the
  concatenation identification followed by `twoIso`.
* `PairEffect.eval_localMap`, `PairEffect.eval_localMap₂₁`, `PairEffect.eval_localMap₁₂`,
  `PairEffect.pairHeadIso_eval_localMap₂₂` : the operator of a local map on the front
  registers.

## References

* Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
  lines 21–35.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Matrix.Norms.L2Operator

namespace TNLean.PEPS.PairEffect

open EuclideanSpace ContinuousLinearMap Matrix
open EncodedFrame (act)

variable {P : Type}

/-! ### The parties used by a monomial -/

namespace Word

/-- A word uses only the parties of `S` when each of its local maps acts at a party of `S`
and each of its pair sources joins two parties of `S`.  Exchanges of tensor factors use no
party.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35 and
`05-frames.tex`, lines 99–102: a bounded change uses a fixed list of parties. -/
def UsesOnly (S : Set P) : {ℓ ℓ' : Layout P} → Word ℓ ℓ' → Prop
  | _, _, id _ => True
  | _, _, comp w w' => w.UsesOnly S ∧ w'.UsesOnly S
  | _, _, localMap p _ _ _ _ => p ∈ S
  | _, _, source (p := p) (q := q) _ _ _ _ _ => p ∈ S ∧ q ∈ S
  | _, _, swap .. => True
  | _, _, frame _ w => w.UsesOnly S

/-- The number of pair sources of a word. -/
def sourceCount : {ℓ ℓ' : Layout P} → Word ℓ ℓ' → ℕ
  | _, _, id _ => 0
  | _, _, comp w w' => w.sourceCount + w'.sourceCount
  | _, _, localMap .. => 0
  | _, _, source .. => 1
  | _, _, swap .. => 0
  | _, _, frame _ w => w.sourceCount

end Word

namespace PartyChain

/-- A monomial uses only the parties of `S` when its words do and each of its pair effects
joins two parties of `S`. -/
def UsesOnly (S : Set P) : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Prop
  | _, _, final w => w.UsesOnly S
  | _, _, effect (p := p) (q := q) _ _ _ _ w _ rest =>
      p ∈ S ∧ q ∈ S ∧ w.UsesOnly S ∧ rest.UsesOnly S

/-- The number of pair sources of a monomial. -/
def sourceCount : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → ℕ
  | _, _, final w => w.sourceCount
  | _, _, effect _ _ _ _ w _ rest => w.sourceCount + rest.sourceCount

end PartyChain

/-! ### Matrices on Euclidean registers -/

section Euclidean

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- One Euclidean register, identified with its space. -/
def oneIso (p : P) (α : Type) [Fintype α] : Mem [⟨p, euc α⟩] ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  TensorProduct.ridIsometry ℂ (EuclideanSpace ℂ α)

/-- `oneIso` on a pure tensor. -/
@[simp]
theorem oneIso_tmul (p : P) (x : EuclideanSpace ℂ α) (c : ℂ) :
    oneIso p α (x ⊗ₜ c) = c • x := by
  simp [oneIso]

/-- The inverse of `oneIso` adjoins the scalar `1`. -/
theorem oneIso_symm_apply (p : P) (x : EuclideanSpace ℂ α) :
    (oneIso p α).symm x = (x ⊗ₜ (1 : ℂ) : Mem [⟨p, euc α⟩]) := by
  rw [LinearIsometryEquiv.symm_apply_eq, oneIso_tmul, one_smul]

/-- Two Euclidean registers `ℂ^α` and `ℂ^β`, identified with `ℂ^{α × β}`. -/
def twoIso (p p' : P) (α β : Type) [Fintype α] [Fintype β] :
    Mem [⟨p, euc α⟩, ⟨p', euc β⟩] ≃ₗᵢ[ℂ] EuclideanSpace ℂ (α × β) :=
  ((TensorProduct.ridIsometry ℂ (EuclideanSpace ℂ β)).lTensor (EuclideanSpace ℂ α)).trans
    (pairIso α β)

/-- `twoIso` on a pure tensor. -/
@[simp]
theorem twoIso_tmul (p p' : P) (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) (c : ℂ) :
    twoIso p p' α β (x ⊗ₜ (y ⊗ₜ c)) = c • pairIso α β (x ⊗ₜ y) := by
  simp [twoIso, LinearIsometryEquiv.lTensor, TensorProduct.tmul_smul]

/-- The inverse of `twoIso` on a product vector. -/
theorem twoIso_symm_pairIso (p p' : P) (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) :
    (twoIso p p' α β).symm (pairIso α β (x ⊗ₜ y)) =
      (x ⊗ₜ (y ⊗ₜ (1 : ℂ)) : Mem [⟨p, euc α⟩, ⟨p', euc β⟩]) := by
  rw [LinearIsometryEquiv.symm_apply_eq, twoIso_tmul, one_smul]

/-! ### The concatenation identification on pure tensors -/

/-- Concatenating the empty layout adjoins the scalar `1`. -/
theorem appendIso_nil_apply (ℓ : Layout P) (w : Mem ℓ) :
    appendIso ([] : Layout P) ℓ w = (1 : ℂ) ⊗ₜ w :=
  rfl

/-- Concatenation of one register on pure tensors. -/
theorem appendIso_one_tmul (r : Reg P) (ℓ : Layout P) (x : r.space) (w : Mem ℓ) :
    appendIso [r] ℓ (x ⊗ₜ w) = (x ⊗ₜ (1 : ℂ)) ⊗ₜ w := by
  simp [appendIso, LinearIsometryEquiv.lTensor]

/-- The inverse of the concatenation with the empty layout is the scalar action. -/
theorem appendIso_nil_symm_tmul (ℓ : Layout P) (a : ℂ) (w : Mem ℓ) :
    (appendIso ([] : Layout P) ℓ).symm (a ⊗ₜ w) = a • w := by
  change TensorProduct.lidIsometry ℂ (Mem ℓ) (a ⊗ₜ w) = _
  simp

/-- The inverse of the concatenation of one register on pure tensors. -/
theorem appendIso_one_symm_tmul (r : Reg P) (ℓ : Layout P) (x : r.space) (w : Mem ℓ) :
    (appendIso [r] ℓ).symm ((x ⊗ₜ (1 : ℂ)) ⊗ₜ w) = (x ⊗ₜ w : Mem (r :: ℓ)) := by
  rw [LinearIsometryEquiv.symm_apply_eq, appendIso_one_tmul]

/-- Concatenation of two registers on pure tensors. -/
theorem appendIso_two_tmul (r r' : Reg P) (ℓ : Layout P) (x : r.space) (y : r'.space)
    (w : Mem ℓ) :
    appendIso [r, r'] ℓ (x ⊗ₜ (y ⊗ₜ w)) = (x ⊗ₜ (y ⊗ₜ (1 : ℂ))) ⊗ₜ w := by
  simp [appendIso, LinearIsometryEquiv.lTensor]

/-- A front Euclidean register is identified by `oneIso`. -/
theorem appendIso_one_symm (p : P) (ℓ : Layout P) (x : EuclideanSpace ℂ α) (w : Mem ℓ) :
    (appendIso [⟨p, euc α⟩] ℓ).symm ((oneIso p α).symm x ⊗ₜ w) =
      (x ⊗ₜ w : Mem (⟨p, euc α⟩ :: ℓ)) := by
  rw [LinearIsometryEquiv.symm_apply_eq, appendIso_one_tmul, oneIso_symm_apply]

/-- The identification of a front pair register is the concatenation identification followed
by `twoIso`. -/
theorem pairHeadIso_eq {p q : P} (ℓ : Layout P) (z : Mem (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ)) :
    pairHeadIso ℓ z = (isoL (twoIso p q α β)).rTensor (Mem ℓ) (appendIso _ ℓ z) := by
  induction z using tmul₃_induction with
  | tmul x y w =>
      rw [pairHeadIso_tmul]
      erw [appendIso_two_tmul]
      rw [rTensor_tmul, isoL_apply, twoIso_tmul, one_smul]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- A front pair register given through `twoIso` and the concatenation identification is read
back by `pairHeadIso`. -/
theorem pairHeadIso_appendIso_symm {p q : P} (ℓ : Layout P) (v : EuclideanSpace ℂ (α × β))
    (w : Mem ℓ) :
    pairHeadIso ℓ ((appendIso [⟨p, euc α⟩, ⟨q, euc β⟩] ℓ).symm ((twoIso p q α β).symm v ⊗ₜ w)) =
      v ⊗ₜ w := by
  rw [pairHeadIso_eq]
  erw [LinearIsometryEquiv.apply_symm_apply]
  rw [rTensor_tmul, isoL_apply, LinearIsometryEquiv.apply_symm_apply]

/-! ### Local maps given by matrices -/

/-- The local map of a matrix from two registers `ℂ^α`, `ℂ^β` of `p` to one register `ℂ^γ`
of `p`. -/
def matLocal₂₁ [DecidableEq α] [DecidableEq β] (p : P) (A : Matrix γ (α × β) ℂ) :
    Mem [⟨p, euc α⟩, ⟨p, euc β⟩] →L[ℂ] Mem [⟨p, euc γ⟩] :=
  isoL (oneIso p γ).symm ∘L act A ∘L isoL (twoIso p p α β)

/-- The local map of a matrix from one register `ℂ^γ` of `p` to two registers `ℂ^α`, `ℂ^β`
of `p`. -/
def matLocal₁₂ [DecidableEq γ] (p : P) (A : Matrix (α × β) γ ℂ) :
    Mem [⟨p, euc γ⟩] →L[ℂ] Mem [⟨p, euc α⟩, ⟨p, euc β⟩] :=
  isoL (twoIso p p α β).symm ∘L act A ∘L isoL (oneIso p γ)

/-- The local map of a matrix on two registers of `p`. -/
def matLocal₂₂ [DecidableEq α] [DecidableEq β] (p : P) (A : Matrix (γ × δ) (α × β) ℂ) :
    Mem [⟨p, euc α⟩, ⟨p, euc β⟩] →L[ℂ] Mem [⟨p, euc γ⟩, ⟨p, euc δ⟩] :=
  isoL (twoIso p p γ δ).symm ∘L act A ∘L isoL (twoIso p p α β)

/-- Composing with linear isometric equivalences on both sides does not increase the norm. -/
theorem norm_comp_isoL_le {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : G ≃ₗᵢ[ℂ] H) (f : F →L[ℂ] G)
    (e' : E ≃ₗᵢ[ℂ] F) : ‖isoL e ∘L f ∘L isoL e'‖ ≤ ‖f‖ := by
  refine (opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _)
    (LinearIsometry.norm_toContinuousLinearMap_le _)).trans ?_
  refine (opNorm_comp_le _ _).trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _) (LinearIsometry.norm_toContinuousLinearMap_le _)

/-- `‖matLocal₂₁ p A‖ ≤ ‖A‖`. -/
theorem norm_matLocal₂₁_le [DecidableEq α] [DecidableEq β] (p : P) (A : Matrix γ (α × β) ℂ) :
    ‖matLocal₂₁ p A‖ ≤ ‖A‖ :=
  norm_comp_isoL_le _ _ _

/-- `‖matLocal₁₂ p A‖ ≤ ‖A‖`. -/
theorem norm_matLocal₁₂_le [DecidableEq γ] (p : P) (A : Matrix (α × β) γ ℂ) :
    ‖matLocal₁₂ p A‖ ≤ ‖A‖ :=
  norm_comp_isoL_le _ _ _

/-- `‖matLocal₂₂ p A‖ ≤ ‖A‖`. -/
theorem norm_matLocal₂₂_le [DecidableEq α] [DecidableEq β] (p : P)
    (A : Matrix (γ × δ) (α × β) ℂ) : ‖matLocal₂₂ p A‖ ≤ ‖A‖ :=
  norm_comp_isoL_le _ _ _

/-- The operator of a local map on the front registers: `U ⊗ 1` in the concatenation
identification. -/
theorem eval_localMap (p : P) {ℓ₁ ℓ₂ : Layout P} (h₁ : ∀ r ∈ ℓ₁, r.owner = p)
    (h₂ : ∀ r ∈ ℓ₂, r.owner = p) (U : Mem ℓ₁ →L[ℂ] Mem ℓ₂) (ℓ : Layout P) (a : Mem ℓ₁)
    (w : Mem ℓ) :
    (Word.localMap p h₁ h₂ U ℓ).eval ((appendIso ℓ₁ ℓ).symm (a ⊗ₜ w)) =
      (appendIso ℓ₂ ℓ).symm (U a ⊗ₜ w) := by
  simp [Word.eval]

end Euclidean

/-- The registers of a one-register layout of `p` are owned by `p`. -/
theorem owner_of_mem_one {p : P} {X : HSpace} :
    ∀ r ∈ ([⟨p, X⟩] : Layout P), r.owner = p := by
  intro r hr
  rw [List.mem_singleton] at hr
  rw [hr]

/-- The registers of a two-register layout of `p` are owned by `p`. -/
theorem owner_of_mem_two {p : P} {X Y : HSpace} :
    ∀ r ∈ ([⟨p, X⟩, ⟨p, Y⟩] : Layout P), r.owner = p := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rfl

/-- The registers of a two-register layout of `p` and `p'` are owned by `p` when `p = p'`. -/
theorem owner_of_mem_pair {p p' : P} {X Y : HSpace} (h : p = p') :
    ∀ r ∈ ([⟨p, X⟩, ⟨p', Y⟩] : Layout P), r.owner = p := by
  subst h
  exact owner_of_mem_two

/-- The empty layout has no registers, so every register in it is owned by `p`. -/
theorem owner_of_mem_nil {p : P} : ∀ r ∈ ([] : Layout P), r.owner = p :=
  fun _ hr => absurd hr List.not_mem_nil

section LocalMaps

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

omit [DecidableEq γ] in
/-- A local map of a matrix from two front registers to one register. -/
theorem eval_localMap₂₁ (p : P) (A : Matrix γ (α × β) ℂ) (ℓ : Layout P)
    (h₁ : ∀ r ∈ ([⟨p, euc α⟩, ⟨p, euc β⟩] : Layout P), r.owner = p)
    (h₂ : ∀ r ∈ ([⟨p, euc γ⟩] : Layout P), r.owner = p)
    (v : EuclideanSpace ℂ (α × β)) (w : Mem ℓ) :
    (Word.localMap p h₁ h₂ (matLocal₂₁ p A) ℓ).eval
        ((appendIso [⟨p, euc α⟩, ⟨p, euc β⟩] ℓ).symm ((twoIso p p α β).symm v ⊗ₜ w)) =
      (act A v ⊗ₜ w : Mem (⟨p, euc γ⟩ :: ℓ)) := by
  rw [eval_localMap, ← appendIso_one_symm p ℓ (act A v) w]
  simp [matLocal₂₁]

omit [DecidableEq α] [DecidableEq β] in
/-- A local map of a matrix from one front register to two registers. -/
theorem eval_localMap₁₂ (p : P) (A : Matrix (α × β) γ ℂ) (ℓ : Layout P)
    (h₁ : ∀ r ∈ ([⟨p, euc γ⟩] : Layout P), r.owner = p)
    (h₂ : ∀ r ∈ ([⟨p, euc α⟩, ⟨p, euc β⟩] : Layout P), r.owner = p)
    (x : EuclideanSpace ℂ γ) (w : Mem ℓ) :
    (Word.localMap p h₁ h₂ (matLocal₁₂ p A) ℓ).eval (x ⊗ₜ w : Mem (⟨p, euc γ⟩ :: ℓ)) =
      (appendIso [⟨p, euc α⟩, ⟨p, euc β⟩] ℓ).symm ((twoIso p p α β).symm (act A x) ⊗ₜ w) := by
  rw [← appendIso_one_symm p ℓ x w, eval_localMap]
  simp [matLocal₁₂]

omit [DecidableEq γ] [DecidableEq δ] in
/-- A local map of a matrix on two front registers acts as the matrix tensored with the
identity. -/
theorem pairHeadIso_eval_localMap₂₂ (p : P) (A : Matrix (γ × δ) (α × β) ℂ) (ℓ : Layout P)
    (h₁ : ∀ r ∈ ([⟨p, euc α⟩, ⟨p, euc β⟩] : Layout P), r.owner = p)
    (h₂ : ∀ r ∈ ([⟨p, euc γ⟩, ⟨p, euc δ⟩] : Layout P), r.owner = p)
    (z : Mem (⟨p, euc α⟩ :: ⟨p, euc β⟩ :: ℓ)) :
    pairHeadIso ℓ ((Word.localMap p h₁ h₂ (matLocal₂₂ p A) ℓ).eval z) =
      (act A).rTensor (Mem ℓ) (pairHeadIso ℓ z) := by
  obtain ⟨y, rfl⟩ : ∃ y : EuclideanSpace ℂ (α × β) ⊗[ℂ] Mem ℓ, z = (pairHeadIso ℓ).symm y :=
    ⟨pairHeadIso ℓ z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  induction y using TensorProduct.inductionOn with
  | tmul v w =>
      have hz : (pairHeadIso (p := p) (q := p) ℓ).symm (v ⊗ₜ w) =
          (appendIso [⟨p, euc α⟩, ⟨p, euc β⟩] ℓ).symm ((twoIso p p α β).symm v ⊗ₜ w) := by
        rw [LinearIsometryEquiv.symm_apply_eq, pairHeadIso_appendIso_symm]
      rw [hz, eval_localMap, rTensor_tmul,
        ← pairHeadIso_appendIso_symm (p := p) (q := p) ℓ (act A v) w]
      simp [matLocal₂₂]
  | add a b ha hb => simp only [map_add, ha, hb]

end LocalMaps


end TNLean.PEPS.PairEffect
