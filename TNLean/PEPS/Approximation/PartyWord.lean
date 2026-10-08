/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TensorProductRegrouping
import TNLean.PEPS.Approximation.PairEffectElimination

/-!
# Registers of parties and source-only words

This file assigns registers to parties for the elimination of normalized pair effects
(Lemma 5.1 `lem:effects`), and defines the operations allowed between pair effects.

A *layout* is a list of registers, each with an owner party and a Hilbert space; its memory
space is the tensor product of the registers.  The order of the list only fixes the order of
the tensor factors.  A *source-only word* (`Word`) is a composition of

* local contractions, acting on registers of one party next to arbitrary other registers,
* preparations of normalized vectors on two fresh registers of two distinct parties
  (pair sources),
* exchanges of adjacent tensor factors, and operations framed by untouched registers.

A stack of `m` pair registers on the parties `(p, q)` consists of `m` registers `ℂ^α` of `p`
alternating with `m` registers `ℂ^β` of `q` (`pairRegs`), identified with `ℂ^{Fin m → α × β}`
(`stackIso`).  The insertion of the input at position `k` among `m - 1` copies of the pair
vector `η` is a source-only word (`insWord`): sources of `η` are prepared in the other `m - 1`
positions, so no permutation of pair registers is needed (`stackIso_insWord`).

## Main definitions

* `PairEffect.Reg`, `PairEffect.Layout`, `PairEffect.Mem` : registers with owners, layouts and
  their memory spaces.
* `PairEffect.Word` : source-only words, with `Word.eval` and `Word.IsAllowed`.
* `PairEffect.IsSourceOnly` : an operator between memories that is the operator of an
  allowed source-only word.
* `PairEffect.pairRegs`, `PairEffect.stackIso` : stacks of pair registers.
* `PairEffect.prepWord`, `PairEffect.insWord` : preparation of `η^{⊗ n}` and insertion at a
  position, by pair sources.

## Main results

* `PairEffect.map_owner_pairRegs` : the owners of a stack.
* `PairEffect.stackIso_prepWord` : `prepWord` prepares `η^{⊗ n}`.
* `PairEffect.stackIso_insWord` : `insWord` is the insertion map `I_k`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open EuclideanSpace CyclicInsertion ContinuousLinearMap

/-! ### Registers, layouts and memory spaces -/

/-- A register: an owner party and a Hilbert space.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 23–25: a party is
a label for a collection of registers, and the memory is the tensor product of the parties'
spaces. -/
structure Reg (P : Type) : Type 1 where
  /-- The party owning the register. -/
  owner : P
  /-- The Hilbert space of the register. -/
  space : HSpace

/-- A layout: a list of registers.  The order only fixes the order of the tensor factors. -/
abbrev Layout (P : Type) : Type 1 := List (Reg P)

variable {P : Type}

/-- The memory space of a layout: the tensor product of its registers. -/
@[reducible] def Mem : Layout P → HSpace
  | [] => HSpace.of ℂ
  | r :: ℓ => HSpace.of (r.space ⊗[ℂ] Mem ℓ)

/-- The Euclidean space `ℂ^α` as a register space. -/
abbrev euc (α : Type) [Fintype α] : HSpace := HSpace.of (EuclideanSpace ℂ α)

/-- The memory of a concatenation is the tensor product of the memories. -/
def appendIso : (ℓ₁ ℓ : Layout P) → Mem (ℓ₁ ++ ℓ) ≃ₗᵢ[ℂ] Mem ℓ₁ ⊗[ℂ] Mem ℓ
  | [], ℓ => (TensorProduct.lidIsometry ℂ (Mem ℓ)).symm
  | r :: ℓ₁, ℓ => ((appendIso ℓ₁ ℓ).lTensor r.space).trans
      (TensorProduct.assocIsometry ℂ r.space (Mem ℓ₁) (Mem ℓ)).symm

/-! ### Source-only words -/

/-- A source-only word from the layout `ℓ` to the layout `ℓ'`.

* `id`, `comp` : the empty word and composition.
* `localMap p h₁ h₂ U ℓ` : a local map `U` from registers `ℓ₁` of the party `p` to registers
  `ℓ₂` of `p`, next to the untouched registers `ℓ`.
* `source hpq U V η ℓ` : preparation of the pair vector `η ∈ U ⊗ V` on a fresh register `U` of
  `p` and a fresh register `V` of `q ≠ p`.
* `swap r r' ℓ` : exchange of two adjacent tensor factors.
* `frame r w` : the word `w` next to the untouched register `r`.

`swap` and `frame` only reorder or skip tensor factors; the memory is the tensor product of
the parties' spaces, in which the order of factors carries no information.

Polynomial-PEPS manuscript (September 24, 2026), allowed monomials without pair effects,
`04-compression.tex`, lines 32–35 and 65–66. -/
inductive Word : Layout P → Layout P → Type 1
  | id (ℓ : Layout P) : Word ℓ ℓ
  | comp {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : Word ℓ₁ ℓ₂) (w' : Word ℓ₂ ℓ₃) : Word ℓ₁ ℓ₃
  | localMap (p : P) {ℓ₁ ℓ₂ : Layout P} (h₁ : ∀ r ∈ ℓ₁, r.owner = p)
      (h₂ : ∀ r ∈ ℓ₂, r.owner = p) (U : Mem ℓ₁ →L[ℂ] Mem ℓ₂) (ℓ : Layout P) :
      Word (ℓ₁ ++ ℓ) (ℓ₂ ++ ℓ)
  | source {p q : P} (hpq : p ≠ q) (U V : HSpace) (η : U ⊗[ℂ] V) (ℓ : Layout P) :
      Word ℓ (⟨p, U⟩ :: ⟨q, V⟩ :: ℓ)
  | swap (r r' : Reg P) (ℓ : Layout P) : Word (r :: r' :: ℓ) (r' :: r :: ℓ)
  | frame (r : Reg P) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') : Word (r :: ℓ) (r :: ℓ')

namespace Word

/-- The operator of a source-only word. -/
def eval : {ℓ ℓ' : Layout P} → Word ℓ ℓ' → (Mem ℓ →L[ℂ] Mem ℓ')
  | _, _, id _ => ContinuousLinearMap.id ℂ _
  | _, _, comp w w' => w'.eval ∘L w.eval
  | _, _, @localMap _ _ ℓ₁ ℓ₂ _ _ U ℓ =>
      isoL (appendIso ℓ₂ ℓ).symm ∘L U.rTensor (Mem ℓ) ∘L isoL (appendIso ℓ₁ ℓ)
  | _, _, source _ U V η ℓ => assocL U V (Mem ℓ) ∘L appendLeft η
  | _, _, swap r r' ℓ => leftCommL r.space r'.space (Mem ℓ)
  | _, _, frame r w => w.eval.lTensor r.space

/-- A source-only word is allowed when its local maps are contractions and its pair vectors are
normalized.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35. -/
def IsAllowed : {ℓ ℓ' : Layout P} → Word ℓ ℓ' → Prop
  | _, _, id _ => True
  | _, _, comp w w' => w.IsAllowed ∧ w'.IsAllowed
  | _, _, localMap _ _ _ U _ => ‖U‖ ≤ 1
  | _, _, source _ _ _ η _ => ‖η‖ = 1
  | _, _, swap .. => True
  | _, _, frame _ w => w.IsAllowed

theorem norm_eval_le_one : {ℓ ℓ' : Layout P} → (w : Word ℓ ℓ') → w.IsAllowed → ‖w.eval‖ ≤ 1
  | _, _, id _, _ => ContinuousLinearMap.norm_id_le
  | _, _, comp w w', h => norm_comp_le_one (norm_eval_le_one w' h.2) (norm_eval_le_one w h.1)
  | _, _, localMap _ _ _ _ _, h => norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
      (norm_comp_le_one ((norm_rTensor_le _ _).trans h)
        (LinearIsometry.norm_toContinuousLinearMap_le _))
  | _, _, source _ _ _ _ _, h => norm_comp_le_one norm_assocL_le
      ((norm_appendLeft_le _).trans h.le)
  | _, _, swap .., _ => norm_leftCommL_le
  | _, _, frame _ w, h => (norm_lTensor_le _ _).trans (norm_eval_le_one w h)

@[simp] theorem eval_comp {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : Word ℓ₁ ℓ₂) (w' : Word ℓ₂ ℓ₃) :
    (comp w w').eval = w'.eval ∘L w.eval :=
  rfl

theorem eval_frame (r : Reg P) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (frame r w).eval = w.eval.lTensor r.space :=
  rfl

theorem eval_source {p q : P} (hpq : p ≠ q) (U V : HSpace) (η : U ⊗[ℂ] V) (ℓ : Layout P) :
    (source hpq U V η ℓ).eval = assocL U V (Mem ℓ) ∘L appendLeft η :=
  rfl

/-- A word framed by a list of untouched registers. -/
def frameList {ℓ ℓ' : Layout P} : (ℓ₀ : Layout P) → Word ℓ ℓ' → Word (ℓ₀ ++ ℓ) (ℓ₀ ++ ℓ')
  | [], w => w
  | r :: ℓ₀, w => frame r (frameList ℓ₀ w)

theorem isAllowed_frameList {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (hw : w.IsAllowed) :
    (ℓ₀ : Layout P) → (frameList ℓ₀ w).IsAllowed
  | [] => hw
  | _ :: ℓ₀ => isAllowed_frameList w hw ℓ₀

end Word

/-- An operator between memories is source-only when it is the operator of an allowed
source-only word: a composition of local contractions and normalized pair sources.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
lines 65–66. -/
def IsSourceOnly {ℓ ℓ' : Layout P} (T : Mem ℓ →L[ℂ] Mem ℓ') : Prop :=
  ∃ w : Word ℓ ℓ', w.IsAllowed ∧ w.eval = T

/-! ### Stacks of pair registers -/

section Stack

variable (p q : P) (α β : Type) [Fintype α] [Fintype β]

/-- `n` pair registers in front of the layout `ℓ`: each pair register consists of a register
`ℂ^α` of the party `p` followed by a register `ℂ^β` of the party `q`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 75–79 and
100–102. -/
@[reducible] def pairsOn : ℕ → Layout P → Layout P
  | 0, ℓ => ℓ
  | n + 1, ℓ => ⟨p, euc α⟩ :: ⟨q, euc β⟩ :: pairsOn n ℓ

/-- A stack of `n` pair registers on the parties `p` and `q`. -/
def pairRegs (n : ℕ) : Layout P := pairsOn p q α β n []

theorem pairsOn_eq (n : ℕ) (ℓ : Layout P) : pairsOn p q α β n ℓ = pairRegs p q α β n ++ ℓ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pairRegs, pairsOn, List.cons_append, ih]

theorem pairRegs_eq (n : ℕ) :
    pairRegs p q α β n = (List.replicate n [⟨p, euc α⟩, ⟨q, euc β⟩]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pairRegs, pairsOn] at ih ⊢
      rw [ih, List.replicate_succ, List.flatten_cons]
      rfl

theorem map_owner_pairRegs (n : ℕ) :
    (pairRegs p q α β n).map Reg.owner = (List.replicate n [p, q]).flatten := by
  rw [pairRegs_eq]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

variable {p q α β}

/-- A pair register at the front of a layout, identified with `ℂ^{α × β}`. -/
def pairHeadIso (ℓ : Layout P) :
    Mem (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (α × β) ⊗[ℂ] Mem ℓ :=
  (TensorProduct.assocIsometry ℂ (EuclideanSpace ℂ α) (EuclideanSpace ℂ β) (Mem ℓ)).symm.trans
    ((pairIso α β).rTensor (Mem ℓ))

theorem pairHeadIso_apply (ℓ : Layout P) (z : Mem (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ)) :
    pairHeadIso ℓ z = (isoL (pairIso α β)).rTensor (Mem ℓ)
      ((TensorProduct.assocIsometry ℂ (EuclideanSpace ℂ α) (EuclideanSpace ℂ β) (Mem ℓ)).symm z) :=
  iso_rTensor_apply _ _

theorem pairHeadIso_tmul (ℓ : Layout P) (x : (⟨p, euc α⟩ : Reg P).space)
    (y : (⟨q, euc β⟩ : Reg P).space) (s : Mem ℓ) :
    pairHeadIso ℓ (x ⊗ₜ (y ⊗ₜ s)) = pairIso α β (x ⊗ₜ y) ⊗ₜ s := by
  rw [pairHeadIso_apply]
  simp only [TensorProduct.assocIsometry_symm_apply, TensorProduct.assoc_symm_tmul,
    rTensor_tmul, isoL_apply]

/-- A pair register at the front passes words on the remaining registers. -/
theorem pairHeadIso_frame {ℓ ℓ' : Layout P} (W : Word ℓ ℓ')
    (z : Mem (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ)) :
    pairHeadIso ℓ' ((Word.frame _ (Word.frame _ W)).eval z) =
      W.eval.lTensor _ (pairHeadIso ℓ z) := by
  induction z using tmul₃_induction with
  | tmul x y t =>
      simp only [Word.eval_frame, lTensor_tmul]
      rw [pairHeadIso_tmul, pairHeadIso_tmul, lTensor_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The pair vector `η ∈ ℂ^{α × β}` as a vector of `ℂ^α ⊗ ℂ^β`. -/
def pairVec (η : EuclideanSpace ℂ (α × β)) : EuclideanSpace ℂ α ⊗[ℂ] EuclideanSpace ℂ β :=
  (pairIso α β).symm η

theorem norm_pairVec (η : EuclideanSpace ℂ (α × β)) : ‖pairVec η‖ = ‖η‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- The pair register prepared by a pair source of `pairVec η` is `η`. -/
theorem pairHeadIso_source {p q : P} (hpq : p ≠ q) (η : EuclideanSpace ℂ (α × β)) (ℓ : Layout P)
    (u : Mem ℓ) :
    pairHeadIso ℓ ((Word.source hpq (euc α) (euc β) (pairVec η) ℓ).eval u) = η ⊗ₜ u := by
  rw [pairHeadIso_apply]
  simp only [Word.eval_source, comp_apply, appendLeft_apply, assocL, isoL_apply,
    LinearIsometryEquiv.symm_apply_apply, rTensor_tmul, pairVec,
    LinearIsometryEquiv.apply_symm_apply]

/-- The rearrangement `ℂ^{α × β} ⊗ (ℂ^{Fin n → α × β} ⊗ G) → ℂ^{Fin (n + 1) → α × β} ⊗ G` that
places the front pair register in position `0` of a stack. -/
def consRearr (n : ℕ) (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    EuclideanSpace ℂ (α × β) ⊗[ℂ] (EuclideanSpace ℂ (Fin n → α × β) ⊗[ℂ] G) →L[ℂ]
      EuclideanSpace ℂ (Fin (n + 1) → α × β) ⊗[ℂ] G :=
  (isoL (consIso (α × β) n)).rTensor G ∘L
    isoL (TensorProduct.assocIsometry ℂ (EuclideanSpace ℂ (α × β))
      (EuclideanSpace ℂ (Fin n → α × β)) G).symm

theorem consRearr_tmul {n : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (v : EuclideanSpace ℂ (α × β)) (s : EuclideanSpace ℂ (Fin n → α × β)) (g : G) :
    consRearr n G (v ⊗ₜ (s ⊗ₜ g)) = consIso (α × β) n (v ⊗ₜ s) ⊗ₜ g := by
  simp only [consRearr, comp_apply, isoL_apply, TensorProduct.assocIsometry_symm_apply,
    TensorProduct.assoc_symm_tmul, rTensor_tmul]

theorem consRearr_lTensor_lTensor {n : ℕ} {G H : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : G →L[ℂ] H)
    (z : EuclideanSpace ℂ (α × β) ⊗[ℂ] (EuclideanSpace ℂ (Fin n → α × β) ⊗[ℂ] G)) :
    consRearr n H ((f.lTensor _).lTensor _ z) = f.lTensor _ (consRearr n G z) := by
  simp only [consRearr, comp_apply, isoL_apply]
  rw [lTensor_lTensor_assoc_symm, rTensor_lTensor_comm]

variable (p q α β) in
/-- A stack of `n` pair registers in front of a layout, identified with
`ℂ^{Fin n → α × β}`. -/
def stackIso : (n : ℕ) → (ℓ : Layout P) →
    Mem (pairsOn p q α β n ℓ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n → α × β) ⊗[ℂ] Mem ℓ
  | 0, ℓ => (TensorProduct.lidIsometry ℂ (Mem ℓ)).symm.trans ((emptyIso (α × β)).rTensor _)
  | n + 1, ℓ => (pairHeadIso (p := p) (q := q) (pairsOn p q α β n ℓ)).trans
      (((stackIso n ℓ).lTensor _).trans
        ((TensorProduct.assocIsometry ℂ _ _ _).symm.trans ((consIso (α × β) n).rTensor _)))

theorem stackIso_zero (ℓ : Layout P) (x : Mem (pairsOn p q α β 0 ℓ)) :
    stackIso p q α β 0 ℓ x = emptyIso (α × β) 1 ⊗ₜ (x : Mem ℓ) := by
  simp only [stackIso, LinearIsometryEquiv.trans_apply, TensorProduct.lidIsometry_symm_apply,
    iso_rTensor_apply, rTensor_tmul, isoL_apply]

theorem stackIso_succ (n : ℕ) (ℓ : Layout P) (z : Mem (pairsOn p q α β (n + 1) ℓ)) :
    stackIso p q α β (n + 1) ℓ z =
      consRearr n (Mem ℓ) ((isoL (stackIso p q α β n ℓ)).lTensor _ (pairHeadIso _ z)) := by
  simp only [stackIso, LinearIsometryEquiv.trans_apply, iso_lTensor_apply, iso_rTensor_apply,
    consRearr, comp_apply, isoL_apply]

/-- A word framed by `n` pair registers. -/
def framePairs {ℓ ℓ' : Layout P} : (n : ℕ) → Word ℓ ℓ' →
    Word (pairsOn p q α β n ℓ) (pairsOn p q α β n ℓ')
  | 0, W => W
  | n + 1, W => .frame _ (.frame _ (framePairs n W))

theorem isAllowed_framePairs {ℓ ℓ' : Layout P} (W : Word ℓ ℓ') (hW : W.IsAllowed) :
    (n : ℕ) → (framePairs (p := p) (q := q) (α := α) (β := β) n W).IsAllowed
  | 0 => hW
  | n + 1 => isAllowed_framePairs W hW n

/-- A stack at the front passes words on the remaining registers. -/
theorem stackIso_framePairs {ℓ ℓ' : Layout P} (W : Word ℓ ℓ') : (n : ℕ) →
    (z : Mem (pairsOn p q α β n ℓ)) →
    stackIso p q α β n ℓ' ((framePairs n W).eval z) = W.eval.lTensor _ (stackIso p q α β n ℓ z)
  | 0, z => by
      simp only [framePairs]
      rw [stackIso_zero, stackIso_zero]
      rfl
  | n + 1, z => by
      have ih : isoL (stackIso p q α β n ℓ') ∘L
          (framePairs (p := p) (q := q) (α := α) (β := β) n W).eval =
          W.eval.lTensor _ ∘L isoL (stackIso p q α β n ℓ) :=
        ContinuousLinearMap.ext fun t => stackIso_framePairs W n t
      rw [stackIso_succ, stackIso_succ, framePairs, pairHeadIso_frame, lTensor_comp_apply, ih,
        lTensor_comp, comp_apply, consRearr_lTensor_lTensor]

variable {p q : P} (hpq : p ≠ q) (η : EuclideanSpace ℂ (α × β))

/-- Preparation of `n` copies of the pair vector `η` as pair sources on `p` and `q`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 75–76 and
103–105. -/
def prepWord : (n : ℕ) → (ℓ : Layout P) → Word ℓ (pairsOn p q α β n ℓ)
  | 0, ℓ => .id ℓ
  | n + 1, ℓ => .comp (prepWord n ℓ)
      (.source hpq (euc α) (euc β) (pairVec η) (pairsOn p q α β n ℓ))

theorem isAllowed_prepWord (hη : ‖η‖ = 1) : (n : ℕ) → (ℓ : Layout P) →
    (prepWord hpq η n ℓ).IsAllowed
  | 0, _ => trivial
  | n + 1, ℓ => ⟨isAllowed_prepWord hη n ℓ, (norm_pairVec η).trans hη⟩

/-- The prepared stack is `η^{⊗ n}`. -/
theorem stackIso_prepWord : (n : ℕ) → (ℓ : Layout P) → (x : Mem ℓ) →
    stackIso p q α β n ℓ ((prepWord hpq η n ℓ).eval x) = tensorPower (Fin n) η ⊗ₜ x
  | 0, ℓ, x => by
      rw [stackIso_zero, emptyIso_one η]
      rfl
  | n + 1, ℓ, x => by
      rw [stackIso_succ]
      simp only [prepWord, Word.eval_comp, comp_apply]
      rw [pairHeadIso_source, lTensor_tmul]
      simp only [isoL_apply]
      rw [stackIso_prepWord n ℓ x, consRearr_tmul, ← tensorPower_succ]

/-- Insertion of the input pair register at position `k` of a stack of `m` pair registers,
the other `m - 1` positions holding pair sources of `η`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 75–79 and 96–98:
each term of the permutation average consists of normalized source preparation followed by a
permutation of the pair registers. -/
def insWord {ℓ : Layout P} : (m : ℕ) → Fin m →
    Word (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ) (pairsOn p q α β m ℓ)
  | n + 1, ⟨0, _⟩ => .frame _ (.frame _ (prepWord hpq η n ℓ))
  | n + 1, ⟨k + 1, hk⟩ => .comp (.source hpq (euc α) (euc β) (pairVec η) _)
      (.frame _ (.frame _ (insWord n ⟨k, Nat.lt_of_succ_lt_succ hk⟩)))

theorem isAllowed_insWord (hη : ‖η‖ = 1) {ℓ : Layout P} : (m : ℕ) → (k : Fin m) →
    (insWord hpq η m k (ℓ := ℓ)).IsAllowed
  | n + 1, ⟨0, _⟩ => isAllowed_prepWord hpq η hη n ℓ
  | n + 1, ⟨k + 1, hk⟩ =>
      ⟨(norm_pairVec η).trans hη, isAllowed_insWord hη n ⟨k, Nat.lt_of_succ_lt_succ hk⟩⟩

/-- **The insertion map as a source-only word.** Under the identification of the stack with
`ℂ^{Fin m → α × β}`, the word `insWord` is the insertion map `I_k` of `η`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 75–98. -/
theorem stackIso_insWord {ℓ : Layout P} : (m : ℕ) → (k : Fin m) →
    (u : Mem (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ)) →
    stackIso p q α β m ℓ ((insWord hpq η m k (ℓ := ℓ)).eval u) =
      (insertAt η k).rTensor (Mem ℓ) (pairHeadIso ℓ u)
  | n + 1, ⟨0, h0⟩, u => by
      induction u using tmul₃_induction with
      | tmul x y s =>
          simp only [insWord]
          rw [stackIso_succ, pairHeadIso_frame, pairHeadIso_tmul, lTensor_tmul, lTensor_tmul]
          simp only [isoL_apply]
          rw [stackIso_prepWord, consRearr_tmul, rTensor_tmul,
            show (⟨0, h0⟩ : Fin (n + 1)) = 0 from rfl, insertAt_zero_eq_consIso]
      | add a b ha hb => simp only [map_add, ha, hb]
  | n + 1, ⟨k + 1, hk⟩, u => by
      induction u using tmul₃_induction with
      | tmul x y s =>
          simp only [insWord, Word.eval_comp, comp_apply]
          rw [stackIso_succ, pairHeadIso_frame, pairHeadIso_source, lTensor_tmul, lTensor_tmul]
          simp only [isoL_apply]
          rw [stackIso_insWord n ⟨k, Nat.lt_of_succ_lt_succ hk⟩, pairHeadIso_tmul,
            rTensor_tmul, consRearr_tmul, rTensor_tmul,
            show (⟨k + 1, hk⟩ : Fin (n + 1)) = Fin.succ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ from rfl,
            insertAt_succ_eq_consIso]
      | add a b ha hb => simp only [map_add, ha, hb]

end Stack

end TNLean.PEPS.PairEffect
