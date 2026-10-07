/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairEffectElimination

/-!
# Pair-effect elimination on a party layout

This file places the monomials of `TNLean.PEPS.PairEffect` on parties and proves the
statements of Lemma 5.1 `lem:effects` about parties: the replaced gate has an expansion
using only local contractions and normalized pair sources, its additional registers are
owned by the endpoint parties of the eliminated effects, and two sources on the same pair of
parties combine into one normalized pair source.

A *layout* is a list of registers, each with an owner party and a Hilbert space; its memory
space is the tensor product of the registers.  The order of the list only fixes the order of
the tensor factors.  A *source-only word* (`Word`) is a composition of

* local contractions, acting on registers of one party next to arbitrary other registers,
* preparations of normalized vectors on two fresh registers of two distinct parties
  (pair sources),
* exchanges of adjacent tensor factors, and operations framed by untouched registers.

An allowed monomial (`PartyChain`) consists of source-only words separated by pair effects:
an effect contracts a register `ℂ^α` of a party `p` and a register `ℂ^β` of another party
`q` with a normalized bra.  Its operator is the `EffectChain` of
`TNLean.PEPS.Approximation.PairEffectElimination` (`PartyChain.toEffectChain`), so the error,
count and coefficient bounds proved there apply.

In the replacement, the stack of an effect occurrence on `(p, q)` consists of `m` pair
registers `ℂ^α ⊗ ℂ^β`, the `ℂ^α` half owned by `p` and the `ℂ^β` half owned by `q`
(`pairRegs`).  The insertion of the input at position `k` among `m - 1` copies of the pair
vector `η` is a source-only word (`insWord`): sources of `η` are prepared in the other `m - 1`
positions.  This identifies the terms of the expansion of the replaced gate with source-only
words (`termList_toGate`), the common garbage vector with a product of pair sources
(`gateIso_comp_prepGate`), and the additional registers with the stacks
(`gateOut_eq`).

## Main definitions

* `PairEffect.Reg`, `PairEffect.Layout`, `PairEffect.Mem` : registers with owners, layouts and
  their memory spaces.
* `PairEffect.Word` : source-only words, with `Word.eval` and `Word.IsAllowed`.
* `PairEffect.IsSourceOnly` : an operator between memories that is the operator of an
  allowed source-only word.
* `PairEffect.PartyChain` : allowed monomials with pair effects on named parties.
* `PairEffect.PartyChain.replaceWord` : the terms of a replaced monomial as source-only words.
* `PairEffect.wordList` : the expansion of the replaced gate into source-only words.
* `PairEffect.gateOut`, `PairEffect.gateIso` : the output layout of the replaced gate and its
  identification with the output space of `PairEffect.replaceGate`.

## Main results

* `PairEffect.PartyChain.replaceTerm_toEffectChain` : each term of a replaced monomial is the
  operator of a source-only word.
* `PairEffect.termList_toGate` : the expansion of the replaced gate, term by term.
* `PairEffect.gateIso_comp_prepGate` : the common garbage vector `Γ_m` is prepared by pair
  sources.
* `PairEffect.gateOut_eq`, `PairEffect.owner_stackRegs` : the additional registers and their
  owners.
* `PairEffect.eval_combineSources` : two sources on one pair of parties combine into one.
* `PairEffect.partyPairEffectElimination` : Lemma 5.1 `lem:effects`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open EuclideanSpace CyclicInsertion ContinuousLinearMap

/-! ### Continuous linear maps of tensor products -/

section TensorExt

variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The continuous linear map of a linear isometric equivalence. -/
abbrev isoL (e : E ≃ₗᵢ[ℂ] F) : E →L[ℂ] F := e.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem isoL_apply (e : E ≃ₗᵢ[ℂ] F) (x : E) : isoL e x = e x := rfl

theorem clm_ext_tmul {f g : E ⊗[ℂ] F →L[ℂ] G} (h : ∀ x y, f (x ⊗ₜ y) = g (x ⊗ₜ y)) : f = g := by
  ext1 z
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem clm_ext_tmul₃ {f g : E ⊗[ℂ] (F ⊗[ℂ] G) →L[ℂ] H}
    (h : ∀ x y z, f (x ⊗ₜ (y ⊗ₜ z)) = g (x ⊗ₜ (y ⊗ₜ z))) : f = g := by
  refine clm_ext_tmul fun x w => ?_
  induction w using TensorProduct.inductionOn with
  | tmul y z => exact h x y z
  | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]

/-- Induction over a triple tensor product `E ⊗ (F ⊗ G)` through its pure tensors. -/
theorem tmul₃_induction {motive : E ⊗[ℂ] (F ⊗[ℂ] G) → Prop} (u : E ⊗[ℂ] (F ⊗[ℂ] G))
    (tmul : ∀ x y z, motive (x ⊗ₜ (y ⊗ₜ z)))
    (add : ∀ a b, motive a → motive b → motive (a + b)) : motive u := by
  induction u using TensorProduct.inductionOn with
  | tmul x w =>
      induction w using TensorProduct.inductionOn with
      | tmul y z => exact tmul x y z
      | add a b ha hb => rw [TensorProduct.tmul_add]; exact add _ _ ha hb
  | add a b ha hb => exact add a b ha hb

@[simp]
theorem isoL_trans (e : E ≃ₗᵢ[ℂ] F) (e' : F ≃ₗᵢ[ℂ] G) : isoL (e.trans e') = isoL e' ∘L isoL e :=
  rfl

theorem isoL_lTensor (e : F ≃ₗᵢ[ℂ] G) : isoL (e.lTensor E) = (isoL e).lTensor E :=
  clm_ext_tmul fun x y => by simp [LinearIsometryEquiv.lTensor_def]

theorem isoL_rTensor (e : E ≃ₗᵢ[ℂ] F) : isoL (e.rTensor G) = (isoL e).rTensor G :=
  clm_ext_tmul fun x y => by simp [LinearIsometryEquiv.rTensor_def]

theorem iso_lTensor_apply (e : F ≃ₗᵢ[ℂ] G) (z : E ⊗[ℂ] F) :
    e.lTensor E z = (isoL e).lTensor E z :=
  DFunLike.congr_fun (isoL_lTensor e) z

theorem iso_rTensor_apply (e : E ≃ₗᵢ[ℂ] F) (z : E ⊗[ℂ] G) :
    e.rTensor G z = (isoL e).rTensor G z :=
  DFunLike.congr_fun (isoL_rTensor e) z

theorem lTensor_comp_appendLeft (f : F →L[ℂ] G) (v : E) :
    f.lTensor E ∘L appendLeft v = appendLeft v ∘L f := by
  ext1 x
  simp only [comp_apply, appendLeft_apply, lTensor_tmul]

theorem lTensor_lTensor_assoc_symm (f : G →L[ℂ] H) (z : E ⊗[ℂ] (F ⊗[ℂ] G)) :
    (TensorProduct.assocIsometry ℂ E F H).symm ((f.lTensor F).lTensor E z) =
      f.lTensor (E ⊗[ℂ] F) ((TensorProduct.assocIsometry ℂ E F G).symm z) := by
  refine DFunLike.congr_fun (f := isoL (TensorProduct.assocIsometry ℂ E F H).symm ∘L
    (f.lTensor F).lTensor E) (g := f.lTensor (E ⊗[ℂ] F) ∘L
      isoL (TensorProduct.assocIsometry ℂ E F G).symm) (clm_ext_tmul₃ fun x y w => ?_) z
  simp only [comp_apply, isoL_apply, lTensor_tmul, TensorProduct.assocIsometry_symm_apply,
    TensorProduct.assoc_symm_tmul]

theorem rTensor_lTensor_comm (f : E →L[ℂ] F) (g : G →L[ℂ] H) (z : E ⊗[ℂ] G) :
    f.rTensor H (g.lTensor E z) = g.lTensor F (f.rTensor G z) := by
  refine DFunLike.congr_fun (f := f.rTensor H ∘L g.lTensor E) (g := g.lTensor F ∘L f.rTensor G)
    (clm_ext_tmul fun x y => ?_) z
  simp only [comp_apply, lTensor_tmul, rTensor_tmul]

theorem leftCommL_lTensor_rTensor (f : F →L[ℂ] G) (z : E ⊗[ℂ] (F ⊗[ℂ] H)) :
    leftCommL E G H ((f.rTensor H).lTensor E z) = f.rTensor (E ⊗[ℂ] H) (leftCommL E F H z) := by
  refine DFunLike.congr_fun (f := leftCommL E G H ∘L (f.rTensor H).lTensor E)
    (g := f.rTensor (E ⊗[ℂ] H) ∘L leftCommL E F H) (clm_ext_tmul₃ fun x y w => ?_) z
  simp only [comp_apply, lTensor_tmul, rTensor_tmul, leftCommL_tmul]

theorem lTensor_comp_apply (f : F →L[ℂ] G) (g : H →L[ℂ] F) (z : E ⊗[ℂ] H) :
    f.lTensor E (g.lTensor E z) = (f ∘L g).lTensor E z := by
  rw [lTensor_comp]
  rfl

theorem rTensor_comp_apply (f : F →L[ℂ] G) (g : H →L[ℂ] F) (z : H ⊗[ℂ] E) :
    f.rTensor E (g.rTensor E z) = (f ∘L g).rTensor E z := by
  rw [rTensor_comp]
  rfl

theorem lTensor_congr_apply {f f' : F →L[ℂ] G} (h : ∀ x, f x = f' x) (z : E ⊗[ℂ] F) :
    f.lTensor E z = f'.lTensor E z := by
  rw [show f = f' from ContinuousLinearMap.ext h]

theorem rTensor_congr_apply {f f' : F →L[ℂ] G} (h : ∀ x, f x = f' x) (z : F ⊗[ℂ] E) :
    f.rTensor E z = f'.rTensor E z := by
  rw [show f = f' from ContinuousLinearMap.ext h]

end TensorExt

/-! ### Euclidean pair and stack identifications -/

section Euclid

variable {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]

/-- The identification `ℂ^α ⊗ ℂ^β ≅ ℂ^{α × β}` with `(x ⊗ y) (a, b) = x a * y b`. -/
def pairIso (α β : Type) [Fintype α] [Fintype β] :
    EuclideanSpace ℂ α ⊗[ℂ] EuclideanSpace ℂ β ≃ₗᵢ[ℂ] EuclideanSpace ℂ (α × β) :=
  ((EuclideanSpace.basisFun α ℂ).tensorProduct (EuclideanSpace.basisFun β ℂ)).repr

@[simp]
theorem pairIso_tmul_apply (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) (i : α × β) :
    pairIso α β (x ⊗ₜ y) i = x i.1 * y i.2 := by
  simp [pairIso, OrthonormalBasis.tensorProduct_repr_tmul_apply', mul_comm]

/-- The identification `ℂ^ι ⊗ ℂ^{Fin n → ι} ≅ ℂ^{Fin (n + 1) → ι}` placing the first factor in
register `0`. -/
def consIso (ι : Type) [Fintype ι] (n : ℕ) :
    EuclideanSpace ℂ ι ⊗[ℂ] EuclideanSpace ℂ (Fin n → ι) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (n + 1) → ι) :=
  (pairIso ι (Fin n → ι)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fin.consEquiv fun _ => ι))

@[simp]
theorem consIso_tmul_apply {n : ℕ} (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ (Fin n → ι))
    (f : Fin (n + 1) → ι) : consIso ι n (x ⊗ₜ y) f = x (f 0) * y (Fin.tail f) := by
  simp [consIso, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    Fin.consEquiv]

theorem piTensor_cons {n : ℕ} (v : EuclideanSpace ℂ ι) (u : Fin n → EuclideanSpace ℂ ι) :
    piTensor (Fin.cons v u : Fin (n + 1) → EuclideanSpace ℂ ι) =
      consIso ι n (v ⊗ₜ piTensor u) := by
  ext f
  simp [piTensor_apply, Fin.prod_univ_succ, Fin.tail]

theorem tensorPower_succ {n : ℕ} (η : EuclideanSpace ℂ ι) :
    tensorPower (Fin (n + 1)) η = consIso ι n (η ⊗ₜ tensorPower (Fin n) η) := by
  rw [tensorPower, tensorPower, ← piTensor_cons]
  congr 1
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem insertAt_zero_eq_consIso {n : ℕ} (η v : EuclideanSpace ℂ ι) :
    insertAt η (0 : Fin (n + 1)) v = consIso ι n (v ⊗ₜ tensorPower (Fin n) η) := by
  rw [insertAt_zero, piTensor_cons]
  rfl

theorem insertAt_succ_eq_consIso {n : ℕ} (η v : EuclideanSpace ℂ ι) (k : Fin n) :
    insertAt η k.succ v = consIso ι n (η ⊗ₜ insertAt η k v) := by
  rw [insertAt_apply, insertAt_apply, ← piTensor_cons, Fin.cons_update]
  congr 2
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

/-- The one-dimensional space `ℂ^{Fin 0 → ι}` identified with `ℂ`. -/
def emptyIso (ι : Type) [Fintype ι] : ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 0 → ι) :=
  (OrthonormalBasis.singleton Unit ℂ).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.ofUnique Unit (Fin 0 → ι)))

theorem emptyIso_one (η : EuclideanSpace ℂ ι) : emptyIso ι 1 = tensorPower (Fin 0) η := by
  ext f
  simp [emptyIso, tensorPower, piTensor_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', OrthonormalBasis.singleton_repr]

end Euclid

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
theorem pairHeadIso_frame {ℓ ℓ' : Layout P} (W : Word ℓ ℓ') (z : Mem (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓ)) :
    pairHeadIso ℓ' ((Word.frame _ (Word.frame _ W)).eval z) = W.eval.lTensor _ (pairHeadIso ℓ z) := by
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

/-! ### Allowed monomials on a party layout -/

/-- An allowed monomial on a party layout: source-only words separated by pair effects.

* `final w` is the source-only word `w`.
* `effect hpq α β ℓS w η rest` applies the source-only word `w`, which ends with a register
  `ℂ^α` of the party `p` and a register `ℂ^β` of the party `q ≠ p` in front of the registers
  `ℓS`, contracts these two registers with the bra `⟨η|`, and continues with `rest`.

Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
lines 32–35: compositions of local contractions, preparations of normalized vectors shared
between two participating parties, and contractions by normalized bras shared between two
participating parties. -/
inductive PartyChain : Layout P → Layout P → Type 1
  | final {ℓX ℓY : Layout P} (w : Word ℓX ℓY) : PartyChain ℓX ℓY
  | effect {ℓX ℓY : Layout P} {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [Fintype β]
      (ℓS : Layout P) (w : Word ℓX (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓS))
      (η : EuclideanSpace ℂ (α × β)) (rest : PartyChain ℓS ℓY) : PartyChain ℓX ℓY

namespace PartyChain

/-- The monomial as a chain of contractions and pair effects. -/
@[reducible] def toEffectChain : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → EffectChain (Mem ℓX) (Mem ℓY)
  | _, _, final w => .final w.eval
  | _, _, effect _ α β ℓS w η rest =>
      .effect α β (Mem ℓS) (isoL (pairHeadIso ℓS) ∘L w.eval) η rest.toEffectChain

/-- A monomial is allowed when its words are allowed and its pair effects are normalized.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35. -/
def IsAllowed : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Prop
  | _, _, final w => w.IsAllowed
  | _, _, effect _ _ _ _ w η rest => w.IsAllowed ∧ ‖η‖ = 1 ∧ rest.IsAllowed

theorem isAllowed_toEffectChain : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    M.IsAllowed → M.toEffectChain.IsAllowed
  | _, _, final w, h => w.norm_eval_le_one h
  | _, _, effect _ _ _ _ w _ rest, h =>
      ⟨norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
        (w.norm_eval_le_one h.1), h.2.1, isAllowed_toEffectChain rest h.2.2⟩

/-- The endpoint parties of the pair effects, in order. -/
def effectParties : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → List (P × P)
  | _, _, final _ => []
  | _, _, effect (p := p) (q := q) _ _ _ _ _ _ rest => (p, q) :: rest.effectParties

theorem length_effectParties : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    M.effectParties.length = M.toEffectChain.effectCount
  | _, _, final _ => rfl
  | _, _, effect _ _ _ _ _ _ rest => by
      simp only [effectParties, toEffectChain, List.length_cons, length_effectParties rest]

variable (m : ℕ)

/-- The stacks of all effect occurrences, in front of the layout `ℓ`. -/
@[reducible] def stackApp : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Layout P → Layout P
  | _, _, final _, ℓ => ℓ
  | _, _, effect (p := p) (q := q) _ α β _ _ _ rest, ℓ => pairsOn p q α β m (stackApp rest ℓ)

/-- The registers of the stacks of all effect occurrences.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 99–102: each
occurrence has its own output stack of `m` pair registers, with the dimensions and endpoint
parties of its vector `η`. -/
def stackRegs : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Layout P
  | _, _, final _ => []
  | _, _, effect (p := p) (q := q) _ α β _ _ _ rest => pairRegs p q α β m ++ stackRegs rest

theorem stackApp_eq : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (ℓ : Layout P) →
    M.stackApp m ℓ = M.stackRegs m ++ ℓ
  | _, _, final _, _ => rfl
  | _, _, effect _ _ _ _ _ _ rest, ℓ => by
      rw [stackApp, stackRegs, pairsOn_eq, stackApp_eq rest ℓ, List.append_assoc]

/-- **Ownership of the stacks.** The stack registers of a monomial are owned by the endpoint
parties of its effects: for each effect on `(p, q)`, `m` pair registers, each consisting of a
register of `p` and a register of `q`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
67–68 and 99–102. -/
theorem owner_stackRegs : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (M.stackRegs m).map Reg.owner =
      M.effectParties.flatMap fun e => (List.replicate m [e.1, e.2]).flatten
  | _, _, final _ => rfl
  | _, _, effect _ _ _ _ _ _ rest => by
      simp only [stackRegs, effectParties, List.map_append, map_owner_pairRegs,
        owner_stackRegs rest, List.flatMap_cons]

/-- The terms of the replaced monomial as source-only words: the effect occurrence number `i`
is replaced by the insertion at position `κ i`, and its stack stays idle afterwards.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 96–106 and
121–123. -/
def replaceWord : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (Fin M.toEffectChain.effectCount → Fin m) → Word ℓX (M.stackApp m ℓY)
  | _, _, final w, _ => w
  | _, _, effect hpq _ _ _ w η rest, κ =>
      .comp w (.comp (insWord hpq η m (κ (0 : Fin (rest.toEffectChain.effectCount + 1))))
        (framePairs m (replaceWord rest (Fin.tail κ))))

theorem isAllowed_replaceWord : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → M.IsAllowed →
    ∀ κ, (M.replaceWord m κ).IsAllowed
  | _, _, final _, h, _ => h
  | _, _, effect hpq _ _ _ _ η rest, h, _ =>
      ⟨h.1, isAllowed_insWord hpq η h.2.1 m _,
        isAllowed_framePairs _ (isAllowed_replaceWord rest h.2.2 _) _⟩

/-- The identification of the stack layout with the stack space of the effect chain. -/
def stackAppIso : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (ℓ : Layout P) →
    Mem (M.stackApp m ℓ) ≃ₗᵢ[ℂ] Mem ℓ ⊗[ℂ] M.toEffectChain.stackSpace m
  | _, _, final _, ℓ => (TensorProduct.ridIsometry ℂ (Mem ℓ)).symm
  | _, _, effect (p := p) (q := q) _ α β _ _ _ rest, ℓ =>
      ((stackIso p q α β m (stackApp m rest ℓ)).trans ((stackAppIso rest ℓ).lTensor _)).trans
        (leftCommIso _ _ _)

theorem stackAppIso_final {ℓX ℓY : Layout P} (w : Word ℓX ℓY) (ℓ : Layout P) (x : Mem ℓ) :
    (final w).stackAppIso m ℓ x = x ⊗ₜ (1 : ℂ) :=
  rfl

theorem stackAppIso_effect {ℓX ℓY : Layout P} {p q : P} (hpq : p ≠ q) (α β : Type)
    [Fintype α] [Fintype β] (ℓS : Layout P) (w : Word ℓX (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓS))
    (η : EuclideanSpace ℂ (α × β)) (rest : PartyChain ℓS ℓY) (ℓ : Layout P)
    (z : Mem ((effect hpq α β ℓS w η rest).stackApp m ℓ)) :
    (effect hpq α β ℓS w η rest).stackAppIso m ℓ z =
      leftCommL _ _ _ ((rest.stackAppIso m ℓ).lTensor _
        (stackIso p q α β m (rest.stackApp m ℓ) z)) :=
  rfl

/-- **Each term of a replaced monomial is source-only.**  The term of the replaced monomial with
insertion positions `κ` is the operator of the allowed source-only word `replaceWord`, read on
the stack layout.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
65–66 and 96–123. -/
theorem replaceTerm_toEffectChain : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (κ : Fin M.toEffectChain.effectCount → Fin m) →
    M.toEffectChain.replaceTerm m κ = isoL (M.stackAppIso m ℓY) ∘L (M.replaceWord m κ).eval
  | _, _, final _, _ => rfl
  | _, _, effect hpq α β ℓS w η rest, κ => by
      have ih := replaceTerm_toEffectChain rest (Fin.tail κ)
      simp only [toEffectChain, EffectChain.replaceTerm]
      rw [ih]
      ext1 x
      simp only [replaceWord, Word.eval_comp, comp_apply, isoL_apply]
      rw [stackAppIso_effect, iso_lTensor_apply, stackIso_framePairs, stackIso_insWord, lTensor_comp_apply]

/-- Preparation of the ideal content `η^{⊗ m}` of every stack by pair sources. -/
def prepStack : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (ℓ : Layout P) →
    Word ℓ (M.stackApp m ℓ)
  | _, _, final _, ℓ => .id ℓ
  | _, _, effect hpq _ _ _ _ η rest, ℓ => .comp (prepStack rest ℓ) (prepWord hpq η m _)

theorem isAllowed_prepStack : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → M.IsAllowed →
    ∀ ℓ, (M.prepStack m ℓ).IsAllowed
  | _, _, final _, _, _ => trivial
  | _, _, effect hpq _ _ _ _ η rest, h, ℓ =>
      ⟨isAllowed_prepStack rest h.2.2 ℓ, isAllowed_prepWord hpq η h.2.1 m _⟩

theorem stackAppIso_prepStack : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (ℓ : Layout P) → (x : Mem ℓ) →
    M.stackAppIso m ℓ ((M.prepStack m ℓ).eval x) = x ⊗ₜ M.toEffectChain.stackVector m
  | _, _, final _, _, _ => rfl
  | _, _, effect hpq α β ℓS w η rest, ℓ, x => by
      simp only [prepStack, Word.eval_comp, comp_apply]
      rw [stackAppIso_effect, iso_lTensor_apply, stackIso_prepWord, lTensor_tmul]
      simp only [isoL_apply]
      rw [stackAppIso_prepStack rest ℓ x, leftCommL_tmul]
      rfl

/-- A word on the layout `ℓ` framed by all stacks. -/
def frameStack {ℓ ℓ' : Layout P} : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    Word ℓ ℓ' → Word (M.stackApp m ℓ) (M.stackApp m ℓ')
  | _, _, final _, W => W
  | _, _, effect _ _ _ _ _ _ rest, W => framePairs m (frameStack rest W)

theorem isAllowed_frameStack {ℓ ℓ' : Layout P} (W : Word ℓ ℓ') (hW : W.IsAllowed) :
    {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (M.frameStack m W).IsAllowed
  | _, _, final _ => hW
  | _, _, effect _ _ _ _ _ _ rest => isAllowed_framePairs _ (isAllowed_frameStack W hW rest) _

theorem stackAppIso_frameStack {ℓ ℓ' : Layout P} (W : Word ℓ ℓ') :
    {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (z : Mem (M.stackApp m ℓ)) →
    M.stackAppIso m ℓ' ((M.frameStack m W).eval z) = W.eval.rTensor _ (M.stackAppIso m ℓ z)
  | _, _, final _, _ => rfl
  | _, _, effect hpq α β ℓS w η rest, z => by
      have ih : isoL (rest.stackAppIso m ℓ') ∘L (rest.frameStack m W).eval =
          W.eval.rTensor _ ∘L isoL (rest.stackAppIso m ℓ) :=
        ContinuousLinearMap.ext fun t => stackAppIso_frameStack W rest t
      rw [stackAppIso_effect, iso_lTensor_apply, stackAppIso_effect, iso_lTensor_apply]
      simp only [frameStack]
      rw [stackIso_framePairs, lTensor_comp_apply, ih, lTensor_comp, comp_apply,
        leftCommL_lTensor_rTensor]

end PartyChain

/-! ### Gate expansions on a party layout -/

/-- A gate expansion `G = ∑_ξ c_ξ M_ξ` into monomials on a party layout.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
lines 55–57. -/
abbrev PartyGate (ℓX ℓY : Layout P) : Type 1 := List (ℂ × PartyChain ℓX ℓY)

variable {ℓX ℓY : Layout P} (m : ℕ)

/-- The gate expansion of effect chains of a gate expansion on a party layout. -/
@[reducible] def toGate : PartyGate ℓX ℓY → GateExpansion (Mem ℓX) (Mem ℓY)
  | [] => []
  | p :: L => (p.1, p.2.toEffectChain) :: toGate L

theorem length_toGate : (L : PartyGate ℓX ℓY) → (toGate L).length = L.length
  | [] => rfl
  | _ :: L => by simp only [toGate, List.length_cons, length_toGate L]

theorem map_norm_toGate : (L : PartyGate ℓX ℓY) →
    (toGate L).map (fun p => ‖p.1‖) = L.map fun p => ‖p.1‖
  | [] => rfl
  | _ :: L => by simp only [toGate, List.map_cons, map_norm_toGate L]

theorem mem_toGate {L : PartyGate ℓX ℓY} {p : ℂ × EffectChain (Mem ℓX) (Mem ℓY)}
    (hp : p ∈ toGate L) : ∃ p' ∈ L, p = (p'.1, p'.2.toEffectChain) := by
  induction L with
  | nil => simp [toGate] at hp
  | cons a L ih =>
      simp only [toGate, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨a, List.mem_cons_self, rfl⟩
      · obtain ⟨p', hp', rfl⟩ := ih hp
        exact ⟨p', List.mem_cons_of_mem _ hp', rfl⟩

/-- The output layout of the replaced gate: the stacks of all effect occurrences of all
monomials in front of the output layout of the gate. -/
@[reducible] def gateOut : PartyGate ℓX ℓY → Layout P
  | [] => ℓY
  | p :: L => p.2.stackApp m (gateOut L)

/-- The identification of the output layout of the replaced gate with the output space
`Y ⊗ inventory` of `replaceGate`. -/
def gateIso : (L : PartyGate ℓX ℓY) → Mem (gateOut m L) ≃ₗᵢ[ℂ] Mem ℓY ⊗[ℂ] inventory m (toGate L)
  | [] => (TensorProduct.ridIsometry ℂ (Mem ℓY)).symm
  | p :: L => (p.2.stackAppIso m (gateOut m L)).trans
      (((gateIso L).rTensor _).trans ((TensorProduct.assocIsometry ℂ _ _ _).trans
        ((TensorProduct.commIsometry ℂ _ _).lTensor _)))

theorem gateIso_nil (x : Mem ℓY) : gateIso m ([] : PartyGate ℓX ℓY) x = x ⊗ₜ (1 : ℂ) :=
  rfl

theorem gateIso_cons (p : ℂ × PartyChain ℓX ℓY) (L : PartyGate ℓX ℓY)
    (z : Mem (gateOut m (p :: L))) :
    gateIso m (p :: L) z =
      (TensorProduct.commIsometry ℂ (inventory m (toGate L)) (p.2.toEffectChain.stackSpace m)).lTensor
        (Mem ℓY) (TensorProduct.assocIsometry ℂ (Mem ℓY) (inventory m (toGate L))
          (p.2.toEffectChain.stackSpace m)
          ((gateIso m L).rTensor (p.2.toEffectChain.stackSpace m)
            (p.2.stackAppIso m (gateOut m L) z))) :=
  rfl

theorem gateIso_cons_clm (p : ℂ × PartyChain ℓX ℓY) (L : PartyGate ℓX ℓY) :
    isoL (gateIso m (p :: L)) =
      isoL ((TensorProduct.commIsometry ℂ (inventory m (toGate L))
          (p.2.toEffectChain.stackSpace m)).lTensor (Mem ℓY)) ∘L
        isoL (TensorProduct.assocIsometry ℂ (Mem ℓY) (inventory m (toGate L))
          (p.2.toEffectChain.stackSpace m)) ∘L
        isoL ((gateIso m L).rTensor (p.2.toEffectChain.stackSpace m)) ∘L
        isoL (p.2.stackAppIso m (gateOut m L)) :=
  rfl

/-- Preparation of the common garbage vector `Γ_m` by pair sources. -/
def prepGate : (L : PartyGate ℓX ℓY) → Word ℓY (gateOut m L)
  | [] => .id ℓY
  | p :: L => .comp (prepGate L) (p.2.prepStack m (gateOut m L))

theorem isAllowed_prepGate : (L : PartyGate ℓX ℓY) → (∀ p ∈ L, p.2.IsAllowed) →
    (prepGate m L).IsAllowed
  | [], _ => trivial
  | p :: L, h => ⟨isAllowed_prepGate L fun q hq => h q (List.mem_cons_of_mem _ hq),
      p.2.isAllowed_prepStack m (h p List.mem_cons_self) _⟩

/-- **The garbage vector is prepared by pair sources.** The word `prepGate` prepares, by
normalized pair sources on the endpoint parties, the common garbage vector `Γ_m` appended in
every branch.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 103–112. -/
theorem gateIso_prepGate : (L : PartyGate ℓX ℓY) → (x : Mem ℓY) →
    gateIso m L ((prepGate m L).eval x) = x ⊗ₜ inventoryVector m (toGate L)
  | [], x => rfl
  | p :: L, x => by
      simp only [prepGate, Word.eval_comp, comp_apply]
      rw [gateIso_cons, PartyChain.stackAppIso_prepStack, iso_rTensor_apply, rTensor_tmul]
      simp only [isoL_apply]
      rw [gateIso_prepGate L x]
      simp only [TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul, iso_lTensor_apply,
        lTensor_tmul, isoL_apply, TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]
      rfl

/-- The expansion of the replaced gate into weighted source-only words: the term of a
monomial `c M` with `n` effects and insertion positions `κ` has coefficient `c / m^n`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
65–67 and 103–125. -/
def wordList : (L : PartyGate ℓX ℓY) → List (ℂ × Word ℓX (gateOut m L))
  | [] => []
  | p :: L =>
      (Finset.univ.toList.map fun κ => (p.1 * ((m : ℂ) ^ p.2.toEffectChain.effectCount)⁻¹,
        Word.comp (p.2.replaceWord m κ) (p.2.frameStack m (prepGate m L)))) ++
      (wordList L).map fun q => (q.1, Word.comp q.2 (p.2.prepStack m (gateOut m L)))

/-- **Each term of the replaced gate is source-only.** The expansion `termList` of the replaced
gate is, term by term, the expansion into the source-only words `wordList`, read on the output
layout `gateOut` through `gateIso`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
65–66 and 103–125. -/
theorem termList_toGate : (L : PartyGate ℓX ℓY) →
    termList m (toGate L) = (wordList m L).map fun q => (q.1, isoL (gateIso m L) ∘L q.2.eval)
  | [] => rfl
  | p :: L => by
      simp only [toGate, termList, wordList, List.map_append, List.map_map]
      congr 1
      · refine List.map_congr_left fun κ _ => Prod.ext rfl ?_
        dsimp only [Function.comp_apply]
        rw [PartyChain.replaceTerm_toEffectChain, gateIso_cons_clm]
        ext1 x
        simp only [Word.eval_comp, comp_apply, isoL_apply]
        rw [PartyChain.stackAppIso_frameStack, iso_rTensor_apply,
          rTensor_comp_apply, show isoL (gateIso m L) ∘L (prepGate m L).eval =
            appendRight (inventoryVector m (toGate L)) from
          ContinuousLinearMap.ext fun y => gateIso_prepGate m L y]
        induction (p.2.stackAppIso m ℓY ((p.2.replaceWord m κ).eval x)) using
          TensorProduct.inductionOn with
        | tmul y s =>
            simp only [rTensor_tmul, appendRight_apply, assocL_tmul,
              TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul, iso_lTensor_apply,
              lTensor_tmul, isoL_apply, TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]
        | add a b ha hb => simp only [map_add, ha, hb]
      · rw [termList_toGate L, List.map_map]
        refine List.map_congr_left fun q _ => Prod.ext rfl ?_
        dsimp only [Function.comp_apply]
        rw [gateIso_cons_clm]
        ext1 x
        simp only [Word.eval_comp, comp_apply, isoL_apply]
        rw [PartyChain.stackAppIso_prepStack, iso_rTensor_apply, rTensor_tmul]
        simp only [isoL_apply, appendLeft_apply]
        induction (gateIso m L (q.2.eval x)) using TensorProduct.inductionOn with
        | tmul y s =>
            simp only [leftCommL_tmul, TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul,
              iso_lTensor_apply, lTensor_tmul, isoL_apply, TensorProduct.commIsometry_apply,
              TensorProduct.comm_tmul]
        | add a b ha hb =>
            simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]

theorem isAllowed_wordList : (L : PartyGate ℓX ℓY) → (∀ p ∈ L, p.2.IsAllowed) →
    ∀ q ∈ wordList m L, q.2.IsAllowed
  | [], _ => by simp [wordList]
  | p :: L, h => by
      have hp := h p List.mem_cons_self
      have hL : ∀ q ∈ L, q.2.IsAllowed := fun q hq => h q (List.mem_cons_of_mem _ hq)
      intro q hq
      simp only [wordList, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨κ, _, rfl⟩ | ⟨q', hq', rfl⟩
      · exact ⟨p.2.isAllowed_replaceWord m hp κ,
          PartyChain.isAllowed_frameStack m _ (isAllowed_prepGate m L hL) p.2⟩
      · exact ⟨isAllowed_wordList L hL q' hq', p.2.isAllowed_prepStack m hp _⟩

/-- **Every term of the replaced gate is source-only.** Each term of the expansion `termList`
of the replaced gate, read on the output layout `gateOut`, is a composition of local
contractions and normalized pair sources.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
65–66. -/
theorem isSourceOnly_termList (L : PartyGate ℓX ℓY) (hL : ∀ p ∈ L, p.2.IsAllowed) :
    ∀ q ∈ termList m (toGate L), IsSourceOnly (isoL (gateIso m L).symm ∘L q.2) := by
  intro q hq
  rw [termList_toGate, List.mem_map] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  refine ⟨w.2, isAllowed_wordList m L hL w hw, ?_⟩
  ext1 x
  simp only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The additional registers of the replaced gate: the stacks of all effect occurrences. -/
theorem gateOut_eq : (L : PartyGate ℓX ℓY) →
    gateOut m L = (L.flatMap fun p => p.2.stackRegs m) ++ ℓY
  | [] => rfl
  | p :: L => by
      simp only [gateOut, PartyChain.stackApp_eq, gateOut_eq L, List.flatMap_cons,
        List.append_assoc]

/-! ### Combining pair sources -/

/-- The regrouping `(U ⊗ V) ⊗ (U' ⊗ V') ≅ (U ⊗ U') ⊗ (V ⊗ V')` of two pair vectors on the same
pair of parties. -/
def pairRegroup (U V U' V' : HSpace) :
    (U ⊗[ℂ] V) ⊗[ℂ] (U' ⊗[ℂ] V') ≃ₗᵢ[ℂ] (U ⊗[ℂ] U') ⊗[ℂ] (V ⊗[ℂ] V') :=
  (TensorProduct.assocIsometry ℂ U V (U' ⊗[ℂ] V')).trans <|
    ((((TensorProduct.assocIsometry ℂ V U' V').symm.trans
      (((TensorProduct.commIsometry ℂ V U').rTensor V').trans
        (TensorProduct.assocIsometry ℂ U' V V'))).lTensor U).trans
      (TensorProduct.assocIsometry ℂ U U' (V ⊗[ℂ] V')).symm)

theorem pairRegroup_tmul (U V U' V' : HSpace) (u : U) (v : V) (u' : U') (v' : V') :
    pairRegroup U V U' V' ((u ⊗ₜ v) ⊗ₜ (u' ⊗ₜ v')) = (u ⊗ₜ u') ⊗ₜ (v ⊗ₜ v') := by
  simp only [pairRegroup, LinearIsometryEquiv.trans_apply, iso_lTensor_apply, iso_rTensor_apply,
    TensorProduct.assocIsometry_apply, TensorProduct.assocIsometry_symm_apply,
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul, lTensor_tmul, rTensor_tmul,
    isoL_apply, TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]

/-- Merging two registers of one party into one register. -/
def mergeIso (p : P) (U U' : HSpace) :
    Mem [⟨p, U⟩, ⟨p, U'⟩] ≃ₗᵢ[ℂ] Mem [⟨p, HSpace.of (U ⊗[ℂ] U')⟩] :=
  (TensorProduct.assocIsometry ℂ U U' ℂ).symm

/-- Two pair sources on the same pair of parties, followed by merging the two registers of each
party. -/
def combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) (η : U ⊗[ℂ] V)
    (η' : U' ⊗[ℂ] V') (ℓ : Layout P) :
    Word ℓ (⟨p, HSpace.of (U ⊗[ℂ] U')⟩ :: ⟨q, HSpace.of (V ⊗[ℂ] V')⟩ :: ℓ) :=
  .comp (.source hpq U' V' η' ℓ) <| .comp (.source hpq U V η _) <|
    .comp (.frame _ (.swap _ _ _)) <|
    .comp (.localMap p (ℓ₁ := [⟨p, U⟩, ⟨p, U'⟩]) (ℓ₂ := [⟨p, HSpace.of (U ⊗[ℂ] U')⟩])
      (by simp) (by simp) (isoL (mergeIso p U U')) (⟨q, V⟩ :: ⟨q, V'⟩ :: ℓ)) <|
    .frame _ (.localMap q (ℓ₁ := [⟨q, V⟩, ⟨q, V'⟩]) (ℓ₂ := [⟨q, HSpace.of (V ⊗[ℂ] V')⟩])
      (by simp) (by simp) (isoL (mergeIso q V V')) ℓ)

theorem isAllowed_combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) {η : U ⊗[ℂ] V}
    {η' : U' ⊗[ℂ] V'} (hη : ‖η‖ = 1) (hη' : ‖η'‖ = 1) (ℓ : Layout P) :
    (combineSources hpq U V U' V' η η' ℓ).IsAllowed :=
  ⟨hη', hη, trivial, LinearIsometry.norm_toContinuousLinearMap_le _,
    LinearIsometry.norm_toContinuousLinearMap_le _⟩

/-- **Combining pair sources.** Two pair sources `η` and `η'` on the same pair of parties,
followed by merging the two registers of each party, are the single pair source of the
regrouped vector `η ⊗ η'`, whose norm is `‖η‖ ‖η'‖`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
68–69 and 124–126. -/
theorem eval_combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) (η : U ⊗[ℂ] V)
    (η' : U' ⊗[ℂ] V') (ℓ : Layout P) :
    (combineSources hpq U V U' V' η η' ℓ).eval =
        (Word.source hpq _ _ (pairRegroup U V U' V' (η ⊗ₜ η')) ℓ).eval ∧
      ‖pairRegroup U V U' V' (η ⊗ₜ η')‖ = ‖η‖ * ‖η'‖ := by
  refine ⟨?_, by rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul]⟩
  ext1 x
  induction η using TensorProduct.inductionOn with
  | add a b ha hb =>
      simp only [combineSources, Word.eval, comp_apply, appendLeft_apply] at ha hb ⊢
      simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | tmul u v =>
      induction η' using TensorProduct.inductionOn with
      | add a b ha hb =>
          simp only [combineSources, Word.eval, comp_apply, appendLeft_apply] at ha hb ⊢
          simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]
      | tmul u' v' =>
          simp [combineSources, Word.eval, appendIso, mergeIso, pairRegroup_tmul,
            TensorProduct.assoc_symm_tmul, TensorProduct.lid_symm_apply,
            LinearIsometryEquiv.symm_lTensor]

/-! ### Lemma 5.1 on a party layout -/

/-- **Elimination of normalized pair effects** (Lemma 5.1 `lem:effects`).  Let
`G = ∑_ξ c_ξ M_ξ` be a gate expansion into `K` allowed monomials on a party layout, each with at
most `r` pair effects, and let `m ≥ 1`.  Then, with the replaced gate `G'_m = replaceGate` and
the common garbage vector `Γ_m = inventoryVector`:

* `Γ_m` is normalized and is prepared by the allowed source-only word `prepGate`;
* `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`;
* read on the output layout `gateOut` through `gateIso`, `G'_m` is the weighted sum of the
  allowed source-only words of `wordList`: local contractions and normalized pair sources;
  equivalently, every term of the expansion `termList` is source-only;
* there are at most `K m^r` such words, with absolute coefficient sum `∑_ξ |c_ξ|`;
* the output layout consists of the stacks of all effect occurrences followed by the output
  layout of `G`, and the stacks of a monomial are owned by the endpoint parties of its effects.

The combination of the sources on one pair of parties into one normalized pair source is
`eval_combineSources`.  The hypothesis that `G` is a contraction is not needed.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
`04-compression.tex`, lines 53–127. -/
theorem partyPairEffectElimination {m r : ℕ} (hm : m ≠ 0) (L : PartyGate ℓX ℓY)
    (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.toEffectChain.effectCount ≤ r) :
    ‖inventoryVector m (toGate L)‖ = 1 ∧
    (∀ x, gateIso m L ((prepGate m L).eval x) = x ⊗ₜ inventoryVector m (toGate L)) ∧
    (prepGate m L).IsAllowed ∧
    ‖replaceGate m (toGate L) - appendRight (inventoryVector m (toGate L)) ∘L gate (toGate L)‖ ≤
      r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum ∧
    replaceGate m (toGate L) =
      ((wordList m L).map fun q => q.1 • (isoL (gateIso m L) ∘L q.2.eval)).sum ∧
    (∀ q ∈ wordList m L, q.2.IsAllowed) ∧
    (∀ q ∈ termList m (toGate L), IsSourceOnly (isoL (gateIso m L).symm ∘L q.2)) ∧
    (wordList m L).length ≤ L.length * m ^ r ∧
    ((wordList m L).map fun q => ‖q.1‖).sum = (L.map fun p => ‖p.1‖).sum ∧
    gateOut m L = (L.flatMap fun p => p.2.stackRegs m) ++ ℓY ∧
    ∀ p ∈ L, (p.2.stackRegs m).map Reg.owner =
      p.2.effectParties.flatMap fun e => (List.replicate m [e.1, e.2]).flatten := by
  have hG : ∀ p ∈ toGate L, p.2.IsAllowed ∧ p.2.effectCount ≤ r := by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := mem_toGate hp
    exact ⟨p'.2.isAllowed_toEffectChain (hL p' hp').1, (hL p' hp').2⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := pairEffectElimination hm (toGate L) hG
  have hA : ∀ p ∈ L, p.2.IsAllowed := fun p hp => (hL p hp).1
  rw [termList_toGate] at h3 h4 h5
  rw [List.map_map] at h3 h5
  rw [List.length_map, length_toGate] at h4
  rw [map_norm_toGate] at h2 h5
  refine ⟨h1, gateIso_prepGate m L, isAllowed_prepGate m L hA, h2, ?_,
    isAllowed_wordList m L hA, isSourceOnly_termList m L hA, h4, ?_, gateOut_eq m L,
    fun p _ => p.2.owner_stackRegs m⟩
  · rw [h3]
    rfl
  · rw [← h5]
    rfl

end TNLean.PEPS.PairEffect
