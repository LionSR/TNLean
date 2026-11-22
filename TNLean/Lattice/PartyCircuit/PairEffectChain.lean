/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TensorProduct.CyclicInsertion
import QICLean.Analysis.TensorProduct.TensorProductContraction

/-!
# Pair effects and the replaced monomial

A monomial of a gate expansion is a composition of contractions, preparations of normalized
pair vectors, and contractions by normalized pair bras (pair effects).  Grouping the steps
between consecutive effects, a monomial with `n` effects is a chain
`F_n ∘ E_n ∘ F_{n-1} ∘ ⋯ ∘ E_1 ∘ F_0`, where each `F_i` is a contraction and each
`E_i = ⟨η_i| ⊗ 1` contracts a pair register with a normalized pair vector `η_i` and leaves a
spectator space untouched.  We formalize such chains as `EffectChain`.

Each effect occurrence receives its own output stack of `m` pair registers.  In the replaced
monomial the effect `⟨η|` is replaced by the cyclic insertion `T_m`, and the stack stays idle
afterwards.  The ideal replacement appends the fixed vector `η^{⊗ m}`.  Telescoping the `n`
replacements in one monomial gives the error `n / √m`.

The expansion of the replaced monomial into its terms and the gate expansions are treated in
`TNLean.Lattice.PartyCircuit.PairEffectElimination`.

## Main definitions

* `PartyCircuit.effectMap` : the pair effect `⟨η| ⊗ 1`.
* `PartyCircuit.HSpace` : a bundled complex inner product space.
* `PartyCircuit.EffectChain` : a monomial written as a chain of contractions and pair effects.
* `PartyCircuit.EffectChain.eval` : the operator of a monomial.
* `PartyCircuit.EffectChain.replace` : the replaced monomial with occurrence-specific stacks.
* `PartyCircuit.EffectChain.replaceTerm` : one term of the expansion of the replaced monomial.

## Main results

* `PartyCircuit.EffectChain.norm_replace_sub_le` : telescoping bound `n / √m` for one monomial.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.Lattice.PartyCircuit

open EuclideanSpace CyclicInsertion ContinuousLinearMap

/-! ### Pair effects -/

/-- The pair effect `⟨η| ⊗ 1 : (ℂ^ι) ⊗ S → S`. -/
def effectMap {ι : Type*} [Fintype ι] (η : EuclideanSpace ℂ ι) (S : Type*)
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] :
    EuclideanSpace ℂ ι ⊗[ℂ] S →L[ℂ] S :=
  (TensorProduct.lidIsometry ℂ S).toLinearIsometry.toContinuousLinearMap ∘L
    (innerSL ℂ η).rTensor S

@[simp]
theorem effectMap_tmul {ι : Type*} [Fintype ι] (η : EuclideanSpace ℂ ι) {S : Type*}
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] (h : EuclideanSpace ℂ ι) (s : S) :
    effectMap η S (h ⊗ₜ[ℂ] s) = ⟪η, h⟫_ℂ • s := by
  simp [effectMap]

theorem norm_effectMap_le {ι : Type*} [Fintype ι] {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℂ S] :
    ‖effectMap η S‖ ≤ 1 := by
  refine (opNorm_comp_le _ _).trans ?_
  calc _ ≤ 1 * ‖innerSL ℂ η‖ := by
        gcongr
        · exact LinearIsometry.norm_toContinuousLinearMap_le _
        · exact norm_rTensor_le _ _
    _ = 1 := by rw [innerSL_apply_norm, hη, one_mul]

/-! ### Monomials as chains of contractions and pair effects -/

/-- A complex inner product space, bundled so that monomials can be indexed by their input and
output spaces. -/
structure HSpace : Type 1 where
  /-- The underlying type. -/
  carrier : Type
  [instNormedAddCommGroup : NormedAddCommGroup carrier]
  [instInnerProductSpace : InnerProductSpace ℂ carrier]

attribute [instance] HSpace.instNormedAddCommGroup HSpace.instInnerProductSpace

instance : CoeSort HSpace Type := ⟨HSpace.carrier⟩

/-- The bundled space of a complex inner product space. -/
abbrev HSpace.of (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : HSpace := ⟨E⟩

/-- A monomial of a gate expansion, written as a chain `F_n ∘ E_n ∘ ⋯ ∘ E_1 ∘ F_0` of
effect-free pieces `F_i` and pair effects `E_i = ⟨η_i| ⊗ 1`.

* `final F` is the effect-free piece `F` with no further effect.
* `effect α β S F η rest` first applies the effect-free piece `F`, which ends with a pair
  register `ℂ^α ⊗ ℂ^β` next to the spectator space `S`, then contracts the pair register with
  the bra `⟨η|`, and continues with the monomial `rest` on `S`.

Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
lines 32–35. -/
inductive EffectChain : HSpace → HSpace → Type 1
  | final {X Y : HSpace} (F : X →L[ℂ] Y) : EffectChain X Y
  | effect {X Y : HSpace} (α β : Type) [Fintype α] [Fintype β] (S : HSpace)
      (F : X →L[ℂ] EuclideanSpace ℂ (α × β) ⊗[ℂ] S)
      (η : EuclideanSpace ℂ (α × β)) (rest : EffectChain S Y) : EffectChain X Y

namespace EffectChain

/-- The operator of a monomial. -/
def eval : {X Y : HSpace} → EffectChain X Y → (X →L[ℂ] Y)
  | _, _, final F => F
  | _, _, effect _ _ S F η rest => rest.eval ∘L effectMap η S ∘L F

/-- The number of pair effects of a monomial. -/
@[reducible] def effectCount : {X Y : HSpace} → EffectChain X Y → ℕ
  | _, _, final _ => 0
  | _, _, effect _ _ _ _ _ rest => rest.effectCount + 1

/-- A monomial is allowed when its effect-free pieces are contractions and its pair effects
are normalized.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35. -/
def IsAllowed : {X Y : HSpace} → EffectChain X Y → Prop
  | _, _, final F => ‖F‖ ≤ 1
  | _, _, effect _ _ _ F η rest => ‖F‖ ≤ 1 ∧ ‖η‖ = 1 ∧ rest.IsAllowed

/-- The stack space of a monomial: one stack of `m` pair registers for each of its effect
occurrences. -/
@[reducible] def stackSpace (m : ℕ) : {X Y : HSpace} → EffectChain X Y → HSpace
  | _, _, final _ => HSpace.of ℂ
  | _, _, effect α β _ _ _ rest =>
      HSpace.of (EuclideanSpace ℂ (Fin m → α × β) ⊗[ℂ] (rest.stackSpace m))

/-- The ideal content of the stacks of a monomial: `η^{⊗ m}` in the stack of each effect
occurrence. -/
def stackVector (m : ℕ) : {X Y : HSpace} → (M : EffectChain X Y) → M.stackSpace m
  | _, _, final _ => (1 : ℂ)
  | _, _, effect _ _ _ _ η rest => tensorPower (Fin m) η ⊗ₜ[ℂ] rest.stackVector m

/-- The replaced monomial: each effect `⟨η|` is replaced by the cyclic insertion `T_m` into
the stack of that occurrence, and the stack stays idle afterwards.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 5.1, `04-compression.tex`,
lines 100–106. -/
def replace (m : ℕ) : {X Y : HSpace} → (M : EffectChain X Y) → (X →L[ℂ] Y ⊗[ℂ] M.stackSpace m)
  | _, _, final F => appendRight (1 : ℂ) ∘L F
  | _, _, effect α β S F η rest =>
      leftCommL _ _ _ ∘L (rest.replace m).lTensor (EuclideanSpace ℂ (Fin m → α × β)) ∘L
        (cyclicInsertion η m).rTensor S ∘L F

/-- One term of the expansion of the replaced monomial: the effect occurrence number `i` is
replaced by the insertion at position `κ i`.  The definition applies no pair bra: it composes
the pieces `F_i` of the monomial with insertions, which are preparations of copies of the
normalized pair vector followed by register permutations (`CyclicInsertion.insertAt_zero`,
`CyclicInsertion.insertAt_perm`).  On a party layout, each term is the operator of a word of
local contractions and normalized pair sources (`PartyChain.replaceTerm_toEffectChain`).

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 96–98 and
121–123. -/
def replaceTerm (m : ℕ) : {X Y : HSpace} →
    (M : EffectChain X Y) → (Fin M.effectCount → Fin m) → (X →L[ℂ] Y ⊗[ℂ] M.stackSpace m)
  | _, _, final F, _ => appendRight (1 : ℂ) ∘L F
  | _, _, effect α β S F η rest, κ =>
      leftCommL _ _ _ ∘L
        (rest.replaceTerm m (Fin.tail κ)).lTensor (EuclideanSpace ℂ (Fin m → α × β)) ∘L
        (insertAt η (κ (0 : Fin (rest.effectCount + 1)))).rTensor S ∘L F

theorem norm_eval_le_one : {X Y : HSpace} → (M : EffectChain X Y) → M.IsAllowed →
    ‖M.eval‖ ≤ 1
  | _, _, final _, h => h
  | _, _, effect _ _ S _ _ rest, h => by
      obtain ⟨hF, hη, hrest⟩ := h
      exact norm_comp_le_one (norm_eval_le_one rest hrest)
        (norm_comp_le_one (norm_effectMap_le hη S) hF)

theorem norm_stackVector (m : ℕ) : {X Y : HSpace} → (M : EffectChain X Y) → M.IsAllowed →
    ‖M.stackVector m‖ = 1
  | _, _, final _, _ => norm_one (α := ℂ)
  | _, _, effect _ _ _ _ η rest, h => by
      obtain ⟨_, hη, hrest⟩ := h
      simp only [stackVector]
      rw [TensorProduct.norm_tmul, norm_tensorPower hη, norm_stackVector m rest hrest, one_mul]

theorem norm_replace_le_one (m : ℕ) : {X Y : HSpace} → (M : EffectChain X Y) →
    M.IsAllowed → ‖M.replace m‖ ≤ 1
  | _, _, final _, h => norm_comp_le_one norm_appendRight_one_le h
  | _, _, effect _ _ _ _ _ rest, h => by
      obtain ⟨hF, hη, hrest⟩ := h
      exact norm_comp_le_one norm_leftCommL_le <| norm_comp_le_one
        ((norm_lTensor_le _ _).trans (norm_replace_le_one m rest hrest)) <|
        norm_comp_le_one ((norm_rTensor_le _ _).trans (norm_cyclicInsertion_le_one hη m)) hF

theorem norm_replaceTerm_le_one (m : ℕ) : {X Y : HSpace} → (M : EffectChain X Y) →
    M.IsAllowed → ∀ κ, ‖M.replaceTerm m κ‖ ≤ 1
  | _, _, final _, h, _ => norm_comp_le_one norm_appendRight_one_le h
  | _, _, effect _ _ _ _ _ rest, h, _ => by
      obtain ⟨hF, hη, hrest⟩ := h
      exact norm_comp_le_one norm_leftCommL_le <| norm_comp_le_one
        ((norm_lTensor_le _ _).trans (norm_replaceTerm_le_one m rest hrest _)) <|
        norm_comp_le_one ((norm_rTensor_le _ _).trans (norm_insertAt_le_one hη _)) hF

/-- The ideal replacement of an effect occurrence appends `η^{⊗ m}` after the original
effect. -/
theorem appendRight_comp_eval_effect {X Y : HSpace} {α β : Type} [Fintype α] [Fintype β]
    {S : HSpace} (m : ℕ) (F : X →L[ℂ] EuclideanSpace ℂ (α × β) ⊗[ℂ] S)
    (η : EuclideanSpace ℂ (α × β)) (rest : EffectChain S Y) :
    appendRight ((effect α β S F η rest).stackVector m) ∘L (effect α β S F η rest).eval =
      leftCommL _ _ _ ∘L
        (appendRight (rest.stackVector m) ∘L rest.eval).lTensor
          (EuclideanSpace ℂ (Fin m → α × β)) ∘L
        (idealInsertion η m).rTensor S ∘L F := by
  simp only [stackVector, eval, ← comp_assoc]
  congr 1
  ext1 t
  induction t using TensorProduct.inductionOn with
  | tmul h s =>
      simp only [comp_apply, effectMap_tmul, map_smul, appendRight_apply, rTensor_tmul,
        idealInsertion_apply, lTensor_tmul]
      simp only [← TensorProduct.smul_tmul', map_smul, leftCommL_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Telescoping bound for one monomial.** Replacing the `n` effects of an allowed monomial
by cyclic insertions changes it by at most `n / √m` from the ideal augmented monomial
`M ⊗ |η_1^{⊗ m} ⊗ ⋯ ⊗ η_n^{⊗ m}⟩`.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 5.1, `04-compression.tex`,
lines 117–121. -/
theorem norm_replace_sub_le {m : ℕ} (hm : m ≠ 0) :
    {X Y : HSpace} → (M : EffectChain X Y) → M.IsAllowed →
    ‖M.replace m - appendRight (M.stackVector m) ∘L M.eval‖ ≤ M.effectCount / Real.sqrt m
  | _, _, final F, _ => by
      simp only [replace, stackVector, eval, sub_self, norm_zero, effectCount,
        CharP.cast_eq_zero, zero_div, le_refl]
  | _, _, effect α β S F η rest, h => by
      obtain ⟨hF, hη, hrest⟩ := h
      rw [appendRight_comp_eval_effect]
      set A := rest.replace m
      set I := appendRight (rest.stackVector m) ∘L rest.eval
      set T := cyclicInsertion η m
      set P := idealInsertion η m
      set W := EuclideanSpace ℂ (Fin m → α × β)
      have hsplit : replace m (effect α β S F η rest) -
          leftCommL _ _ _ ∘L I.lTensor W ∘L P.rTensor S ∘L F =
          leftCommL _ _ _ ∘L ((A - I).lTensor W ∘L T.rTensor S +
            I.lTensor W ∘L (T - P).rTensor S) ∘L F := by
        simp only [replace, lTensor_sub, rTensor_sub, sub_comp, comp_sub, add_comp, comp_add]
        abel
      have hI : ‖I‖ ≤ 1 := norm_comp_le_one
        ((norm_appendRight_le _).trans (norm_stackVector m rest hrest).le)
        (norm_eval_le_one rest hrest)
      have hA := norm_replace_sub_le hm rest hrest
      have hT : ‖T‖ ≤ 1 := norm_cyclicInsertion_le_one hη m
      have hTP := norm_rTensor_cyclicInsertion_sub_ideal_le hη hm S
      have hmid : ‖(A - I).lTensor W ∘L T.rTensor S + I.lTensor W ∘L (T - P).rTensor S‖ ≤
          (rest.effectCount + 1 : ℕ) / Real.sqrt m := by
        refine (norm_add_le _ _).trans ?_
        have h1 : ‖(A - I).lTensor W ∘L T.rTensor S‖ ≤ rest.effectCount / Real.sqrt m :=
          (opNorm_comp_le _ _).trans <| by
            calc _ ≤ ‖A - I‖ * 1 := by
                  gcongr
                  · exact norm_lTensor_le _ _
                  · exact (norm_rTensor_le _ _).trans hT
              _ ≤ _ := by rw [mul_one]; exact hA
        have h2 : ‖I.lTensor W ∘L (T - P).rTensor S‖ ≤ 1 / Real.sqrt m :=
          (opNorm_comp_le _ _).trans <| by
            calc _ ≤ 1 * (1 / Real.sqrt m) := by
                  gcongr
                  · exact (norm_lTensor_le _ _).trans hI
              _ = _ := one_mul _
        calc _ ≤ rest.effectCount / Real.sqrt m + 1 / Real.sqrt m := add_le_add h1 h2
          _ = _ := by push_cast; ring
      rw [hsplit]
      refine (opNorm_comp_le _ _).trans ?_
      refine (mul_le_mul norm_leftCommL_le le_rfl (norm_nonneg _) zero_le_one).trans ?_
      rw [one_mul]
      refine (opNorm_comp_le _ _).trans ?_
      calc _ ≤ ((rest.effectCount + 1 : ℕ) / Real.sqrt m) * 1 :=
            mul_le_mul hmid hF (norm_nonneg _) (by positivity)
        _ = _ := by rw [mul_one]

end EffectChain

end TNLean.Lattice.PartyCircuit
