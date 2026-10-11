/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameBoundedChanges

/-!
# Rank-one operators on blocks of sites as allowed monomials

The last step of the proof of Lemma 6.3 of the polynomial-PEPS manuscript reads a product of
normalized vectors and covectors on groups of sites, each group on at most two parties, as a
monomial allowed by Theorem 5.2. This file provides the pieces of that reading on the registers
of an encoded frame, one register per site and per tag (`TNLean.PEPS.Approximation.FrameRegisters`).

* `PairEffect.PartyChain.append`: two monomials applied in succession.
* `PairEffect.rankOneChain`: on two registers `ℂ^α` of `p_A` and `ℂ^β` of `p_B`, the
  rank-one map `|v⟩⟨w|` followed by a change of the owners to `p_A'` and `p_B'`. The bra is a
  normalized pair effect when `p_A ≠ p_B` and a private contraction otherwise; the ket is a
  normalized pair source when `p_A' ≠ p_B'` and a private preparation otherwise
  (`pairHeadIso_rankOneChain`).
* `EncodedFrame.RankOneBlock`: a block of sites split into a part `T` and a part `U`, with the
  complement `E`, and two unit vectors on `(T → Fin q) × (U → Fin q)`; its operator is
  `|v⟩⟨w|_{T ∪ U} ⊗ 1_E` (`RankOneBlock.op_apply`). Products of operators of pairwise disjoint
  blocks are computed entrywise (`RankOneBlock.prod_op_apply`).
* `EncodedFrame.exists_rankOneBlock_chain`: if the sites of `T` are held by `p_A` before and
  `p_A'` after, and those of `U` by `p_B` and `p_B'`, the operator `1_tags ⊗ op` is an allowed
  monomial on the registers of the frame, using only these four parties, with at most one pair
  source and at most one pair effect.

## Main definitions

* `PairEffect.PartyChain.append`, `PairEffect.rankOneChain`.
* `EncodedFrame.RankOneBlock`, `EncodedFrame.RankOneBlock.op`, `EncodedFrame.zeroPair`.

## Main results

* `PairEffect.PartyChain.eval_append`, `PairEffect.PartyChain.append_props`.
* `PairEffect.pairHeadIso_rankOneChain`, `PairEffect.rankOneChain_props`.
* `EncodedFrame.RankOneBlock.op_apply`, `EncodedFrame.RankOneBlock.prod_op_apply`.
* `EncodedFrame.exists_pairVec`: a vector on the sites of a group read on its two parts.
* `EncodedFrame.exists_rankOneBlock_chain`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 306–316; allowed monomials, `04-compression.tex`, lines 32–35.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

/-! ### Composing monomials -/

namespace TNLean.PEPS.PairEffect.PartyChain

variable {P : Type}

/-- Two monomials applied in succession: first `M`, then `M'`. -/
def append {ℓZ : Layout P} : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → PartyChain ℓY ℓZ →
    PartyChain ℓX ℓZ
  | _, _, final w, M' => M'.precomp w
  | _, _, effect hpq α β ℓS w η rest, M' => effect hpq α β ℓS w η (rest.append M')

theorem eval_append {ℓZ : Layout P} : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (M' : PartyChain ℓY ℓZ) →
      (M.append M').toEffectChain.eval = M'.toEffectChain.eval ∘L M.toEffectChain.eval
  | _, _, final w, M' => eval_precomp w M'
  | _, _, effect _ _ _ _ _ _ rest, M' => by
      change (rest.append M').toEffectChain.eval ∘L _ ∘L _ =
        M'.toEffectChain.eval ∘L (rest.toEffectChain.eval ∘L _ ∘L _)
      rw [eval_append rest M']
      rfl

/-- Composing two allowed monomials on a list of parties gives an allowed monomial on the same
list; the pair sources and the pair effects add up. -/
theorem append_props {ℓZ : Layout P} (S : Set P) : {ℓX ℓY : Layout P} →
    (M : PartyChain ℓX ℓY) → (M' : PartyChain ℓY ℓZ) → M.IsAllowed → M.UsesOnly S →
      M'.IsAllowed → M'.UsesOnly S →
      (M.append M').IsAllowed ∧ (M.append M').UsesOnly S ∧
        (M.append M').sourceCount = M.sourceCount + M'.sourceCount ∧
        (M.append M').toEffectChain.effectCount =
          M.toEffectChain.effectCount + M'.toEffectChain.effectCount
  | _, _, final w, M', hM, hMS, hM', hM'S => by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := precomp_props w S hM hMS M' hM' hM'S
      refine ⟨h₁, h₂, h₃, ?_⟩
      rw [append, h₄]
      exact (zero_add _).symm
  | _, _, effect _ _ _ _ _ _ rest, M', hM, hMS, hM', hM'S => by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := append_props S rest M' hM.2.2 hMS.2.2.2 hM' hM'S
      refine ⟨⟨hM.1, hM.2.1, h₁⟩, ⟨hMS.1, hMS.2.1, hMS.2.2.1, h₂⟩, ?_, ?_⟩
      · change _ + (rest.append M').sourceCount = (_ + rest.sourceCount) + _
        rw [h₃, Nat.add_assoc]
      · change (rest.append M').toEffectChain.effectCount + 1 =
          (rest.toEffectChain.effectCount + 1) + _
        rw [h₄]
        omega

end TNLean.PEPS.PairEffect.PartyChain

/-! ### A rank-one map on two front registers -/

namespace TNLean.PEPS.PairEffect

open EncodedFrame (act act_apply_apply)

variable {P : Type} {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The contraction of two registers `ℂ^α`, `ℂ^β` with the bra `⟨w|`. -/
def braLocal (p p' : P) (w : EuclideanSpace ℂ (α × β)) :
    Mem [⟨p, euc α⟩, ⟨p', euc β⟩] →L[ℂ] Mem ([] : Layout P) :=
  innerSL ℂ w ∘L isoL (twoIso p p' α β)

/-- The preparation of the vector `|v⟩` on two registers `ℂ^α`, `ℂ^β`. -/
def ketLocal (p p' : P) (v : EuclideanSpace ℂ (α × β)) :
    Mem ([] : Layout P) →L[ℂ] Mem [⟨p, euc α⟩, ⟨p', euc β⟩] :=
  isoL (twoIso p p' α β).symm ∘L (ContinuousLinearMap.id ℂ ℂ).smulRight v

omit [DecidableEq α] [DecidableEq β] in
theorem norm_braLocal_le (p p' : P) (w : EuclideanSpace ℂ (α × β)) :
    ‖braLocal p p' w‖ ≤ ‖w‖ := by
  refine (opNorm_comp_le _ _).trans ?_
  rw [innerSL_apply_norm]
  exact mul_le_of_le_one_right (norm_nonneg _) (LinearIsometry.norm_toContinuousLinearMap_le _)

omit [DecidableEq α] [DecidableEq β] in
theorem norm_ketLocal_le (p p' : P) (v : EuclideanSpace ℂ (α × β)) :
    ‖ketLocal p p' v‖ ≤ ‖v‖ := by
  refine (opNorm_comp_le _ _).trans ?_
  rw [norm_smulRight_apply]
  refine (mul_le_of_le_one_left (by positivity)
    (LinearIsometry.norm_toContinuousLinearMap_le _)).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) norm_id_le

open Classical in
/-- The bra `⟨w|` on two front registers: a normalized pair effect when the two owners differ,
and a private contraction otherwise. -/
def braChain (pA pB : P) (w : EuclideanSpace ℂ (α × β)) (ℓ : Layout P) :
    PartyChain (⟨pA, euc α⟩ :: ⟨pB, euc β⟩ :: ℓ) ℓ :=
  if h : pA = pB then
    .final (Word.localMap pA (ℓ₁ := [⟨pA, euc α⟩, ⟨pB, euc β⟩]) (ℓ₂ := [])
      (owner_of_mem_pair h) owner_of_mem_nil (braLocal pA pB w) ℓ)
  else .effect h α β ℓ (.id _) w (.final (.id ℓ))

open Classical in
/-- The ket `|v⟩` on two fresh front registers: a normalized pair source when the two owners
differ, and a private preparation otherwise. -/
def ketWord (pA pB : P) (v : EuclideanSpace ℂ (α × β)) (ℓ : Layout P) :
    Word ℓ (⟨pA, euc α⟩ :: ⟨pB, euc β⟩ :: ℓ) :=
  if h : pA = pB then
    Word.localMap pA (ℓ₁ := []) (ℓ₂ := [⟨pA, euc α⟩, ⟨pB, euc β⟩]) owner_of_mem_nil
      (owner_of_mem_pair h) (ketLocal pA pB v) ℓ
  else .source h (euc α) (euc β) (pairVec v) ℓ

/-- **A rank-one map with a change of owners.** The bra `⟨w|` on registers of `p_A` and `p_B`,
followed by the ket `|v⟩` on fresh registers of `p_A'` and `p_B'`. -/
def rankOneChain (pA pB pA' pB' : P) (v w : EuclideanSpace ℂ (α × β)) (ℓ : Layout P) :
    PartyChain (⟨pA, euc α⟩ :: ⟨pB, euc β⟩ :: ℓ) (⟨pA', euc α⟩ :: ⟨pB', euc β⟩ :: ℓ) :=
  (braChain pA pB w ℓ).postcomp (ketWord pA' pB' v ℓ)

omit [DecidableEq α] [DecidableEq β] in
theorem eval_braChain (pA pB : P) (w : EuclideanSpace ℂ (α × β)) (ℓ : Layout P)
    (y : EuclideanSpace ℂ (α × β)) (t : Mem ℓ) :
    (braChain pA pB w ℓ).toEffectChain.eval ((pairHeadIso (p := pA) (q := pB) ℓ).symm (y ⊗ₜ t)) =
      ⟪w, y⟫_ℂ • t := by
  unfold braChain
  split_ifs with h
  · have hz : (pairHeadIso (p := pA) (q := pB) ℓ).symm (y ⊗ₜ t) =
        (appendIso [⟨pA, euc α⟩, ⟨pB, euc β⟩] ℓ).symm ((twoIso pA pB α β).symm y ⊗ₜ t) := by
      rw [LinearIsometryEquiv.symm_apply_eq, pairHeadIso_appendIso_symm]
    change (Word.localMap pA _ _ (braLocal pA pB w) ℓ).eval _ = _
    rw [hz, eval_localMap, appendIso_nil_symm_tmul]
    simp [braLocal]
  · simp only [EffectChain.eval, Word.eval,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, isoL_apply,
      LinearIsometryEquiv.apply_symm_apply, effectMap_tmul]

omit [DecidableEq α] [DecidableEq β] in
theorem pairHeadIso_ketWord (pA pB : P) (v : EuclideanSpace ℂ (α × β)) (ℓ : Layout P)
    (t : Mem ℓ) : pairHeadIso ℓ ((ketWord pA pB v ℓ).eval t) = v ⊗ₜ t := by
  unfold ketWord
  split_ifs with h
  · have ht : t = (appendIso ([] : Layout P) ℓ).symm ((1 : ℂ) ⊗ₜ t) := by
      rw [appendIso_nil_symm_tmul, one_smul]
    rw [ht, eval_localMap]
    have hk : ketLocal (α := α) (β := β) pA pB v (1 : ℂ) = (twoIso pA pB α β).symm v := by
      simp [ketLocal]
    rw [hk, pairHeadIso_appendIso_symm, ← ht]
  · exact pairHeadIso_source h v ℓ t

omit [DecidableEq α] [DecidableEq β] in
/-- `|v⟩⟨w|` applied to `y` is `⟨w, y⟩ v`. -/
theorem act_vecMulVec_star (v w y : EuclideanSpace ℂ (α × β)) :
    act (vecMulVec v.ofLp (star w.ofLp)) y = ⟪w, y⟫_ℂ • v := by
  ext i
  rw [act_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, PiLp.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [vecMulVec_apply, Pi.star_apply]
  ring

omit [DecidableEq α] [DecidableEq β] in
/-- **The operator of the rank-one chain.** It acts on the two front registers as `|v⟩⟨w|`,
tensored with the identity of the untouched registers. -/
theorem pairHeadIso_rankOneChain (pA pB pA' pB' : P) (v w : EuclideanSpace ℂ (α × β))
    (ℓ : Layout P) (z : Mem (⟨pA, euc α⟩ :: ⟨pB, euc β⟩ :: ℓ)) :
    pairHeadIso ℓ ((rankOneChain pA pB pA' pB' v w ℓ).toEffectChain.eval z) =
      (act (vecMulVec v.ofLp (star w.ofLp))).rTensor (Mem ℓ) (pairHeadIso ℓ z) := by
  classical
  obtain ⟨Y, rfl⟩ : ∃ Y, z = (pairHeadIso (p := pA) (q := pB) (α := α) (β := β) ℓ).symm Y :=
    ⟨pairHeadIso ℓ z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply, rankOneChain, PartyChain.eval_postcomp]
  induction Y using TensorProduct.inductionOn with
  | tmul y t =>
      rw [ContinuousLinearMap.comp_apply, eval_braChain, map_smul, map_smul,
        pairHeadIso_ketWord, rTensor_tmul, act_vecMulVec_star, TensorProduct.smul_tmul']
  | add a b ha hb => simp only [map_add, ha, hb]

omit [DecidableEq α] [DecidableEq β] in
/-- The rank-one chain of two unit vectors is allowed and uses only the four owners. It has at
most one pair source, and none when `p_A' = p_B'`, and at most one pair effect, and none when
`p_A = p_B`. -/
theorem rankOneChain_props (pA pB pA' pB' : P) {v w : EuclideanSpace ℂ (α × β)} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (ℓ : Layout P) {S : Set P} (hA : pA ∈ S) (hB : pB ∈ S) (hA' : pA' ∈ S)
    (hB' : pB' ∈ S) :
    (rankOneChain pA pB pA' pB' v w ℓ).IsAllowed ∧
      (rankOneChain pA pB pA' pB' v w ℓ).UsesOnly S ∧
      (rankOneChain pA pB pA' pB' v w ℓ).sourceCount ≤ 1 ∧
      (pA' = pB' → (rankOneChain pA pB pA' pB' v w ℓ).sourceCount = 0) ∧
      (rankOneChain pA pB pA' pB' v w ℓ).toEffectChain.effectCount ≤ 1 ∧
      (pA = pB → (rankOneChain pA pB pA' pB' v w ℓ).toEffectChain.effectCount = 0) := by
  have hk : (ketWord pA' pB' v ℓ).IsAllowed ∧ (ketWord pA' pB' v ℓ).UsesOnly S ∧
      (ketWord pA' pB' v ℓ).sourceCount ≤ 1 ∧
      (pA' = pB' → (ketWord pA' pB' v ℓ).sourceCount = 0) := by
    unfold ketWord
    split_ifs with h
    · exact ⟨(norm_ketLocal_le _ _ _).trans hv.le, hA', Nat.zero_le _, fun _ => rfl⟩
    · exact ⟨(norm_pairVec v).trans hv, ⟨hA', hB'⟩, le_rfl, fun h' => absurd h' h⟩
  have hb : (braChain pA pB w ℓ).IsAllowed ∧ (braChain pA pB w ℓ).UsesOnly S ∧
      (braChain pA pB w ℓ).sourceCount = 0 ∧
      (braChain pA pB w ℓ).toEffectChain.effectCount ≤ 1 ∧
      (pA = pB → (braChain pA pB w ℓ).toEffectChain.effectCount = 0) := by
    unfold braChain
    split_ifs with h
    · exact ⟨(norm_braLocal_le _ _ _).trans hw.le, hA, rfl, Nat.zero_le _, fun _ => rfl⟩
    · exact ⟨⟨trivial, hw, trivial⟩, ⟨hA, hB, trivial, trivial⟩, rfl, le_rfl,
        fun h' => absurd h' h⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := PartyChain.postcomp_props S _ _ hk.1 hk.2.1 hb.1 hb.2.1
  refine ⟨h₁, h₂, ?_, fun h => ?_, ?_, fun h => ?_⟩
  · rw [rankOneChain, h₃, hb.2.2.1, zero_add]
    exact hk.2.2.1
  · rw [rankOneChain, h₃, hb.2.2.1, zero_add]
    exact hk.2.2.2 h
  · rw [rankOneChain, h₄]
    exact hb.2.2.2.1
  · rw [rankOneChain, h₄]
    exact hb.2.2.2.2 h

end TNLean.PEPS.PairEffect

/-! ### Rank-one blocks of sites -/

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

variable (ι q) in
/-- A rank-one block: the sites outside `E`, split into `T` and `U = (T ∪ E)ᶜ`, carry the
rank-one map `|v⟩⟨w|`, with `v` and `w` vectors on `(T → Fin q) × (U → Fin q)`; the sites of
`E` are untouched. -/
structure RankOneBlock where
  /-- The first part of the block. -/
  T : Finset ι
  /-- The sites outside the block. -/
  E : Finset ι
  /-- The first part of the block lies in the block. -/
  disj : Disjoint T E
  /-- The output vector. -/
  ket : EuclideanSpace ℂ ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
  /-- The input vector. -/
  bra : EuclideanSpace ℂ ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))

namespace RankOneBlock

variable (b : RankOneBlock ι q)

/-- The operator `|v⟩⟨w|_{T ∪ U} ⊗ 1_E` of a block. -/
def op : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  sheetPlace b.disj (vecMulVec b.ket.ofLp (star b.bra.ofLp))

/-- The output vector read on a configuration of all sites. -/
def ketAt (c : ι → Fin q) : ℂ :=
  b.ket ((fun x : b.T => c x), (fun x : ↥(b.T ∪ b.E)ᶜ => c x))

/-- The input vector read on a configuration of all sites. -/
def braAt (c : ι → Fin q) : ℂ :=
  b.bra ((fun x : b.T => c x), (fun x : ↥(b.T ∪ b.E)ᶜ => c x))

/-- The entries of the operator of a block. -/
theorem op_apply (c' c : ι → Fin q) :
    b.op c' c = if ∀ x ∈ b.E, c' x = c x then b.ketAt c' * star (b.braAt c) else 0 := by
  rw [op, sheetPlace_apply]
  have hE : ((fun x : b.E => c' x) = fun x : b.E => c x) ↔ ∀ x ∈ b.E, c' x = c x :=
    ⟨fun h x hx => congrFun h ⟨x, hx⟩, fun h => funext fun x => h x x.2⟩
  simp only [hE, vecMulVec_apply, Pi.star_apply]
  split_ifs <;> simp [ketAt, braAt]

private theorem notMem_E_of_mem_T {x : ι} (hx : x ∈ b.T) : x ∉ b.E :=
  Finset.disjoint_left.mp b.disj hx

theorem ketAt_congr {c c' : ι → Fin q} (h : ∀ x ∉ b.E, c x = c' x) : b.ketAt c = b.ketAt c' := by
  have h₁ : (fun x : b.T => c x) = fun x : b.T => c' x :=
    funext fun x => h x (b.notMem_E_of_mem_T x.2)
  have h₂ : (fun x : ↥(b.T ∪ b.E)ᶜ => c x) = fun x : ↥(b.T ∪ b.E)ᶜ => c' x :=
    funext fun x => h x fun hx => Finset.mem_compl.mp x.2 (Finset.mem_union_right _ hx)
  rw [ketAt, ketAt, h₁, h₂]

theorem braAt_congr {c c' : ι → Fin q} (h : ∀ x ∉ b.E, c x = c' x) : b.braAt c = b.braAt c' := by
  have h₁ : (fun x : b.T => c x) = fun x : b.T => c' x :=
    funext fun x => h x (b.notMem_E_of_mem_T x.2)
  have h₂ : (fun x : ↥(b.T ∪ b.E)ᶜ => c x) = fun x : ↥(b.T ∪ b.E)ᶜ => c' x :=
    funext fun x => h x fun hx => Finset.mem_compl.mp x.2 (Finset.mem_union_right _ hx)
  rw [braAt, braAt, h₁, h₂]

/-- **Products of disjoint blocks.** If every site lies outside all blocks of the list but at
most one, the product of their operators has the entry `∏_b v_b(c') \overline{w_b(c)}` when `c'`
and `c` agree outside all blocks, and `0` otherwise. -/
theorem prod_op_apply : (bs : List (RankOneBlock ι q)) →
    bs.Pairwise (fun b b' => ∀ x, x ∈ b.E ∨ x ∈ b'.E) → (c' c : ι → Fin q) →
    (bs.map op).prod c' c = if ∀ x, (∀ b ∈ bs, x ∈ b.E) → c' x = c x then
      (bs.map fun b => b.ketAt c' * star (b.braAt c)).prod else 0
  | [], _, c', c => by
      have h : (c' = c) ↔ ∀ x, (∀ b ∈ ([] : List (RankOneBlock ι q)), x ∈ b.E) → c' x = c x :=
        ⟨fun h x _ => congrFun h x, fun h => funext fun x => h x fun b hb => absurd hb
          List.not_mem_nil⟩
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply, h]
  | b :: bs, hd, c', c => by
      have hdb : ∀ b' ∈ bs, ∀ x, x ∈ b.E ∨ x ∈ b'.E := (List.pairwise_cons.mp hd).1
      have ih := prod_op_apply bs (List.pairwise_cons.mp hd).2
      set c₀ : ι → Fin q := fun x => if x ∈ b.E then c' x else c x with hc₀
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply,
        Finset.sum_eq_single c₀ (fun a _ ha => ?_) (fun h => absurd (Finset.mem_univ _) h)]
      · rw [op_apply, ih, ite_eq_left fun x hx => by rw [hc₀]; simp [hx]]
        have hrest : ∀ x, (∀ b' ∈ bs, x ∈ b'.E) → c₀ x = c x ↔
            (∀ b' ∈ b :: bs, x ∈ b'.E) → c' x = c x := by
          intro x
          by_cases hx : x ∈ b.E
          · simp [hc₀, hx]
          · simp only [hc₀, hx, ite_false, List.mem_cons, forall_eq_or_imp, false_and,
              false_implies, iff_true]
            simp
        have hb : b.braAt c₀ = b.braAt c := b.braAt_congr fun x hx => by simp [hc₀, hx]
        have hk : (bs.map fun b' => b'.ketAt c₀ * star (b'.braAt c)) =
            bs.map fun b' => b'.ketAt c' * star (b'.braAt c) := by
          refine List.map_congr_left fun b' hb' => ?_
          rw [b'.ketAt_congr fun x hx => ?_]
          rcases hdb b' hb' x with h | h
          · simp [hc₀, h]
          · exact absurd h hx
        simp only [forall_congr' hrest, hb, hk, List.map_cons, List.prod_cons]
        split_ifs <;> ring
      · rw [op_apply, ih]
        split_ifs with h₁ h₂
        · refine absurd (funext fun x => ?_) ha
          by_cases hx : x ∈ b.E
          · rw [← h₁ x hx]
            simp [hc₀, hx]
          · rw [h₂ x fun b' hb' => (hdb b' hb' x).resolve_left hx]
            simp [hc₀, hx]
        all_goals simp

end RankOneBlock

/-- The basis vector of the zero configuration on `(T → Fin q) × (U → Fin q)`, the analogue of
`zeroVec` on the two parts of a block. -/
def zeroPair [NeZero q] (T E : Finset ι) :
    EuclideanSpace ℂ ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) :=
  EuclideanSpace.single (0, 0) 1

theorem norm_zeroPair [NeZero q] (T E : Finset ι) : ‖zeroPair (q := q) T E‖ = 1 := by
  simp [zeroPair]

/-- The zero basis vector read on a configuration: `1` if the configuration vanishes on
`T ∪ U`, and `0` otherwise. -/
theorem zeroPair_apply [NeZero q] (T E : Finset ι) (h : Disjoint T E) (c : ι → Fin q) :
    zeroPair (q := q) T E ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) =
      if ∀ x ∉ E, c x = 0 then 1 else 0 := by
  rw [zeroPair, PiLp.single_apply]
  congr 1
  apply propext
  constructor
  · intro hc x hx
    by_cases hT : x ∈ T
    · exact congrFun (congrArg Prod.fst hc) ⟨x, hT⟩
    · exact congrFun (congrArg Prod.snd hc) ⟨x, by simp [hT, hx]⟩
  · intro hc
    refine Prod.ext (funext fun x => hc x (Finset.disjoint_left.mp h x.2))
      (funext fun x => hc x fun hx => Finset.mem_compl.mp x.2 (Finset.mem_union_right _ hx))

/-- **A vector on a group of sites, read on two parts.** Let the group be the set of sites
satisfying `O`, with complement `E`, and let `T` be part of it. Every vector `f` on the
configurations of the group is a vector of the same norm on `(T → Fin q) × (U → Fin q)`,
`U = (T ∪ E)ᶜ`, with the same values on every configuration. -/
theorem exists_pairVec (O : ι → Prop) [DecidablePred O] {T : Finset ι} (hT : ∀ x ∈ T, O x)
    (f : EuclideanSpace ℂ ({x // O x} → Fin q)) :
    ∃ v : EuclideanSpace ℂ ((T → Fin q) × (↥(T ∪ Finset.univ.filter fun x => ¬O x)ᶜ → Fin q)),
      ‖v‖ = ‖f‖ ∧ ∀ c : ι → Fin q,
        v ((fun x : T => c x),
          (fun x : ↥(T ∪ Finset.univ.filter fun x => ¬O x)ᶜ => c x)) = f fun x => c x.1 := by
  set E := Finset.univ.filter fun x => ¬O x
  have hU : ∀ x : {x // O x}, x.1 ∉ T → x.1 ∈ (T ∪ E)ᶜ := fun x hx => by
    simp [E, hx, x.2]
  have hO : ∀ x : ↥(T ∪ E)ᶜ, O x.1 := fun x => by
    have := Finset.mem_compl.mp x.2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_not, E] at this
    exact this.2
  let e : ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ≃ ({x // O x} → Fin q) :=
    { toFun := fun ab x => if hx : x.1 ∈ T then ab.1 ⟨x.1, hx⟩ else ab.2 ⟨x.1, hU x hx⟩
      invFun := fun d => (fun x => d ⟨x.1, hT x.1 x.2⟩, fun x => d ⟨x.1, hO x⟩)
      left_inv := fun ab => by
        refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
        · simp [x.2]
        · have hx : x.1 ∉ T := fun h => Finset.mem_compl.mp x.2 (Finset.mem_union_left _ h)
          simp [hx]
      right_inv := fun d => funext fun x => by
        by_cases hx : x.1 ∈ T <;> simp [hx] }
  refine ⟨WithLp.toLp 2 fun ab => f (e ab), ?_, fun c => ?_⟩
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp e (fun d => ‖f d‖ ^ 2)
  · change f (e _) = _
    refine congrArg (fun d => f d) (funext fun x => ?_)
    by_cases hx : x.1 ∈ T <;> simp [e, hx]

variable {pos : ι → ℝ × ℝ} {Party : Type}

/-- **A rank-one block as an allowed monomial on the registers of a frame.** Let the sites of
`T` be held by `p_A` before and by `p_A'` after, those of `U = (T ∪ E)ᶜ` by `p_B` and `p_B'`,
and the sites of `E` by the same party before and after. For unit vectors `v` and `w`, the
operator `1_tags ⊗ |v⟩⟨w|_{T ∪ U} ⊗ 1_E` is, in canonical coordinates, the operator of an
allowed monomial from the registers of the frame with owners `own` to those with owners `own'`
that uses only `p_A`, `p_B`, `p_A'` and `p_B'`, with at most one normalized pair source, none
when `p_A' = p_B'`, and at most one normalized pair effect, none when `p_A = p_B`. It groups
the registers of `T` and of `U`, applies `rankOneChain`, and ungroups.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 306–316: each group
vector on at most two owners is a normalized pair state or effect, or a private map. -/
theorem exists_rankOneBlock_chain [NeZero q] (l : List (Hole pos q Party)) (own own' : ι → Party)
    (b : RankOneBlock ι q) {pA pB pA' pB' : Party} (hA : ∀ x ∈ b.T, own x = pA)
    (hB : ∀ x ∈ (b.T ∪ b.E)ᶜ, own x = pB) (hA' : ∀ x ∈ b.T, own' x = pA')
    (hB' : ∀ x ∈ (b.T ∪ b.E)ᶜ, own' x = pB') (hE : ∀ x ∈ b.E, own x = own' x)
    (hv : ‖b.ket‖ = 1) (hw : ‖b.bra‖ = 1) {S : Set Party} (hSA : pA ∈ S) (hSB : pB ∈ S)
    (hSA' : pA' ∈ S) (hSB' : pB' ∈ S) :
    ∃ M : PartyChain (layoutRegs q l own) (layoutRegs q l own'),
      M.IsAllowed ∧ M.UsesOnly S ∧ M.sourceCount ≤ 1 ∧ (pA' = pB' → M.sourceCount = 0) ∧
      M.toEffectChain.effectCount ≤ 1 ∧ (pA = pB → M.toEffectChain.effectCount = 0) ∧
      ∀ z, layoutIso l own' (M.toEffectChain.eval z) =
        act ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ b.op) (layoutIso l own z) := by
  set Mm := rankOneChain pA pB pA' pB' b.ket b.bra
    (tagRegs l ++ siteRegs q own (listE (sites ι) b.T b.E))
  obtain ⟨m₁, m₂, m₃, m₃', m₄, m₄'⟩ := rankOneChain_props pA pB pA' pB' hv hw
    (tagRegs l ++ siteRegs q own (listE (sites ι) b.T b.E)) hSA hSB hSA' hSB'
  obtain ⟨g₁, g₂, g₃⟩ := groupWord_props (q := q) own nodup_sites mem_sites (tagRegs l) hA hB
    (V := S) hSA hSB
  have r := isReordering_relabelRest (q := q) own own' mem_sites b.disj hE (tagRegs l)
    ⟨pA', euc (b.T → Fin q)⟩ ⟨pB', euc (↥(b.T ∪ b.E)ᶜ → Fin q)⟩
  obtain ⟨u₁, u₂, u₃⟩ := ungroupWord_props (q := q) own' nodup_sites mem_sites (tagRegs l)
    hA' hB' (V := S) hSA' hSB'
  let tail := (relabelRest own own' mem_sites b.disj hE (tagRegs l)
    ⟨pA', euc (b.T → Fin q)⟩ ⟨pB', euc (↥(b.T ∪ b.E)ᶜ → Fin q)⟩).comp
      (ungroupWord own' nodup_sites mem_sites (tagRegs l) hA' hB')
  obtain ⟨p₁, p₂, p₃, p₄⟩ := PartyChain.postcomp_props S Mm tail ⟨r.isAllowed, u₁⟩
    ⟨r.usesOnly _, u₂⟩ m₁ m₂
  let G := groupWord (q := q) own nodup_sites mem_sites (tagRegs l) hA hB
  obtain ⟨q₁, q₂, q₃, q₄⟩ := PartyChain.precomp_props G S g₁ g₂ (Mm.postcomp tail) p₁ p₂
  have hsrc : ((Mm.postcomp tail).precomp G).sourceCount = Mm.sourceCount := by
    rw [q₃, p₃, g₃]
    change 0 + (Mm.sourceCount + (Word.sourceCount _ + Word.sourceCount _)) = _
    rw [r.sourceCount_eq, u₃]
    simp
  refine ⟨(Mm.postcomp tail).precomp G, q₁, q₂, hsrc ▸ m₃, fun h => hsrc ▸ m₃' h,
    (q₄.trans p₄) ▸ m₄, fun h => (q₄.trans p₄) ▸ m₄' h, fun z => ?_⟩
  · rw [PartyChain.eval_precomp, PartyChain.eval_postcomp]
    exact layoutIso_place l own own' b.disj hA hB hA' hB' hE Mm.toEffectChain.eval _
      (pairHeadIso_rankOneChain pA pB pA' pB' b.ket b.bra _) z

end TNLean.PEPS.EncodedFrame
