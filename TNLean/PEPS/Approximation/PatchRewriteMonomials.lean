/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PatchRewriteTruncation
import TNLean.PEPS.Approximation.SiteChainMonomials

/-!
# The small-patch rewrite as a sum of allowed monomials

The last step of the proof of the second assertion of Lemma 6.3 `lem:small-rewrite` of the
polynomial-PEPS manuscript reads every product term of the truncated branch expansion as a
monomial allowed by Theorem 5.2, on the registers of the two frames, one register per site and
per tag, each held by its owner (`TNLean.PEPS.Approximation.FrameRegisters`).

For a branch `(a, s, b)` and a choice of one vector on every open-leg group of its network, the
product term, placed in the tag block `|a⟩⟨b|`, is a scalar of modulus at most one times the
operator of the following monomial from the registers of `F_old` to those of `F_new`
(`SmallPatchRewrite.exists_termChain`):

1. on the open input legs of each patch bra, the normalized covector of the term, contracted at
   the at most two old owners of these legs (a pair effect or a private map), the legs then being
   reset to `|0⟩`;
2. on every site touched by the branch, `|0⟩⟨0|`, contracted at the old owner and prepared at the
   new owner; this imposes the zero bras of the old-hole decoders and transfers the reset raw
   registers;
3. on the open output legs of each patch ket, the normalized vector of the term, prepared at the
   at most two new owners (a pair source or a private map) after contracting the zeros;
4. on the tags, `⟨b|` on the affected old tags and `|a⟩` on the affected new tags, each at its
   tag owner.

Every site in no selected square is untouched and keeps its owner. The monomial uses only the
specified parties, with at most `2m` normalized pair sources and at most `2m` normalized pair
effects. Combined with the approximation by product terms (`exists_contractive_approx`), this
gives the contraction `M_δ` with `‖M_δ - M‖ ≤ δ` as a sum of at most `N k^{2m}` allowed
monomials with coefficients of modulus at most one (`exists_allowed_monomial_approx`), where `N`
is the number of branches and `k` the truncation rank; if every hole and every patch has at most
`D` cylinder terms, `N ≤ D^{r_new + m + r_old}` (`exists_allowed_monomial_approx_of_card_le`).

**Scope restriction (polynomial count):** the count `N k^{2m}` is polynomial in `L` for
`δ = L^{-a}` once `D ≤ C L^c` and `m`, `r_old`, `r_new` are bounded; the patch data do not record
the cylinder-term bound `∑_j d_j ≤ C L^c` of Proposition 4.1 (`03-patches.tex`, lines 24–49), so
`exists_allowed_monomial_approx_of_card_le` states the count with `D` as an explicit parameter.
Documented in `docs/paper-gaps/polypeps_small_rewrite_monomials.tex`. Elimination: carry the
bound of Proposition 4.1 on the patch and hole data once Proposition 4.1 is formalized, and
specialize `D`.

## Main definitions

* `EncodedFrame.tagBraWord`, `EncodedFrame.tagKetWord`, `EncodedFrame.tagChangeWord`: the tag
  maps of a branch.

## Main results

* `EncodedFrame.SmallPatchRewrite.liftBranch_apply`, `EncodedFrame.SmallPatchRewrite.liftBranch_mul`.
* `EncodedFrame.SmallPatchRewrite.exists_termChain`: a product term as an allowed monomial.
* `EncodedFrame.SmallPatchRewrite.exists_allowed_monomial_approx`: the second assertion of
  Lemma 6.3, with the count `N k^{2m}`.
* `EncodedFrame.SmallPatchRewrite.exists_allowed_monomial_approx_of_card_le`: the same, with the
  number of cylinder terms as an explicit parameter.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 214–217; proof lines 254–341, in particular lines 262–273 and 306–316;
  allowed monomials, `04-compression.tex`, lines 32–35.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

open PairEffect SiteChain

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}

/-! ### Operators on the registers of a frame from basis vectors -/

/-- An operator between the registers of two frames is determined, in canonical coordinates,
by its values on the basis vectors `|τ⟩ ⊗ ⊗_x |c x⟩`. -/
theorem layoutIso_eq_act_of_basis (l l' : List (Hole pos q Party)) (own own' : ι → Party)
    (f : Mem (layoutRegs q l own) →L[ℂ] Mem (layoutRegs q l' own'))
    (A : Matrix (TagSpace l' × (ι → Fin q)) (TagSpace l × (ι → Fin q)) ℂ)
    (hf : ∀ τ c, layoutIso l' own' (f (layoutVec l own τ c)) =
      act A (EuclideanSpace.single (τ, c) (1 : ℂ)))
    (z : Mem (layoutRegs q l own)) : layoutIso l' own' (f z) = act A (layoutIso l own z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (layoutIso l own).symm y := ⟨layoutIso l own z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply, act_eq_matL]
  conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨τ, c⟩ := i
  rw [EuclideanSpace.basisFun_apply, layoutIso_symm_single, hf, act_eq_matL]

/-! ### The tag maps of a branch -/

section Tags

/-- The bra `⟨a|` on one register `ℂ^α`. -/
def regBra (p : Party) {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    Mem [⟨p, euc α⟩] →L[ℂ] Mem ([] : Layout Party) :=
  innerSL ℂ (EuclideanSpace.single a (1 : ℂ)) ∘L isoL (oneIso p α)

/-- The preparation of `|a⟩` on one register `ℂ^α`. -/
def regKet (p : Party) {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    Mem ([] : Layout Party) →L[ℂ] Mem [⟨p, euc α⟩] :=
  isoL (oneIso p α).symm ∘L (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single a 1)

theorem norm_regBra_le (p : Party) {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    ‖regBra p a‖ ≤ 1 := by
  refine (opNorm_comp_le _ _).trans ?_
  rw [innerSL_apply_norm, PiLp.norm_single, norm_one, one_mul]
  exact LinearIsometry.norm_toContinuousLinearMap_le _

theorem norm_regKet_le (p : Party) {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    ‖regKet p a‖ ≤ 1 := by
  refine (opNorm_comp_le _ _).trans ?_
  rw [norm_smulRight_apply]
  refine (mul_le_of_le_one_left (by positivity)
    (LinearIsometry.norm_toContinuousLinearMap_le _)).trans ?_
  simp

/-- The tag registers of a list of holes contracted with the basis bra `⟨b|`, each at its tag
owner. -/
def tagBraWord : (l : List (Hole pos q Party)) → TagSpace l → (tail : Layout Party) →
    Word (tagRegs l ++ tail) tail
  | [], _, tail => .id tail
  | h :: l, b, tail => .comp
      (Word.localMap h.tagOwner (ℓ₁ := [⟨h.tagOwner, euc h.patch.Tag⟩]) (ℓ₂ := [])
        owner_of_mem_one owner_of_mem_nil (regBra h.tagOwner b.1) (tagRegs l ++ tail))
      (tagBraWord l b.2 tail)

/-- The tag registers of a list of holes prepared in the basis vector `|a⟩`, each at its tag
owner. -/
def tagKetWord : (l : List (Hole pos q Party)) → TagSpace l → (tail : Layout Party) →
    Word tail (tagRegs l ++ tail)
  | [], _, tail => .id tail
  | h :: l, a, tail => .comp (tagKetWord l a.2 tail)
      (Word.localMap h.tagOwner (ℓ₁ := []) (ℓ₂ := [⟨h.tagOwner, euc h.patch.Tag⟩])
        owner_of_mem_nil owner_of_mem_one (regKet h.tagOwner a.1) (tagRegs l ++ tail))

theorem eval_tagBraWord (tail : Layout Party) (y : Mem tail) :
    (l : List (Hole pos q Party)) → (b τ : TagSpace l) →
      (tagBraWord l b tail).eval ((appendIso (tagRegs l) tail).symm (tagVec l τ ⊗ₜ y)) =
        (if τ = b then (1 : ℂ) else 0) • y
  | [], b, τ => by
      change (appendIso ([] : Layout Party) tail).symm ((1 : ℂ) ⊗ₜ y) = _
      rw [appendIso_nil_symm_tmul, show τ = b from Subsingleton.elim (α := Unit) τ b]
      simp
  | h :: l, ⟨b, bs⟩, ⟨t, τ⟩ => by
      change (tagBraWord l bs tail).eval ((Word.localMap h.tagOwner _ _
        (regBra h.tagOwner b) (tagRegs l ++ tail)).eval
          ((EuclideanSpace.single t (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) ⊗ₜ
            (appendIso (tagRegs l) tail).symm (tagVec l τ ⊗ₜ y))) = _
      rw [← appendIso_one_symm h.tagOwner (tagRegs l ++ tail), eval_localMap,
        appendIso_nil_symm_tmul, map_smul, eval_tagBraWord tail y l bs τ, smul_smul]
      congr 1
      simp only [regBra, ContinuousLinearMap.comp_apply, isoL_apply,
        LinearIsometryEquiv.apply_symm_apply, innerSL_apply_apply, EuclideanSpace.inner_single_left,
        PiLp.single_apply, map_one]
      have hpair : ((t, τ) : TagSpace (h :: l)) = (b, bs) ↔ b = t ∧ τ = bs :=
        ⟨fun h' => ⟨(Prod.mk.inj h').1.symm, (Prod.mk.inj h').2⟩,
          fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩
      refine Eq.trans ?_ (if_congr hpair rfl rfl).symm
      by_cases h₁ : b = t <;> by_cases h₂ : τ = bs <;> simp [h₁, h₂]

theorem eval_tagKetWord (tail : Layout Party) (y : Mem tail) :
    (l : List (Hole pos q Party)) → (a : TagSpace l) →
      (tagKetWord l a tail).eval y = (appendIso (tagRegs l) tail).symm (tagVec l a ⊗ₜ y)
  | [], a => by
      change y = (appendIso ([] : Layout Party) tail).symm ((1 : ℂ) ⊗ₜ y)
      rw [appendIso_nil_symm_tmul, one_smul]
  | h :: l, ⟨a, as⟩ => by
      change (Word.localMap h.tagOwner (ℓ₁ := []) (ℓ₂ := [⟨h.tagOwner, euc h.patch.Tag⟩])
        owner_of_mem_nil owner_of_mem_one (regKet h.tagOwner a) (tagRegs l ++ tail)).eval
        ((tagKetWord l as tail).eval y) = _
      rw [eval_tagKetWord tail y l as]
      have ht : (appendIso (tagRegs l) tail).symm (tagVec l as ⊗ₜ y) =
          (appendIso ([] : Layout Party) (tagRegs l ++ tail)).symm ((1 : ℂ) ⊗ₜ
            (appendIso (tagRegs l) tail).symm (tagVec l as ⊗ₜ y)) := by
        rw [appendIso_nil_symm_tmul, one_smul]
      rw [ht, eval_localMap]
      have hk : regKet h.tagOwner a (1 : ℂ) =
          (oneIso h.tagOwner h.patch.Tag).symm (EuclideanSpace.single a 1) := by
        simp [regKet]
      rw [hk, appendIso_one_symm]
      rfl

theorem tagBraWord_props (tail : Layout Party) {S : Set Party} :
    (l : List (Hole pos q Party)) → (∀ h ∈ l, h.tagOwner ∈ S) → (b : TagSpace l) →
      (tagBraWord l b tail).IsAllowed ∧ (tagBraWord l b tail).UsesOnly S ∧
        (tagBraWord l b tail).sourceCount = 0
  | [], _, _ => ⟨trivial, trivial, rfl⟩
  | h :: l, hS, b => by
      obtain ⟨h₁, h₂, h₃⟩ := tagBraWord_props tail l (fun h' hh' => hS h' (List.mem_cons_of_mem _ hh'))
        b.2
      exact ⟨⟨norm_regBra_le _ _, h₁⟩, ⟨hS h List.mem_cons_self, h₂⟩,
        by simp [tagBraWord, Word.sourceCount, h₃]⟩

theorem tagKetWord_props (tail : Layout Party) {S : Set Party} :
    (l : List (Hole pos q Party)) → (∀ h ∈ l, h.tagOwner ∈ S) → (a : TagSpace l) →
      (tagKetWord l a tail).IsAllowed ∧ (tagKetWord l a tail).UsesOnly S ∧
        (tagKetWord l a tail).sourceCount = 0
  | [], _, _ => ⟨trivial, trivial, rfl⟩
  | h :: l, hS, a => by
      obtain ⟨h₁, h₂, h₃⟩ := tagKetWord_props tail l (fun h' hh' => hS h' (List.mem_cons_of_mem _ hh'))
        a.2
      exact ⟨⟨h₁, norm_regKet_le _ _⟩, ⟨h₂, hS h List.mem_cons_self⟩,
        by simp [tagKetWord, Word.sourceCount, h₃]⟩

/-- **The tag maps of a branch.** On the registers of a frame with holes `U ++ A`, contract the
tags of `A` with `⟨b|` and prepare tags of `A'` in `|a⟩`, each at its tag owner, leaving the tags
of `U` and the raw registers untouched. -/
def tagChangeWord (U A A' : List (Hole pos q Party)) (b : TagSpace A) (a : TagSpace A')
    (own : ι → Party) : Word (layoutRegs q (U ++ A) own) (layoutRegs q (U ++ A') own) :=
  (tagSplit U A (siteRegs q own (sites ι))).comp <|
    (Word.frameList (tagRegs U) (tagBraWord A b (siteRegs q own (sites ι)))).comp <|
      (Word.frameList (tagRegs U) (tagKetWord A' a (siteRegs q own (sites ι)))).comp
        (tagMerge U A' (siteRegs q own (sites ι)))

theorem eval_tagChangeWord (U A A' : List (Hole pos q Party)) (b : TagSpace A) (a : TagSpace A')
    (own : ι → Party) (τ : TagSpace (U ++ A)) (c : ι → Fin q) :
    (tagChangeWord U A A' b a own).eval (layoutVec (U ++ A) own τ c) =
      (if (tagAppendEquiv U A τ).2 = b then (1 : ℂ) else 0) •
        layoutVec (U ++ A') own ((tagAppendEquiv U A').symm ((tagAppendEquiv U A τ).1, a)) c := by
  simp only [tagChangeWord, Word.eval_comp, ContinuousLinearMap.comp_apply, layoutVec]
  rw [eval_tagSplit, Word.eval_frameList_appendIso_symm, eval_tagBraWord,
    TensorProduct.tmul_smul, LinearIsometryEquiv.map_smul, map_smul,
    Word.eval_frameList_appendIso_symm, eval_tagKetWord, map_smul, eval_tagMerge]

theorem tagChangeWord_props (U A A' : List (Hole pos q Party)) (b : TagSpace A) (a : TagSpace A')
    (own : ι → Party) {S : Set Party} (hA : ∀ h ∈ A, h.tagOwner ∈ S)
    (hA' : ∀ h ∈ A', h.tagOwner ∈ S) :
    (tagChangeWord U A A' b a own).IsAllowed ∧ (tagChangeWord U A A' b a own).UsesOnly S ∧
      (tagChangeWord U A A' b a own).sourceCount = 0 := by
  obtain ⟨b₁, b₂, b₃⟩ := tagBraWord_props (siteRegs q own (sites ι)) A hA b
  obtain ⟨k₁, k₂, k₃⟩ := tagKetWord_props (siteRegs q own (sites ι)) A' hA' a
  have s := isReordering_tagSplit (q := q) (siteRegs q own (sites ι)) U A
  have m := isReordering_tagMerge (q := q) (siteRegs q own (sites ι)) U A'
  refine ⟨⟨s.isAllowed, (Word.isAllowed_frameList_iff _ _).2 b₁,
      (Word.isAllowed_frameList_iff _ _).2 k₁, m.isAllowed⟩,
    ⟨s.usesOnly S, (Word.usesOnly_frameList_iff _ _ _).2 b₂,
      (Word.usesOnly_frameList_iff _ _ _).2 k₂, m.usesOnly S⟩, ?_⟩
  simp only [tagChangeWord, Word.sourceCount, s.sourceCount_eq, m.sourceCount_eq,
    Word.sourceCount_frameList, b₃, k₃]

end Tags

/-! ### Branches of the rewrite on the registers of the frames -/

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

/-- The entries of a matrix placed in the tag block of a branch. -/
theorem liftBranch_apply (β : R.Branch) (Y : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (τ' : TagSpace (R.untouched ++ R.newAffected)) (c' : ι → Fin q)
    (τ : TagSpace (R.untouched ++ R.oldAffected)) (c : ι → Fin q) :
    R.liftBranch β Y (τ', c') (τ, c) =
      if (tagAppendEquiv R.untouched R.newAffected τ').2 = β.1 ∧
          (tagAppendEquiv R.untouched R.oldAffected τ).2 = β.2.2 ∧
          (tagAppendEquiv R.untouched R.newAffected τ').1 =
            (tagAppendEquiv R.untouched R.oldAffected τ).1 then Y c' c else 0 := by
  simp only [liftBranch, layoutEquiv, reindex_apply, submatrix_apply, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply, tagLift, of_apply, Matrix.one_apply]
  by_cases h₁ : (tagAppendEquiv R.untouched R.newAffected τ').2 = β.1 <;>
    by_cases h₂ : (tagAppendEquiv R.untouched R.oldAffected τ).2 = β.2.2 <;>
    by_cases h₃ : (tagAppendEquiv R.untouched R.newAffected τ').1 =
      (tagAppendEquiv R.untouched R.oldAffected τ).1 <;> simp [h₁, h₂, h₃]

/-- A matrix in the tag block of a branch is the tag block of the identity after the matrix on
the raw registers. -/
theorem liftBranch_mul (β : R.Branch) (Y : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    R.liftBranch β 1 *
        ((1 : Matrix (TagSpace (R.untouched ++ R.oldAffected))
          (TagSpace (R.untouched ++ R.oldAffected)) ℂ) ⊗ₖ Y) = R.liftBranch β Y := by
  ext ⟨τ', c'⟩ ⟨τ, c⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single τ (fun τ'' _ h => Finset.sum_eq_zero fun c'' _ => by
      simp [kroneckerMap_apply, h])
      (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single c' (fun c'' _ h => by
      rw [liftBranch_apply]
      simp [Ne.symm h])
      (fun h => absurd (Finset.mem_univ _) h)]
  rw [liftBranch_apply, liftBranch_apply]
  simp only [kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
  split_ifs <;> simp

theorem liftBranch_sum_smul (β : R.Branch) {κ : Type*} [Fintype κ] (a : κ → ℂ)
    (Y : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    R.liftBranch β (∑ k, a k • Y k) = ∑ k, a k • R.liftBranch β (Y k) := by
  ext x y
  simp only [liftBranch, reindex_apply, submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    kroneckerMap_apply, tagLift, of_apply, smul_eq_mul]
  split_ifs
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc (G := ℂ) _ _ _
  · simp only [zero_mul, mul_zero, Finset.sum_const_zero]

theorem liftBranch_smul (β : R.Branch) (a : ℂ) (Y : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    R.liftBranch β (a • Y) = a • R.liftBranch β Y := by
  ext x y
  simp only [liftBranch, reindex_apply, submatrix_apply, Matrix.smul_apply,
    kroneckerMap_apply, tagLift, of_apply, smul_eq_mul]
  split_ifs
  · simp only [mul_assoc]
  · simp only [zero_mul, mul_zero]

/-- **The tag maps of a branch as a word.** Contracting the affected old tags with `⟨b|` and
preparing the affected new tags in `|a⟩` acts, in canonical coordinates, as the tag block
`|a⟩⟨b| ⊗ 1` of the branch. -/
theorem layoutIso_tagChangeWord (β : R.Branch) (own : ι → Party)
    (z : Mem (layoutRegs q (R.untouched ++ R.oldAffected) own)) :
    layoutIso (R.untouched ++ R.newAffected) own
        ((tagChangeWord R.untouched R.oldAffected R.newAffected β.2.2 β.1 own).eval z) =
      act (R.liftBranch β 1) (layoutIso (R.untouched ++ R.oldAffected) own z) := by
  refine layoutIso_eq_act_of_basis _ _ _ _ _ _ (fun τ c => ?_) z
  rw [eval_tagChangeWord, LinearIsometryEquiv.map_smul, layoutIso_layoutVec]
  ext ⟨τ', c'⟩
  rw [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  change _ = (R.liftBranch β 1 *ᵥ (EuclideanSpace.single (τ, c) (1 : ℂ)).ofLp) (τ', c')
  rw [PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply, liftBranch_apply,
    Matrix.one_apply]
  have h : (τ', c') = ((tagAppendEquiv R.untouched R.newAffected).symm
      ((tagAppendEquiv R.untouched R.oldAffected τ).1, β.1), c) ↔
      ((tagAppendEquiv R.untouched R.newAffected τ').2 = β.1 ∧
        (tagAppendEquiv R.untouched R.newAffected τ').1 =
          (tagAppendEquiv R.untouched R.oldAffected τ).1) ∧ c' = c := by
    rw [Prod.mk.injEq, Equiv.eq_symm_apply, Prod.ext_iff]
    tauto
  rw [if_congr h rfl rfl]
  by_cases h₁ : (tagAppendEquiv R.untouched R.newAffected τ').2 = β.1 <;>
    by_cases h₂ : (tagAppendEquiv R.untouched R.oldAffected τ).2 = β.2.2 <;>
    by_cases h₃ : (tagAppendEquiv R.untouched R.newAffected τ').1 =
      (tagAppendEquiv R.untouched R.oldAffected τ).1 <;>
    by_cases h₄ : c' = c <;> simp [h₁, h₂, h₃, h₄]

end SmallPatchRewrite

end TNLean.PEPS.EncodedFrame
