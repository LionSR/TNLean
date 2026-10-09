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

/-! ### Product terms as allowed monomials -/

section Terms

variable [NeZero q]

omit [Fintype ι] [DecidableEq ι] [NeZero q] in
theorem act_smul {m n : Type*} [Fintype n] (a : ℂ) (A : Matrix m n ℂ)
    (ψ : EuclideanSpace ℂ n) : act (a • A) ψ = a • act A ψ := by
  ext i
  simp [act, Matrix.smul_mulVec]

omit [Fintype ι] [DecidableEq ι] [NeZero q] in
theorem act_sum {m n κ : Type*} [Fintype n] [Fintype κ] (A : κ → Matrix m n ℂ)
    (ψ : EuclideanSpace ℂ n) : act (∑ k, A k) ψ = ∑ k, act (A k) ψ := by
  ext i
  simp [act, Matrix.sum_mulVec]

theorem exists_of_mem_encSteps {s : Step ι q} : (l : List (Hole pos q Party)) →
    (t : TagSpace l) → s ∈ encSteps l t → ∃ h ∈ l, ∃ j, s.sites = h.patch.tagSample j
  | [], _, hs => absurd hs List.not_mem_nil
  | h :: l, t, hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨h, List.mem_cons_self, t.1, rfl⟩
    · obtain ⟨h', hh', j, hj⟩ := exists_of_mem_encSteps l t.2 hs
      exact ⟨h', List.mem_cons_of_mem _ hh', j, hj⟩

theorem exists_of_mem_decSteps {s : Step ι q} : (l : List (Hole pos q Party)) →
    (t : TagSpace l) → s ∈ decSteps l t → ∃ h ∈ l, ∃ j, s.sites = h.patch.tagSample j
  | [], _, hs => absurd hs List.not_mem_nil
  | h :: l, t, hs => by
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨h', hh', j, hj⟩ := exists_of_mem_decSteps l t.2 hs
      exact ⟨h', List.mem_cons_of_mem _ hh', j, hj⟩
    · rw [List.mem_singleton.mp hs]
      exact ⟨h, List.mem_cons_self, t.1, rfl⟩

namespace SmallPatchRewrite

variable (R : SmallPatchRewrite pos q Party)

/-- Every site of a step of a branch lies in the physical sample of a patch or of an affected
hole, so by condition (iv) its old and new owners belong to the specified list. -/
theorem owners_mem_parties_of_mem_branchSteps (hR : R.Conditions) (β : R.Branch)
    {s : Step ι q} (hs : s ∈ R.branchSteps β) {x : ι} (hx : x ∈ s.sites) :
    R.ownerOld x ∈ R.parties ∧ R.ownerNew x ∈ R.parties := by
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨h, hh, j, hj⟩ := exists_of_mem_encSteps _ _ hs
      obtain ⟨j', hj'⟩ := h.patch.exists_mem_sample_of_mem_tagSample (hj ▸ hx)
      exact R.owners_mem_parties_of_mem_sample hR
        (Or.inr ⟨h, List.mem_append_right _ hh, j', hj'⟩)
    · obtain ⟨P, hP, j, hj, -, -⟩ := exists_of_mem_patchSteps _ _ hs
      obtain ⟨j', hj'⟩ := P.exists_mem_sample_of_mem_tagSample (hj ▸ hx)
      exact R.owners_mem_parties_of_mem_sample hR (Or.inl ⟨P, hP, j', hj'⟩)
  · obtain ⟨h, hh, j, hj⟩ := exists_of_mem_decSteps _ _ hs
    obtain ⟨j', hj'⟩ := h.patch.exists_mem_sample_of_mem_tagSample (hj ▸ hx)
    exact R.owners_mem_parties_of_mem_sample hR
      (Or.inr ⟨h, List.mem_append_left _ hh, j', hj'⟩)

theorem owners_mem_parties_of_not_untouched (hR : R.Conditions) (β : R.Branch) {x : ι}
    (hx : ¬Untouched (R.branchChain β) x) :
    R.ownerOld x ∈ R.parties ∧ R.ownerNew x ∈ R.parties := by
  simp only [Untouched, not_forall, not_not] at hx
  obtain ⟨k, hk⟩ := hx
  exact R.owners_mem_parties_of_mem_branchSteps hR β (List.getElem_mem (l := R.branchSteps β) k.2)
    hk

/-- **A site touched by no step of a branch keeps its owner**, by condition (ii). -/
theorem ownerOld_eq_ownerNew_of_untouched (hR : R.Conditions) (β : R.Branch) {x : ι}
    (hx : Untouched (R.branchChain β) x) : R.ownerOld x = R.ownerNew x := by
  refine R.ownerOld_eq_ownerNew_of_direct hR β.2.1 fun hxP => ?_
  obtain ⟨s, hs, hxs⟩ := (mem_patchSquares_iff _ _).mp hxP
  obtain ⟨k, -, -, hk⟩ := exists_get_append₃_eq_mid (encSteps R.newAffected β.1)
    (patchSteps R.patches β.2.1) (decSteps R.oldAffected β.2.2) hs
  exact hx k (by
    change x ∈ ((encSteps R.newAffected β.1 ++ patchSteps R.patches β.2.1 ++
      decSteps R.oldAffected β.2.2).get k).sites
    rw [hk]
    exact hxs)

/-- The vertices of a branch network with open legs are at most `2m`. -/
theorem card_open_vertices_le (hR : R.Conditions) (β : R.Branch) :
    (∑ j, if ∃ x, IsOpen (R.branchChain β) (.inl j) x then 1 else 0) +
      (∑ j, if ∃ x, IsOpen (R.branchChain β) (.inr j) x then 1 else 0) ≤
        2 * R.patches.length := by
  classical
  rw [← Fintype.sum_sum_type (f := fun v => if ∃ x, IsOpen (R.branchChain β) v x then 1 else 0),
    Finset.sum_boole, Nat.cast_id]
  refine (Finset.card_le_card fun v hv => ?_).trans (R.card_patchVertices_le β)
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hv).2
  exact R.mem_patchVertices_of_isOpen hR β hx

/-- **A product term of a branch as an allowed monomial.** Under the four conditions of
Lemma 6.3, let `(a, s, b)` be a branch and let a unit vector be chosen on every open-leg group of
its network (one of the orthonormal families of the whole-group truncation). Then the product
term placed in the tag block, `|a⟩⟨b| ⊗ T ⊗ 1`, is `σ` times the operator of an allowed monomial
from the registers of `F_old` to those of `F_new`, one register per site and per tag, with
`|σ| ≤ 1`. The monomial uses only the specified parties and has at most `2m` normalized pair
sources and at most `2m` normalized pair effects. It consumes the open inputs of each patch bra
by its normalized covector at their at most two old owners, contracts every touched raw register
with `⟨0|` at its old owner and prepares `|0⟩` at its new owner, prepares the open outputs of each
patch ket by its normalized vector at their at most two new owners, and replaces the affected
tags by `⟨b|` and `|a⟩` at their tag owners; every other register is untouched.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 262–273 and 306–316:
after restoring the factored private maps and direct identities, each product term is precisely
a monomial allowed by Theorem 5.2, with boundedly many pair states and effects and a coefficient
of absolute value at most one. -/
theorem exists_termChain (hR : R.Conditions) (β : R.Branch)
    {r : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length → ℕ}
    (e : (v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r v) →
      EuclideanSpace ℂ (Group (R.branchChain β) v))
    (he : ∀ v, Orthonormal ℂ (e v))
    (i : (v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r v)) :
    ∃ (σ : ℂ) (M : PartyChain R.oldFrame.regs R.newFrame.regs), ‖σ‖ ≤ 1 ∧ M.IsAllowed ∧
      M.UsesOnly (R.parties : Set Party) ∧ M.sourceCount ≤ 2 * R.patches.length ∧
      M.toEffectChain.effectCount ≤ 2 * R.patches.length ∧
      ∀ z, σ • R.newFrame.regIso (M.toEffectChain.eval z) =
        act (R.liftBranch β (termOp (R.branchChain β) e i)) (R.oldFrame.regIso z) := by
  set l := R.untouched ++ R.oldAffected
  set S : Set Party := (R.parties : Set Party)
  have hbra := fun j : Fin (R.branchSteps β).length =>
    exists_braVertexBlock (q := q) l R.ownerOld S (IsOpen (R.branchChain β) (.inl j))
      (fun _ => by
        obtain ⟨P, hP, hPx⟩ := R.exists_owners_of_isOpen_inl hR β j
        exact ⟨P, hP, fun x hx => ⟨(hPx x hx).1, (hPx x hx).2.1⟩⟩)
      (e (.inl j) (i (.inl j))) ((he _).1 _)
  choose B sB hsB hBE hBK hBB MB hMB₁ hMB₂ hMB₃ hMB₄ hMB₅ using hbra
  have hket := fun j : Fin (R.branchSteps β).length =>
    exists_ketVertexBlock (q := q) l R.ownerNew S (IsOpen (R.branchChain β) (.inr j))
      (fun _ => by
        obtain ⟨P, hP, hPx⟩ := R.exists_owners_of_isOpen_inr hR β j
        exact ⟨P, hP, fun x hx => ⟨(hPx x hx).1, (hPx x hx).2.2⟩⟩)
      (e (.inr j) (i (.inr j))) ((he _).1 _)
  choose K sK hsK hKE hKB hKK MK hMK₁ hMK₂ hMK₃ hMK₄ hMK₅ using hket
  set W := (sites ι).filter fun x => decide (¬Untouched (R.branchChain β) x) with hWdef
  have hWn : W.Nodup := nodup_sites.filter _
  have hW : ∀ x, x ∈ W ↔ ¬Untouched (R.branchChain β) x := fun x => by simp [hWdef, mem_sites]
  obtain ⟨M₁, a₁, a₂, a₃, a₄, a₅⟩ := exists_chain_listProd (layoutIso l R.ownerOld) S
    (fun j => (1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ (B j).op)
    (fun j => if ∃ x, IsOpen (R.branchChain β) (.inl j) x then 1 else 0)
    (fun j => if ∃ x, IsOpen (R.branchChain β) (.inl j) x then 1 else 0)
    (List.finRange _) fun j _ => ⟨MB j, hMB₁ j, hMB₂ j, hMB₃ j, hMB₄ j, hMB₅ j⟩
  obtain ⟨M₂, b₁, b₂, b₃, b₄, b₅⟩ := exists_zeroChain l S W hWn R.ownerOld R.ownerNew
    (fun x hx => R.owners_mem_parties_of_not_untouched hR β ((hW x).mp hx))
    (fun x hx => R.ownerOld_eq_ownerNew_of_untouched hR β (by simpa [hW] using hx))
  obtain ⟨M₃, c₁, c₂, c₃, c₄, c₅⟩ := exists_chain_listProd (layoutIso l R.ownerNew) S
    (fun j => (1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ (K j).op)
    (fun j => if ∃ x, IsOpen (R.branchChain β) (.inr j) x then 1 else 0)
    (fun j => if ∃ x, IsOpen (R.branchChain β) (.inr j) x then 1 else 0)
    (List.finRange _) fun j _ => ⟨MK j, hMK₁ j, hMK₂ j, hMK₃ j, hMK₄ j, hMK₅ j⟩
  set Wt := tagChangeWord R.untouched R.oldAffected R.newAffected β.2.2 β.1 R.ownerNew
  obtain ⟨t₁, t₂, t₃⟩ := tagChangeWord_props R.untouched R.oldAffected R.newAffected β.2.2 β.1
    R.ownerNew (S := S) (fun h hh => hR.tag_owners_mem h (List.mem_append_left _ hh))
    (fun h hh => hR.tag_owners_mem h (List.mem_append_right _ hh))
  obtain ⟨d₁, d₂, d₃, d₄⟩ := PartyChain.append_props S M₁ M₂ a₁ a₂ b₁ b₂
  obtain ⟨e₁, e₂, e₃, e₄⟩ := PartyChain.append_props S (M₁.append M₂) M₃ d₁ d₂ c₁ c₂
  obtain ⟨f₁, f₂, f₃, f₄⟩ := PartyChain.postcomp_props S ((M₁.append M₂).append M₃) Wt t₁ t₂
    e₁ e₂
  have hsum : ∀ g : Fin (R.branchSteps β).length → ℕ,
      ((List.finRange _).map g).sum = ∑ j, g j := fun g => by
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have hcount := R.card_open_vertices_le hR β
  rw [hsum] at a₃ a₄ c₃ c₄
  refine ⟨(∏ j, sB j) * ∏ j, sK j, ((M₁.append M₂).append M₃).postcomp Wt, ?_, f₁, f₂, ?_, ?_,
    fun z => ?_⟩
  · rw [norm_mul, norm_prod, norm_prod]
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul
          (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => hsB j)
          (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => hsK j)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [f₃, e₃, d₃, b₃, t₃]
    change _ ≤ _ at hcount
    omega
  · rw [f₄, e₄, d₄, b₄]
    omega
  · have hT := termOp_eq_smul_prod (R.branchChain β) e i B K sB sK hBE hBK hBB hKE hKB hKK hWn hW
    have hB : ((List.finRange _).map fun j => (1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ
        (B j).op).prod = 1 ⊗ₖ ((List.ofFn B).map RankOneBlock.op).prod := by
      rw [prod_map_one_kronecker, List.ofFn_eq_map, List.map_map]
      rfl
    have hK : ((List.finRange _).map fun j => (1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ
        (K j).op).prod = 1 ⊗ₖ ((List.ofFn K).map RankOneBlock.op).prod := by
      rw [prod_map_one_kronecker, List.ofFn_eq_map, List.map_map]
      rfl
    rw [hT, liftBranch_smul, act_smul]
    congr 1
    rw [PartyChain.eval_postcomp, ContinuousLinearMap.comp_apply, PartyChain.eval_append,
      ContinuousLinearMap.comp_apply, PartyChain.eval_append, ContinuousLinearMap.comp_apply]
    change layoutIso (R.untouched ++ R.newAffected) R.ownerNew
        (Wt.eval (M₃.toEffectChain.eval (M₂.toEffectChain.eval (M₁.toEffectChain.eval z)))) =
      act _ (layoutIso l R.ownerOld z)
    rw [layoutIso_tagChangeWord, c₅, b₅, a₅, hB, hK, ← act_mul, ← act_mul, ← act_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← mul_kronecker_mul, one_mul, ← mul_kronecker_mul, one_mul, liftBranch_mul]

/-- **Lemma 6.3, the rewrite as a sum of allowed monomials.** Under the four conditions of
Lemma 6.3, for every `δ > 0` (for instance `δ = L^{-a}`) let `N` be the number of branches, `m`
the number of additional patches and `k = ⌈(4 N m / δ)²⌉ + 1`. There are a contraction `M_δ` with
`‖M_δ - M‖ ≤ δ` and an expansion `M_δ = ∑_t c_t M_t` into at most `N k^{2m}` monomials `M_t` from
the registers of `F_old` to those of `F_new` (one register per site and per tag, each held by its
owner), each allowed in the sense of Theorem 5.2, using only the specified parties, with at most
`2m` normalized pair sources and at most `2m` normalized pair effects, and with coefficients
`|c_t| ≤ 1`. The expansion is read in canonical coordinates.

With `norm_act_refVec_sub_le_of_approx` and `rewrite_error_le_inv_pow_twenty`, the choice
`δ = L^{-30}` gives the reference-vector error `O(L^{-20})` of the final assertion of Lemma 6.3.
The count `N k^{2m}` is polynomial in `L` once `N` is; see
`exists_allowed_monomial_approx_of_card_le` and the scope restriction in the module docstring.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 214–217;
proof lines 254–341. -/
theorem exists_allowed_monomial_approx (hR : R.Conditions) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : PartyGate R.oldFrame.regs R.newFrame.regs,
      G.length ≤ Fintype.card R.Branch *
        truncationRank (Fintype.card R.Branch) ((2 * R.patches.length : ℕ) : ℝ) δ ^
          (2 * R.patches.length) ∧
      (∀ p ∈ G, ‖p.1‖ ≤ 1 ∧ p.2.IsAllowed ∧ p.2.UsesOnly (R.parties : Set Party) ∧
        p.2.sourceCount ≤ 2 * R.patches.length ∧
        p.2.toEffectChain.effectCount ≤ 2 * R.patches.length) ∧
      ∃ Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ, ‖Ma‖ ≤ 1 ∧ ‖Ma - R.rewrite‖ ≤ δ ∧
        ∀ z, (G.map fun p => p.1 • R.newFrame.regIso (p.2.toEffectChain.eval z)).sum =
          act Ma (R.oldFrame.regIso z) := by
  obtain ⟨r, e, c, -, he, hc, hcard, h1, h2⟩ := R.exists_contractive_approx hR hδ
  choose σ M hσ hM₁ hM₂ hM₃ hM₄ hM₅ using fun (β : R.Branch)
    (ii : (v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) → Fin (r β v)) =>
      R.exists_termChain hR β (e β) (he β) ii
  set a : ℂ := (((1 + δ / 2)⁻¹ : ℝ) : ℂ) with ha
  have hna : ‖a‖ ≤ 1 := by
    rw [ha, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  let κ := Σ β : R.Branch, ((v : Fin (R.branchSteps β).length ⊕ Fin (R.branchSteps β).length) →
    Fin (r β v))
  refine ⟨(Finset.univ : Finset κ).toList.map fun t => (a * c t.1 t.2 * σ t.1 t.2, M t.1 t.2),
    ?_, ?_, _, h1, h2, fun z => ?_⟩
  · rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_sigma]
    calc _ ≤ ∑ _β : R.Branch, truncationRank (Fintype.card R.Branch)
          ((2 * R.patches.length : ℕ) : ℝ) δ ^ (2 * R.patches.length) :=
          Finset.sum_le_sum fun β _ => hcard β
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  · intro p hp
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hp
    refine ⟨?_, hM₁ _ _, hM₂ _ _, hM₃ _ _, hM₄ _ _⟩
    rw [norm_mul, norm_mul]
    calc _ ≤ (1 : ℝ) * 1 * 1 := mul_le_mul (mul_le_mul hna (hc _ _) (norm_nonneg _) zero_le_one)
          (hσ _ _) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · rw [List.map_map, Finset.sum_map_toList, act_smul, act_sum, Finset.smul_sum]
    simp only [Function.comp_apply]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [liftBranch_sum_smul, act_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ii _ => ?_
    rw [act_smul, ← hM₅, smul_smul, smul_smul, mul_assoc]

omit [NeZero q] in
theorem truncationRank_mono {N N' g δ : ℝ} (hN : 0 ≤ N) (hNN' : N ≤ N') (hg : 0 ≤ g)
    (hδ : 0 < δ) : truncationRank N g δ ≤ truncationRank N' g δ := by
  unfold truncationRank
  gcongr

/-- **Lemma 6.3, the count with the number of cylinder terms as a parameter.** If every affected
hole and every additional patch has at most `D` cylinder terms, the expansion of
`exists_allowed_monomial_approx` has at most `D^E k'^{2m}` allowed monomials, with
`E = r_new + m + r_old` and `k' = ⌈(4 D^E m / δ)²⌉ + 1`. For `δ = L^{-a}`, this count is polynomial
in `L` when `D ≤ C L^c` (the cylinder-term bound `∑_j d_j ≤ C L^c` of Proposition 4.1) and `m`,
`r_old`, `r_new` are bounded.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 214–217;
proof lines 254–257 and 331–342. -/
theorem exists_allowed_monomial_approx_of_card_le (hR : R.Conditions) {δ : ℝ} (hδ : 0 < δ)
    {D : ℕ} (hnew : ∀ h ∈ R.newAffected, Fintype.card h.patch.Tag ≤ D)
    (hpatch : ∀ P ∈ R.patches, Fintype.card P.Tag ≤ D)
    (hold : ∀ h ∈ R.oldAffected, Fintype.card h.patch.Tag ≤ D) :
    ∃ G : PartyGate R.oldFrame.regs R.newFrame.regs,
      G.length ≤ D ^ (R.newAffected.length + R.patches.length + R.oldAffected.length) *
        truncationRank ((D ^ (R.newAffected.length + R.patches.length +
          R.oldAffected.length) : ℕ) : ℝ) ((2 * R.patches.length : ℕ) : ℝ) δ ^
          (2 * R.patches.length) ∧
      (∀ p ∈ G, ‖p.1‖ ≤ 1 ∧ p.2.IsAllowed ∧ p.2.UsesOnly (R.parties : Set Party) ∧
        p.2.sourceCount ≤ 2 * R.patches.length ∧
        p.2.toEffectChain.effectCount ≤ 2 * R.patches.length) ∧
      ∃ Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ, ‖Ma‖ ≤ 1 ∧ ‖Ma - R.rewrite‖ ≤ δ ∧
        ∀ z, (G.map fun p => p.1 • R.newFrame.regIso (p.2.toEffectChain.eval z)).sum =
          act Ma (R.oldFrame.regIso z) := by
  obtain ⟨G, hG, rest⟩ := R.exists_allowed_monomial_approx hR hδ
  have hN := R.card_branch_le hnew hpatch hold
  refine ⟨G, hG.trans (Nat.mul_le_mul hN (Nat.pow_le_pow_left ?_ _)), rest⟩
  exact truncationRank_mono (Nat.cast_nonneg _) (by exact_mod_cast hN) (Nat.cast_nonneg _) hδ

end SmallPatchRewrite

end Terms

end TNLean.PEPS.EncodedFrame
