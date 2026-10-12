/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameRegisters
import TNLean.PEPS.Approximation.RegisterReordering

/-!
# The registers of two encoded frames and the two-sheet exchange

The two-sheet exchange of Lemma 6.6 acts on the registers of two frames, those of the first
frame followed by those of the second (`twoLayoutIso` identifies them with the product of the
canonical coordinates of the two frames). Its proof implements the exchange by a register
renaming `ℛ` and private corrections at `P∘` (`05-frames.tex`, lines 485–515). This file writes
both on the registers of the frames:

* `TwoSheetExchange.renameWord` is the renaming as a word of exchanges of tensor factors: the
  tags of each frame are split into those of the holes outside and inside `Y`, the raw registers
  of the sites in `Y` of each sheet are moved next to its inside tags, these blocks are exchanged
  between the sheets, and everything is merged back. No register changes its party. Its operator
  in canonical coordinates is `ℛ` (`twoLayoutIso_renameWord`).
* `correctionLayoutWord` moves the raw registers of `U` of both sheets to the front, applies a
  matrix `W` to them as one private contraction at `P∘`, and moves them back; its operator is
  `1_tags ⊗ (1_{T E} ⊗ W)` (`twoLayoutIso_correctionLayoutWord`).

## Main definitions

* `EncodedFrame.twoLayoutIso`: the registers of two frames in canonical coordinates.
* `EncodedFrame.correctionLayoutWord`, `EncodedFrame.twoSheetPlace`.
* `EncodedFrame.TwoSheetExchange.renameWord`.

## Main results

* `EncodedFrame.twoLayoutIso_eq_act_of_basis`: operators on two frames are determined by their
  values on basis vectors.
* `EncodedFrame.twoLayoutIso_correctionLayoutWord`, `EncodedFrame.correctionLayoutWord_props`.
* `EncodedFrame.TwoSheetExchange.twoLayoutIso_renameWord`,
  `EncodedFrame.TwoSheetExchange.isReordering_renameWord`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.6 `lem:exchange`,
  `05-frames.tex`, lines 481–561.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

open PairEffect ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### The registers of two frames in canonical coordinates -/

section TwoLayout

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

/-- The registers of two frames, those of the first followed by those of the second, identified
with the product `ℂ^{L₁ × L₂}` of their canonical coordinates. -/
def twoLayoutIso (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party) :
    Mem (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q))) :=
  (appendIso _ _).trans ((((layoutIso l₁ own₁).rTensor _).trans
    ((layoutIso l₂ own₂).lTensor _)).trans (pairIso _ _))

theorem twoLayoutIso_symm_single (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party)
    (τ₁ : TagSpace l₁) (c₁ : ι → Fin q) (τ₂ : TagSpace l₂) (c₂ : ι → Fin q) :
    (twoLayoutIso l₁ l₂ own₁ own₂).symm (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)) =
      (appendIso _ _).symm (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ layoutVec l₂ own₂ τ₂ c₂) := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  change _ = pairIso _ _ ((layoutIso l₂ own₂).lTensor _ ((layoutIso l₁ own₁).rTensor _
    (appendIso _ _ ((appendIso _ _).symm (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ
      layoutVec l₂ own₂ τ₂ c₂)))))
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul,
    layoutIso_layoutVec, layoutIso_layoutVec, pairIso_single_tmul_single]

theorem twoLayoutIso_basis (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party)
    (τ₁ : TagSpace l₁) (c₁ : ι → Fin q) (τ₂ : TagSpace l₂) (c₂ : ι → Fin q) :
    twoLayoutIso l₁ l₂ own₁ own₂
        ((appendIso _ _).symm (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ layoutVec l₂ own₂ τ₂ c₂)) =
      EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ) := by
  rw [← twoLayoutIso_symm_single, LinearIsometryEquiv.apply_symm_apply]

/-- Two operators on the registers of two frames agree in canonical coordinates as soon as they
agree on the basis vectors. -/
theorem twoLayoutIso_eq_act_of_basis (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party)
    (l₁' l₂' : List (Hole pos q Party)) (own₁' own₂' : ι → Party)
    (f : Mem (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂) →L[ℂ]
      Mem (layoutRegs q l₁' own₁' ++ layoutRegs q l₂' own₂'))
    (A : Matrix ((TagSpace l₁' × (ι → Fin q)) × (TagSpace l₂' × (ι → Fin q)))
      ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q))) ℂ)
    (hf : ∀ τ₁ c₁ τ₂ c₂, twoLayoutIso l₁' l₂' own₁' own₂'
      (f ((appendIso _ _).symm (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ layoutVec l₂ own₂ τ₂ c₂))) =
        act A (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)))
    (z : Mem (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂)) :
    twoLayoutIso l₁' l₂' own₁' own₂' (f z) = act A (twoLayoutIso l₁ l₂ own₁ own₂ z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (twoLayoutIso l₁ l₂ own₁ own₂).symm y :=
    ⟨twoLayoutIso l₁ l₂ own₁ own₂ z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨τ₁, c₁⟩, ⟨τ₂, c₂⟩⟩ := i
  rw [EuclideanSpace.basisFun_apply, twoLayoutIso_symm_single, hf]

end TwoLayout

/-! ### A private contraction on the raw registers of `U` on two sheets -/

section Correction

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ} {T E : Finset ι}

/-- The sites of `sites ι` in `U = (T ∪ E)ᶜ`. -/
abbrev sitesU (T E : Finset ι) : List ι := listT (sites ι) (T ∪ E)ᶜ

/-- The sites of `sites ι` in `T ∪ E`. -/
abbrev sitesR (T E : Finset ι) : List ι := listR (sites ι) (T ∪ E)ᶜ

/-- The raw registers of `U` on two sheets, identified with `ℂ^{(U → Fin q) × (U → Fin q)}`. -/
def pairUIso (own₁ own₂ : ι → Party) :
    Mem (siteRegs q own₁ (sitesU T E) ++ siteRegs q own₂ (sitesU T E)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) :=
  (appendIso _ _).trans ((((groupIso own₁ _ (equivT nodup_sites mem_sites)).rTensor _).trans
    ((groupIso own₂ _ (equivT nodup_sites mem_sites)).lTensor _)).trans (pairIso _ _))

theorem pairUIso_siteVec (own₁ own₂ : ι → Party) (c₁ c₂ : ι → Fin q) :
    pairUIso (T := T) (E := E) own₁ own₂ ((appendIso _ _).symm
        (siteVec own₁ (sitesU T E) c₁ ⊗ₜ siteVec own₂ (sitesU T E) c₂)) =
      EuclideanSpace.single ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x))
        (1 : ℂ) := by
  change pairIso _ _ ((groupIso own₂ _ (equivT nodup_sites mem_sites)).lTensor _
    ((groupIso own₁ _ (equivT nodup_sites mem_sites)).rTensor _
      (appendIso _ _ ((appendIso _ _).symm
        (siteVec own₁ (sitesU T E) c₁ ⊗ₜ siteVec own₂ (sitesU T E) c₂))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul,
    groupIso_siteVec own₁ _ _ Subtype.val (fun _ => rfl) c₁,
    groupIso_siteVec own₂ _ _ Subtype.val (fun _ => rfl) c₂]
  exact pairIso_single_tmul_single _ _

/-- **The corrections as one private contraction.** On two layouts of frames whose raw registers
of `U = (T ∪ E)ᶜ` are all held by `P`, move the raw registers of `U` of both sheets to the front
by exchanges of tensor factors, apply the matrix `W` to them as one private contraction at `P`,
and move them back.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 500–515. -/
def correctionLayoutWord (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ) :
    Word (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂)
      (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂) :=
  let pU : ι → Bool := fun x => decide (x ∈ (T ∪ E)ᶜ)
  let k₁ := tagRegs l₁
  let k₂ := tagRegs l₂
  let U₁ := siteRegs q own₁ (sitesU T E)
  let R₁ := siteRegs q own₁ (sitesR T E)
  let U₂ := siteRegs q own₂ (sitesU T E)
  let R₂ := siteRegs q own₂ (sitesR T E)
  let rest := k₁ ++ (R₁ ++ (k₂ ++ R₂))
  have hU : ∀ r ∈ U₁ ++ U₂, r.owner = P := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact owner_siteRegs (fun x hx => h₁ x ((mem_listT mem_sites x).mp hx)) r hr
    · exact owner_siteRegs (fun x hx => h₂ x ((mem_listT mem_sites x).mp hx)) r hr
  .comp (Word.assocWord k₁ (siteRegs q own₁ (sites ι)) (layoutRegs q l₂ own₂)) <|
  .comp (Word.frameList k₁ (partWordApp own₁ pU (layoutRegs q l₂ own₂) (sites ι))) <|
  .comp (Word.frameList k₁ (Word.frameList U₁ (Word.frameList R₁ (Word.frameList k₂
    (partWord own₂ pU (sites ι)))))) <|
  .comp (Word.exchangeBlocks k₁ U₁ (R₁ ++ (k₂ ++ (U₂ ++ R₂)))) <|
  .comp (Word.frameList U₁ (Word.frameList k₁ (Word.frameList R₁
    (Word.exchangeBlocks k₂ U₂ R₂)))) <|
  .comp (Word.frameList U₁ (Word.frameList k₁ (Word.exchangeBlocks R₁ U₂ (k₂ ++ R₂)))) <|
  .comp (Word.frameList U₁ (Word.exchangeBlocks k₁ U₂ (R₁ ++ (k₂ ++ R₂)))) <|
  .comp (Word.unassocWord U₁ U₂ rest) <|
  .comp (Word.localMap P (ℓ₁ := U₁ ++ U₂) (ℓ₂ := U₁ ++ U₂) hU hU
    (isoL (pairUIso own₁ own₂).symm ∘L act W ∘L isoL (pairUIso own₁ own₂)) rest) <|
  .comp (Word.assocWord U₁ U₂ rest) <|
  .comp (Word.frameList U₁ (Word.exchangeBlocks U₂ k₁ (R₁ ++ (k₂ ++ R₂)))) <|
  .comp (Word.frameList U₁ (Word.frameList k₁ (Word.exchangeBlocks U₂ R₁ (k₂ ++ R₂)))) <|
  .comp (Word.frameList U₁ (Word.frameList k₁ (Word.frameList R₁
    (Word.exchangeBlocks U₂ k₂ R₂)))) <|
  .comp (Word.exchangeBlocks U₁ k₁ (R₁ ++ (k₂ ++ (U₂ ++ R₂)))) <|
  .comp (Word.frameList k₁ (Word.frameList U₁ (Word.frameList R₁ (Word.frameList k₂
    (unpartWord own₂ pU (sites ι)))))) <|
  .comp (Word.frameList k₁ (unpartWordApp own₁ pU (layoutRegs q l₂ own₂) (sites ι))) <|
  Word.unassocWord k₁ (siteRegs q own₁ (sites ι)) (layoutRegs q l₂ own₂)

theorem pairUIso_symm_single (h : Disjoint T E) (own₁ own₂ : ι → Party) (c₁ c₂ : ι → Fin q)
    (u : (↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) :
    (pairUIso (T := T) (E := E) own₁ own₂).symm (EuclideanSpace.single u (1 : ℂ)) =
      (appendIso _ _).symm (siteVec own₁ (sitesU T E) (merge h ((fun x : T => c₁ x), u.1) c₁) ⊗ₜ
        siteVec own₂ (sitesU T E) (merge h ((fun x : T => c₂ x), u.2) c₂)) := by
  rw [LinearIsometryEquiv.symm_apply_eq, pairUIso_siteVec, merge_restrict_U, merge_restrict_U]

theorem merge_self_of_mem_union (h : Disjoint T E) (u : ↥(T ∪ E)ᶜ → Fin q) (c : ι → Fin q)
    {x : ι} (hx : x ∈ T ∪ E) : merge h ((fun y : T => c y), u) c x = c x := by
  rcases Finset.mem_union.mp hx with hT | hE
  · exact threeSplit_symm_apply_of_mem_left h _ _ _ hT
  · exact merge_of_mem_E h _ c hE

theorem mem_of_mem_sitesR {x : ι} (hx : x ∈ sitesR T E) : x ∈ T ∪ E :=
  not_not.mp (Finset.mem_compl.not.mp ((mem_listR mem_sites x).mp hx))

/-- **The corrections on basis vectors.** The configurations of the two sheets on `U` are
mixed by `W`; those on `T ∪ E` and the tags are untouched. -/
theorem eval_correctionLayoutWord (h : Disjoint T E) (l₁ l₂ : List (Hole pos q Party))
    (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (τ₁ : TagSpace l₁) (c₁ : ι → Fin q) (τ₂ : TagSpace l₂) (c₂ : ι → Fin q) :
    (correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).eval
        ((appendIso (layoutRegs q l₁ own₁) (layoutRegs q l₂ own₂)).symm
          (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ layoutVec l₂ own₂ τ₂ c₂)) =
      ∑ u, W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x)) •
        (appendIso (layoutRegs q l₁ own₁) (layoutRegs q l₂ own₂)).symm
          (layoutVec l₁ own₁ τ₁ (merge h ((fun x : T => c₁ x), u.1) c₁) ⊗ₜ
            layoutVec l₂ own₂ τ₂ (merge h ((fun x : T => c₂ x), u.2) c₂)) := by
  simp only [correctionLayoutWord, layoutVec, Word.eval_comp, ContinuousLinearMap.comp_apply]
  simp only [Word.eval_assocWord_appendIso_symm, Word.eval_frameList_appendIso_symm,
    eval_partWordApp, eval_partWord, Word.eval_exchangeBlocks_appendIso_symm,
    Word.eval_unassocWord_appendIso_symm, eval_localMap]
  have hloc : (isoL (pairUIso (T := T) (E := E) own₁ own₂).symm ∘L act W ∘L
      isoL (pairUIso own₁ own₂)) ((appendIso _ _).symm
        (siteVec own₁ (sitesU T E) c₁ ⊗ₜ siteVec own₂ (sitesU T E) c₂)) =
      ∑ u, W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x)) •
        (appendIso _ _).symm (siteVec own₁ (sitesU T E) (merge h ((fun x : T => c₁ x), u.1) c₁) ⊗ₜ
          siteVec own₂ (sitesU T E) (merge h ((fun x : T => c₂ x), u.2) c₂)) := by
    simp only [ContinuousLinearMap.comp_apply, isoL_apply]
    rw [pairUIso_siteVec, ← (EuclideanSpace.basisFun _ ℂ).sum_repr (act W _), map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [LinearIsometryEquiv.map_smul, EuclideanSpace.basisFun_repr, act_single_apply,
      EuclideanSpace.basisFun_apply, pairUIso_symm_single h]
  rw [hloc]
  set κ : (↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q) → ℂ :=
    fun u => W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x))
  simp only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_sum, map_smul]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  rw [siteVec_congr own₁ (sitesR T E) (c' := merge h ((fun x : T => c₁ x), u.1) c₁)
      fun x hx => (merge_self_of_mem_union h _ c₁ (mem_of_mem_sitesR hx)).symm,
    siteVec_congr own₂ (sitesR T E) (c' := merge h ((fun x : T => c₂ x), u.2) c₂)
      fun x hx => (merge_self_of_mem_union h _ c₂ (mem_of_mem_sitesR hx)).symm]
  simp only [Word.eval_assocWord_appendIso_symm, Word.eval_frameList_appendIso_symm,
    Word.eval_exchangeBlocks_appendIso_symm, Word.eval_unassocWord_appendIso_symm,
    eval_unpartWord, eval_unpartWordApp]

theorem threeSplit_fst (h : Disjoint T E) (c : ι → Fin q) :
    (threeSplit q T E h c).1 = ((fun x : T => c x), (fun x : E => c x)) :=
  rfl

theorem threeSplit_snd (h : Disjoint T E) (c : ι → Fin q) :
    (threeSplit q T E h c).2 = fun x : ↥(T ∪ E)ᶜ => c x :=
  rfl

/-- The operator `W` on the two copies of `U = (T ∪ E)ᶜ`, tensored with the identity on the
two copies of `T` and `E`, on the raw registers of two sheets. -/
abbrev twoSheetPlace (h : Disjoint T E)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ) :
    Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ :=
  (((1 : Matrix (((T → Fin q) × (E → Fin q)) × ((T → Fin q) × (E → Fin q)))
      (((T → Fin q) × (E → Fin q)) × ((T → Fin q) × (E → Fin q))) ℂ) ⊗ₖ W).submatrix
    (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)).submatrix
    (threeSplit₂ h) (threeSplit₂ h)

theorem sum_single_merge₂ (h : Disjoint T E) (l₁ l₂ : List (Hole pos q Party))
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (τ₁ : TagSpace l₁) (c₁ : ι → Fin q) (τ₂ : TagSpace l₂) (c₂ : ι → Fin q) :
    ∑ u, W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x)) •
        (EuclideanSpace.single ((τ₁, merge h ((fun x : T => c₁ x), u.1) c₁),
          (τ₂, merge h ((fun x : T => c₂ x), u.2) c₂)) (1 : ℂ) :
          EuclideanSpace ℂ ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q)))) =
      act (liftTags (l₁ := l₁) (l₂ := l₂) (twoSheetPlace h W))
        (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)) := by
  ext ⟨⟨τ₁', c₁'⟩, ⟨τ₂', c₂'⟩⟩
  simp only [act_apply_apply, PiLp.ofLp_single, Matrix.mulVec_single_one, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, liftTags,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Equiv.prodProdProdComm_apply, Equiv.prodCongr_apply, Prod.map]
  set u₀ : (↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q) :=
    ((fun x : ↥(T ∪ E)ᶜ => c₁' x), (fun x : ↥(T ∪ E)ᶜ => c₂' x))
  set B : Prop := τ₁' = τ₁ ∧ τ₂' = τ₂
  set A : Prop := (((fun x : T => c₁ x) = fun x : T => c₁' x) ∧
      (fun x : E => c₁' x) = fun x : E => c₁ x) ∧
    (((fun x : T => c₂ x) = fun x : T => c₂' x) ∧ (fun x : E => c₂' x) = fun x : E => c₂ x)
  have key : ∀ u : (↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q),
      (Pi.single ((τ₁, merge h ((fun x : T => c₁ x), u.1) c₁),
        (τ₂, merge h ((fun x : T => c₂ x), u.2) c₂)) (1 : ℂ) :
          (TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q)) → ℂ)
          ((τ₁', c₁'), (τ₂', c₂')) =
        if u = u₀ then (if B then 1 else 0) * (if A then 1 else 0) else 0 := by
    intro u
    rw [Pi.single_apply, ite_zero_mul_ite_zero, mul_one, ← ite_and]
    congr 1
    simp only [merge_eq_iff, u₀, A, B, Prod.ext_iff]
    exact propext (by tauto)
  simp_rw [key, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hB : (if (τ₁', τ₂') = (τ₁, τ₂) then (1 : ℂ) else 0) = if B then 1 else 0 := by
    congr 1
    simp [B]
  have hA : (if (((threeSplit q T E h c₁').1, (threeSplit q T E h c₂').1) =
      ((threeSplit q T E h c₁).1, (threeSplit q T E h c₂).1)) then (1 : ℂ) else 0) =
        if A then 1 else 0 := by
    congr 1
    simp only [A, Prod.mk.injEq, threeSplit_fst]
    exact propext (by tauto)
  rw [hB, hA]
  simp only [threeSplit_snd, u₀]
  split_ifs <;> ring

/-- **The corrections in canonical coordinates.** The correction word acts on the registers of
the two frames as `1_tags ⊗ (1_{T E} ⊗ W)`. -/
theorem twoLayoutIso_correctionLayoutWord (h : Disjoint T E) (l₁ l₂ : List (Hole pos q Party))
    (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (z : Mem (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂)) :
    twoLayoutIso l₁ l₂ own₁ own₂ ((correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).eval z) =
      act (liftTags (l₁ := l₁) (l₂ := l₂) (twoSheetPlace h W)) (twoLayoutIso l₁ l₂ own₁ own₂ z) :=
  twoLayoutIso_eq_act_of_basis l₁ l₂ own₁ own₂ l₁ l₂ own₁ own₂ _ _ (fun τ₁ c₁ τ₂ c₂ => by
    rw [eval_correctionLayoutWord h, map_sum, ← sum_single_merge₂]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [LinearIsometryEquiv.map_smul, twoLayoutIso_basis]) z

/-- The corrections form an allowed word using only `P`, without pair sources. -/
theorem correctionLayoutWord_props (l₁ l₂ : List (Hole pos q Party))
    (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    {W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ} (hW : ‖W‖ ≤ 1) :
    (correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).IsAllowed ∧
      (correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).UsesOnly {P} ∧
      (correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).sourceCount = 0 := by
  have hloc : ‖isoL (pairUIso (T := T) (E := E) own₁ own₂).symm ∘L act W ∘L
      isoL (pairUIso own₁ own₂)‖ ≤ 1 :=
    (norm_comp_isoL_le _ _ _).trans ((norm_act W).le.trans hW)
  simp only [correctionLayoutWord, Word.IsAllowed, Word.UsesOnly, Word.sourceCount,
    Word.isAllowed_frameList_iff, Word.usesOnly_frameList_iff, Word.sourceCount_frameList,
    Word.IsReordering.isAllowed, Word.IsReordering.usesOnly, Word.IsReordering.sourceCount_eq,
    Word.isReordering_assocWord, Word.isReordering_unassocWord, Word.isReordering_exchangeBlocks,
    isReordering_partWordApp, isReordering_partWord, isReordering_unpartWordApp,
    isReordering_unpartWord, hloc, Set.mem_singleton_iff, and_self]

end Correction

/-! ### The renaming of a two-sheet exchange -/

namespace TwoSheetExchange

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ} (X : TwoSheetExchange pos q Party)

/-- The sites in the region `Y`, in the order of `sites ι`. -/
abbrev sitesY : List ι := listT (sites ι) X.region

/-- The sites outside the region `Y`, in the order of `sites ι`. -/
abbrev sitesN : List ι := listR (sites ι) X.region

/-- **The renaming `ℛ` as a word of exchanges of tensor factors.** Split the tags of both frames
into those of the holes outside and inside `Y`, move the raw registers of the sites in `Y` of
each sheet next to its inside tags, exchange these blocks between the two sheets, and merge back.
Every register keeps its party: a raw register of the first sheet at a site of `Y` becomes the
register of the second new frame at that site, whose owner is the old owner on the first sheet.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 485–490. -/
def renameWord : Word (X.frame₁.regs ++ X.frame₂.regs) (X.newFrame₁.regs ++ X.newFrame₂.regs) :=
  let pY : ι → Bool := fun x => decide (x ∈ X.region)
  let o₁ := tagRegs X.out₁
  let i₁ := tagRegs X.in₁
  let o₂ := tagRegs X.out₂
  let i₂ := tagRegs X.in₂
  let Y₁ := siteRegs q X.owner₁ X.sitesY
  let N₁ := siteRegs q X.owner₁ X.sitesN
  let Y₂ := siteRegs q X.owner₂ X.sitesY
  let N₂ := siteRegs q X.owner₂ X.sitesN
  let Y₁' := siteRegs q X.newFrame₁.owner X.sitesY
  let N₁' := siteRegs q X.newFrame₁.owner X.sitesN
  let Y₂' := siteRegs q X.newFrame₂.owner X.sitesY
  .comp (Word.assocWord (tagRegs (X.out₁ ++ X.in₁)) (siteRegs q X.owner₁ (sites ι))
    X.frame₂.regs) <|
  .comp (tagSplit X.out₁ X.in₁ (siteRegs q X.owner₁ (sites ι) ++ X.frame₂.regs)) <|
  .comp (Word.frameList o₁ (Word.frameList i₁ (partWordApp X.owner₁ pY X.frame₂.regs
    (sites ι)))) <|
  .comp (Word.frameList o₁ (Word.frameList i₁ (Word.frameList Y₁ (Word.frameList N₁
    (tagSplit X.out₂ X.in₂ (siteRegs q X.owner₂ (sites ι))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₁ (Word.frameList Y₁ (Word.frameList N₁
    (Word.frameList o₂ (Word.frameList i₂ (partWord X.owner₂ pY (sites ι)))))))) <|
  .comp (Word.frameList o₁ (Word.swapPairs i₁ Y₁ N₁ o₂ i₂ Y₂ N₂)) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (relabelSitesApp X.owner₂ X.newFrame₁.owner
    (N₁ ++ (o₂ ++ (i₁ ++ (Y₁ ++ N₂)))) X.sitesY fun x hx => by
      simp [(mem_listT mem_sites x).mp hx]))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (relabelSitesApp X.owner₁
    X.newFrame₁.owner (o₂ ++ (i₁ ++ (Y₁ ++ N₂))) X.sitesN fun x hx => by
      simp [(mem_listR mem_sites x).mp hx])))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (relabelSitesApp X.owner₁ X.newFrame₂.owner N₂
      X.sitesY fun x hx => by simp [(mem_listT mem_sites x).mp hx]))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (Word.frameList Y₂' (relabelSites X.owner₂
      X.newFrame₂.owner X.sitesN fun x hx => by simp [(mem_listR mem_sites x).mp hx])))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (unpartWord X.newFrame₂.owner pY (sites ι)))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (tagMerge X.out₂ X.in₁ (siteRegs q X.newFrame₂.owner (sites ι))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (unpartWordApp X.newFrame₁.owner pY
    X.newFrame₂.regs (sites ι)))) <|
  .comp (tagMerge X.out₁ X.in₂ (siteRegs q X.newFrame₁.owner (sites ι) ++ X.newFrame₂.regs)) <|
  Word.unassocWord (tagRegs (X.out₁ ++ X.in₂)) (siteRegs q X.newFrame₁.owner (sites ι))
    X.newFrame₂.regs

/-- **The renaming on basis vectors.** Inside `Y` the configurations and the inside tags of the
two sheets change places. -/
theorem eval_renameWord (τ₁ : TagSpace (X.out₁ ++ X.in₁)) (c₁ : ι → Fin q)
    (τ₂ : TagSpace (X.out₂ ++ X.in₂)) (c₂ : ι → Fin q) :
    X.renameWord.eval ((appendIso X.frame₁.regs X.frame₂.regs).symm
        (layoutVec (X.out₁ ++ X.in₁) X.owner₁ τ₁ c₁ ⊗ₜ
          layoutVec (X.out₂ ++ X.in₂) X.owner₂ τ₂ c₂)) =
      (appendIso X.newFrame₁.regs X.newFrame₂.regs).symm
        (layoutVec (X.out₁ ++ X.in₂) X.newFrame₁.owner
            ((tagAppendEquiv X.out₁ X.in₂).symm
              ((tagAppendEquiv X.out₁ X.in₁ τ₁).1, (tagAppendEquiv X.out₂ X.in₂ τ₂).2))
            (fun x => if x ∈ X.region then c₂ x else c₁ x) ⊗ₜ
          layoutVec (X.out₂ ++ X.in₁) X.newFrame₂.owner
            ((tagAppendEquiv X.out₂ X.in₁).symm
              ((tagAppendEquiv X.out₂ X.in₂ τ₂).1, (tagAppendEquiv X.out₁ X.in₁ τ₁).2))
            (fun x => if x ∈ X.region then c₁ x else c₂ x)) := by
  set c₁' : ι → Fin q := fun x => if x ∈ X.region then c₂ x else c₁ x
  set c₂' : ι → Fin q := fun x => if x ∈ X.region then c₁ x else c₂ x
  have hY₁ : siteVec X.owner₁ X.sitesY c₁ = siteVec X.owner₁ X.sitesY c₂' :=
    siteVec_congr _ _ fun x hx => by simp [c₂', (mem_listT mem_sites x).mp hx]
  have hN₁ : siteVec X.owner₁ X.sitesN c₁ = siteVec X.owner₁ X.sitesN c₁' :=
    siteVec_congr _ _ fun x hx => by simp [c₁', (mem_listR mem_sites x).mp hx]
  have hY₂ : siteVec X.owner₂ X.sitesY c₂ = siteVec X.owner₂ X.sitesY c₁' :=
    siteVec_congr _ _ fun x hx => by simp [c₁', (mem_listT mem_sites x).mp hx]
  have hN₂ : siteVec X.owner₂ X.sitesN c₂ = siteVec X.owner₂ X.sitesN c₂' :=
    siteVec_congr _ _ fun x hx => by simp [c₂', (mem_listR mem_sites x).mp hx]
  simp only [renameWord, layoutVec, Word.eval_comp, ContinuousLinearMap.comp_apply]
  simp only [Word.eval_assocWord_appendIso_symm, eval_tagSplit, Word.eval_frameList_appendIso_symm,
    eval_partWordApp, hY₁, hN₁]
  rw [eval_tagSplit]
  simp only [Word.eval_frameList_appendIso_symm, eval_partWord, hY₂, hN₂, Word.eval_swapPairs,
    eval_relabelSitesApp, eval_relabelSites, eval_unpartWord, eval_tagMerge, eval_unpartWordApp,
    Word.eval_unassocWord_appendIso_symm]

/-- **The renaming in canonical coordinates** is the renaming `ℛ` of `TwoSheetExchange.rename`. -/
theorem twoLayoutIso_renameWord
    (z : Mem (X.frame₁.regs ++ X.frame₂.regs)) :
    twoLayoutIso (X.out₁ ++ X.in₂) (X.out₂ ++ X.in₁) X.newFrame₁.owner X.newFrame₂.owner
        (X.renameWord.eval z) =
      act X.rename (twoLayoutIso (X.out₁ ++ X.in₁) (X.out₂ ++ X.in₂) X.owner₁ X.owner₂ z) :=
  twoLayoutIso_eq_act_of_basis _ _ _ _ _ _ _ _ _ _ (fun τ₁ c₁ τ₂ c₂ => by
    rw [eval_renameWord, twoLayoutIso_basis, rename, act_toMatrix_symm_single]
    rfl) z

/-- The renaming is a reordering: an allowed word using no party and no pair source. -/
@[simp] theorem isReordering_renameWord : X.renameWord.IsReordering := by
  simp [renameWord]

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
