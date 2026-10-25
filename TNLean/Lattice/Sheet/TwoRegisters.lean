/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Registers
import TNLean.Lattice.Sheet.Reordering

/-!
# The raw registers of two sheets and the corrections of an exchange

The two-sheet exchange of Lemma 6.6 acts on the registers of two sheets, each a block of front
registers followed by one raw register per site; the first sheet comes first
(`twoFrontLayoutIso` identifies them with the product of the canonical coordinates of the two
sheets). Its proof applies private corrections at `P∘` to the raw registers of
`U = Λ ∖ (T ∪ E)` of both sheets (`05-frames.tex`, lines 500–515).

* `frontCorrectionWord` moves the raw registers of `U` of both sheets to the front, applies a
  matrix `W` to them as one private contraction at `P∘`, and moves them back; its operator is
  `1_fronts ⊗ (1_{T E} ⊗ W)` (`twoFrontLayoutIso_frontCorrectionWord`).

For encoded frames the front blocks are the tag registers of the holes
(`TNLean.PEPS.Approximation.TwoSheetRegisters`); for sheets without holes they are empty. Nothing
here depends on a geometry of the sites.

## Main definitions

* `Sheet.twoFrontLayoutIso`: the registers of two sheets in canonical coordinates.
* `Sheet.pairUIso`: the raw registers of `U` on two sheets.
* `Sheet.frontCorrectionWord`, `Sheet.twoSheetPlace`, `Sheet.liftFront`.

## Main results

* `Sheet.twoFrontLayoutIso_eq_act_of_basis`: operators on two sheets are determined by
  their values on basis vectors.
* `Sheet.eval_frontCorrectionWord`: the corrections on basis vectors.
* `Sheet.twoFrontLayoutIso_frontCorrectionWord`, `Sheet.frontCorrectionWord_props`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.6 `lem:exchange`,
  `05-frames.tex`, lines 481–561.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

namespace TNLean.Lattice.Sheet

open PartyCircuit ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### The registers of two sheets in canonical coordinates -/

section TwoFrontLayout

variable [Fintype ι] [DecidableEq ι] {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂]
  [DecidableEq κ₂]

/-- The registers of two sheets, each a block of front registers followed by its raw registers,
those of the first followed by those of the second, identified with the product
`ℂ^{(κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q))}` of their canonical coordinates. -/
def twoFrontLayoutIso (k₁ : Layout Party) (i₁ : Mem k₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₁)
    (own₁ : ι → Party) (k₂ : Layout Party) (i₂ : Mem k₂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₂)
    (own₂ : ι → Party) :
    Mem ((k₁ ++ siteRegs q own₁ (sites ι)) ++ (k₂ ++ siteRegs q own₂ (sites ι))) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q))) :=
  (appendIso _ _).trans ((((frontLayoutIso k₁ i₁ own₁).rTensor _).trans
    ((frontLayoutIso k₂ i₂ own₂).lTensor _)).trans (pairIso _ _))

theorem twoFrontLayoutIso_symm_single (k₁ : Layout Party)
    (i₁ : Mem k₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₁) (own₁ : ι → Party) (k₂ : Layout Party)
    (i₂ : Mem k₂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₂) (own₂ : ι → Party)
    (τ₁ : κ₁) (c₁ : ι → Fin q) (τ₂ : κ₂) (c₂ : ι → Fin q) :
    (twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂).symm
        (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)) =
      (appendIso _ _).symm
        (frontLayoutVec k₁ i₁ own₁ τ₁ c₁ ⊗ₜ frontLayoutVec k₂ i₂ own₂ τ₂ c₂) := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  change _ = pairIso _ _ ((frontLayoutIso k₂ i₂ own₂).lTensor _
    ((frontLayoutIso k₁ i₁ own₁).rTensor _ (appendIso _ _ ((appendIso _ _).symm
      (frontLayoutVec k₁ i₁ own₁ τ₁ c₁ ⊗ₜ frontLayoutVec k₂ i₂ own₂ τ₂ c₂)))))
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul, frontLayoutIso_frontLayoutVec,
    frontLayoutIso_frontLayoutVec, pairIso_single_tmul_single]

theorem twoFrontLayoutIso_basis (k₁ : Layout Party) (i₁ : Mem k₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₁)
    (own₁ : ι → Party) (k₂ : Layout Party) (i₂ : Mem k₂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₂)
    (own₂ : ι → Party) (τ₁ : κ₁) (c₁ : ι → Fin q) (τ₂ : κ₂) (c₂ : ι → Fin q) :
    twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂
        ((appendIso _ _).symm (frontLayoutVec k₁ i₁ own₁ τ₁ c₁ ⊗ₜ
          frontLayoutVec k₂ i₂ own₂ τ₂ c₂)) =
      EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ) := by
  rw [← twoFrontLayoutIso_symm_single, LinearIsometryEquiv.apply_symm_apply]

/-- An operator on the registers of two sheets agrees in canonical coordinates with a matrix as
soon as they agree on the basis vectors. -/
theorem twoFrontLayoutIso_eq_act_of_basis (k₁ : Layout Party)
    (i₁ : Mem k₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₁) (own₁ : ι → Party) (k₂ : Layout Party)
    (i₂ : Mem k₂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₂) (own₂ : ι → Party)
    (f : Mem ((k₁ ++ siteRegs q own₁ (sites ι)) ++ (k₂ ++ siteRegs q own₂ (sites ι))) →L[ℂ]
      Mem ((k₁ ++ siteRegs q own₁ (sites ι)) ++ (k₂ ++ siteRegs q own₂ (sites ι))))
    (A : Matrix ((κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q)))
      ((κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q))) ℂ)
    (hf : ∀ τ₁ c₁ τ₂ c₂, twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂
      (f ((appendIso _ _).symm (frontLayoutVec k₁ i₁ own₁ τ₁ c₁ ⊗ₜ
        frontLayoutVec k₂ i₂ own₂ τ₂ c₂))) =
        act A (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)))
    (z : Mem ((k₁ ++ siteRegs q own₁ (sites ι)) ++ (k₂ ++ siteRegs q own₂ (sites ι)))) :
    twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂ (f z) =
      act A (twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂ z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂).symm y :=
    ⟨twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂ z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨τ₁, c₁⟩, ⟨τ₂, c₂⟩⟩ := i
  rw [EuclideanSpace.basisFun_apply, twoFrontLayoutIso_symm_single, hf]

end TwoFrontLayout

/-! ### A private contraction on the raw registers of `U` on two sheets -/

section Correction

variable [Fintype ι] [DecidableEq ι] {T E : Finset ι} {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁]
  [Fintype κ₂] [DecidableEq κ₂]

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

/-- **The corrections as one private contraction.** On two sheets, each a block of front
registers followed by its raw registers, whose raw registers of `U = (T ∪ E)ᶜ` are all held by
`P`, move the raw registers of `U` of both sheets to the front by exchanges of tensor factors,
apply the matrix `W` to them as one private contraction at `P`, and move them back.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 500–515. -/
def frontCorrectionWord (k₁ k₂ : Layout Party) (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ) :
    Word ((k₁ ++ siteRegs q own₁ (sites ι)) ++ (k₂ ++ siteRegs q own₂ (sites ι)))
      ((k₁ ++ siteRegs q own₁ (sites ι)) ++ (k₂ ++ siteRegs q own₂ (sites ι))) :=
  let pU : ι → Bool := fun x => decide (x ∈ (T ∪ E)ᶜ)
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
  .comp (Word.assocWord k₁ (siteRegs q own₁ (sites ι)) (k₂ ++ siteRegs q own₂ (sites ι))) <|
  .comp (Word.frameList k₁ (partWordApp own₁ pU (k₂ ++ siteRegs q own₂ (sites ι)) (sites ι))) <|
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
  .comp (Word.frameList k₁ (unpartWordApp own₁ pU (k₂ ++ siteRegs q own₂ (sites ι)) (sites ι))) <|
  Word.unassocWord k₁ (siteRegs q own₁ (sites ι)) (k₂ ++ siteRegs q own₂ (sites ι))

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
mixed by `W`; those on `T ∪ E` and the front registers are untouched. -/
theorem eval_frontCorrectionWord (h : Disjoint T E) (k₁ k₂ : Layout Party)
    (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (t₁ : Mem k₁) (c₁ : ι → Fin q) (t₂ : Mem k₂) (c₂ : ι → Fin q) :
    (frontCorrectionWord k₁ k₂ own₁ own₂ h₁ h₂ W).eval
        ((appendIso (k₁ ++ siteRegs q own₁ (sites ι)) (k₂ ++ siteRegs q own₂ (sites ι))).symm
          ((appendIso k₁ (siteRegs q own₁ (sites ι))).symm (t₁ ⊗ₜ siteVec own₁ (sites ι) c₁) ⊗ₜ
            (appendIso k₂ (siteRegs q own₂ (sites ι))).symm (t₂ ⊗ₜ siteVec own₂ (sites ι) c₂))) =
      ∑ u, W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x)) •
        (appendIso (k₁ ++ siteRegs q own₁ (sites ι)) (k₂ ++ siteRegs q own₂ (sites ι))).symm
          ((appendIso k₁ (siteRegs q own₁ (sites ι))).symm
              (t₁ ⊗ₜ siteVec own₁ (sites ι) (merge h ((fun x : T => c₁ x), u.1) c₁)) ⊗ₜ
            (appendIso k₂ (siteRegs q own₂ (sites ι))).symm
              (t₂ ⊗ₜ siteVec own₂ (sites ι) (merge h ((fun x : T => c₂ x), u.2) c₂))) := by
  simp only [frontCorrectionWord, Word.eval_comp, ContinuousLinearMap.comp_apply]
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

/-- The operator `G` on the raw registers of two sheets, tensored with the identity on their
front registers, in the canonical coordinates `(κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q))`. -/
def liftFront (G : Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ) :
    Matrix ((κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q)))
      ((κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q))) ℂ :=
  ((1 : Matrix (κ₁ × κ₂) (κ₁ × κ₂) ℂ) ⊗ₖ G).submatrix
    (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)

theorem sum_single_merge₂_liftFront (h : Disjoint T E)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (τ₁ : κ₁) (c₁ : ι → Fin q) (τ₂ : κ₂) (c₂ : ι → Fin q) :
    ∑ u, W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x)) •
        (EuclideanSpace.single ((τ₁, merge h ((fun x : T => c₁ x), u.1) c₁),
          (τ₂, merge h ((fun x : T => c₂ x), u.2) c₂)) (1 : ℂ) :
          EuclideanSpace ℂ ((κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q)))) =
      act (liftFront (κ₁ := κ₁) (κ₂ := κ₂) (twoSheetPlace h W))
        (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)) := by
  ext ⟨⟨τ₁', c₁'⟩, ⟨τ₂', c₂'⟩⟩
  simp only [act_apply_apply, PiLp.ofLp_single, Matrix.mulVec_single_one, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, liftFront,
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
          (κ₁ × (ι → Fin q)) × (κ₂ × (ι → Fin q)) → ℂ)
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
the two sheets as `1_fronts ⊗ (1_{T E} ⊗ W)`. -/
theorem twoFrontLayoutIso_frontCorrectionWord (h : Disjoint T E) (k₁ : Layout Party)
    (i₁ : Mem k₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₁) (k₂ : Layout Party)
    (i₂ : Mem k₂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ₂) (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (z : Mem ((k₁ ++ siteRegs q own₁ (sites ι)) ++ (k₂ ++ siteRegs q own₂ (sites ι)))) :
    twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂
        ((frontCorrectionWord k₁ k₂ own₁ own₂ h₁ h₂ W).eval z) =
      act (liftFront (κ₁ := κ₁) (κ₂ := κ₂) (twoSheetPlace h W))
        (twoFrontLayoutIso k₁ i₁ own₁ k₂ i₂ own₂ z) :=
  twoFrontLayoutIso_eq_act_of_basis k₁ i₁ own₁ k₂ i₂ own₂ _ _ (fun τ₁ c₁ τ₂ c₂ => by
    rw [frontLayoutVec, frontLayoutVec, eval_frontCorrectionWord h, map_sum,
      ← sum_single_merge₂_liftFront]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [LinearIsometryEquiv.map_smul, ← frontLayoutVec, ← frontLayoutVec,
      twoFrontLayoutIso_basis]) z

/-- The corrections form an allowed word using only `P`, without pair sources. -/
theorem frontCorrectionWord_props (k₁ k₂ : Layout Party)
    (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    {W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ} (hW : ‖W‖ ≤ 1) :
    (frontCorrectionWord k₁ k₂ own₁ own₂ h₁ h₂ W).IsAllowed ∧
      (frontCorrectionWord k₁ k₂ own₁ own₂ h₁ h₂ W).UsesOnly {P} ∧
      (frontCorrectionWord k₁ k₂ own₁ own₂ h₁ h₂ W).sourceCount = 0 := by
  have hloc : ‖isoL (pairUIso (T := T) (E := E) own₁ own₂).symm ∘L act W ∘L
      isoL (pairUIso own₁ own₂)‖ ≤ 1 :=
    (norm_comp_isoL_le _ _ _).trans ((norm_act W).le.trans hW)
  simp only [frontCorrectionWord, Word.IsAllowed, Word.UsesOnly, Word.sourceCount,
    Word.isAllowed_frameList_iff, Word.usesOnly_frameList_iff, Word.sourceCount_frameList,
    Word.IsReordering.isAllowed, Word.IsReordering.usesOnly, Word.IsReordering.sourceCount_eq,
    Word.isReordering_assocWord, Word.isReordering_unassocWord, Word.isReordering_exchangeBlocks,
    isReordering_partWordApp, isReordering_partWord, isReordering_unpartWordApp,
    isReordering_unpartWord, hloc, Set.mem_singleton_iff, and_self]

end Correction

end TNLean.Lattice.Sheet
