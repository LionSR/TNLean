/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SiteRegisters

/-!
# The registers of an encoded frame

A sheet has one raw register `ℂ^q` at each site, with a specified owner for each register, and
an encoded frame has in addition one tag register for each hole, held by a specified party
(`05-frames.tex`, lines 13–20 and Definition 6.1). This file lists these registers as a party
layout, one register per tag followed by one register per site (`layoutRegs`, `Frame.regs`),
and identifies their tensor product with the canonical coordinates `TagSpace × (Λ → Fin q)` in
which the encodings and the operators of the frame act (`layoutIso`, `Frame.regIso`): the basis
vector `|τ⟩ ⊗ ⊗_x |c x⟩` goes to `|τ, c⟩` (`layoutIso_layoutVec`).

It then places a monomial acting on two grouped registers on this layout. For disjoint `T`
and `E`, with `U = (T ∪ E)ᶜ`, `groupWord` moves the raw registers of `T` and of `U` in front by
exchanges of tensor factors and groups each block into one register `ℂ^{T → Fin q}`,
`ℂ^{U → Fin q}` by a private unitary at its owner; `ungroupWord` undoes this at the owners after
a change. If a map acts on the two grouped registers as `M ⊗ 1`, then grouping, applying it,
renaming the untouched owners and ungrouping acts on the registers of the frame, in canonical
coordinates, as `1_tags ⊗ (1_E ⊗ M)` (`layoutIso_place`).

## Main definitions

* `EncodedFrame.groupWord`, `EncodedFrame.ungroupWord`: grouping the raw registers of two
  regions.
* `EncodedFrame.sites`, `EncodedFrame.layoutRegs`, `EncodedFrame.layoutVec`,
  `EncodedFrame.layoutIso`: the registers of a frame and their canonical coordinates.
* `EncodedFrame.Frame.regs`, `EncodedFrame.Frame.regIso`.

## Main results

* `EncodedFrame.eval_groupWord`, `EncodedFrame.eval_ungroupWord`, `EncodedFrame.groupWord_props`,
  `EncodedFrame.ungroupWord_props`: grouping is an allowed word at the owners of the regions.
* `EncodedFrame.layoutIso_layoutVec`: the identification on basis vectors.
* `EncodedFrame.layoutIso_place`: a grouped monomial acts on the frame as `1_tags ⊗ (1_E ⊗ M)`.
* `EncodedFrame.Frame.map_owner_regs`: one register per tag and per site, each held by its
  owner.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 13–20 (sheets), 71–82
  (Definition 6.1 `def:frame`), 94–96 (canonical site and sheet coordinates with the owners of
  the registers specified separately); allowed monomials, `04-compression.tex`, lines 21–35.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Kronecker

namespace TNLean.PEPS.EncodedFrame

open PairEffect ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### Grouping the raw registers of two regions -/

section Group

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem owner_siteRegs {own : ι → Party} {S : List ι} {p : Party} (h : ∀ x ∈ S, own x = p) :
    ∀ r ∈ siteRegs q own S, r.owner = p := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact h x hx

/-- The sites of the list `S` in `T`, in their order in `S`. -/
abbrev listT (S : List ι) (T : Finset ι) : List ι := (partSites (fun x => decide (x ∈ T)) S).1

/-- The sites of the list `S` outside `T`. -/
abbrev listR (S : List ι) (T : Finset ι) : List ι := (partSites (fun x => decide (x ∈ T)) S).2

/-- The sites of the list `S` in `U = (T ∪ E)ᶜ`. -/
abbrev listU (S : List ι) (T E : Finset ι) : List ι :=
  (partSites (fun x => decide (x ∈ (T ∪ E)ᶜ)) (listR S T)).1

/-- The sites of the list `S` in `E`, when `T` and `E` are disjoint. -/
abbrev listE (S : List ι) (T E : Finset ι) : List ι :=
  (partSites (fun x => decide (x ∈ (T ∪ E)ᶜ)) (listR S T)).2

variable {S : List ι} {T E : Finset ι}

omit [Fintype ι] in
theorem mem_listT (hall : ∀ x, x ∈ S) (x : ι) : x ∈ listT S T ↔ x ∈ T := by
  simp [mem_partSites_fst, hall]

omit [Fintype ι] in
theorem mem_listR (hall : ∀ x, x ∈ S) (x : ι) : x ∈ listR S T ↔ x ∉ T := by
  simp [mem_partSites_snd, hall]

theorem mem_listU (hall : ∀ x, x ∈ S) (x : ι) : x ∈ listU S T E ↔ x ∈ (T ∪ E)ᶜ := by
  simp only [mem_partSites_fst, mem_partSites_snd, hall, true_and, decide_eq_true_eq,
    decide_eq_false_iff_not, Finset.mem_compl, Finset.mem_union]
  tauto

theorem mem_listE (hall : ∀ x, x ∈ S) (h : Disjoint T E) (x : ι) : x ∈ listE S T E ↔ x ∈ E := by
  simp only [mem_partSites_snd, hall, true_and, decide_eq_false_iff_not, Finset.mem_compl,
    Finset.mem_union, not_not]
  constructor
  · rintro ⟨hT, hTE | hE⟩
    · exact absurd hTE hT
    · exact hE
  · intro hE
    exact ⟨Finset.disjoint_right.mp h hE, Or.inr hE⟩

omit [Fintype ι] in
theorem nodup_listT (hS : S.Nodup) : (listT S T).Nodup := nodup_partSites_fst _ hS

theorem nodup_listU (hS : S.Nodup) : (listU S T E).Nodup :=
  nodup_partSites_fst _ (nodup_partSites_snd _ hS)

/-- The positions of `listT S T` enumerate `T`. -/
def equivT (hS : S.Nodup) (hall : ∀ x, x ∈ S) : Fin (listT S T).length ≃ T :=
  (List.Nodup.getEquiv _ (nodup_listT hS)).trans (Equiv.subtypeEquivRight (mem_listT hall))

/-- The positions of `listU S T E` enumerate `U = (T ∪ E)ᶜ`. -/
def equivU (hS : S.Nodup) (hall : ∀ x, x ∈ S) : Fin (listU S T E).length ≃ ↥(T ∪ E)ᶜ :=
  (List.Nodup.getEquiv _ (nodup_listU hS)).trans (Equiv.subtypeEquivRight (mem_listU hall))

omit [Fintype ι] in
theorem groupIso_listT_siteVec (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (c : ι → Fin q) :
    groupIso own (listT S T) (equivT hS hall) (siteVec own (listT S T) c) =
      EuclideanSpace.single (fun x : T => c x) (1 : ℂ) :=
  groupIso_siteVec own _ _ Subtype.val (fun _ => rfl) c

theorem groupIso_listU_siteVec (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (c : ι → Fin q) :
    groupIso own (listU S T E) (equivU hS hall) (siteVec own (listU S T E) c) =
      EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ) :=
  groupIso_siteVec own _ _ Subtype.val (fun _ => rfl) c

/-- **Grouping two regions.** The raw registers of `T`, held by `pA`, and those of
`U = (T ∪ E)ᶜ`, held by `pB`, moved to the front by exchanges of tensor factors and grouped into
one register `ℂ^{T → Fin q}` and one register `ℂ^{U → Fin q}` by a private unitary at their
owner. The registers `ℓ₀` in front and the raw registers of `E` are untouched. -/
def groupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S) (ℓ₀ : Layout Party)
    {pA pB : Party} (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) :
    Word (ℓ₀ ++ siteRegs q own S)
      (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (ℓ₀ ++ siteRegs q own (listE S T E))) :=
  .comp (Word.frameList ℓ₀ (partWord own _ S)) <|
  .comp (Word.frameList ℓ₀ (Word.frameList (siteRegs q own (listT S T))
    (partWord own (fun x => decide (x ∈ (T ∪ E)ᶜ)) (listR S T)))) <|
  .comp (Word.exchangeBlocks ℓ₀ (siteRegs q own (listT S T))
    (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E))) <|
  .comp (Word.localMap pA (ℓ₁ := siteRegs q own (listT S T)) (ℓ₂ := [⟨pA, euc (T → Fin q)⟩])
    (owner_siteRegs fun x hx => hA x ((mem_listT hall x).mp hx)) owner_of_mem_one
    (isoL ((groupIso own _ (equivT hS hall)).trans (oneIso pA _).symm))
    (ℓ₀ ++ (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E)))) <|
  .comp (.frame _ (Word.exchangeBlocks ℓ₀ (siteRegs q own (listU S T E))
    (siteRegs q own (listE S T E)))) <|
  .frame _ (Word.localMap pB (ℓ₁ := siteRegs q own (listU S T E))
    (ℓ₂ := [⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩])
    (owner_siteRegs fun x hx => hB x ((mem_listU hall x).mp hx)) owner_of_mem_one
    (isoL ((groupIso own _ (equivU hS hall)).trans (oneIso pB _).symm))
    (ℓ₀ ++ siteRegs q own (listE S T E)))

/-- **Ungrouping two regions**, the inverse of `groupWord` for the owners `own`. -/
def ungroupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S) (ℓ₀ : Layout Party)
    {pA pB : Party} (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) :
    Word (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (ℓ₀ ++ siteRegs q own (listE S T E)))
      (ℓ₀ ++ siteRegs q own S) :=
  .comp (.frame _ (Word.localMap pB (ℓ₁ := [⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩])
    (ℓ₂ := siteRegs q own (listU S T E)) owner_of_mem_one
    (owner_siteRegs fun x hx => hB x ((mem_listU hall x).mp hx))
    (isoL ((oneIso pB _).trans (groupIso own _ (equivU hS hall)).symm))
    (ℓ₀ ++ siteRegs q own (listE S T E)))) <|
  .comp (.frame _ (Word.exchangeBlocks (siteRegs q own (listU S T E)) ℓ₀
    (siteRegs q own (listE S T E)))) <|
  .comp (Word.localMap pA (ℓ₁ := [⟨pA, euc (T → Fin q)⟩]) (ℓ₂ := siteRegs q own (listT S T))
    owner_of_mem_one (owner_siteRegs fun x hx => hA x ((mem_listT hall x).mp hx))
    (isoL ((oneIso pA _).trans (groupIso own _ (equivT hS hall)).symm))
    (ℓ₀ ++ (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E)))) <|
  .comp (Word.exchangeBlocks (siteRegs q own (listT S T)) ℓ₀
    (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E))) <|
  .comp (Word.frameList ℓ₀ (Word.frameList (siteRegs q own (listT S T))
    (unpartWord own (fun x => decide (x ∈ (T ∪ E)ᶜ)) (listR S T)))) <|
  Word.frameList ℓ₀ (unpartWord own _ S)

/-- **Grouping on basis vectors.** The basis vector of a configuration `c` is sent to
`|c|_T⟩ ⊗ |c|_U⟩` in front of the untouched registers. -/
theorem eval_groupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) (t : Mem ℓ₀) (c : ι → Fin q) :
    (groupWord own hS hall ℓ₀ hA hB).eval ((appendIso ℓ₀ _).symm (t ⊗ₜ siteVec own S c)) =
      ((EuclideanSpace.single (fun x : T => c x) (1 : ℂ) : EuclideanSpace ℂ (T → Fin q)) ⊗ₜ
        ((EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ) :
            EuclideanSpace ℂ (↥(T ∪ E)ᶜ → Fin q)) ⊗ₜ
          (appendIso ℓ₀ (siteRegs q own (listE S T E))).symm
            (t ⊗ₜ siteVec own (listE S T E) c)) :
        Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
          (ℓ₀ ++ siteRegs q own (listE S T E)))) := by
  simp only [groupWord, Word.eval_comp, ContinuousLinearMap.comp_apply]
  rw [Word.eval_frameList_appendIso_symm, eval_partWord, Word.eval_frameList_appendIso_symm,
    Word.eval_frameList_appendIso_symm, eval_partWord, Word.eval_exchangeBlocks_appendIso_symm,
    eval_localMap, isoL_apply, LinearIsometryEquiv.trans_apply, groupIso_listT_siteVec,
    appendIso_one_symm, Word.eval_frame, Word.eval_frame, lTensor_tmul,
    Word.eval_exchangeBlocks_appendIso_symm, lTensor_tmul, eval_localMap, isoL_apply,
    LinearIsometryEquiv.trans_apply, groupIso_listU_siteVec, appendIso_one_symm]

/-- **Ungrouping on basis vectors**, the inverse of `eval_groupWord`. -/
theorem eval_ungroupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) (t : Mem ℓ₀) (c : ι → Fin q) :
    (ungroupWord own hS hall ℓ₀ hA hB).eval
        ((EuclideanSpace.single (fun x : T => c x) (1 : ℂ) : EuclideanSpace ℂ (T → Fin q)) ⊗ₜ
          ((EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ) :
              EuclideanSpace ℂ (↥(T ∪ E)ᶜ → Fin q)) ⊗ₜ
            (appendIso ℓ₀ (siteRegs q own (listE S T E))).symm
              (t ⊗ₜ siteVec own (listE S T E) c)) :
          Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
            (ℓ₀ ++ siteRegs q own (listE S T E)))) =
      (appendIso ℓ₀ _).symm (t ⊗ₜ siteVec own S c) := by
  simp only [ungroupWord, Word.eval_comp, ContinuousLinearMap.comp_apply]
  rw [Word.eval_frame, Word.eval_frame, lTensor_tmul,
    ← appendIso_one_symm pB (ℓ₀ ++ siteRegs q own (listE S T E))
      (EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ)),
    eval_localMap, isoL_apply, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, ← groupIso_listU_siteVec own hS hall c,
    LinearIsometryEquiv.symm_apply_apply, lTensor_tmul, Word.eval_exchangeBlocks_appendIso_symm,
    ← appendIso_one_symm pA
      (ℓ₀ ++ (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E)))
      (EuclideanSpace.single (fun x : T => c x) (1 : ℂ)),
    eval_localMap, isoL_apply, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, ← groupIso_listT_siteVec own hS hall c,
    LinearIsometryEquiv.symm_apply_apply, Word.eval_exchangeBlocks_appendIso_symm,
    Word.eval_frameList_appendIso_symm, Word.eval_frameList_appendIso_symm,
    Word.eval_frameList_appendIso_symm, eval_unpartWord, eval_unpartWord]

/-- Grouping is an allowed word using only the owners of the two regions, without pair
sources. -/
theorem groupWord_props (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) {V : Set Party} (hpA : pA ∈ V) (hpB : pB ∈ V) :
    (groupWord (q := q) own hS hall ℓ₀ hA hB).IsAllowed ∧
      (groupWord (q := q) own hS hall ℓ₀ hA hB).UsesOnly V ∧
      (groupWord (q := q) own hS hall ℓ₀ hA hB).sourceCount = 0 := by
  have a := (isReordering_partWord (q := q) own (fun x => decide (x ∈ T)) S).frameList ℓ₀
  have b := ((isReordering_partWord (q := q) own (fun x => decide (x ∈ (T ∪ E)ᶜ))
    (listR S T)).frameList (siteRegs q own (listT S T))).frameList ℓ₀
  have e₁ := Word.isReordering_exchangeBlocks ℓ₀ (siteRegs q own (listT S T))
    (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E))
  have e₂ := Word.isReordering_exchangeBlocks ℓ₀ (siteRegs q own (listU S T E))
    (siteRegs q own (listE S T E))
  refine ⟨⟨a.isAllowed, b.isAllowed, e₁.isAllowed, LinearIsometry.norm_toContinuousLinearMap_le _,
      e₂.isAllowed, LinearIsometry.norm_toContinuousLinearMap_le _⟩,
    ⟨a.usesOnly V, b.usesOnly V, e₁.usesOnly V, hpA, e₂.usesOnly V, hpB⟩, ?_⟩
  simp only [groupWord, Word.sourceCount, a.sourceCount_eq, b.sourceCount_eq, e₁.sourceCount_eq,
    e₂.sourceCount_eq]

/-- Ungrouping is an allowed word using only the owners of the two regions, without pair
sources. -/
theorem ungroupWord_props (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) {V : Set Party} (hpA : pA ∈ V) (hpB : pB ∈ V) :
    (ungroupWord (q := q) own hS hall ℓ₀ hA hB).IsAllowed ∧
      (ungroupWord (q := q) own hS hall ℓ₀ hA hB).UsesOnly V ∧
      (ungroupWord (q := q) own hS hall ℓ₀ hA hB).sourceCount = 0 := by
  have a := (isReordering_unpartWord (q := q) own (fun x => decide (x ∈ T)) S).frameList ℓ₀
  have b := ((isReordering_unpartWord (q := q) own (fun x => decide (x ∈ (T ∪ E)ᶜ))
    (listR S T)).frameList (siteRegs q own (listT S T))).frameList ℓ₀
  have e₁ := Word.isReordering_exchangeBlocks (siteRegs q own (listU S T E)) ℓ₀
    (siteRegs q own (listE S T E))
  have e₂ := Word.isReordering_exchangeBlocks (siteRegs q own (listT S T)) ℓ₀
    (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E))
  refine ⟨⟨LinearIsometry.norm_toContinuousLinearMap_le _, e₁.isAllowed,
      LinearIsometry.norm_toContinuousLinearMap_le _, e₂.isAllowed, b.isAllowed, a.isAllowed⟩,
    ⟨hpB, e₁.usesOnly V, hpA, e₂.usesOnly V, b.usesOnly V, a.usesOnly V⟩, ?_⟩
  simp only [ungroupWord, Word.sourceCount, a.sourceCount_eq, b.sourceCount_eq, e₁.sourceCount_eq,
    e₂.sourceCount_eq]

end Group

/-! ### A monomial on two grouped registers, placed on the raw registers -/

section Placement

variable [Fintype ι] [DecidableEq ι] {S : List ι} {T E : Finset ι}

/-- The configuration equal to `ab.1` on `T`, to `c` on `E`, and to `ab.2` on `(T ∪ E)ᶜ`. -/
def merge (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) (c : ι → Fin q) :
    ι → Fin q :=
  (threeSplit q T E h).symm ((ab.1, fun x : E => c x), ab.2)

theorem merge_restrict_T (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
    (c : ι → Fin q) : (fun x : T => merge h ab c x) = ab.1 :=
  funext fun x => threeSplit_symm_apply_of_mem_left h _ _ _ x.2

theorem merge_restrict_U (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
    (c : ι → Fin q) : (fun x : ↥(T ∪ E)ᶜ => merge h ab c x) = ab.2 :=
  funext fun x => threeSplit_symm_apply_of_notMem h _ _ _ (Finset.mem_compl.mp x.2)

theorem merge_of_mem_E (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
    (c : ι → Fin q) {x : ι} (hx : x ∈ E) : merge h ab c x = c x :=
  threeSplit_symm_apply_of_mem_right h _ _ _ hx

/-- The raw registers of `E`, held by the owners `own` before the change, named with the owners
`own'` after it; the two agree on `E`. -/
def relabelRest (own own' : ι → Party) (hall : ∀ x, x ∈ S) (h : Disjoint T E)
    (hE : ∀ x ∈ E, own x = own' x) (ℓ₀ : Layout Party) (rA rB : Reg Party) :
    Word (rA :: rB :: (ℓ₀ ++ siteRegs q own (listE S T E)))
      (rA :: rB :: (ℓ₀ ++ siteRegs q own' (listE S T E))) :=
  .frame rA (.frame rB (Word.frameList ℓ₀ (relabelSites own own' (listE S T E)
    fun x hx => hE x ((mem_listE hall h x).mp hx))))

theorem isReordering_relabelRest (own own' : ι → Party) (hall : ∀ x, x ∈ S) (h : Disjoint T E)
    (hE : ∀ x ∈ E, own x = own' x) (ℓ₀ : Layout Party) (rA rB : Reg Party) :
    (relabelRest (q := q) own own' hall h hE ℓ₀ rA rB).IsReordering := by
  simp [relabelRest]

/-- **A monomial on grouped registers, read on the raw registers.** Let `f` act on a register
`ℂ^{T → Fin q}` and a register `ℂ^{U → Fin q}`, `U = (T ∪ E)ᶜ`, in front of untouched
registers, as `M ⊗ 1`. Grouping the raw registers of `T` and `U` (at their owners before),
applying `f`, and ungrouping them (at their owners after) maps the basis vector of a raw
configuration `c` to `∑_{ab} M_{ab, (c|_T, c|_U)} |merge ab c⟩`, with every register of `E`
and every register in front untouched. -/
theorem eval_place (own own' : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (h : Disjoint T E) (ℓ₀ : Layout Party) {pA pB pA' pB' : Party}
    (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB)
    (hA' : ∀ x ∈ T, own' x = pA') (hB' : ∀ x ∈ (T ∪ E)ᶜ, own' x = pB')
    (hE : ∀ x ∈ E, own x = own' x)
    (f : Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (ℓ₀ ++ siteRegs q own (listE S T E))) →L[ℂ]
      Mem (⟨pA', euc (T → Fin q)⟩ :: ⟨pB', euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (ℓ₀ ++ siteRegs q own (listE S T E))))
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (hf : ∀ z, pairHeadIso _ (f z) = (matL M).rTensor _ (pairHeadIso _ z))
    (t : Mem ℓ₀) (c : ι → Fin q) :
    (ungroupWord own' hS hall ℓ₀ hA' hB').eval
        ((relabelRest own own' hall h hE ℓ₀ _ _).eval
          (f ((groupWord own hS hall ℓ₀ hA hB).eval
            ((appendIso ℓ₀ _).symm (t ⊗ₜ siteVec own S c))))) =
      ∑ ab, M ab ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) •
        (appendIso ℓ₀ _).symm (t ⊗ₜ siteVec own' S (merge h ab c)) := by
  rw [eval_groupWord]
  set R₀ := (appendIso ℓ₀ (siteRegs q own (listE S T E))).symm
    (t ⊗ₜ siteVec own (listE S T E) c)
  have hz : f ((EuclideanSpace.single (fun x : T => c x) (1 : ℂ) :
        EuclideanSpace ℂ (T → Fin q)) ⊗ₜ
      ((EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ) :
        EuclideanSpace ℂ (↥(T ∪ E)ᶜ → Fin q)) ⊗ₜ R₀)) =
      ∑ ab, M ab ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) •
        ((EuclideanSpace.single ab.1 (1 : ℂ) : EuclideanSpace ℂ (T → Fin q)) ⊗ₜ
          ((EuclideanSpace.single ab.2 (1 : ℂ) : EuclideanSpace ℂ (↥(T ∪ E)ᶜ → Fin q)) ⊗ₜ
            R₀) : Mem (⟨pA', euc (T → Fin q)⟩ :: ⟨pB', euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
              (ℓ₀ ++ siteRegs q own (listE S T E)))) := by
    apply (pairHeadIso (p := pA') (q := pB') (α := T → Fin q) (β := ↥(T ∪ E)ᶜ → Fin q)
      (ℓ₀ ++ siteRegs q own (listE S T E))).injective
    rw [hf, pairHeadIso_tmul, pairIso_single_tmul_single, rTensor_tmul, map_sum]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun ab _ => by
      rw [LinearIsometryEquiv.map_smul, pairHeadIso_tmul, pairIso_single_tmul_single])
    conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr
      (matL M (EuclideanSpace.single ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) 1))]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, matL_single_apply,
      TensorProduct.smul_tmul']
  rw [hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [map_smul, map_smul]
  congr 1
  rw [relabelRest, Word.eval_frame, lTensor_tmul, Word.eval_frame, lTensor_tmul,
    Word.eval_frameList_appendIso_symm, eval_relabelSites, ← merge_restrict_T h ab c,
    ← merge_restrict_U h ab c, siteVec_congr own' (listE S T E) (c' := merge h ab c)
      fun x hx => (merge_of_mem_E h ab c ((mem_listE hall h x).mp hx)).symm]
  exact eval_ungroupWord own' hS hall ℓ₀ hA' hB' t (merge h ab c)

theorem merge_eq_iff (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
    (c c' : ι → Fin q) : c' = merge h ab c ↔
      ab = ((fun x : T => c' x), (fun x : ↥(T ∪ E)ᶜ => c' x)) ∧
        (fun x : E => c' x) = (fun x : E => c x) := by
  constructor
  · rintro rfl
    refine ⟨Prod.ext (merge_restrict_T h ab c).symm (merge_restrict_U h ab c).symm, ?_⟩
    funext x
    exact merge_of_mem_E h ab c x.2
  · rintro ⟨rfl, hE⟩
    funext x
    by_cases hT : x ∈ T
    · rw [merge, threeSplit_symm_apply_of_mem_left h _ _ _ hT]
    · by_cases hx : x ∈ E
      · rw [merge, threeSplit_symm_apply_of_mem_right h _ _ _ hx]
        exact congrFun hE ⟨x, hx⟩
      · rw [merge, threeSplit_symm_apply_of_notMem h _ _ _ (by simp [hT, hx])]

/-- The coordinates of the placed monomial: `∑_{ab} M_{ab, (c|_T, c|_U)} |τ, merge ab c⟩` is the
column `(τ, c)` of `1_tags ⊗ (1_E ⊗ M)`. -/
theorem sum_single_merge {κ : Type} [Fintype κ] [DecidableEq κ] (h : Disjoint T E)
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (τ : κ) (c : ι → Fin q) :
    ∑ ab, M ab ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) •
        (EuclideanSpace.single (τ, merge h ab c) (1 : ℂ) : EuclideanSpace ℂ (κ × (ι → Fin q))) =
      act ((1 : Matrix κ κ ℂ) ⊗ₖ sheetPlace h M) (EuclideanSpace.single (τ, c) (1 : ℂ)) := by
  ext ⟨τ', c'⟩
  simp only [PiLp.ofLp_single, Matrix.mulVec_single_one, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, sheetPlace_apply]
  have key : ∀ ab, (Pi.single (τ, merge h ab c) (1 : ℂ) : κ × (ι → Fin q) → ℂ) (τ', c') =
      if ab = ((fun x : T => c' x), (fun x : ↥(T ∪ E)ᶜ => c' x)) then
        (if τ' = τ then 1 else 0) *
          (if (fun x : E => c' x) = (fun x : E => c x) then 1 else 0) else 0 := by
    intro ab
    rw [Pi.single_apply]
    simp only [Prod.mk.injEq, merge_eq_iff]
    by_cases h₁ : τ' = τ <;>
      by_cases h₂ : ab = ((fun x : T => c' x), (fun x : ↥(T ∪ E)ᶜ => c' x)) <;>
      by_cases h₃ : (fun x : E => c' x) = (fun x : E => c x) <;> simp [h₁, h₂, h₃]
  simp_rw [key, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> ring

end Placement

/-! ### Matrix actions on Euclidean registers -/

/-- The two matrix actions `act` and `matL` on Euclidean vectors agree. -/
theorem act_eq_matL {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ)
    (ψ : EuclideanSpace ℂ n) : act A ψ = matL A ψ :=
  rfl

/-- The permutation matrix of a bijection `e` sends the basis vector `|i⟩` to `|e i⟩`. -/
theorem act_toMatrix_symm_single {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (i : α) :
    act (e.symm.toPEquiv.toMatrix : Matrix β α ℂ) (EuclideanSpace.single i (1 : ℂ)) =
      EuclideanSpace.single (e i) (1 : ℂ) := by
  ext j
  simp only [PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, PiLp.single_apply,
    Equiv.symm_apply_eq]

/-! ### The registers of an encoded frame -/

section FrameLayout

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

variable (ι) in
/-- The sites of the lattice, listed in a fixed order. The order only fixes the order of the
tensor factors. -/
def sites : List ι := (Finset.univ : Finset ι).toList

omit [DecidableEq ι] in
theorem nodup_sites : (sites ι).Nodup := Finset.nodup_toList _

omit [DecidableEq ι] in
theorem mem_sites (x : ι) : x ∈ sites ι := Finset.mem_toList.mpr (Finset.mem_univ x)

attribute [irreducible] sites

variable (ι) in
/-- The positions of `sites ι` enumerate the sites. -/
def sitesEquiv : Fin (sites ι).length ≃ ι :=
  List.Nodup.getEquivOfForallMemList _ nodup_sites mem_sites

variable (q) in
/-- **The registers of a frame.** One register `ℂ^{Tag}` per hole of `l`, held by its tag owner,
followed by one raw register `ℂ^q` per site, held by its owner `own`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 13–20 (a sheet has one raw register `ℂ^q` at
each site and a specified owner for each register) and Definition 6.1 `def:frame`, lines 71–82
(a specified party holds each hole's tag). -/
abbrev layoutRegs (l : List (Hole pos q Party)) (own : ι → Party) : Layout Party :=
  tagRegs l ++ siteRegs q own (sites ι)

/-- The basis vector `|τ⟩ ⊗ |c⟩` of the registers of a frame. -/
def layoutVec (l : List (Hole pos q Party)) (own : ι → Party) (τ : TagSpace l)
    (c : ι → Fin q) : Mem (layoutRegs q l own) :=
  (appendIso _ _).symm (tagVec l τ ⊗ₜ siteVec own (sites ι) c)

/-- **The registers of a frame in canonical coordinates.** The tensor product of the registers
of a frame is identified with `ℂ^{TagSpace l × (ι → Fin q)}`, the space on which the encoding
`K_F` and the operators of the frame act, by sending `|τ⟩ ⊗ ⊗_x |c x⟩` to `|τ, c⟩`
(`layoutIso_layoutVec`).

Polynomial-PEPS manuscript, `05-frames.tex`, lines 15–19 (canonical raw reference vectors with
sites indexed by position) and 94–96 (vectors are compared in their canonical site and sheet
coordinates while the owners of their registers are specified separately). -/
def layoutIso (l : List (Hole pos q Party)) (own : ι → Party) :
    Mem (layoutRegs q l own) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (TagSpace l × (ι → Fin q)) :=
  (appendIso _ _).trans ((((tagIso l).rTensor _).trans
    ((groupIso own (sites ι) (sitesEquiv ι)).lTensor _)).trans (pairIso _ _))

/-- The canonical coordinates on basis vectors: `|τ⟩ ⊗ ⊗_x |c x⟩ ↦ |τ, c⟩`. -/
theorem layoutIso_layoutVec (l : List (Hole pos q Party)) (own : ι → Party) (τ : TagSpace l)
    (c : ι → Fin q) :
    layoutIso l own (layoutVec l own τ c) = EuclideanSpace.single (τ, c) (1 : ℂ) := by
  change pairIso (TagSpace l) (ι → Fin q) ((groupIso own (sites ι) (sitesEquiv ι)).lTensor _
    ((tagIso l).rTensor _ (appendIso (tagRegs l) (siteRegs q own (sites ι))
      ((appendIso (tagRegs l) (siteRegs q own (sites ι))).symm
        (tagVec l τ ⊗ₜ siteVec own (sites ι) c))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul, tagIso_tagVec,
    groupIso_siteVec own _ _ id (fun _ => rfl) c]
  exact pairIso_single_tmul_single τ c

/-- The basis vector `|τ, c⟩` read on the registers of a frame. -/
theorem layoutIso_symm_single (l : List (Hole pos q Party)) (own : ι → Party) (τ : TagSpace l)
    (c : ι → Fin q) :
    (layoutIso l own).symm (EuclideanSpace.single (τ, c) (1 : ℂ)) = layoutVec l own τ c := by
  rw [LinearIsometryEquiv.symm_apply_eq, layoutIso_layoutVec]

/-- **A monomial on two grouped regions, placed on the registers of a frame.** If `f` acts on a
register `ℂ^{T → Fin q}` and a register `ℂ^{U → Fin q}`, `U = (T ∪ E)ᶜ`, in front of the tag
registers and the raw registers of `E` as `M ⊗ 1`, then grouping the raw registers of `T` and
`U` at their owners before, applying `f`, and ungrouping at their owners after acts on the
registers of the frame, in canonical coordinates, as `1_tags ⊗ (1_E ⊗ M)`. -/
theorem layoutIso_place {T E : Finset ι} (l : List (Hole pos q Party)) (own own' : ι → Party)
    (h : Disjoint T E) {pA pB pA' pB' : Party}
    (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB)
    (hA' : ∀ x ∈ T, own' x = pA') (hB' : ∀ x ∈ (T ∪ E)ᶜ, own' x = pB')
    (hE : ∀ x ∈ E, own x = own' x)
    (f : Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (tagRegs l ++ siteRegs q own (listE (sites ι) T E))) →L[ℂ]
      Mem (⟨pA', euc (T → Fin q)⟩ :: ⟨pB', euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (tagRegs l ++ siteRegs q own (listE (sites ι) T E))))
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (hf : ∀ z, pairHeadIso _ (f z) = (matL M).rTensor _ (pairHeadIso _ z))
    (z : Mem (layoutRegs q l own)) :
    layoutIso l own' ((ungroupWord own' nodup_sites mem_sites (tagRegs l) hA' hB').eval
        ((relabelRest own own' mem_sites h hE (tagRegs l) _ _).eval
          (f ((groupWord own nodup_sites mem_sites (tagRegs l) hA hB).eval z)))) =
      act ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ sheetPlace h M) (layoutIso l own z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (layoutIso l own).symm y := ⟨layoutIso l own z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply, act_eq_matL]
  have hy : (layoutIso l own).symm y =
      ∑ i, y i • layoutVec l own i.1 i.2 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearIsometryEquiv.map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      layoutIso_symm_single]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  rw [hy]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨τ, c⟩ := i
  rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, ← act_eq_matL,
    ← sum_single_merge, layoutVec,
    eval_place own own' nodup_sites mem_sites h (tagRegs l) hA hB hA' hB' hE f M hf, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [LinearIsometryEquiv.map_smul, ← layoutVec, layoutIso_layoutVec]

end FrameLayout

section FrameRegs

variable [Fintype ι] [DecidableEq ι]

namespace Frame

variable {pos : ι → ℝ × ℝ} (F : Frame pos q Party)

/-- **The registers of an encoded frame**: one register per tag, held by the tag owner, and one
raw register `ℂ^q` per site, held by the raw owner.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 13–20 and Definition 6.1 `def:frame`,
lines 71–82. -/
abbrev regs : PairEffect.Layout Party := layoutRegs q F.holes F.owner

/-- The registers of a frame identified with the canonical coordinates `F.Layout` of its tags and
raw sites (`05-frames.tex`, lines 94–96). -/
abbrev regIso : Mem F.regs ≃ₗᵢ[ℂ] EuclideanSpace ℂ F.Layout := layoutIso F.holes F.owner

theorem map_owner_regs : F.regs.map Reg.owner =
    F.holes.map Hole.tagOwner ++ (sites ι).map F.owner := by
  simp only [List.map_append, siteRegs, List.map_map]
  congr 1
  induction F.holes with
  | nil => rfl
  | cons h l ih => simp only [tagRegs, List.map_cons, ih]

end Frame

end FrameRegs

end TNLean.PEPS.EncodedFrame
