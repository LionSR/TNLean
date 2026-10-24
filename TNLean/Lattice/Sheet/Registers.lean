/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.SiteRegisters
import TNLean.Lattice.Sheet.Monomials

/-!
# Grouping the raw registers of a sheet

A sheet has one raw register `ℂ^q` at each site, with a specified owner for each register
(`05-frames.tex`, lines 13–20). This file places a monomial acting on two grouped registers on
the raw registers of a sheet, behind an arbitrary block of front registers. For disjoint `T` and
`E`, with `U = (T ∪ E)ᶜ`, `groupWord` moves the raw registers of `T` and of `U` in front by
exchanges of tensor factors and groups each block into one register `ℂ^{T → Fin q}`,
`ℂ^{U → Fin q}` by a private unitary at its owner; `ungroupWord` undoes this at the owners after
a change. If a map acts on the two grouped registers as `M ⊗ 1`, then grouping, applying it,
renaming the untouched owners and ungrouping maps the basis vector of a configuration `c` to
`∑_{ab} M_{ab, (c|_T, c|_U)} |merge ab c⟩` (`eval_place`).

The front registers are any block `k` identified with `ℂ^κ`; followed by the raw registers of the
sites, listed in a fixed order (`sites`), they are identified with `ℂ^{κ × (ι → Fin q)}`
(`frontLayoutIso`), and the placed monomial acts there as `1_κ ⊗ (1_E ⊗ M)`
(`frontLayoutIso_place`). For an encoded frame the front block is the tag registers of its
holes (`TNLean.PEPS.Approximation.FrameRegisters`); for a sheet without holes it is empty.
Nothing here depends on a geometry of the sites.

## Main definitions

* `Sheet.groupWord`, `Sheet.ungroupWord`: grouping the raw registers of two
  regions.
* `Sheet.merge`, `Sheet.relabelRest`.
* `Sheet.sites`, `Sheet.sitesEquiv`: the sites in a fixed order.
* `Sheet.frontLayoutIso`, `Sheet.frontLayoutVec`: front registers followed by the
  raw registers, in canonical coordinates, and their basis vectors.

## Main results

* `Sheet.eval_groupWord`, `Sheet.eval_ungroupWord`, `Sheet.groupWord_props`,
  `Sheet.ungroupWord_props`: grouping is an allowed word at the owners of the regions.
* `Sheet.eval_place`: a grouped monomial on basis vectors.
* `Sheet.frontLayoutIso_place`: a grouped monomial acts as `1_κ ⊗ (1_E ⊗ M)`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 13–20 (sheets), 94–96
  (canonical site and sheet coordinates with the owners of the registers specified separately);
  allowed monomials, `04-compression.tex`, lines 21–35.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Kronecker

namespace TNLean.Lattice.Sheet

open PartyCircuit ContinuousLinearMap EuclideanSpace

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
    (hf : ∀ z, pairHeadIso _ (f z) = (act M).rTensor _ (pairHeadIso _ z))
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
      (act M (EuclideanSpace.single ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) 1))]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, act_single_apply,
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
  simp only [act_apply_apply, PiLp.ofLp_single, Matrix.mulVec_single_one, WithLp.ofLp_sum,
    WithLp.ofLp_smul,
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

/-- The permutation matrix of a bijection `e` sends the basis vector `|i⟩` to `|e i⟩`. -/
theorem act_toMatrix_symm_single {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (i : α) :
    act (e.symm.toPEquiv.toMatrix : Matrix β α ℂ) (EuclideanSpace.single i (1 : ℂ)) =
      EuclideanSpace.single (e i) (1 : ℂ) := by
  ext j
  simp only [act_apply_apply, PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply,
    PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, PiLp.single_apply,
    Equiv.symm_apply_eq]

/-! ### Front registers followed by the raw registers -/

section FrontLayout

variable [Fintype ι] [DecidableEq ι]

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

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- **Front registers and raw registers in canonical coordinates.** A block `k` of registers,
identified with `ℂ^κ` by `i`, followed by one raw register `ℂ^q` per site, held by its owner
`own`, is identified with `ℂ^{κ × (ι → Fin q)}` by sending `x ⊗ ⊗_y |c y⟩` to `i x ⊗ |c⟩`
(`frontLayoutIso_frontLayoutVec`).

Polynomial-PEPS manuscript, `05-frames.tex`, lines 15–19 and 94–96. -/
def frontLayoutIso (k : Layout Party) (i : Mem k ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ) (own : ι → Party) :
    Mem (k ++ siteRegs q own (sites ι)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ × (ι → Fin q)) :=
  (appendIso _ _).trans (((i.rTensor _).trans
    ((groupIso own (sites ι) (sitesEquiv ι)).lTensor _)).trans (pairIso _ _))

/-- The basis vector `i⁻¹ |τ⟩ ⊗ |c⟩` of front registers followed by the raw registers. -/
def frontLayoutVec (k : Layout Party) (i : Mem k ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ) (own : ι → Party)
    (τ : κ) (c : ι → Fin q) : Mem (k ++ siteRegs q own (sites ι)) :=
  (appendIso _ _).symm (i.symm (EuclideanSpace.single τ (1 : ℂ)) ⊗ₜ siteVec own (sites ι) c)

/-- The canonical coordinates on basis vectors: `i⁻¹ |τ⟩ ⊗ ⊗_x |c x⟩ ↦ |τ, c⟩`. -/
theorem frontLayoutIso_frontLayoutVec (k : Layout Party) (i : Mem k ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (own : ι → Party) (τ : κ) (c : ι → Fin q) :
    frontLayoutIso k i own (frontLayoutVec k i own τ c) =
      EuclideanSpace.single (τ, c) (1 : ℂ) := by
  change pairIso κ (ι → Fin q) ((groupIso own (sites ι) (sitesEquiv ι)).lTensor _
    (i.rTensor _ (appendIso k (siteRegs q own (sites ι))
      ((appendIso k (siteRegs q own (sites ι))).symm
        (i.symm (EuclideanSpace.single τ (1 : ℂ)) ⊗ₜ siteVec own (sites ι) c))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul, LinearIsometryEquiv.apply_symm_apply,
    groupIso_siteVec own _ _ id (fun _ => rfl) c]
  exact pairIso_single_tmul_single τ c

/-- The basis vector `|τ, c⟩` read on front registers followed by the raw registers. -/
theorem frontLayoutIso_symm_single (k : Layout Party) (i : Mem k ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (own : ι → Party) (τ : κ) (c : ι → Fin q) :
    (frontLayoutIso k i own).symm (EuclideanSpace.single (τ, c) (1 : ℂ)) =
      frontLayoutVec k i own τ c := by
  rw [LinearIsometryEquiv.symm_apply_eq, frontLayoutIso_frontLayoutVec]

/-- **A monomial on two grouped regions, placed behind front registers.** If `f` acts on a
register `ℂ^{T → Fin q}` and a register `ℂ^{U → Fin q}`, `U = (T ∪ E)ᶜ`, in front of a block `k`
of registers and the raw registers of `E` as `M ⊗ 1`, then grouping the raw registers of `T` and
`U` at their owners before, applying `f`, and ungrouping at their owners after acts on `k`
followed by the raw registers, in canonical coordinates, as `1_κ ⊗ (1_E ⊗ M)`. -/
theorem frontLayoutIso_place {T E : Finset ι} (k : Layout Party)
    (i : Mem k ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ) (own own' : ι → Party)
    (h : Disjoint T E) {pA pB pA' pB' : Party}
    (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB)
    (hA' : ∀ x ∈ T, own' x = pA') (hB' : ∀ x ∈ (T ∪ E)ᶜ, own' x = pB')
    (hE : ∀ x ∈ E, own x = own' x)
    (f : Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (k ++ siteRegs q own (listE (sites ι) T E))) →L[ℂ]
      Mem (⟨pA', euc (T → Fin q)⟩ :: ⟨pB', euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (k ++ siteRegs q own (listE (sites ι) T E))))
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (hf : ∀ z, pairHeadIso _ (f z) = (act M).rTensor _ (pairHeadIso _ z))
    (z : Mem (k ++ siteRegs q own (sites ι))) :
    frontLayoutIso k i own' ((ungroupWord own' nodup_sites mem_sites k hA' hB').eval
        ((relabelRest own own' mem_sites h hE k _ _).eval
          (f ((groupWord own nodup_sites mem_sites k hA hB).eval z)))) =
      act ((1 : Matrix κ κ ℂ) ⊗ₖ sheetPlace h M) (frontLayoutIso k i own z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (frontLayoutIso k i own).symm y :=
    ⟨frontLayoutIso k i own z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  have hy : (frontLayoutIso k i own).symm y =
      ∑ j, y j • frontLayoutVec k i own j.1 j.2 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearIsometryEquiv.map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      frontLayoutIso_symm_single]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  rw [hy]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨τ, c⟩ := j
  rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    ← sum_single_merge, frontLayoutVec,
    eval_place own own' nodup_sites mem_sites h k hA hB hA' hB' hE f M hf, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [LinearIsometryEquiv.map_smul, ← frontLayoutVec, frontLayoutIso_frontLayoutVec]

end FrontLayout

end TNLean.Lattice.Sheet
