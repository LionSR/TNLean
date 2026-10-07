/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapCorrection

/-!
# Exchanging assignments between two sheets

Lemma 6.6 of the polynomial-PEPS manuscript exchanges, inside a plane region `Y`, the raw
ownership assignments and the encoded holes (with their tag owners) of two encoded frames. Every
hole's outer square lies on one side of `∂Y`. With a party `P∘`,
`Z = {x : the two old raw owners of x are not both P∘} ∪ H⁺(F₁) ∪ H⁺(F₂)`, `T = Z ∩ Y`,
`E = Z ∖ Y` and `U = Λ ∖ Z`, if `I_Ω(T:E) ≤ L^{-60}` the exchange is implemented by a register
renaming `ℛ` followed by the private swap `F_A` of the two sheets at `A = Y ∩ U` and the private
buffer correction `D_U = (V^{⊗2})ᴴ F_{B_T} V^{⊗2}` on the two copies of `U`, with reference
error at most `4 L^{-30}`.

The swaps `F_S` of the two sheets and the buffer correction `D_U` are constructed in
`TNLean.PEPS.Approximation.SheetSwapCorrection`.

## Main definitions

* `EncodedFrame.TwoSheetExchange`: two frames whose holes are listed as the holes outside `Y`
  followed by the holes inside `Y`, and the exchanged frames.
* `EncodedFrame.TwoSheetExchange.rename`: the renaming `ℛ`.
* `EncodedFrame.TwoSheetExchange.exchangeOp`: the implemented map `C = D_U F_A ℛ`.
* `EncodedFrame.TwoSheetExchange.ofFrames`, `EncodedFrame.TwoSheetExchange.tagReorder`: exchange
  data of two frames whose holes are listed in any order, and the relabelling of tags that
  regroups them.

## Main results

* `EncodedFrame.TwoSheetExchange.rename_mul_encoder`: `ℛ K_in = K_out F_{Y ∩ Λ}`
  (`eq:exchange-intertwining`).
* `EncodedFrame.TwoSheetExchange.exchangeOp_mul_encoder`: `C K_in = K_out D_U F_T`
  (`eq:exchange-exact-map`).
* `EncodedFrame.TwoSheetExchange.exchange`,
  `EncodedFrame.TwoSheetExchange.exchange_ofFrames`: Lemma 6.6 `lem:exchange` for the map
  `C = D_U F_A ℛ`, for the grouped hole lists, and for hole lists in any order after the
  relabelling of tags.

## Scope

**Scope restriction (monomial structure):** Lemma 6.6 asserts that the exchange is implemented
by private contractions and register renaming, using `P∘` and the owners of the renamed registers
and tags, and is therefore a bounded change in the sense of Theorem 5.2. Here `C = D_U F_A ℛ` is
constructed, `D_U` and `F_A` act on the raw registers of `U` alone, which `P∘` holds on both
sheets before and after the exchange, and `ℛ` keeps every register at its party. Reading this as
an allowed monomial of Theorem 5.2 needs a model of operators placed on parties, which the library
does not yet have. Documented in `docs/paper-gaps/polypeps_ownership_change_monomials.tex`.

The source condition that every hole's outer square lies on one side of `∂Y` enters through the
classification of the holes as outside or inside `Y`, which is part of the data, and through its
consequence for the physical samples of the outer squares. `TwoSheetExchange` lists the holes of
each frame as those outside `Y` followed by those inside `Y`; `exchange_ofFrames` treats frames
whose holes are listed in any order, through the canonical identification of tag orderings
(`05-frames.tex`, lines 84–85).

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.6 `lem:exchange` and its proof,
  `05-frames.tex`, lines 458–570.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open EuclideanSpace (vecKron)
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

/-! ### Exchange data -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type*}

/-- **Data of Lemma 6.6.** Two encoded frames on two sheets and the physical sample `Y ∩ Λ` of a
plane region `Y`. The holes of each frame are listed as the holes whose outer squares lie outside
`Y`, followed by those whose outer squares lie inside `Y`: every hole's entire outer square lies on
one side of `∂Y`. Since encodings of holes with disjoint footprints commute, any listing of the
holes is related to this one by the canonical identification of tag orderings (`05-frames.tex`,
lines 84–85; see `ofFrames`). The source condition concerns the outer squares in the plane; here
the classification is the split into `out` and `in` lists, and its consequence for the physical
samples is recorded.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 461–464. -/
structure TwoSheetExchange (pos : ι → ℝ × ℝ) (q : ℕ) (Party : Type*) where
  /-- The raw owners of the first sheet. -/
  owner₁ : ι → Party
  /-- The raw owners of the second sheet. -/
  owner₂ : ι → Party
  /-- The holes of the first frame outside `Y`. -/
  out₁ : List (Hole pos q Party)
  /-- The holes of the first frame inside `Y`. -/
  in₁ : List (Hole pos q Party)
  /-- The holes of the second frame outside `Y`. -/
  out₂ : List (Hole pos q Party)
  /-- The holes of the second frame inside `Y`. -/
  in₂ : List (Hole pos q Party)
  /-- The physical sample `Y ∩ Λ` of the region. -/
  region : Finset ι
  /-- The holes of the first frame have pairwise disjoint outer footprints. -/
  disjoint₁ : PairwiseDisjointOuter ((out₁ ++ in₁).map Hole.patch)
  /-- The holes of the second frame have pairwise disjoint outer footprints. -/
  disjoint₂ : PairwiseDisjointOuter ((out₂ ++ in₂).map Hole.patch)
  /-- The outer squares of the holes inside `Y` lie in `Y`. -/
  inside : ∀ h ∈ in₁ ++ in₂, (h.patch.outer : Set ι) ⊆ region
  /-- The outer squares of the holes outside `Y` avoid `Y`. -/
  outside : ∀ h ∈ out₁ ++ out₂, Disjoint (h.patch.outer : Set ι) region

/-- Holes outside and inside `Y` have disjoint outer footprints. -/
theorem pairwiseDisjointOuter_append {o i : List (Hole pos q Party)} {Y : Finset ι}
    (ho : PairwiseDisjointOuter (o.map Hole.patch)) (hi : PairwiseDisjointOuter (i.map Hole.patch))
    (hoY : ∀ h ∈ o, Disjoint (h.patch.outer : Set ι) Y)
    (hiY : ∀ h ∈ i, (h.patch.outer : Set ι) ⊆ Y) :
    PairwiseDisjointOuter ((o ++ i).map Hole.patch) := by
  rw [PairwiseDisjointOuter, List.map_append, List.pairwise_append]
  refine ⟨ho, hi, ?_⟩
  intro a ha b hb
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ha
  obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hb
  rw [← Finset.disjoint_coe]
  exact Set.disjoint_of_subset_right (hiY h' hh') (hoY h hh)

theorem footprint_mono {l l' : List (SquarePatch pos q)} (h : ∀ p ∈ l, p ∈ l') :
    footprint l ⊆ footprint l' := fun _ ⟨p, hp, hx⟩ => ⟨p, h p hp, hx⟩

/-- The operator acting as `G` on the raw registers of two sheets and as the identity on the
tags of two lists of holes. -/
def liftTags {l₁ l₂ : List (Hole pos q Party)}
    (G : Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ) :
    Matrix ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q)))
      ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q))) ℂ :=
  ((1 : Matrix (TagSpace l₁ × TagSpace l₂) (TagSpace l₁ × TagSpace l₂) ℂ) ⊗ₖ G).submatrix
    (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)

theorem norm_liftTags_le {l₁ l₂ : List (Hole pos q Party)}
    (G : Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ) :
    ‖liftTags (l₁ := l₁) (l₂ := l₂) G‖ ≤ ‖G‖ :=
  (norm_submatrix_equiv_le _ _).trans (l2_opNorm_one_kronecker_le G)

/-- A two-sheet raw operator commuting with every product of raw parts of the two encodings
passes through the product `K₁ ⊗ K₂` of the encodings. -/
theorem liftTags_mul_kronecker [NeZero q] {l₁ l₂ : List (Hole pos q Party)}
    {G : Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ}
    (hG : ∀ a b, Commute G (rawProd l₁ a ⊗ₖ rawProd l₂ b)) :
    liftTags G * (frameEncoder l₁ ⊗ₖ frameEncoder l₂) =
      (frameEncoder l₁ ⊗ₖ frameEncoder l₂) * G := by
  have hK : frameEncoder l₁ ⊗ₖ frameEncoder l₂ =
      (stack fun t : TagSpace l₁ × TagSpace l₂ => rawProd l₁ t.1 ⊗ₖ rawProd l₂ t.2).submatrix
        (Equiv.prodProdProdComm _ _ _ _) (Equiv.refl _) := by
    ext ⟨⟨a, x⟩, ⟨b, y⟩⟩ ⟨r₁, r₂⟩
    rfl
  set S : TagSpace l₁ × TagSpace l₂ → Matrix ((ι → Fin q) × (ι → Fin q))
    ((ι → Fin q) × (ι → Fin q)) ℂ := fun t => rawProd l₁ t.1 ⊗ₖ rawProd l₂ t.2
  have hS : ((1 : Matrix (TagSpace l₁ × TagSpace l₂) (TagSpace l₁ × TagSpace l₂) ℂ) ⊗ₖ G) *
      stack S = stack S * G := one_kronecker_mul_stack fun t => hG t.1 t.2
  rw [hK, liftTags]
  rw [submatrix_mul_equiv]
  rw [hS]
  conv_rhs => rw [← submatrix_id_id G, ← Equiv.coe_refl, submatrix_mul_equiv]

namespace TwoSheetExchange

variable (X : TwoSheetExchange pos q Party)

/-- The first frame `F₁`. -/
abbrev frame₁ : Frame pos q Party := ⟨X.owner₁, X.out₁ ++ X.in₁, X.disjoint₁⟩

/-- The second frame `F₂`. -/
abbrev frame₂ : Frame pos q Party := ⟨X.owner₂, X.out₂ ++ X.in₂, X.disjoint₂⟩

theorem disjoint_new₁ : PairwiseDisjointOuter ((X.out₁ ++ X.in₂).map Hole.patch) :=
  pairwiseDisjointOuter_append X.disjoint₁.left X.disjoint₂.right
    (fun h hh => X.outside h (List.mem_append_left _ hh))
    (fun h hh => X.inside h (List.mem_append_right _ hh))

theorem disjoint_new₂ : PairwiseDisjointOuter ((X.out₂ ++ X.in₁).map Hole.patch) :=
  pairwiseDisjointOuter_append X.disjoint₂.left X.disjoint₁.right
    (fun h hh => X.outside h (List.mem_append_right _ hh))
    (fun h hh => X.inside h (List.mem_append_left _ hh))

/-- The first frame after the exchange: inside `Y` it carries the raw ownership assignment and
the holes, with their tag owners, of the second frame (`05-frames.tex`, lines 462–464). -/
abbrev newFrame₁ : Frame pos q Party :=
  ⟨fun x => if x ∈ X.region then X.owner₂ x else X.owner₁ x, X.out₁ ++ X.in₂, X.disjoint_new₁⟩

/-- The second frame after the exchange. -/
abbrev newFrame₂ : Frame pos q Party :=
  ⟨fun x => if x ∈ X.region then X.owner₁ x else X.owner₂ x, X.out₂ ++ X.in₁, X.disjoint_new₂⟩

/-- The renaming of registers: inside `Y`, the raw registers of the two sheets and the tags of the
holes exchange their sheet names; every register keeps its party (`05-frames.tex`, lines
485–489). -/
def renameEquiv : X.frame₁.Layout × X.frame₂.Layout ≃ X.newFrame₁.Layout × X.newFrame₂.Layout where
  toFun y :=
    let a₁ := tagAppendEquiv X.out₁ X.in₁ y.1.1
    let a₂ := tagAppendEquiv X.out₂ X.in₂ y.2.1
    let r := sheetSwap q X.region (y.1.2, y.2.2)
    (((tagAppendEquiv X.out₁ X.in₂).symm (a₁.1, a₂.2), r.1),
      ((tagAppendEquiv X.out₂ X.in₁).symm (a₂.1, a₁.2), r.2))
  invFun y :=
    let a₁ := tagAppendEquiv X.out₁ X.in₂ y.1.1
    let a₂ := tagAppendEquiv X.out₂ X.in₁ y.2.1
    let r := sheetSwap q X.region (y.1.2, y.2.2)
    (((tagAppendEquiv X.out₁ X.in₁).symm (a₁.1, a₂.2), r.1),
      ((tagAppendEquiv X.out₂ X.in₂).symm (a₂.1, a₁.2), r.2))
  left_inv y := by
    obtain ⟨⟨τ₁, x₁⟩, ⟨τ₂, x₂⟩⟩ := y
    have h := (sheetSwap q X.region).symm_apply_apply (x₁, x₂)
    simp only [Equiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
    rw [sheetSwap_symm] at h
    simp only [h]
  right_inv y := by
    obtain ⟨⟨τ₁, x₁⟩, ⟨τ₂, x₂⟩⟩ := y
    have h := (sheetSwap q X.region).symm_apply_apply (x₁, x₂)
    simp only [Equiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
    rw [sheetSwap_symm] at h
    simp only [h]

/-- **The renaming `ℛ`** between the two-sheet layouts before and after the exchange. -/
def rename : Matrix (X.newFrame₁.Layout × X.newFrame₂.Layout)
    (X.frame₁.Layout × X.frame₂.Layout) ℂ :=
  X.renameEquiv.symm.toPEquiv.toMatrix

theorem norm_rename_le_one : ‖X.rename‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- The raw part of the encoding of the holes outside `Y` acts off `Y`. -/
theorem exists_out_form [NeZero q] {o : List (Hole pos q Party)}
    (ho : ∀ h ∈ o, h ∈ X.out₁ ++ X.out₂) (a : TagSpace o) :
    ∃ O' : Matrix (↥X.regionᶜ → Fin q) (↥X.regionᶜ → Fin q) ℂ,
      (rawProd o a).submatrix (sheetSplit q X.region).symm (sheetSplit q X.region).symm =
        1 ⊗ₖ O' :=
  exists_one_kronecker_of_mem_supportedOperators
    (disjoint_footprint_of_forall fun p hp => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact X.outside h (ho h hh))
    (rawProd_mem_supportedOperators o a)

/-- The raw part of the encoding of the holes inside `Y` acts on `Y`. -/
theorem exists_in_form [NeZero q] {i : List (Hole pos q Party)}
    (hi : ∀ h ∈ i, h ∈ X.in₁ ++ X.in₂) (a : TagSpace i) :
    ∃ I' : Matrix (X.region → Fin q) (X.region → Fin q) ℂ,
      (rawProd i a).submatrix (sheetSplit q X.region).symm (sheetSplit q X.region).symm =
        I' ⊗ₖ 1 :=
  exists_kronecker_one_of_mem_supportedOperators
    (supportedOperators_mono (fun x hx => by
      obtain ⟨p, hp, hx⟩ := hx
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact X.inside h (hi h hh) hx)
    (rawProd_mem_supportedOperators i a))

/-- **Exact intertwining identity (`eq:exchange-intertwining`).** `ℛ K_in = K_out F_{Y ∩ Λ}`,
where `K_in` and `K_out` are the products of the two frames' encoders before and after the
exchange. Every hole lies on one side of `∂Y`, so for every selected radius its raw squares and
its tag change sheet together.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 482–498. -/
theorem rename_mul_encoder [NeZero q] :
    X.rename * (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) =
      (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) * sheetSwapOp q X.region := by
  rw [rename, PEquiv.toMatrix_toPEquiv_mul, sheetSwapOp, PEquiv.mul_toMatrix_toPEquiv,
    sheetSwap_symm]
  ext ⟨⟨τ₁, x₁⟩, ⟨τ₂, x₂⟩⟩ ⟨r₁, r₂⟩
  obtain ⟨O₁, hO₁⟩ := X.exists_out_form (fun h hh => List.mem_append_left _ hh)
    (tagAppendEquiv X.out₁ X.in₂ τ₁).1
  obtain ⟨O₂, hO₂⟩ := X.exists_out_form (fun h hh => List.mem_append_right _ hh)
    (tagAppendEquiv X.out₂ X.in₁ τ₂).1
  obtain ⟨I₁, hI₁⟩ := X.exists_in_form (fun h hh => List.mem_append_left _ hh)
    (tagAppendEquiv X.out₂ X.in₁ τ₂).2
  obtain ⟨I₂, hI₂⟩ := X.exists_in_form (fun h hh => List.mem_append_right _ hh)
    (tagAppendEquiv X.out₁ X.in₂ τ₁).2
  simp only [submatrix_apply, kroneckerMap_apply, id, Frame.encoder, frameEncoder, stack_apply,
    renameEquiv, Equiv.coe_fn_symm_mk]
  rw [rawProd_append, rawProd_append, rawProd_append, rawProd_append]
  simp only [Equiv.apply_symm_apply]
  rw [apply_eq_submatrix_apply (_ * _) (sheetSplit q X.region),
    mul_submatrix_sheetSplit hO₁ hI₁,
    apply_eq_submatrix_apply (rawProd X.out₂ _ * rawProd X.in₂ _) (sheetSplit q X.region),
    mul_submatrix_sheetSplit hO₂ hI₂,
    apply_eq_submatrix_apply (rawProd X.out₁ _ * rawProd X.in₂ _) (sheetSplit q X.region),
    mul_submatrix_sheetSplit hO₁ hI₂,
    apply_eq_submatrix_apply (rawProd X.out₂ _ * rawProd X.in₁ _) (sheetSplit q X.region),
    mul_submatrix_sheetSplit hO₂ hI₁]
  simp only [kroneckerMap_apply, sheetSplit_sheetSwap_fst, sheetSplit_sheetSwap_snd]
  ring

/-! ### The partition and the exchange map -/

variable (P : Party)

open Classical in
/-- The set `Z = {x : the two old raw owners of x are not both P∘} ∪ H⁺(F₁) ∪ H⁺(F₂)`
(`eq:exchange-Z`).

Polynomial-PEPS manuscript, Lemma 6.6, `05-frames.tex`, lines 466–470. -/
def exchangeEnv : Finset ι :=
  Finset.univ.filter fun x =>
    ¬(X.owner₁ x = P ∧ X.owner₂ x = P) ∨ x ∈ X.frame₁.outerHoles ∨ x ∈ X.frame₂.outerHoles

/-- `T = Z ∩ Y` (`eq:exchange-partition`). -/
def tSet : Finset ι := X.exchangeEnv P ∩ X.region

/-- `E = Z ∖ Y` (`eq:exchange-partition`). -/
def eSet : Finset ι := X.exchangeEnv P \ X.region

/-- `A = Y ∩ U = Y ∖ Z`, where the private swap `F_A` acts (`05-frames.tex`, line 512). -/
def aSet : Finset ι := X.region \ X.exchangeEnv P

theorem mem_exchangeEnv {x : ι} : x ∈ X.exchangeEnv P ↔
    ¬(X.owner₁ x = P ∧ X.owner₂ x = P) ∨ x ∈ X.frame₁.outerHoles ∨ x ∈ X.frame₂.outerHoles := by
  classical
  unfold exchangeEnv
  simp

theorem disjoint_tSet_eSet : Disjoint (X.tSet P) (X.eSet P) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [tSet, eSet, Finset.mem_inter, Finset.mem_sdiff] at hx hx'
  exact hx'.2 hx.2

theorem tSet_union_eSet : X.tSet P ∪ X.eSet P = X.exchangeEnv P := by
  ext x
  simp only [tSet, eSet, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem mem_tSet_iff (x : ι) : x ∈ X.tSet P ↔ x ∈ X.region ∧ x ∉ X.aSet P := by
  simp only [tSet, aSet, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem aSet_subset_region : X.aSet P ⊆ X.region := Finset.sdiff_subset

/-- `A` lies in `U = Λ ∖ Z`. -/
theorem aSet_subset_compl : X.aSet P ⊆ (X.tSet P ∪ X.eSet P)ᶜ := by
  intro x hx
  rw [tSet_union_eSet, Finset.mem_compl]
  exact (Finset.mem_sdiff.mp hx).2

/-- Every register of `U = Λ ∖ Z` is raw and held by `P∘` on both sheets, before the exchange
(`05-frames.tex`, lines 500–501). -/
theorem owner_eq_of_notMem_exchangeEnv {x : ι} (hx : x ∉ X.exchangeEnv P) :
    X.owner₁ x = P ∧ X.owner₂ x = P := by
  by_contra h
  exact hx ((X.mem_exchangeEnv P).mpr (Or.inl h))

/-- Every register of `U` is held by `P∘` on both sheets after the exchange as well. -/
theorem newOwner_eq_of_notMem_exchangeEnv {x : ι} (hx : x ∉ X.exchangeEnv P) :
    X.newFrame₁.owner x = P ∧ X.newFrame₂.owner x = P := by
  obtain ⟨h₁, h₂⟩ := X.owner_eq_of_notMem_exchangeEnv P hx
  change (if x ∈ X.region then X.owner₂ x else X.owner₁ x) = P ∧
    (if x ∈ X.region then X.owner₁ x else X.owner₂ x) = P
  split_ifs <;> exact ⟨by assumption, by assumption⟩

/-- The renaming keeps every register at its party: the new owner of the register of the first
sheet at `x ∈ Y` is the old owner of the second sheet there (`05-frames.tex`, lines 487–489). -/
theorem newFrame₁_owner_of_mem {x : ι} (hx : x ∈ X.region) :
    X.newFrame₁.owner x = X.owner₂ x := ite_eq_left hx

theorem newFrame₂_owner_of_mem {x : ι} (hx : x ∈ X.region) :
    X.newFrame₂.owner x = X.owner₁ x := ite_eq_left hx

theorem footprint_new₁_subset :
    footprint ((X.out₁ ++ X.in₂).map Hole.patch) ⊆ (↑(X.tSet P ∪ X.eSet P) : Set ι) := by
  rw [tSet_union_eSet, List.map_append, footprint_append]
  rintro x (hx | hx)
  · exact (X.mem_exchangeEnv P).mpr (Or.inr (Or.inl (footprint_mono (fun p hp => by
      simp only [Frame.patches, List.map_append, List.mem_append]; exact Or.inl hp) hx)))
  · exact (X.mem_exchangeEnv P).mpr (Or.inr (Or.inr (footprint_mono (fun p hp => by
      simp only [Frame.patches, List.map_append, List.mem_append]; exact Or.inr hp) hx)))

theorem footprint_new₂_subset :
    footprint ((X.out₂ ++ X.in₁).map Hole.patch) ⊆ (↑(X.tSet P ∪ X.eSet P) : Set ι) := by
  rw [tSet_union_eSet, List.map_append, footprint_append]
  rintro x (hx | hx)
  · exact (X.mem_exchangeEnv P).mpr (Or.inr (Or.inr (footprint_mono (fun p hp => by
      simp only [Frame.patches, List.map_append, List.mem_append]; exact Or.inl hp) hx)))
  · exact (X.mem_exchangeEnv P).mpr (Or.inr (Or.inl (footprint_mono (fun p hp => by
      simp only [Frame.patches, List.map_append, List.mem_append]; exact Or.inr hp) hx)))

/-- **The implemented map `C = D_U F_A ℛ`.** First rename the sheets inside `Y`, then apply the
private swap `F_A` and then the private buffer correction `D_U`, in this order; both act on raw
registers of `U` alone and as the identity on the tags.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 485–489 and 512–527. -/
def exchangeOp (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    Matrix (X.newFrame₁.Layout × X.newFrame₂.Layout) (X.frame₁.Layout × X.frame₂.Layout) ℂ :=
  liftTags (l₁ := X.out₁ ++ X.in₂) (l₂ := X.out₂ ++ X.in₁)
    (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.aSet P)) * X.rename

theorem norm_exchangeOp_le_one (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    ‖X.exchangeOp P σ‖ ≤ 1 :=
  l2_opNorm_mul_le_one ((norm_liftTags_le _).trans (l2_opNorm_mul_le_one
    (norm_sheetBufferCorrection_le_one _ σ) (norm_sheetSwapOp_le_one _))) X.norm_rename_le_one

/-- The corrections `D_U` and `F_A` commute with the raw parts of the encoders after the
exchange: they act on `U`, away from every hole of both sheets (`05-frames.tex`, lines
514–515). -/
theorem commute_correction [NeZero q] (σ : SplittingData q (X.tSet P) (X.eSet P))
    (a : TagSpace (X.out₁ ++ X.in₂)) (b : TagSpace (X.out₂ ++ X.in₁)) :
    Commute (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.aSet P))
      (rawProd (X.out₁ ++ X.in₂) a ⊗ₖ rawProd (X.out₂ ++ X.in₁) b) := by
  have h₁ := supportedOperators_mono (X.footprint_new₁_subset P)
    (rawProd_mem_supportedOperators _ a)
  have h₂ := supportedOperators_mono (X.footprint_new₂_subset P)
    (rawProd_mem_supportedOperators _ b)
  refine Commute.mul_left (commute_sheetBufferCorrection _ σ h₁ h₂)
    (commute_sheetSwapOp_kronecker ?_ h₁ h₂)
  exact Finset.disjoint_coe.mpr (Finset.disjoint_of_subset_right (X.aSet_subset_compl P)
    disjoint_compl_right)

-- Two copies of the configurations `((t, e), u)` of three regions form a fourfold product of
-- function types; synthesizing their decidable equality exceeds the default instance size.
set_option synthInstance.maxSize 512 in
/-- **The net map on the sheets (`eq:exchange-net-map`).** `D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T}
𝒱^{⊗2}`, in the coordinates `((t, e), u)` of both sheets.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 516–526. -/
theorem sheetBufferCorrection_mul_sheetSwapOp (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.tSet P) =
      Matrix.submatrix ((((1 : Matrix _ _ ℂ) ⊗ₖ σ.V) ⊗ₖ ((1 : Matrix _ _ ℂ) ⊗ₖ σ.V))ᴴ *
          ((tbSwap (X.tSet P → Fin q) (X.eSet P → Fin q) (X.tSet P → Fin q)
            ((X.eSet P → Fin q) ⊕ (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q))).toPEquiv.toMatrix :
              Matrix _ _ ℂ) *
          (((1 : Matrix _ _ ℂ) ⊗ₖ σ.V) ⊗ₖ ((1 : Matrix _ _ ℂ) ⊗ₖ σ.V)))
        (threeSplit₂ (X.disjoint_tSet_eSet P)) (threeSplit₂ (X.disjoint_tSet_eSet P)) := by
  rw [sheetSwapOp_eq_submatrix (X.disjoint_tSet_eSet P), sheetBufferCorrection,
    submatrix_mul_equiv, bufferCorrection_mul_tSwap]

/-- **The exact map (`eq:exchange-exact-map`).** `C K_in = K_out D_U F_T`, and
`D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T} 𝒱^{⊗2}` (`sheetBufferCorrection_mul_sheetSwapOp`).

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 512–532. -/
theorem exchangeOp_mul_encoder [NeZero q] (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    X.exchangeOp P σ * (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) =
      (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) *
        (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.tSet P)) := by
  rw [exchangeOp, Matrix.mul_assoc, rename_mul_encoder, ← Matrix.mul_assoc]
  rw [show X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder =
    frameEncoder (X.out₁ ++ X.in₂) ⊗ₖ frameEncoder (X.out₂ ++ X.in₁) from rfl,
    liftTags_mul_kronecker (X.commute_correction P σ), Matrix.mul_assoc, Matrix.mul_assoc,
    sheetSwapOp_mul_sheetSwapOp (X.mem_tSet_iff P) (X.aSet_subset_region P)]

/-- **Lemma 6.6 (two-sheet exchange).** Consider two encoded frames and a region `Y` such that
every hole's entire outer square lies on one side of `∂Y`. Inside `Y`, exchange the two raw
ownership assignments and the two lists of encoded holes, with their tag owners. Let `P∘` be a
party and `Z`, `T`, `E`, `U` as in `eq:exchange-Z` and `eq:exchange-partition`. If
`I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data such that the map
`C = D_U F_A ℛ`, a register renaming followed by a private swap and a private buffer correction
on the registers of `U` (all held by `P∘` before and after, `owner_eq_of_notMem_exchangeEnv`,
`newOwner_eq_of_notMem_exchangeEnv`), is a contraction with
`C K_in = K_out D_U F_T` and
`‖C (Ω_{F₁} ⊗ Ω_{F₂}) - Ω_{F₁'} ⊗ Ω_{F₂'}‖ ≤ 4 L^{-30}`. No raw register is transferred: the
renaming keeps every register at its party (`newFrame₁_owner_of_mem`).

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 460–479; proof
lines 481–561. -/
theorem exchange [NeZero q] {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hL : 0 < L)
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω (X.tSet P) (X.eSet P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q (X.tSet P) (X.eSet P),
      σ.error (X.disjoint_tSet_eSet P) Ω ≤ L ^ (-30 : ℤ) ∧
      ‖X.exchangeOp P σ‖ ≤ 1 ∧
      X.exchangeOp P σ * (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) =
        (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) *
          (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.tSet P)) ∧
      ‖act (X.exchangeOp P σ) (vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω)) -
        vecKron (X.newFrame₁.refVec Ω) (X.newFrame₂.refVec Ω)‖ ≤ 4 * L ^ (-30 : ℤ) := by
  set h := X.disjoint_tSet_eSet P
  obtain ⟨σ, hσ⟩ := exists_sheetSplitting_zpow h hΩ hL hI
  refine ⟨σ, hσ, X.norm_exchangeOp_le_one P σ, X.exchangeOp_mul_encoder P σ, ?_⟩
  have hKout : ‖X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder‖ ≤ 1 :=
    l2_opNorm_kronecker_le_one X.newFrame₁.norm_encoder_le_one X.newFrame₂.norm_encoder_le_one
  have hin : vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω) =
      act (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) (vecKron Ω Ω) :=
    (act_kronecker_vecKron _ _ _ _).symm
  have hout : vecKron (X.newFrame₁.refVec Ω) (X.newFrame₂.refVec Ω) =
      act (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) (vecKron Ω Ω) :=
    (act_kronecker_vecKron _ _ _ _).symm
  rw [hin, hout, ← act_mul, X.exchangeOp_mul_encoder P σ, act_mul, ← act_sub_right]
  refine (norm_act_le_of_norm_le_one hKout _).trans ?_
  rw [sheetSwapOp_eq_submatrix h, sheetBufferCorrection, submatrix_mul_equiv,
    norm_act_submatrix_sub]
  set ω : EuclideanSpace ℂ _ := WithLp.toLp 2 (splitVec h Ω)
  have hω : (WithLp.toLp 2 (⇑(vecKron Ω Ω) ∘ (threeSplit₂ h).symm) : EuclideanSpace ℂ _) =
      vecKron ω ω := rfl
  have hω1 : ‖ω‖ = 1 := by
    have h2 := norm_toLp_sq (splitVec h Ω)
    rw [star_splitVec_dotProduct_splitVec h hΩ, Complex.one_re] at h2
    nlinarith [norm_nonneg ω]
  rw [hω]
  refine (norm_act_bufferCorrection_mul_tSwap_sub_le σ.isIsometry σ.star_s σ.star_s' hω1).trans ?_
  have he : ‖act ((1 : Matrix _ _ ℂ) ⊗ₖ σ.V) ω - WithLp.toLp 2 (tensorPurification σ.s σ.s')‖ =
      σ.error h Ω := rfl
  rw [he]
  linarith

/-! ### Frames with holes in any order -/

/-- **Exchange data of two arbitrary frames.** Let `F₁`, `F₂` be encoded frames and `Y` the
physical sample of a plane region, and let `out` classify the holes of both frames as outside or
inside the region, consistently with the physical samples: the outer footprint of a hole classified
as outside avoids `Y`, and that of a hole classified as inside lies in `Y`. List the holes of each
frame as those outside followed by those inside, keeping their relative order; this is a
reordering of the tags of each frame.

In the source every hole's outer square lies on one side of `∂Y`, and that side gives the
classification (`05-frames.tex`, lines 461–464). Passing it as `out` keeps the source's choice for
a hole whose outer square has empty physical sample, which is compatible with either side.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 461–464. -/
def ofFrames (F₁ F₂ : Frame pos q Party) (Y : Finset ι) (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ F₁.holes ++ F₂.holes, out h = true → Disjoint (h.patch.outer : Set ι) Y)
    (hin : ∀ h ∈ F₁.holes ++ F₂.holes, out h = false → (h.patch.outer : Set ι) ⊆ Y) :
    TwoSheetExchange pos q Party where
  owner₁ := F₁.owner
  owner₂ := F₂.owner
  out₁ := F₁.holes.filter out
  in₁ := F₁.holes.filter fun h => !out h
  out₂ := F₂.holes.filter out
  in₂ := F₂.holes.filter fun h => !out h
  region := Y
  disjoint₁ := F₁.disjoint.perm ((List.filter_append_perm _ _).symm.map _) fun h => Disjoint.symm h
  disjoint₂ := F₂.disjoint.perm ((List.filter_append_perm _ _).symm.map _) fun h => Disjoint.symm h
  inside h hh := by
    rcases List.mem_append.mp hh with hh | hh
    · have h₁ := List.mem_filter.mp hh
      exact hin h (List.mem_append_left _ h₁.1) (by simpa using h₁.2)
    · have h₁ := List.mem_filter.mp hh
      exact hin h (List.mem_append_right _ h₁.1) (by simpa using h₁.2)
  outside h hh := by
    rcases List.mem_append.mp hh with hh | hh
    · have h₁ := List.mem_filter.mp hh
      exact hout h (List.mem_append_left _ h₁.1) h₁.2
    · have h₁ := List.mem_filter.mp hh
      exact hout h (List.mem_append_right _ h₁.1) h₁.2

theorem mem_footprint_perm {l l' : List (Hole pos q Party)} (hp : l.Perm l') {x : ι} :
    x ∈ footprint (l.map Hole.patch) ↔ x ∈ footprint (l'.map Hole.patch) :=
  ⟨fun ⟨p, hp', hx⟩ => ⟨p, (hp.map _).subset hp', hx⟩,
    fun ⟨p, hp', hx⟩ => ⟨p, (hp.map _).symm.subset hp', hx⟩⟩

/-- For two arbitrary frames, the set `Z` of `eq:exchange-Z` is computed from the frames
themselves. -/
theorem mem_ofFrames_exchangeEnv (F₁ F₂ : Frame pos q Party) (Y : Finset ι)
    (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ F₁.holes ++ F₂.holes, out h = true → Disjoint (h.patch.outer : Set ι) Y)
    (hin : ∀ h ∈ F₁.holes ++ F₂.holes, out h = false → (h.patch.outer : Set ι) ⊆ Y) (P : Party)
    {x : ι} :
    x ∈ (ofFrames F₁ F₂ Y out hout hin).exchangeEnv P ↔
      ¬(F₁.owner x = P ∧ F₂.owner x = P) ∨ x ∈ F₁.outerHoles ∨ x ∈ F₂.outerHoles := by
  rw [mem_exchangeEnv]
  exact Iff.or Iff.rfl (Iff.or (mem_footprint_perm (List.filter_append_perm _ _))
    (mem_footprint_perm (List.filter_append_perm _ _)))

/-- The relabelling of the two-sheet layout of two lists of holes along bijections `e₁`, `e₂` of
their tag configurations, acting as the identity on the raw registers. -/
def tagReorder {l₁ l₁' l₂ l₂' : List (Hole pos q Party)} (e₁ : TagSpace l₁ ≃ TagSpace l₁')
    (e₂ : TagSpace l₂ ≃ TagSpace l₂') :
    Matrix ((TagSpace l₁' × (ι → Fin q)) × (TagSpace l₂' × (ι → Fin q)))
      ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q))) ℂ :=
  ((e₁.prodCongr (Equiv.refl _)).prodCongr (e₂.prodCongr (Equiv.refl _))).symm.toPEquiv.toMatrix

theorem norm_tagReorder_le_one {l₁ l₁' l₂ l₂' : List (Hole pos q Party)}
    (e₁ : TagSpace l₁ ≃ TagSpace l₁') (e₂ : TagSpace l₂ ≃ TagSpace l₂') :
    ‖tagReorder e₁ e₂‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- **Canonical identification of tag orderings.** For bijections of tag configurations that
identify the raw parts of the encodings, the relabelling carries `K_{l₁} ⊗ K_{l₂}` to
`K_{l₁'} ⊗ K_{l₂'}`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 75–76 (the fixed ordering of the tags of
Definition 6.1) and 84–85 (encodings of distinct holes commute after the canonical
identification of tag orderings). -/
theorem tagReorder_mul_kronecker [NeZero q] {l₁ l₁' l₂ l₂' : List (Hole pos q Party)}
    {e₁ : TagSpace l₁ ≃ TagSpace l₁'} {e₂ : TagSpace l₂ ≃ TagSpace l₂'}
    (he₁ : ∀ t, rawProd l₁' (e₁ t) = rawProd l₁ t) (he₂ : ∀ t, rawProd l₂' (e₂ t) = rawProd l₂ t) :
    tagReorder e₁ e₂ * (frameEncoder l₁ ⊗ₖ frameEncoder l₂) =
      frameEncoder l₁' ⊗ₖ frameEncoder l₂' := by
  rw [← frameEncoder_submatrix_of_rawProd_eq e₁ he₁, ← frameEncoder_submatrix_of_rawProd_eq e₂ he₂,
    tagReorder, PEquiv.toMatrix_toPEquiv_mul]
  ext ⟨⟨a, x⟩, ⟨b, y⟩⟩ ⟨r₁, r₂⟩
  simp

/-- **Lemma 6.6 (two-sheet exchange), frames with holes in any order.** Let `F₁`, `F₂` be encoded
frames and `Y` the physical sample of a region, with the holes of both frames classified as
outside or inside the region as in `ofFrames`. With `Z`, `T`, `E` computed from the two frames
(`mem_ofFrames_exchangeEnv`), if `I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are bijections
`e₁`, `e₂` of tag configurations identifying the encodings of each frame with the encodings of
its holes listed as those outside followed by those inside (the canonical identification of tag
orderings), and splitting data with error at most `L^{-30}`, such that the map
`C = D_U F_A ℛ G`, the implemented map `exchangeOp` after the relabelling `G = tagReorder e₁ e₂`,
is a contraction with `C (K_{F₁} ⊗ K_{F₂}) = K_out D_U F_T` and
`‖C (Ω_{F₁} ⊗ Ω_{F₂}) - Ω_{F₁'} ⊗ Ω_{F₂'}‖ ≤ 4 L^{-30}`.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 460–479, with the
canonical identification of tag orderings of lines 75–76 and 84–85; proof lines 481–561. -/
theorem exchange_ofFrames [NeZero q] (F₁ F₂ : Frame pos q Party) (Y : Finset ι)
    (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ F₁.holes ++ F₂.holes, out h = true → Disjoint (h.patch.outer : Set ι) Y)
    (hin : ∀ h ∈ F₁.holes ++ F₂.holes, out h = false → (h.patch.outer : Set ι) ⊆ Y) (P : Party)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ} (hL : 0 < L)
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω
      ((ofFrames F₁ F₂ Y out hout hin).tSet P) ((ofFrames F₁ F₂ Y out hout hin).eSet P) ≤
        L ^ (-60 : ℤ)) :
    ∃ (e₁ : TagSpace F₁.holes ≃ TagSpace (ofFrames F₁ F₂ Y out hout hin).frame₁.holes)
      (e₂ : TagSpace F₂.holes ≃ TagSpace (ofFrames F₁ F₂ Y out hout hin).frame₂.holes),
      (∀ t, rawProd _ (e₁ t) = rawProd F₁.holes t) ∧ (∀ t, rawProd _ (e₂ t) = rawProd F₂.holes t) ∧
      ∃ σ : SplittingData q ((ofFrames F₁ F₂ Y out hout hin).tSet P)
          ((ofFrames F₁ F₂ Y out hout hin).eSet P),
        σ.error ((ofFrames F₁ F₂ Y out hout hin).disjoint_tSet_eSet P) Ω ≤ L ^ (-30 : ℤ) ∧
        ‖(ofFrames F₁ F₂ Y out hout hin).exchangeOp P σ * tagReorder e₁ e₂‖ ≤ 1 ∧
        (ofFrames F₁ F₂ Y out hout hin).exchangeOp P σ * tagReorder e₁ e₂ *
            (F₁.encoder ⊗ₖ F₂.encoder) =
          ((ofFrames F₁ F₂ Y out hout hin).newFrame₁.encoder ⊗ₖ
              (ofFrames F₁ F₂ Y out hout hin).newFrame₂.encoder) *
            (sheetBufferCorrection ((ofFrames F₁ F₂ Y out hout hin).disjoint_tSet_eSet P) σ *
              sheetSwapOp q ((ofFrames F₁ F₂ Y out hout hin).tSet P)) ∧
        ‖act ((ofFrames F₁ F₂ Y out hout hin).exchangeOp P σ * tagReorder e₁ e₂)
            (vecKron (F₁.refVec Ω) (F₂.refVec Ω)) -
          vecKron ((ofFrames F₁ F₂ Y out hout hin).newFrame₁.refVec Ω)
            ((ofFrames F₁ F₂ Y out hout hin).newFrame₂.refVec Ω)‖ ≤ 4 * L ^ (-30 : ℤ) := by
  set X := ofFrames F₁ F₂ Y out hout hin
  obtain ⟨σ, hσ, hC, hK, herr⟩ := X.exchange P hΩ hL hI
  obtain ⟨e₁, he₁⟩ := exists_tagEquiv_of_perm F₁.disjoint (List.filter_append_perm
    out F₁.holes).symm
  obtain ⟨e₂, he₂⟩ := exists_tagEquiv_of_perm F₂.disjoint (List.filter_append_perm
    out F₂.holes).symm
  have hG : tagReorder e₁ e₂ * (F₁.encoder ⊗ₖ F₂.encoder) =
      X.frame₁.encoder ⊗ₖ X.frame₂.encoder :=
    tagReorder_mul_kronecker he₁ he₂
  refine ⟨e₁, e₂, he₁, he₂, σ, hσ, l2_opNorm_mul_le_one hC (norm_tagReorder_le_one e₁ e₂), ?_, ?_⟩
  · rw [Matrix.mul_assoc]
    exact (congrArg _ hG).trans hK
  · have hv : act (tagReorder e₁ e₂) (vecKron (F₁.refVec Ω) (F₂.refVec Ω)) =
        vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω) := by
      rw [Frame.refVec, Frame.refVec, Frame.refVec, Frame.refVec, ← act_kronecker_vecKron,
        ← act_kronecker_vecKron, ← act_mul, hG]
      rfl
    rw [act_mul]
    erw [hv]
    exact herr

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
