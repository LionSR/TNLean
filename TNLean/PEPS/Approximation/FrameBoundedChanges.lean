/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameRegisters

/-!
# Births, deaths and exchanges as bounded changes

test
-/

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker

/-! ### Composing a monomial with words -/

namespace TNLean.PEPS.PairEffect.PartyChain

variable {P : Type}

/-- A monomial preceded by a word. -/
def precomp {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) : PartyChain ℓX ℓY → PartyChain ℓ₀ ℓY
  | final w' => final (.comp w w')
  | effect hpq α β ℓS w' η rest => effect hpq α β ℓS (.comp w w') η rest

/-- A monomial followed by a word. -/
def postcomp {ℓX ℓY ℓZ : Layout P} : PartyChain ℓX ℓY → Word ℓY ℓZ → PartyChain ℓX ℓZ
  | final w', w => final (.comp w' w)
  | effect hpq α β ℓS w' η rest, w => effect hpq α β ℓS w' η (rest.postcomp w)

theorem eval_precomp {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) :
    (M : PartyChain ℓX ℓY) → (M.precomp w).toEffectChain.eval = M.toEffectChain.eval ∘L w.eval
  | final _ => rfl
  | effect .. => rfl

theorem eval_postcomp {ℓX ℓY ℓZ : Layout P} :
    (M : PartyChain ℓX ℓY) → (w : Word ℓY ℓZ) →
      (M.postcomp w).toEffectChain.eval = w.eval ∘L M.toEffectChain.eval
  | final _, _ => rfl
  | effect _ _ _ _ _ _ rest, w => by
      change (rest.postcomp w).toEffectChain.eval ∘L _ ∘L _ = _
      rw [eval_postcomp rest w]
      rfl

theorem precomp_props {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) (S : Set P) (hw : w.IsAllowed)
    (hS : w.UsesOnly S) : (M : PartyChain ℓX ℓY) → M.IsAllowed → M.UsesOnly S →
      (M.precomp w).IsAllowed ∧ (M.precomp w).UsesOnly S ∧
        (M.precomp w).sourceCount = w.sourceCount + M.sourceCount ∧
        (M.precomp w).toEffectChain.effectCount = M.toEffectChain.effectCount
  | final _, hM, hMS => ⟨⟨hw, hM⟩, ⟨hS, hMS⟩, rfl, rfl⟩
  | effect .. , hM, hMS => ⟨⟨⟨hw, hM.1⟩, hM.2⟩, ⟨hMS.1, hMS.2.1, ⟨hS, hMS.2.2.1⟩, hMS.2.2.2⟩,
      by simp only [precomp, sourceCount, Word.sourceCount, Nat.add_assoc], rfl⟩

theorem postcomp_props {ℓX ℓY ℓZ : Layout P} (S : Set P) :
    (M : PartyChain ℓX ℓY) → (w : Word ℓY ℓZ) → w.IsAllowed → w.UsesOnly S → M.IsAllowed →
      M.UsesOnly S → (M.postcomp w).IsAllowed ∧ (M.postcomp w).UsesOnly S ∧
        (M.postcomp w).sourceCount = M.sourceCount + w.sourceCount ∧
        (M.postcomp w).toEffectChain.effectCount = M.toEffectChain.effectCount
  | final _, _, hw, hS, hM, hMS => ⟨⟨hM, hw⟩, ⟨hMS, hS⟩, rfl, rfl⟩
  | effect _ _ _ _ _ _ rest, w, hw, hS, hM, hMS => by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := postcomp_props S rest w hw hS hM.2.2 hMS.2.2.2
      refine ⟨⟨hM.1, hM.2.1, h₁⟩, ⟨hMS.1, hMS.2.1, hMS.2.2.1, h₂⟩, ?_, ?_⟩
      · simp only [postcomp, sourceCount, h₃, Nat.add_assoc]
      · change (rest.postcomp w).toEffectChain.effectCount + 1 = _
        rw [h₄]

end TNLean.PEPS.PairEffect.PartyChain

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}

namespace Frame

variable (F : Frame pos q Party)

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

variable {T : Finset ι} {P Q : Party}

/-- **Lemma 6.5 (homogeneous birth): the birth is a bounded change involving only `P∘` and
`Q∘`.** In an encoded frame `F`, let `T` be a set of raw sites owned by `P∘` and disjoint from
every outer hole footprint, and let `E` and `U = Λ ∖ (T ∪ E)` be as in `eq:birth-partition`. If
`I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data and an allowed monomial `w`
from the registers of `F` (one per site and per tag, each held by its owner) to the registers
of the frame `F'` in which `T` is owned by `Q∘`, such that:

* `w` uses only `P∘` and `Q∘` and at most one normalized pair source; for `Q∘ ≠ P∘` it groups the
  registers of `T` and of `U` at `P∘`, applies the private contraction `⟨s| (1_T ⊗ V)` at `P∘`,
  prepares the pair state `s` on `T` held by `Q∘` and `B_T` held by `P∘`, applies `Vᴴ` at `P∘`,
  and ungroups `T` at `Q∘` and `U` at `P∘`, with exchanges of tensor factors in between;
* in canonical coordinates the operator of `w` is `1_tags ⊗ B` for the canonical map `B` of
  `eq:birth-map`, and `(1 ⊗ B) K_F = K_{F'} B`;
* the reference-vector error is at most `L^{-30}`: `‖w Ω_F - Ω_{F'}‖ ≤ L^{-30}`, with the
  reference vectors read on the registers of the two frames.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–407; proof lines
413–437 and 445–446; bounded changes, lines 99–105; allowed monomials, `04-compression.tex`,
lines 32–35. -/
theorem birth_bounded [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * F.encoder =
        (F.changeOwner T Q).encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ∃ w : Word F.regs (F.changeOwner T Q).regs,
        w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
        (∀ z, (F.changeOwner T Q).regIso (w.eval z) =
          act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) (F.regIso z)) ∧
        ‖w.eval (F.regIso.symm (F.refVec Ω)) -
          (F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)‖ ≤ L ^ (-30 : ℤ) := by
  obtain ⟨σ, hσ, -, -, hK, herr⟩ := F.birth (Q := Q) hTP hTH hΩ hI
  set hTE := F.disjoint_birthEnv hTP hTH
  obtain ⟨wm, hwA, hwU, hwS, hwE⟩ := exists_birthWord P Q σ
    (tagRegs F.holes ++ siteRegs q F.owner (listE (sites ι) T (F.birthEnv P)))
  have hB : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, F.owner x = P := fun x hx =>
    F.owner_eq_of_notMem_birthEnv fun h => Finset.mem_compl.mp hx (Finset.mem_union_right _ h)
  have hA' : ∀ x ∈ T, (F.changeOwner T Q).owner x = Q := fun x hx => by
    simp only [hx, ↓reduceIte]
  have hB' : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, (F.changeOwner T Q).owner x = P := fun x hx => by
    have hxT : x ∉ T := fun h => Finset.mem_compl.mp hx (Finset.mem_union_left _ h)
    simpa only [hxT, ↓reduceIte] using hB x hx
  have hE : ∀ x ∈ F.birthEnv P, F.owner x = (F.changeOwner T Q).owner x := fun x hx => by
    have hxT : x ∉ T := fun hT => Finset.disjoint_left.mp hTE hT hx
    simp only [hxT, ↓reduceIte]
  obtain ⟨g₁, g₂, g₃⟩ := groupWord_props (q := q) F.owner nodup_sites mem_sites (tagRegs F.holes)
    hTP hB (V := {P, Q}) (Set.mem_insert P _) (Set.mem_insert P _)
  obtain ⟨r₁, r₂, r₃⟩ := relabelRest_props (q := q) F.owner (F.changeOwner T Q).owner mem_sites
    hTE hE (tagRegs F.holes) ⟨Q, euc (T → Fin q)⟩ ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩
    {P, Q}
  obtain ⟨u₁, u₂, u₃⟩ := ungroupWord_props (q := q) (F.changeOwner T Q).owner nodup_sites
    mem_sites (tagRegs F.holes) hA' hB' (V := {P, Q}) (Set.mem_insert_of_mem P rfl)
    (Set.mem_insert P _)
  let W : Word F.regs (F.changeOwner T Q).regs :=
    (groupWord F.owner nodup_sites mem_sites (tagRegs F.holes) hTP hB).comp <|
      wm.comp <| (relabelRest F.owner (F.changeOwner T Q).owner mem_sites hTE hE
        (tagRegs F.holes) _ _).comp <|
        ungroupWord (F.changeOwner T Q).owner nodup_sites mem_sites (tagRegs F.holes) hA' hB'
  have heval : ∀ z, (F.changeOwner T Q).regIso (W.eval z) =
      act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ sheetBirthOp hTE σ)
        (F.regIso z) := by
    intro z
    rw [sheetBirthOp_eq_submatrix]
    exact layoutIso_place F.holes F.owner (F.changeOwner T Q).owner hTE hTP hB hA' hB' hE
      wm.eval _ hwE z
  refine ⟨σ, hσ, hK, W, ⟨g₁, hwA, r₁, u₁⟩, ⟨g₂, hwU, r₂, u₂⟩, ?_, heval, ?_⟩
  · change Word.sourceCount _ + (Word.sourceCount _ + (Word.sourceCount _ +
      Word.sourceCount _)) ≤ 1
    rw [g₃, r₃, u₃]
    omega
  · rw [← (F.changeOwner T Q).regIso.norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply,
      heval, LinearIsometryEquiv.apply_symm_apply]
    exact herr

/-- **Lemma 6.5 (homogeneous death): the death is a bounded change involving only `P∘` and
`Q∘`.** Let `F` be the frame *after* the death, in which `T` is owned by `P∘` and avoids every
outer hole footprint, and let the frame before the death be `F'`, in which `T` is owned by
`Q∘`. If `I_Ω(T:E) ≤ L^{-60}` for `E` computed in `F`, there are splitting data and an allowed
monomial from the registers of `F'` to those of `F`, using only `P∘` and `Q∘`, without pair
sources and with at most one normalized pair effect, whose operator in canonical coordinates is
`1_tags ⊗ B` for the canonical map `B` of `eq:birth-map`, with `(1 ⊗ B) K_{F'} = K_F B` and
reference-vector error `‖M Ω_{F'} - Ω_F‖ ≤ L^{-30}`. For `Q∘ ≠ P∘` it groups the registers of
`T` at `Q∘` and of `U` at `P∘`, applies `V` at `P∘`, contracts `T` and `B_T` with the pair effect
`⟨s|` held by `Q∘` and `P∘`, reinserts `s` and applies `Vᴴ` at `P∘`, and ungroups at `P∘`.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 407–410; proof lines
439–446. -/
theorem death_bounded [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * (F.changeOwner T Q).encoder =
        F.encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ∃ M : PartyChain (F.changeOwner T Q).regs F.regs,
        M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧ M.toEffectChain.effectCount ≤ 1 ∧
        (∀ z, F.regIso (M.toEffectChain.eval z) =
          act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) ((F.changeOwner T Q).regIso z)) ∧
        ‖M.toEffectChain.eval ((F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)) -
          F.regIso.symm (F.refVec Ω)‖ ≤ L ^ (-30 : ℤ) := by
  obtain ⟨σ, hσ, -, -, hK, herr⟩ := F.death (Q := Q) hTP hTH hΩ hI
  set hTE := F.disjoint_birthEnv hTP hTH
  obtain ⟨Mm, hMA, hMU, hMS, hMe, hME⟩ := exists_deathChain P Q σ
    (tagRegs F.holes ++ siteRegs q (F.changeOwner T Q).owner (listE (sites ι) T (F.birthEnv P)))
  have hB' : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, F.owner x = P := fun x hx =>
    F.owner_eq_of_notMem_birthEnv fun h => Finset.mem_compl.mp hx (Finset.mem_union_right _ h)
  have hA : ∀ x ∈ T, (F.changeOwner T Q).owner x = Q := fun x hx => by
    simp only [hx, ↓reduceIte]
  have hB : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, (F.changeOwner T Q).owner x = P := fun x hx => by
    have hxT : x ∉ T := fun h => Finset.mem_compl.mp hx (Finset.mem_union_left _ h)
    simpa only [hxT, ↓reduceIte] using hB' x hx
  have hE : ∀ x ∈ F.birthEnv P, (F.changeOwner T Q).owner x = F.owner x := fun x hx => by
    have hxT : x ∉ T := fun hT => Finset.disjoint_left.mp hTE hT hx
    simp only [hxT, ↓reduceIte]
  obtain ⟨g₁, g₂, g₃⟩ := groupWord_props (q := q) (F.changeOwner T Q).owner nodup_sites
    mem_sites (tagRegs F.holes) hA hB (V := {P, Q}) (Set.mem_insert_of_mem P rfl)
    (Set.mem_insert P _)
  obtain ⟨r₁, r₂, r₃⟩ := relabelRest_props (q := q) (F.changeOwner T Q).owner F.owner mem_sites
    hTE hE (tagRegs F.holes) ⟨P, euc (T → Fin q)⟩ ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩
    {P, Q}
  obtain ⟨u₁, u₂, u₃⟩ := ungroupWord_props (q := q) F.owner nodup_sites mem_sites
    (tagRegs F.holes) hTP hB' (V := {P, Q}) (Set.mem_insert P _) (Set.mem_insert P _)
  let tail := (relabelRest (F.changeOwner T Q).owner F.owner mem_sites hTE hE
    (tagRegs F.holes) ⟨P, euc (T → Fin q)⟩ ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩).comp
      (ungroupWord F.owner nodup_sites mem_sites (tagRegs F.holes) hTP hB')
  obtain ⟨p₁, p₂, p₃, p₄⟩ := PartyChain.postcomp_props {P, Q} Mm tail ⟨r₁, u₁⟩ ⟨r₂, u₂⟩ hMA hMU
  let G := groupWord (q := q) (F.changeOwner T Q).owner nodup_sites mem_sites (tagRegs F.holes) hA hB
  obtain ⟨q₁, q₂, q₃, q₄⟩ := PartyChain.precomp_props G {P, Q} g₁ g₂ (Mm.postcomp tail) p₁ p₂
  have heval : ∀ z, F.regIso (((Mm.postcomp tail).precomp G).toEffectChain.eval z) =
      act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ sheetBirthOp hTE σ)
        ((F.changeOwner T Q).regIso z) := by
    intro z
    rw [PartyChain.eval_precomp, PartyChain.eval_postcomp, sheetBirthOp_eq_submatrix]
    exact layoutIso_place F.holes (F.changeOwner T Q).owner F.owner hTE hA hB hTP hB' hE
      Mm.toEffectChain.eval _ hME z
  refine ⟨σ, hσ, hK, (Mm.postcomp tail).precomp G, q₁, q₂, ?_, ?_, heval, ?_⟩
  · rw [q₃, p₃, g₃, hMS]
    change 0 + (0 + (Word.sourceCount _ + Word.sourceCount _)) = 0
    rw [r₃, u₃]
  · rw [q₄, p₄]
    exact hMe
  · rw [← F.regIso.norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply, heval,
      LinearIsometryEquiv.apply_symm_apply]
    exact herr

end Frame

end TNLean.PEPS.EncodedFrame
