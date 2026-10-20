/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Registers
import TNLean.PEPS.Approximation.TagRegisters

/-!
# The registers of an encoded frame

A sheet has one raw register `ℂ^q` at each site, with a specified owner for each register, and
an encoded frame has in addition one tag register for each hole, held by a specified party
(`05-frames.tex`, lines 13–20 and Definition 6.1). This file lists these registers as a party
layout, one register per tag followed by one register per site (`layoutRegs`, `Frame.regs`),
and identifies their tensor product with the canonical coordinates `TagSpace × (Λ → Fin q)` in
which the encodings and the operators of the frame act (`layoutIso`, `Frame.regIso`): the basis
vector `|τ⟩ ⊗ ⊗_x |c x⟩` goes to `|τ, c⟩` (`layoutIso_layoutVec`).

The grouping of the raw registers of two regions and the placement of a monomial on two grouped
registers behind an arbitrary block of front registers are stated in
`TNLean.Lattice.Sheet.Registers`. Read with the tag registers as the front block, a map acting on
the two grouped registers as `M ⊗ 1` acts on the registers of the frame, in canonical
coordinates, as `1_tags ⊗ (1_E ⊗ M)` (`layoutIso_place`).

## Main definitions

* `EncodedFrame.layoutRegs`, `EncodedFrame.layoutVec`, `EncodedFrame.layoutIso`: the registers of
  a frame and their canonical coordinates.
* `EncodedFrame.Frame.regs`, `EncodedFrame.Frame.regIso`.

## Main results

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

/-! ### The registers of an encoded frame -/

section FrameLayout

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

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
    (hf : ∀ z, pairHeadIso _ (f z) = (act M).rTensor _ (pairHeadIso _ z))
    (z : Mem (layoutRegs q l own)) :
    layoutIso l own' ((ungroupWord own' nodup_sites mem_sites (tagRegs l) hA' hB').eval
        ((relabelRest own own' mem_sites h hE (tagRegs l) _ _).eval
          (f ((groupWord own nodup_sites mem_sites (tagRegs l) hA hB).eval z)))) =
      act ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ sheetPlace h M) (layoutIso l own z) :=
  frontLayoutIso_place (tagRegs l) (tagIso l) own own' h hA hB hA' hB' hE f M hf z

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
