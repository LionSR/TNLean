/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Birth
import TNLean.PEPS.Approximation.SheetSplitting

/-!
# Homogeneous birth and death

Lemma 6.5 of the polynomial-PEPS manuscript changes the owner of a set `T` of raw sites of an
encoded frame from `P∘` to `Q∘`, keeping every hole, its encoding and its tag owner. With
`E = {x : owner x ≠ P∘} ∪ H⁺(F)` and `U = Λ ∖ (T ∪ E)`, the splitting consequence of Lemma 6.4
gives an isometry `V` on `U` and unit vectors `s`, `s'` with `‖𝒱 Ω - s ⊗ s'‖ ≤ L^{-30}` when
`I_Ω(T:E) ≤ L^{-60}`, where `𝒱 = 1_{TE} ⊗ V`. The canonical map of the birth is
`B = 𝒱ᴴ (|s⟩⟨s|_{T B_T} ⊗ 1_{E B_E}) 𝒱`.

The canonical map `B`, its contraction and reference-error bounds, and the fact that on a sheet
it commutes with every operator acting on a subset of `E` do not depend on the holes and are
stated in `TNLean.Lattice.Sheet.Birth`. This file reads them in an encoded frame: `B` commutes
with every hole encoder, all of which are supported in `E`, so the same bound holds for the
encoded reference vectors.

## Main definitions

* `EncodedFrame.Frame.changeOwner`, `EncodedFrame.Frame.birthEnv`: the frame after a change of
  the owner of `T`, and the set `E` of `eq:birth-partition`.

## Main results

* `EncodedFrame.Frame.birth`, `EncodedFrame.Frame.death`: Lemma 6.5 `lem:birth`.

The bounded-change clause of Lemma 6.5, that the birth is a private contraction at `P∘`, one
normalized pair source between `Q∘` and `P∘` and a private contraction at `P∘`, and the death the
same with one normalized pair effect, is `Frame.birth_bounded` and `Frame.death_bounded` in
`TNLean.PEPS.Approximation.FrameBoundedChanges`, on the registers of the frame with one register
per site and per tag.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.5 `lem:birth` and its proof,
  `05-frames.tex`, lines 396–456.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame
open TNLean.Lattice.Sheet

/-! ### Birth and death in an encoded frame -/

section FrameOwnership

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type*}

/-- The frame obtained by changing the owner of the raw registers of `T` to `Q`, keeping every
hole, its encoding and its tag owner. -/
abbrev Frame.changeOwner (F : Frame pos q Party) (T : Finset ι) (Q : Party) :
    Frame pos q Party where
  owner x := if x ∈ T then Q else F.owner x
  holes := F.holes
  disjoint := F.disjoint

open Classical in
/-- The set `E = {x : owner x ≠ P∘} ∪ H⁺(F)` of `eq:birth-partition`. It contains the whole outer
footprint of every hole, even where the raw owner is `P∘`.

Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 400–405 and 454–456. -/
def Frame.birthEnv (F : Frame pos q Party) (P : Party) : Finset ι :=
  Finset.univ.filter fun x => F.owner x ≠ P ∨ x ∈ F.outerHoles

namespace Frame

variable (F : Frame pos q Party) {T : Finset ι} {P Q : Party}

theorem mem_birthEnv {x : ι} : x ∈ F.birthEnv P ↔ F.owner x ≠ P ∨ x ∈ F.outerHoles := by
  classical
  unfold birthEnv
  simp

theorem outerHoles_subset_birthEnv : F.outerHoles ⊆ (F.birthEnv P : Set ι) := fun _ hx =>
  (F.mem_birthEnv).mpr (Or.inr hx)

/-- Every register outside `E` is owned by `P∘`. -/
theorem owner_eq_of_notMem_birthEnv {x : ι} (hx : x ∉ F.birthEnv P) : F.owner x = P := by
  by_contra h
  exact hx ((F.mem_birthEnv).mpr (Or.inl h))

/-- After the change of owner, every register outside `E` is owned by `P∘` or `Q∘`. -/
theorem changeOwner_owner_of_notMem_birthEnv {x : ι} (hx : x ∉ F.birthEnv P) :
    (F.changeOwner T Q).owner x = P ∨ (F.changeOwner T Q).owner x = Q := by
  change (if x ∈ T then Q else F.owner x) = P ∨ (if x ∈ T then Q else F.owner x) = Q
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl (F.owner_eq_of_notMem_birthEnv hx)

/-- `T` and `E` are disjoint when `T` is owned by `P∘` and avoids every outer hole footprint. -/
theorem disjoint_birthEnv (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) : Disjoint T (F.birthEnv P) := by
  rw [Finset.disjoint_left]
  intro x hxT hxE
  rcases (F.mem_birthEnv).mp hxE with h | h
  · exact h (hTP x hxT)
  · exact Set.disjoint_left.mp hTH hxT h

/-- The ownership facts used by both directions of a homogeneous birth: when `T` is owned by `P∘`
and avoids every outer hole footprint, the sites outside `T ∪ E` are owned by `P∘` both before and
after `T` is handed to `Q∘`, the sites of `T` are owned by `Q∘` afterwards, and the owners on `E`
are unchanged.

Polynomial-PEPS manuscript, proof of Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 413–446. -/
theorem changeOwner_birth_owners (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) :
    (∀ x ∈ (T ∪ F.birthEnv P)ᶜ, F.owner x = P) ∧ (∀ x ∈ T, (F.changeOwner T Q).owner x = Q) ∧
      (∀ x ∈ (T ∪ F.birthEnv P)ᶜ, (F.changeOwner T Q).owner x = P) ∧
      ∀ x ∈ F.birthEnv P, (F.changeOwner T Q).owner x = F.owner x := by
  have hB : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, F.owner x = P := fun x hx =>
    F.owner_eq_of_notMem_birthEnv fun h => Finset.mem_compl.mp hx (Finset.mem_union_right _ h)
  refine ⟨hB, fun x hx => by simp only [hx, ↓reduceIte], fun x hx => ?_, fun x hx => ?_⟩
  · have hxT : x ∉ T := fun h => Finset.mem_compl.mp hx (Finset.mem_union_left _ h)
    simpa only [hxT, ↓reduceIte] using hB x hx
  · have hxT : x ∉ T := fun hT => Finset.disjoint_left.mp (F.disjoint_birthEnv hTP hTH) hT hx
    simp only [hxT, ↓reduceIte]

/-- **Lemma 6.5 (homogeneous birth).** In an encoded frame `F`, let `T` be a set of raw sites
owned by `P∘` and disjoint from every outer hole footprint, and let `E` and `U` be as in
`eq:birth-partition`. If `I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data
whose canonical map `B` is a Hermitian contraction, acting as the identity on `E` and on the
tags, with `(1 ⊗ B) K_F = K_{F'} B` for the frame `F'` in which `T` is owned by `Q∘`, and
`‖(1 ⊗ B) Ω_F - Ω_{F'}‖ ≤ L^{-30}`. Every register `B` acts on lies outside `E`, so it is owned
by `P∘` before the birth and by `P∘` or `Q∘` after it (`owner_eq_of_notMem_birthEnv`,
`changeOwner_owner_of_notMem_birthEnv`).

The frames `F` and `F'` differ only in raw owners, and the encoding and the reference vector do
not depend on raw owners (Definition 6.1, `05-frames.tex`, lines 71–82), so `K_{F'} = K_F` and
`Ω_{F'} = Ω_F`; the identity `(1 ⊗ B) K_F = K_{F'} B` says that `B` commutes with the encoding.
The change of owner from `P∘` to `Q∘` is the content of the bounded-change clause,
`Frame.birth_bounded`.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–407; proof lines
413–437. -/
theorem birth [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      (sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ).IsHermitian ∧
      ‖sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ‖ ≤ 1 ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * F.encoder =
        (F.changeOwner T Q).encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) (F.refVec Ω) -
        (F.changeOwner T Q).refVec Ω‖ ≤ L ^ (-30 : ℤ) := by
  set hTE := F.disjoint_birthEnv hTP hTH
  obtain ⟨σ, hσ⟩ := exists_sheetSplitting_zpow hTE hΩ hI
  have hcomm : ∀ t, Commute (sheetBirthOp hTE σ) (rawProd F.holes t) := fun t =>
    commute_sheetBirthOp hTE σ F.outerHoles_subset_birthEnv
      (rawProd_mem_supportedOperators F.holes t)
  refine ⟨σ, hσ, sheetBirthOp_isHermitian hTE σ, norm_sheetBirthOp_le_one hTE σ,
    one_kronecker_mul_frameEncoder hcomm, ?_⟩
  exact (norm_act_one_kronecker_refVec_sub_le F hcomm Ω).trans
    ((norm_act_sheetBirthOp_sub_le hTE σ Ω).trans hσ)

/-- **Lemma 6.5 (homogeneous death).** The reversed operation. Let `F` be the frame *after* the
death, in which `T` is owned by `P∘` and avoids every outer hole footprint, and let the frame
before the death be `F` with `T` owned by `Q∘`. If `I_Ω(T:E) ≤ L^{-60}` for `E` computed in `F`,
the same canonical map `B = Bᴴ`, now with the reverse input and output ownership, satisfies
`(1 ⊗ B) K_{F_before} = K_F B` and `‖(1 ⊗ B) Ω_{F_before} - Ω_F‖ ≤ L^{-30}`.

Since the encoding and the reference vector do not depend on raw owners, this is the statement of
`birth` read in the frame after the death; its content beyond `birth` is that the hypotheses,
and the set `E`, are those of the frame after the death (`05-frames.tex`, lines 407–410).

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 407–410; proof lines
439–446. -/
theorem death [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      (sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ).IsHermitian ∧
      ‖sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ‖ ≤ 1 ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * (F.changeOwner T Q).encoder =
        F.encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) ((F.changeOwner T Q).refVec Ω) -
        F.refVec Ω‖ ≤ L ^ (-30 : ℤ) :=
  F.birth (Q := Q) hTP hTH hΩ hI

end Frame

end FrameOwnership

end TNLean.PEPS.EncodedFrame
