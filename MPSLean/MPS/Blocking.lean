/-
Copyright (c) 2026 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.MPS.Defs

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin


open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Blocked physical dimension: the number of length-`L` words over an alphabet of size `d`.

We implement this as `Fintype.card (Fin L → Fin d)` to avoid painful casts. -/
noncomputable def blockPhysDim (d L : ℕ) : ℕ :=
  Fintype.card (Fin L → Fin d)

lemma blockPhysDim_eq_pow (d L : ℕ) : blockPhysDim d L = d ^ L := by
  classical
  unfold blockPhysDim
  -- `Fintype.card_fun` gives `card (α → β) = card β ^ card α`.
  simp [Fintype.card_fin]

/-- Decode a blocked physical index into the corresponding length-`L` word. -/
noncomputable def decodeBlock (d L : ℕ) : Fin (blockPhysDim d L) → (Fin L → Fin d) :=
  (Fintype.equivFin (Fin L → Fin d)).symm

/-- Turn a blocked physical index into a list (word) of length `L`. -/
noncomputable def wordOfBlock (d L : ℕ) (i : Fin (blockPhysDim d L)) : List (Fin d) :=
  List.ofFn (decodeBlock d L i)

@[simp] lemma length_wordOfBlock (d L : ℕ) (i : Fin (blockPhysDim d L)) :
    (wordOfBlock d L i).length = L := by
  classical
  simp [wordOfBlock]

/-- Block (coarse-grain) an MPS tensor by grouping `L` physical sites into one. -/
noncomputable def blockTensor (A : MPSTensor d D) (L : ℕ) :
    MPSTensor (blockPhysDim d L) D :=
  fun i => evalWord A (wordOfBlock d L i)

/-- Flatten a word in blocked indices into an ordinary word in `Fin d` (list-level). -/
noncomputable def flattenBlockedWord (d L : ℕ) : List (Fin (blockPhysDim d L)) → List (Fin d)
  | w => (w.map (wordOfBlock d L)).flatten

@[simp] lemma flattenBlockedWord_nil (d L : ℕ) : flattenBlockedWord d L [] = [] := by
  simp [flattenBlockedWord]

lemma flattenBlockedWord_cons (d L : ℕ) (i : Fin (blockPhysDim d L))
    (w : List (Fin (blockPhysDim d L))) :
    flattenBlockedWord d L (i :: w) = wordOfBlock d L i ++ flattenBlockedWord d L w := by
  simp [flattenBlockedWord]

lemma evalWord_blockTensor (A : MPSTensor d D) (L : ℕ) :
    ∀ w : List (Fin (blockPhysDim d L)),
      evalWord (blockTensor (d := d) (D := D) A L) w =
        evalWord A (flattenBlockedWord d L w) := by
  intro w
  induction w with
  | nil =>
      simp [flattenBlockedWord, evalWord]
  | cons i w ih =>
      -- Flattening splits off the first block word:
      -- `flattenBlockedWord (i :: w) = wordOfBlock i ++ flattenBlockedWord w`.
      simp [evalWord, blockTensor, flattenBlockedWord_cons, ih, evalWord_append]

/-- Length of a flattened blocked word. -/
lemma length_flattenBlockedWord (d L : ℕ) :
    ∀ w : List (Fin (blockPhysDim d L)), (flattenBlockedWord d L w).length = w.length * L := by
  intro w
  induction w with
  | nil =>
      simp [flattenBlockedWord]
  | cons i w ih =>
      -- Flattening splits off the first block word.
      simp [flattenBlockedWord_cons, ih, length_wordOfBlock,
        Nat.succ_mul, Nat.add_comm]

lemma mpv_blockTensor_eq_mpv (A : MPSTensor d D) (L N : ℕ)
    (σ : Fin N → Fin (blockPhysDim d L)) :
    ∃ σflat : Fin (N * L) → Fin d,
      mpv (blockTensor (d := d) (D := D) A L) σ = mpv A σflat := by
  classical
  -- Flatten the blocked word `List.ofFn σ`.
  set flat : List (Fin d) := flattenBlockedWord d L (List.ofFn σ) with flat_def
  have hlen : flat.length = N * L := by
    -- Use the general length lemma together with `length_ofFn`.
    simpa [flat_def] using (length_flattenBlockedWord (d := d) (L := L) (List.ofFn σ))
  -- Read off elements of `flat` to build a configuration of length `N * L`.
  set σflat : Fin (N * L) → Fin d :=
    fun i => flat.get (Fin.cast hlen.symm i) with σflat_def
  -- `List.ofFn σflat` reconstructs `flat`.
  have hofFn : List.ofFn σflat = flat := by
    rw [σflat_def]
    -- Rewrite `flat` as a `List.ofFn` over its `get` function.
    conv_rhs => rw [← List.ofFn_get flat]
    -- Now cast the domain of the `ofFn` on the LHS to match `flat.length`.
    have hcongr := (List.ofFn_congr (m := N * L) (n := flat.length) hlen.symm
      (fun i : Fin (N * L) => flat.get (Fin.cast hlen.symm i)))
    -- Simplify the casted index.
    -- The RHS becomes `List.ofFn flat.get`.
    simpa [Function.comp, Fin.cast_cast] using hcongr
  refine ⟨σflat, ?_⟩
  -- Expand `mpv` and use the `evalWord` compatibility lemma.
  simp only [mpv, coeff]
  -- Convert the blocked evalWord to a flattened evalWord.
  -- Then use `hofFn` to rewrite `List.ofFn σflat` to `flat`.
  simp [hofFn, flat_def, evalWord_blockTensor]

/-- Physical blocking preserves the `SameMPV` relation. -/
theorem SameMPV.blockTensor {A B : MPSTensor d D} (hSame : SameMPV A B) (L : ℕ) :
    SameMPV (MPSTensor.blockTensor (d := d) (D := D) A L)
      (MPSTensor.blockTensor (d := d) (D := D) B L) := by
  intro N σ
  classical
  -- Use the same flattened configuration for both tensors.
  set flat : List (Fin d) := flattenBlockedWord d L (List.ofFn σ) with flat_def
  have hlen : flat.length = N * L := by
    simpa [flat_def] using (length_flattenBlockedWord (d := d) (L := L) (List.ofFn σ))
  set σflat : Fin (N * L) → Fin d :=
    fun i => flat.get (Fin.cast hlen.symm i) with σflat_def
  have hofFn : List.ofFn σflat = flat := by
    rw [σflat_def]
    conv_rhs => rw [← List.ofFn_get flat]
    have hcongr :=
      (List.ofFn_congr (m := N * L) (n := flat.length) hlen.symm
        (fun i : Fin (N * L) => flat.get (Fin.cast hlen.symm i)))
    simpa [Function.comp, Fin.cast_cast] using hcongr
  have hblock (T : MPSTensor d D) :
      mpv (MPSTensor.blockTensor (d := d) (D := D) T L) σ = mpv T σflat := by
    simp [mpv, coeff, hofFn, flat_def, evalWord_blockTensor]
  calc
    mpv (MPSTensor.blockTensor (d := d) (D := D) A L) σ = mpv A σflat := hblock A
    _ = mpv B σflat := hSame (N * L) σflat
    _ = mpv (MPSTensor.blockTensor (d := d) (D := D) B L) σ := (hblock B).symm

end MPSTensor
