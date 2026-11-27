/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.Tensor.Physical.PhysicalRotation
import QICLean.Kraus.BlockedConfiguration
import QICLean.Kraus.BlockingTransfer

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.BigOperators

/-!
# Physical blocking of matrix product tensors

The blocked alphabet, the blocked family, and the word and blocking identities
of a finite matrix family are the declarations of the `Kraus` namespace
(`Kraus.blockPhysDim`, `Kraus.blockTensor`, `Kraus.evalWord_blockTensor`, and
their companions). This file holds what is specific to matrix product tensors:
Kronecker lifts of physical operators, configuration equivalences, canonical
normalization, and matrix-product-vector statements.
-/

open MPTensor

open scoped Matrix
open Kraus (blockPhysDim blockPhysDim_eq_pow singleBlockEquiv decodeBlock wordOfBlock
  decodeBlockEquiv decodeBlock_decodeBlockEquiv_symm blockTensor flattenBlockedWord
  evalWord_blockTensor length_flattenBlockedWord)

namespace MPSTensor

variable {d D L : ℕ}

/-- Fixed-length injectivity persists at positive multiples of the length. -/
theorem _root_.MPTensor.isNBlkInjective_mul_of_isNBlkInjective {α : Type*}
    (A : MPTensor α (Fin D)) {N m : ℕ} (hm : 0 < m) (hN : Kraus.IsNBlkInjective A N) :
    Kraus.IsNBlkInjective A (m * N) := by
  -- Use word-span factorization here rather than importing the higher-level
  -- Wielandt theorem `Kraus.wordSpan_top_of_mul` into basic blocking.
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · simpa [hm0] using hN
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have hih : Kraus.wordSpan A (m * N) = ⊤ := ih hm_pos
        rw [Nat.succ_mul]
        change Kraus.wordSpan A (m * N + N) = ⊤
        rw [Kraus.wordSpan_add, hih, hN]
        apply eq_top_iff.mpr
        intro M _
        simpa using
          (Submodule.mul_mem_mul
            (show M ∈ (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) from
              Submodule.mem_top)
            (show (1 : Matrix (Fin D) (Fin D) ℂ) ∈
                (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) from
              Submodule.mem_top))

/-! ### The Kronecker-power lift of a physical-index operator through blocking

For a physical-index operator `P` on `Fin d`, the blocked operator `blockKron`
acts on the blocked physical index `Fin (blockPhysDim d L)` by the entrywise
product of `P` over the `L` decoded sites.  This is the operator that makes
blocking commute with physical twisting. -/

section KroneckerLift

variable {m n p : ℕ}

/-- The Kronecker-power lift of a physical-index map `P : ℂⁿ → ℂᵐ` through length-`L`
blocking: `(blockKron P) I J = ∏ k, P (decode I k) (decode J k)`.  The map may be
rectangular, as for the layers `(V⁽ʲ⁾)^{⊗2^{k-j}}` of arXiv:2307.01696, eq. (16). -/
noncomputable def blockKron (L : ℕ) (P : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin (blockPhysDim m L)) (Fin (blockPhysDim n L)) ℂ :=
  fun I J => ∏ k : Fin L, P (decodeBlock m L I k) (decodeBlock n L J k)

/-- The Kronecker lift is multiplicative: `blockKron L (P * Q) = blockKron L P *
blockKron L Q`.  Summing over the intermediate blocked index is summing over
length-`L` words, and the product distributes site by site. -/
lemma blockKron_mul (L : ℕ) (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin p) ℂ) :
    blockKron L (P * Q) = blockKron L P * blockKron L Q := by
  classical
  ext I J
  simp only [blockKron, Matrix.mul_apply]
  -- Sum over the intermediate blocked index = sum over words.
  rw [← Equiv.sum_comp (decodeBlockEquiv n L).symm
    (fun K => (∏ k : Fin L, P (decodeBlock m L I k) (decodeBlock n L K k)) *
      ∏ k : Fin L, Q (decodeBlock n L K k) (decodeBlock p L J k))]
  simp only [decodeBlock_decodeBlockEquiv_symm]
  -- Distribute the product over the sum of words.
  rw [Finset.prod_univ_sum (t := fun _ : Fin L => (Finset.univ : Finset (Fin n)))
    (f := fun (k : Fin L) (a : Fin n) =>
      P (decodeBlock m L I k) a * Q a (decodeBlock p L J k)),
    Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.prod_mul_distrib]

/-- The Kronecker lift of the identity is the identity. -/
lemma blockKron_one (L : ℕ) :
    blockKron L (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  classical
  ext I J
  simp only [blockKron, Matrix.one_apply]
  by_cases hIJ : I = J
  · simp [hIJ]
  · rw [ite_eq_right hIJ]
    -- Some site differs, contributing a zero factor.
    have : ∃ k : Fin L, decodeBlock d L I k ≠ decodeBlock d L J k := by
      by_contra hcon
      rw [not_exists] at hcon
      exact hIJ ((decodeBlockEquiv d L).injective (funext fun k => not_not.1 (hcon k)))
    obtain ⟨k, hk⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ k) (Matrix.one_apply_ne hk)

/-- The Kronecker lift commutes with the conjugate transpose:
`(blockKron L P)ᴴ = blockKron L (Pᴴ)`. -/
lemma blockKron_conjTranspose (L : ℕ) (P : Matrix (Fin m) (Fin n) ℂ) :
    (blockKron L P)ᴴ = blockKron L Pᴴ := by
  ext I J
  simp only [Matrix.conjTranspose_apply, blockKron, star_prod]

/-- The Kronecker power preserves unitarity: if `P * Pᴴ = 1` then
`blockKron L P * (blockKron L P)ᴴ = 1`. -/
lemma blockKron_mul_conjTranspose (L : ℕ) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P * Pᴴ = 1) :
    blockKron L P * (blockKron L P)ᴴ = 1 := by
  rw [blockKron_conjTranspose, ← blockKron_mul, hP, blockKron_one]

/-- **Blocking commutes with physical maps**: blocking `W · C` over `L` sites gives
`W^{⊗L}` applied to `C` blocked over `L` sites.

arXiv:2307.01696, eq. (16): the layer `(V⁽ʲ⁾)^{⊗2^{k-j}}` acts sitewise on the regrouped
block. -/
theorem blockTensor_rotatePhysical (W : Matrix (Fin m) (Fin n) ℂ) (C : MPSTensor n D)
    (L : ℕ) :
    blockTensor (rotatePhysical W C) L =
      rotatePhysical (blockKron L W) (blockTensor C L) := by
  classical
  funext I
  change Kraus.evalWord (rotatePhysical W C) (List.ofFn (decodeBlock m L I)) = _
  rw [evalWord_rotatePhysical_ofFn, rotatePhysical_apply]
  exact (Fintype.sum_equiv (decodeBlockEquiv n L) _ _ fun J => rfl).symm

end KroneckerLift

/-- Right-canonical normalization propagates from letters to words of any fixed length.

If
\[
  \sum_a A_aA_a^\dagger=I,
\]
then the same equation holds after replacing letters by words of length \(L\):
\[
  \sum_\rho A_\rho A_\rho^\dagger=I.
\]
This is the iterated form of the normalization used in arXiv:quant-ph/0608197,
Theorem 12, proof line 1450. -/
theorem sum_evalWord_mul_conjTranspose_evalWord
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hRight : ∑ i : Fin d, A i * (A i)ᴴ = 1) :
    ∀ L : ℕ,
      ∑ ρ : Fin L → Fin d,
        Kraus.evalWord A (List.ofFn ρ) * (Kraus.evalWord A (List.ofFn ρ))ᴴ = 1 := by
  classical
  intro L
  let Aadj : Fin d → Matrix (Fin D) (Fin D) ℂ := fun i => (A i)ᴴ
  have hLeft : ∑ i : Fin d, (Aadj i)ᴴ * Aadj i = 1 := by
    simpa [Aadj] using hRight
  let revEquiv : (Fin L → Fin d) ≃ (Fin L → Fin d) :=
    Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin d))
  calc
    ∑ ρ : Fin L → Fin d,
        Kraus.evalWord A (List.ofFn ρ) * (Kraus.evalWord A (List.ofFn ρ))ᴴ
      = ∑ ρ : Fin L → Fin d,
          (Kraus.evalWord Aadj (List.ofFn (revEquiv ρ)))ᴴ *
            Kraus.evalWord Aadj (List.ofFn (revEquiv ρ)) := by
            refine Finset.sum_congr rfl ?_
            intro ρ _
            have hword :
                List.ofFn (revEquiv ρ) = (List.ofFn ρ).reverse := by
              simpa [revEquiv, Equiv.arrowCongr, Function.comp_def] using
                (List.ofFn_reverse ρ).symm
            have hAdjEval :
                (Kraus.evalWord Aadj (List.ofFn (revEquiv ρ)))ᴴ =
                  Kraus.evalWord A (List.ofFn ρ) := by
              simpa [Aadj, hword] using
                Kraus.evalWord_conjTranspose (A := fun i => (A i)ᴴ)
                  (List.ofFn (revEquiv ρ))
            have hEvalAdj :
                Kraus.evalWord Aadj (List.ofFn (revEquiv ρ)) =
                  (Kraus.evalWord A (List.ofFn ρ))ᴴ := by
              simpa using congrArg Matrix.conjTranspose hAdjEval
            rw [hAdjEval, hEvalAdj]
    _ = ∑ ρ : Fin L → Fin d,
          (Kraus.evalWord Aadj (List.ofFn ρ))ᴴ * Kraus.evalWord Aadj (List.ofFn ρ) := by
          simpa [revEquiv] using
            (Fintype.sum_equiv revEquiv
              (f := fun ρ : Fin L → Fin d =>
                (Kraus.evalWord Aadj (List.ofFn (revEquiv ρ)))ᴴ *
                  Kraus.evalWord Aadj (List.ofFn (revEquiv ρ)))
              (g := fun ρ : Fin L → Fin d =>
                (Kraus.evalWord Aadj (List.ofFn ρ))ᴴ * Kraus.evalWord Aadj (List.ofFn ρ))
              (by intro ρ; rfl))
    _ = 1 := Kraus.sum_evalWord_conjTranspose_mul_evalWord Aadj hLeft L

variable {d D : ℕ}

@[simp] lemma mpv_blockTensor_one (A : MPSTensor d D) {N : ℕ}
    (σ : Fin N → Fin (blockPhysDim d 1)) :
    mpv (blockTensor (d := d) (n := Fin D) A 1) σ =
      mpv A (fun n => singleBlockEquiv d (σ n)) := by
  simp [mpv, coeff, evalWord_blockTensor, List.map_ofFn]
  rfl

/-- Physical blocking preserves the `SameMPV` relation. -/
theorem _root_.MPTensor.SameMPV.blockTensor {A B : MPSTensor d D} (hSame : SameMPV A B) (L : ℕ) :
    SameMPV (Kraus.blockTensor (d := d) (n := Fin D) A L)
      (Kraus.blockTensor (d := d) (n := Fin D) B L) := by
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
      mpv (Kraus.blockTensor (d := d) (n := Fin D) T L) σ = mpv T σflat := by
    simp [mpv, coeff, hofFn, flat_def, evalWord_blockTensor]
  calc
    mpv (Kraus.blockTensor (d := d) (n := Fin D) A L) σ = mpv A σflat := hblock A
    _ = mpv B σflat := hSame (N * L) σflat
    _ = mpv (Kraus.blockTensor (d := d) (n := Fin D) B L) σ := (hblock B).symm

end MPSTensor
