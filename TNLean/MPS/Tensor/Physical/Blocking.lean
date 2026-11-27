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

Blocking `L` sites is `Kraus.block A L`, the family indexed by the words `Fin L → α`; the
word and configuration identities of a blocked family are `Kraus.evalWord_block` and
`Kraus.ofFn_blockConfigEquiv`. This file holds what is specific to matrix product tensors:
Kronecker lifts of physical operators, canonical normalization, and matrix-product-vector
statements.
-/

open MPTensor

open scoped Matrix

namespace MPSTensor

variable {α : Type*} {D L : ℕ}

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

For a physical-index operator `P` from `β` to `α`, the blocked operator `blockKron` acts on
the blocked physical index `Fin L → α` by the entrywise product of `P` over the `L` sites.
This is the operator that makes blocking commute with physical twisting. -/

section KroneckerLift

variable {β γ : Type*}

/-- The Kronecker-power lift of a physical-index map `P : ℂ^β → ℂ^α` through length-`L`
blocking: `(blockKron P) I J = ∏ k, P (I k) (J k)`.  The map may be rectangular, as for the
layers `(V⁽ʲ⁾)^{⊗2^{k-j}}` of arXiv:2307.01696, eq. (16). -/
def blockKron (L : ℕ) (P : Matrix α β ℂ) : Matrix (Fin L → α) (Fin L → β) ℂ :=
  fun I J => ∏ k : Fin L, P (I k) (J k)

@[simp] lemma blockKron_apply (L : ℕ) (P : Matrix α β ℂ) (I : Fin L → α) (J : Fin L → β) :
    blockKron L P I J = ∏ k : Fin L, P (I k) (J k) := rfl

/-- The Kronecker lift is multiplicative: `blockKron L (P * Q) = blockKron L P *
blockKron L Q`.  Summing over the intermediate blocked index is summing over
length-`L` words, and the product distributes site by site. -/
lemma blockKron_mul [Fintype β] [DecidableEq β] (L : ℕ) (P : Matrix α β ℂ)
    (Q : Matrix β γ ℂ) :
    blockKron L (P * Q) = blockKron L P * blockKron L Q := by
  ext I J
  simp only [blockKron, Matrix.mul_apply]
  rw [Finset.prod_univ_sum (t := fun _ : Fin L => (Finset.univ : Finset β))
    (f := fun (k : Fin L) (a : β) => P (I k) a * Q a (J k)), Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun w _ => Finset.prod_mul_distrib

/-- The Kronecker lift of the identity is the identity. -/
lemma blockKron_one [DecidableEq α] (L : ℕ) :
    blockKron L (1 : Matrix α α ℂ) = 1 := by
  ext I J
  simp only [blockKron, Matrix.one_apply]
  by_cases hIJ : I = J
  · simp [hIJ]
  · rw [ite_eq_right hIJ]
    -- Some site differs, contributing a zero factor.
    obtain ⟨k, hk⟩ : ∃ k : Fin L, I k ≠ J k := Function.ne_iff.mp hIJ
    exact Finset.prod_eq_zero (Finset.mem_univ k) (Matrix.one_apply_ne hk)

/-- The Kronecker lift commutes with the conjugate transpose:
`(blockKron L P)ᴴ = blockKron L (Pᴴ)`. -/
lemma blockKron_conjTranspose (L : ℕ) (P : Matrix α β ℂ) :
    (blockKron L P)ᴴ = blockKron L Pᴴ := by
  ext I J
  simp only [Matrix.conjTranspose_apply, blockKron, star_prod]

/-- The Kronecker power preserves unitarity: if `P * Pᴴ = 1` then
`blockKron L P * (blockKron L P)ᴴ = 1`. -/
lemma blockKron_mul_conjTranspose [Fintype α] [DecidableEq α] (L : ℕ) (P : Matrix α α ℂ)
    (hP : P * Pᴴ = 1) :
    blockKron L P * (blockKron L P)ᴴ = 1 := by
  rw [blockKron_conjTranspose, ← blockKron_mul, hP, blockKron_one]

/-- **Blocking commutes with physical maps**: blocking `W · C` over `L` sites gives
`W^{⊗L}` applied to `C` blocked over `L` sites.

arXiv:2307.01696, eq. (16): the layer `(V⁽ʲ⁾)^{⊗2^{k-j}}` acts sitewise on the regrouped
block. -/
theorem block_rotatePhysical [Fintype β] (W : Matrix α β ℂ) (C : MPTensor β (Fin D))
    (L : ℕ) :
    Kraus.block (rotatePhysical W C) L =
      rotatePhysical (blockKron L W) (Kraus.block C L) := by
  funext I
  rw [Kraus.block_apply, evalWord_rotatePhysical_ofFn]
  rfl

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
    [Fintype α] (A : α → Matrix (Fin D) (Fin D) ℂ)
    (hRight : ∑ i : α, A i * (A i)ᴴ = 1) :
    ∀ L : ℕ,
      ∑ ρ : Fin L → α,
        Kraus.evalWord A (List.ofFn ρ) * (Kraus.evalWord A (List.ofFn ρ))ᴴ = 1 := by
  classical
  intro L
  let Aadj : α → Matrix (Fin D) (Fin D) ℂ := fun i => (A i)ᴴ
  have hLeft : ∑ i : α, (Aadj i)ᴴ * Aadj i = 1 := by
    simpa [Aadj] using hRight
  let revEquiv : (Fin L → α) ≃ (Fin L → α) :=
    Equiv.arrowCongr Fin.revPerm (Equiv.refl α)
  calc
    ∑ ρ : Fin L → α,
        Kraus.evalWord A (List.ofFn ρ) * (Kraus.evalWord A (List.ofFn ρ))ᴴ
      = ∑ ρ : Fin L → α,
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
    _ = ∑ ρ : Fin L → α,
          (Kraus.evalWord Aadj (List.ofFn ρ))ᴴ * Kraus.evalWord Aadj (List.ofFn ρ) := by
          simpa [revEquiv] using
            (Fintype.sum_equiv revEquiv
              (f := fun ρ : Fin L → α =>
                (Kraus.evalWord Aadj (List.ofFn (revEquiv ρ)))ᴴ *
                  Kraus.evalWord Aadj (List.ofFn (revEquiv ρ)))
              (g := fun ρ : Fin L → α =>
                (Kraus.evalWord Aadj (List.ofFn ρ))ᴴ * Kraus.evalWord Aadj (List.ofFn ρ))
              (by intro ρ; rfl))
    _ = 1 := Kraus.sum_evalWord_conjTranspose_mul_evalWord Aadj hLeft L

/-- Blocking one site reads every block as its single letter. -/
@[simp] lemma mpv_block_one (A : MPTensor α (Fin D)) {N : ℕ} (σ : Fin N → Fin 1 → α) :
    mpv (Kraus.block A 1) σ = mpv A (fun n => σ n 0) := by
  simp only [mpv, coeff, Kraus.evalWord_block]
  congr 2
  induction N with
  | zero => rfl
  | succ N ih => simp [List.ofFn_succ, ih (fun n => σ n.succ)]

/-- Physical blocking preserves the `SameMPV` relation. -/
theorem _root_.MPTensor.SameMPV.block {A B : MPTensor α (Fin D)} (hSame : SameMPV A B)
    (L : ℕ) : SameMPV (Kraus.block A L) (Kraus.block B L) := by
  intro N σ
  have hblock (T : MPTensor α (Fin D)) :
      mpv (Kraus.block T L) σ = mpv T (Kraus.blockConfigEquiv α N L σ) := by
    simp only [mpv, coeff, Kraus.evalWord_block, Kraus.ofFn_blockConfigEquiv]
  rw [hblock, hblock, hSame]

end MPSTensor
