/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BlockingInfrastructure

/-!
# Block-to-letter translation of the boundary block matrix equation

After blocking \(L_0\) sites into one, the comparison used when closing the
periodic boundary in [Cirac--Perez-Garcia--Schuch--Verstraete 2021,
arXiv:2011.12127, Section IV.C, lines 2078--2079] reduces to the single-site
matrix identity for the blocked tensor \(A^{[L_0]}\). The result transports the
blocked matrix identity to ordinary length-\(L_0\) and length-\(L_0 K\) word
products of \(A\).

Starting from the blocked matrix equation
\[
  X \, A^{w(b)} \, A^{\mathrm{flatten}(w(c_b))}
  =
  A^{w(b)} \, Y_{c_b},
\]
where \(b\) is a single block letter and \(c_b\) is an iterated block index of the
complement, the result gives the block matrix equation used by the
boundary-matrix commutation lemma from the coordinate comparison, with the first
factor ranging over every length-\(L_0\) word and the complement over every
length-\(L_0K\) word.

The proof sends each length-\(L_0\) word \(s\) to its canonical block letter in
\(\mathrm{Fin}(d^{L_0})\) and regroups each length-\(L_0 K\) complement word \(c\)
through the isomorphism \(\mathrm{Fin}(d^{L_0 K}) \cong (\mathrm{Fin}(d^{L_0}))^K\),
both invertible by the blocking round-trip lemmas.

This is the block-to-word form of the comparison used when closing the periodic
boundary in the normal range-reduction argument; see
docs/paper-gaps/cpgsv21_normal_range_reduction.tex for the remaining
comparison at the periodic boundary.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2021] arXiv:2011.12127,
  Section IV.C, lines 2078--2079
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- **Block-to-letter translation of the boundary block matrix equation.**

Suppose the blocked tensor satisfies, for every single block letter \(b\) and
every iterated block index \(c_b\) of the complement,
\[
  X \, A^{w(b)} \, A^{\mathrm{flatten}(w(c_b))} = A^{w(b)} \, Y_{c_b},
\]
where \(w(b)\) is the length-\(L_0\) word of \(b\) and \(\widetilde{w(c_b)}\) is the
length-\(L_0 K\) complement word obtained by concatenating the blocks of \(c_b\).
Then there is a complement-indexed family \(Y\)
for which the block matrix equation
\[
  X \, A^{\sigma_{\mathrm{tail}}} \, A^{\sigma_{\mathrm{comp}}}
  = A^{\sigma_{\mathrm{tail}}} \, Y_{\sigma_{\mathrm{comp}}}
\]
holds for *every* length-\(L_0\) head word \(\sigma_{\mathrm{tail}}\) and *every*
length-\(L_0 K\) complement word \(\sigma_{\mathrm{comp}}\).

The conclusion is the block matrix equation used by the boundary-matrix
commutation step. -/
theorem block_matEq_of_blocked_matEq
    {A : MPSTensor d D} {L₀ Kb : ℕ}
    {X : Matrix (Fin D) (Fin D) ℂ}
    (YB : Fin (blockPhysDim (blockPhysDim d L₀) Kb) → Matrix (Fin D) (Fin D) ℂ)
    (hBlk : ∀ (b : Fin (blockPhysDim d L₀))
        (cb : Fin (blockPhysDim (blockPhysDim d L₀) Kb)),
      X * evalWord A (wordOfBlock d L₀ b)
          * evalWord A (flattenBlockedWord d L₀ (wordOfBlock (blockPhysDim d L₀) Kb cb))
        = evalWord A (wordOfBlock d L₀ b) * YB cb) :
    ∃ Y : (Fin (L₀ * Kb) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (s : Fin L₀ → Fin d) (c : Fin (L₀ * Kb) → Fin d),
        X * evalWord A (List.ofFn s) * evalWord A (List.ofFn c)
          = evalWord A (List.ofFn s) * Y c := by
  refine ⟨fun c =>
    YB (directToIteratedBlockIndex d L₀ Kb
      (blockIndexOfList d (L₀ * Kb) (List.ofFn c) (by simp))), ?_⟩
  intro s c
  -- Regard the head word as a single block letter.
  set b : Fin (blockPhysDim d L₀) :=
    blockIndexOfList d L₀ (List.ofFn s) (by simp) with hb
  have hbword : wordOfBlock d L₀ b = List.ofFn s := by
    rw [hb]; exact wordOfBlock_blockIndexOfList d L₀ (List.ofFn s) (by simp)
  -- Regard the complement word as a grouped iterated block index.
  set i : Fin (blockPhysDim d (L₀ * Kb)) :=
    blockIndexOfList d (L₀ * Kb) (List.ofFn c) (by simp) with hi
  set cb : Fin (blockPhysDim (blockPhysDim d L₀) Kb) :=
    directToIteratedBlockIndex d L₀ Kb i with hcb
  have hcword :
      flattenBlockedWord d L₀ (wordOfBlock (blockPhysDim d L₀) Kb cb) = List.ofFn c := by
    rw [hcb, flattenBlockedWord_wordOfBlock_directToIteratedBlockIndex, hi]
    exact wordOfBlock_blockIndexOfList d (L₀ * Kb) (List.ofFn c) (by simp)
  have hmain := hBlk b cb
  rw [hbword, hcword] at hmain
  simpa [hb, hi, hcb] using hmain

end MPSTensor
