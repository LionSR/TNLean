/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BlockingInfrastructure

/-!
# Block-to-letter translation of the boundary block matrix equation

The boundary-closing argument of
[Cirac--Perez-Garcia--Schuch--Verstraete 2021, arXiv:2011.12127, Section IV.C,
lines 2078--2079] reduces, after blocking \(L_0\) sites into one, to the
single-site windowed matrix equation already proved for the blocked tensor
`blockTensor A L₀`.  This file supplies the bookkeeping that turns that blocked
equation back into a statement about ordinary length-\(L_0\) and
length-\(L_0 K\) words of `A`.

`MPSTensor.block_matEq_of_blocked_matEq` takes the blocked matrix equation
\[
  X \, A^{w(b)} \, A^{\mathrm{flatten}(w(c_b))}
  =
  A^{w(b)} \, Y_{c_b},
\]
where \(b\) is a single block letter and \(c_b\) is an iterated block index of the
complement, and produces the block matrix equation in the shape consumed by
`MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_block_matEq` (the "L2"
step), with the head ranging over every length-\(L_0\) word and the complement
over every length-\(L_0 K\) word.

The head realization uses `blockIndexOfList` / `wordOfBlock_blockIndexOfList`;
the complement grouping uses `directToIteratedBlockIndex` /
`flattenBlockedWord_wordOfBlock_directToIteratedBlockIndex`.

This is a step of the boundary-closing decomposition for the normal
range-reduction argument; see `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`
and the tracking issue for the remaining boundary-closing obligation.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2021] arXiv:2011.12127,
  Section IV.C, lines 2078--2079
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- **Block-to-letter translation of the boundary block matrix equation.**

Suppose the blocked tensor satisfies, for every single block letter `b` and every
iterated block index `cb` of the complement,
\[
  X \, A^{w(b)} \, A^{\mathrm{flatten}(w(c_b))} = A^{w(b)} \, Y_{c_b},
\]
where `w(b)` is the length-\(L_0\) word of `b` and `flatten (w(cb))` is the
length-\(L_0 K\) complement word.  Then there is a complement-indexed family `Y`
for which the block matrix equation
\[
  X \, A^{\sigma_{\mathrm{tail}}} \, A^{\sigma_{\mathrm{comp}}}
  = A^{\sigma_{\mathrm{tail}}} \, Y_{\sigma_{\mathrm{comp}}}
\]
holds for *every* length-\(L_0\) head word `σ_tail` and *every* length-\(L_0 K\)
complement word `σ_comp`.

The head word is realized as a single block letter through `blockIndexOfList`, and
the complement word is grouped into `K` blocks through `directToIteratedBlockIndex`;
both round-trip through `wordOfBlock`/`flattenBlockedWord`.  The resulting equation
is in the exact shape consumed by
`boundary_matrix_commutes_of_isNBlkInjective_of_block_matEq`. -/
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
  -- Realize the head `s` as a single block letter `b`.
  set b : Fin (blockPhysDim d L₀) :=
    blockIndexOfList d L₀ (List.ofFn s) (by simp) with hb
  have hbword : wordOfBlock d L₀ b = List.ofFn s := by
    rw [hb]; exact wordOfBlock_blockIndexOfList d L₀ (List.ofFn s) (by simp)
  -- Realize the complement `c` as a grouped iterated block index `cb`.
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
