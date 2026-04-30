/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Douglas factorization: range inclusion implies right factorization

This file states the easy algebraic half of Wolf's Douglas theorem in the
finite-dimensional matrix setting: if the range of `A` is contained in the range
of `B`, then `A = B * C` for some matrix `C`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 5.1][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix

namespace Douglas

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Finite-dimensional factorization form of the easy direction of Douglas' theorem:
range inclusion for `mulVec` implies a right factorization. -/
theorem factorization_of_range_mulVecLin_le
    {A B : Mat} (hAB : A.mulVecLin.range ≤ B.mulVecLin.range) :
    ∃ C : Mat, A = B * C := by
  classical
  have hcol : ∀ j : Fin D, ∃ c : Fin D → ℂ, B.mulVec c = A.col j := by
    intro j
    have hAj_mem : A.col j ∈ A.mulVecLin.range := by
      refine ⟨Pi.single j 1, ?_⟩
      change A.mulVec (Pi.single j 1) = A.col j
      exact Matrix.mulVec_single_one A j
    have hBj_mem : A.col j ∈ B.mulVecLin.range := hAB hAj_mem
    rcases hBj_mem with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [Matrix.mulVecLin_apply] using hc
  choose c hc using hcol
  let C : Mat := fun i j => c j i
  refine ⟨C, ?_⟩
  apply Matrix.ext_col
  intro j
  have hCcol : C.col j = c j := by
    ext i
    rfl
  calc
    A.col j = B.mulVec (c j) := by
      symm
      exact hc j
    _ = B.mulVec (C.col j) := by rw [hCcol]
    _ = B.mulVec (C.mulVec (Pi.single j 1)) := by
      rw [Matrix.mulVec_single_one]
    _ = (B * C).mulVec (Pi.single j 1) := by
      simpa using (Matrix.mulVec_mulVec (Pi.single j 1) B C)
    _ = (B * C).col j := by
      exact Matrix.mulVec_single_one (B * C) j

/-- User-facing vectorwise range-inclusion form of the easy direction of Douglas' theorem. -/
theorem factorization_of_forall_mulVec_mem_range
    {A B : Mat}
    (hAB : ∀ v : Fin D → ℂ, A.mulVec v ∈ B.mulVecLin.range) :
    ∃ C : Mat, A = B * C := by
  apply factorization_of_range_mulVecLin_le
  intro w hw
  rcases hw with ⟨v, rfl⟩
  simpa [Matrix.mulVecLin_apply] using hAB v

end Douglas
