/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.VirtualSandwich
import TNLean.MPS.MPU.SimpleSupportCompression
import TNLean.MPS.MPDO.BondSimilarity
import TNLean.MPS.MPDO.PhysicalBlocking

/-!
# Bond similarities, blocking and simplicity

For square matrices `A` and `B` with `B * A = 1` (hence also `A * B = 1`), the
virtual sandwich `U ↦ A U B` is a bond similarity. This file shows that it

* commutes with physical blocking: the blocked letters of `A U B` are
  `A (U^{i₁j₁} ⋯ U^{i_Lj_L}) B`, by telescoping `B * A = 1`;
* preserves and reflects simplicity;
* preserves the MPU property, since it leaves every periodic operator unchanged;
* preserves the two source-cut ranks of every blocking.

Each statement has a corollary for `A = X` and `B = X⁻¹` with `X : GL (Fin D) ℂ`.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Proposition IV.5,
  lines 773--804 (the treatment of similarities of the bond space).
* MPU programme notes, milestone M-D (`MD.tex`), Lemma 1.2.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Word evaluation of a bond similarity is the similarity of the word evaluation.
The empty word uses `A * B = 1`, which follows from `B * A = 1` for square matrices.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem evalWord_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin D) ℂ) (hBA : B * A = 1) :
    ∀ is js : List (Fin d),
      evalWord (virtualSandwich A U B) is js = A * evalWord U is js * B
  | [], [] => by simp [mul_eq_one_comm.mp hBA]
  | [], _ :: _ => by simp [evalWord]
  | _ :: _, [] => by simp [evalWord]
  | i :: is, j :: js => by
    rw [evalWord_cons, evalWord_cons, evalWord_virtualSandwich A U B hBA is js,
      virtualSandwich_apply]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]

/-- Blocking commutes with a bond similarity: `(A U B)_L = A U_L B` for every `L`,
including `L = 0`.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem blockTensor_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin D) ℂ) (hBA : B * A = 1) (L : ℕ) :
    blockTensor (virtualSandwich A U B) L = virtualSandwich A (blockTensor U L) B := by
  funext i j
  simp only [blockTensor_apply, virtualSandwich_apply]
  exact evalWord_virtualSandwich A U B hBA _ _

/-- Blocking commutes with the similarity by an invertible matrix `X`.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem blockTensor_virtualSandwich_gl (X : GL (Fin D) ℂ) (U : MPOTensor d D) (L : ℕ) :
    blockTensor (virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) L =
      virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) (blockTensor U L)
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
  blockTensor_virtualSandwich _ U _ (Units.inv_mul X) L

/-- A bond similarity preserves simplicity.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem IsMPUSimple.virtualSandwich {U : MPOTensor d D} (hU : IsMPUSimple U)
    (A B : Matrix (Fin D) (Fin D) ℂ) (hBA : B * A = 1) :
    IsMPUSimple (virtualSandwich A U B) :=
  hU.rectangularSandwich A B hBA

/-- A bond similarity preserves and reflects simplicity.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem isMPUSimple_virtualSandwich_iff {U : MPOTensor d D}
    (A B : Matrix (Fin D) (Fin D) ℂ) (hBA : B * A = 1) :
    IsMPUSimple (virtualSandwich A U B) ↔ IsMPUSimple U :=
  ⟨isMPUSimple_of_rectangularSandwich U A B hBA, fun hU ↦ hU.virtualSandwich A B hBA⟩

/-- The similarity by an invertible matrix `X` preserves simplicity.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem IsMPUSimple.virtualSandwich_gl {U : MPOTensor d D} (hU : IsMPUSimple U)
    (X : GL (Fin D) ℂ) :
    IsMPUSimple (MPOTensor.virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :=
  hU.virtualSandwich _ _ (Units.inv_mul X)

/-- The similarity by an invertible matrix `X` preserves and reflects simplicity.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem isMPUSimple_virtualSandwich_gl_iff {U : MPOTensor d D} (X : GL (Fin D) ℂ) :
    IsMPUSimple (MPOTensor.virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ↔ IsMPUSimple U :=
  isMPUSimple_virtualSandwich_iff _ _ (Units.inv_mul X)

/-- A bond similarity leaves every periodic operator unchanged.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem mpo_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ) (U : MPOTensor d D)
    (B : Matrix (Fin D) (Fin D) ℂ) (hBA : B * A = 1) (N : ℕ) :
    mpo (virtualSandwich A U B) N = mpo U N := by
  refine mpo_eq_of_conj (G := B) (H := A) hBA (mul_eq_one_comm.mp hBA) ?_ N
  intro i j
  simp only [virtualSandwich_apply, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [Matrix.mul_assoc, hBA, Matrix.mul_one]

/-- A bond similarity preserves the MPU property.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem IsMPU.virtualSandwich {U : MPOTensor d D} (hU : IsMPU U)
    (A B : Matrix (Fin D) (Fin D) ℂ) (hBA : B * A = 1) :
    IsMPU (virtualSandwich A U B) := fun N hN ↦ by
  rw [mpo_virtualSandwich A U B hBA N]
  exact hU N hN

/-- The similarity by an invertible matrix `X` preserves the MPU property.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem IsMPU.virtualSandwich_gl {U : MPOTensor d D} (hU : IsMPU U) (X : GL (Fin D) ℂ) :
    IsMPU (MPOTensor.virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :=
  hU.virtualSandwich _ _ (Units.inv_mul X)

/-- A bond similarity preserves the right source-cut rank of every blocking.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem rightRank_blockTensor_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ)
    (U : MPOTensor d D) (B : Matrix (Fin D) (Fin D) ℂ) (hBA : B * A = 1) (L : ℕ) :
    r[blockTensor (virtualSandwich A U B) L] = r[blockTensor U L] := by
  rw [blockTensor_virtualSandwich A U B hBA L]
  exact rightRank_virtualSandwich A _ B (Units.mk A B (mul_eq_one_comm.mp hBA) hBA).isUnit
    (Units.mk B A hBA (mul_eq_one_comm.mp hBA)).isUnit

/-- A bond similarity preserves the left source-cut rank of every blocking.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem leftRank_blockTensor_virtualSandwich (A : Matrix (Fin D) (Fin D) ℂ)
    (U : MPOTensor d D) (B : Matrix (Fin D) (Fin D) ℂ) (hBA : B * A = 1) (L : ℕ) :
    ℓ[blockTensor (virtualSandwich A U B) L] = ℓ[blockTensor U L] := by
  rw [blockTensor_virtualSandwich A U B hBA L]
  exact leftRank_virtualSandwich A _ B (Units.mk A B (mul_eq_one_comm.mp hBA) hBA).isUnit
    (Units.mk B A hBA (mul_eq_one_comm.mp hBA)).isUnit

/-- The similarity by an invertible matrix `X` preserves the right source-cut rank of every
blocking.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem rightRank_blockTensor_virtualSandwich_gl (X : GL (Fin D) ℂ) (U : MPOTensor d D)
    (L : ℕ) :
    r[blockTensor (virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) L] = r[blockTensor U L] :=
  rightRank_blockTensor_virtualSandwich _ U _ (Units.inv_mul X) L

/-- The similarity by an invertible matrix `X` preserves the left source-cut rank of every
blocking.

Source: arXiv:1703.09188, Proposition IV.5, lines 773--804; MD.tex Lemma 1.2. -/
theorem leftRank_blockTensor_virtualSandwich_gl (X : GL (Fin D) ℂ) (U : MPOTensor d D)
    (L : ℕ) :
    ℓ[blockTensor (virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) L] = ℓ[blockTensor U L] :=
  leftRank_blockTensor_virtualSandwich _ U _ (Units.inv_mul X) L

end MPOTensor
