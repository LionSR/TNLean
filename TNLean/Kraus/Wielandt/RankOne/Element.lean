/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixFittingRange
import TNLean.Kraus.WordSpan

/-!
# Bounded word powers in a finite Kraus family

This file constructs a bounded-length word-span element whose range lies in the
sum of the generalized eigenspaces for nonzero eigenvalues. It gives only the
intermediate Fitting-projector-power step $A_1^r = A_1^r P$ in Sanz,
Pérez-García, Wolf, and Cirac, arXiv:0909.5347, Lemma 2(b), not the final
rank-one element $|\varphi\rangle\langle\psi|$.
-/

open scoped Matrix
open Module

namespace Kraus

variable {d D : ℕ}

/-- A power of an evaluated word belongs to the word span at the multiplied length. -/
theorem evalWord_pow_mem_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)) (k : ℕ) :
    (MPSTensor.evalWord K w) ^ k ∈ wordSpan K (k * w.length) := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hw : MPSTensor.evalWord K w ∈ wordSpan K w.length :=
        evalWord_mem_wordSpan K w
      have hprod :
          (MPSTensor.evalWord K w) ^ k * MPSTensor.evalWord K w ∈
            wordSpan K (k * w.length + w.length) := by
        rw [wordSpan_add]
        exact Submodule.mul_mem_mul ih hw
      simpa [pow_succ, Nat.succ_mul] using hprod

/-- A word matrix with a nonzero eigenvalue has a nonzero bounded power whose range lies
in the sum of its generalized eigenspaces for nonzero eigenvalues.

This is only the intermediate Fitting-projector-power step
$A_1^r = A_1^r P$ in arXiv:0909.5347, Lemma 2(b). It is weaker than the
rank-one-element conclusion of that lemma. -/
theorem exists_nonzero_pow_evalWord_mem_wordSpan_range_le
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (w₀ : List (Fin d))
    (μ : ℂ) (φ : Fin D → ℂ)
    (hμ : μ ≠ 0) (hφ : φ ≠ 0)
    (heig : MPSTensor.evalWord K w₀ *ᵥ φ = μ • φ) :
    ∃ P : Matrix (Fin D) (Fin D) ℂ,
      P ∈ wordSpan K (D * w₀.length) ∧
      P ≠ 0 ∧
      LinearMap.range (Matrix.toLin' P) ≤
        ⨆ (ν : ℂ) (_ : ν ≠ 0),
          End.maxGenEigenspace (Matrix.toLin' (MPSTensor.evalWord K w₀)) ν := by
  classical
  refine ⟨(MPSTensor.evalWord K w₀) ^ D, ?_, ?_, ?_⟩
  · simpa [Nat.mul_comm] using evalWord_pow_mem_wordSpan K w₀ D
  · have hpow : ((MPSTensor.evalWord K w₀) ^ D) *ᵥ φ = μ ^ D • φ :=
      Matrix.pow_mulVec_eq_smul_of_mulVec_eq_smul
        (M := MPSTensor.evalWord K w₀) (φ := φ) (μ := μ) heig D
    have hμpow : μ ^ D ≠ 0 := pow_ne_zero _ hμ
    intro hP0
    have hzero : ((MPSTensor.evalWord K w₀) ^ D) *ᵥ φ = 0 := by
      simp [hP0]
    have : μ ^ D • φ = 0 := by
      simpa [hpow] using hzero
    exact hφ (smul_eq_zero.mp this |>.resolve_left hμpow)
  · let f : End ℂ (Fin D → ℂ) := Matrix.toLin' (MPSTensor.evalWord K w₀)
    have hrange :
        LinearMap.range (f ^ D) ≤
          ⨆ (ν : ℂ) (_ : ν ≠ 0), End.maxGenEigenspace f ν :=
      Module.End.range_pow_le_iSup_maxGenEigenspace_ne_zero
        (D := D) f
    simpa [f, Matrix.toLin'_pow] using hrange

end Kraus
