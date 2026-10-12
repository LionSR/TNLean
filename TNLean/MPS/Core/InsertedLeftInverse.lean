/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.TracePairing
import TNLean.MPS.Chain.OneSidedInverse

/-!
# Left inverses for letters with a nonzero insertion

If the letters of a tensor span the full matrix algebra and the inserted
matrix is nonzero, the family of left-weighted letters has a matrix-valued
left inverse. The insertion itself may be singular. This is the algebraic
cancellation needed in the extended-support intersection argument at the
endpoints of arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The two-letter products through any nonzero insertion span the full
matrix algebra. Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem span_range_insertedLetters_eq_top
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0) :
    Submodule.span ℂ (Set.range fun ij : Fin d × Fin d => A ij.1 * W * A ij.2) = ⊤ := by
  have hspan := span_range_evalWord_mul_nonzero_mul_evalWord_eq_top
    (Kraus.isNBlkInjective_one_of_isInjective hA) hW
  have hrange :
      Set.range (fun uv : (Fin 1 → Fin d) × (Fin 1 → Fin d) =>
        Kraus.evalWord A (List.ofFn uv.1) * W * Kraus.evalWord A (List.ofFn uv.2)) =
      Set.range (fun ij : Fin d × Fin d => A ij.1 * W * A ij.2) := by
    ext M
    constructor
    · rintro ⟨⟨u, v⟩, rfl⟩
      exact ⟨(u 0, v 0), by simp [List.ofFn_succ, Kraus.evalWord]⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨(fun _ => i, fun _ => j), by simp [List.ofFn_succ, Kraus.evalWord]⟩
  rwa [hrange] at hspan

/-- Singular inserted letters admit matrix-valued cancellation: there are
matrices \(R_j\) with \(\sum_j R_j W A^j=I\). This follows from the actual
full two-sided span, not from an assumed inverse of \(W\).
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem exists_leftInverse_insertedLetters
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : W ≠ 0) :
    ∃ R : Fin d → Matrix (Fin D) (Fin D) ℂ, ∑ j, R j * W * A j = 1 := by
  classical
  have hsurj :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination ℂ
      (fun ij : Fin d × Fin d => A ij.1 * W * A ij.2)).mp
      (span_range_insertedLetters_eq_top A hA W hW)
  obtain ⟨c, hc⟩ := hsurj 1
  have hc' : ∑ i, ∑ j, c (i, j) • (A i * W * A j) = 1 := by
    simpa only [Fintype.linearCombination_apply, Fintype.sum_prod_type] using hc
  refine ⟨fun j => ∑ i, c (i, j) • A i, ?_⟩
  simp only [Finset.sum_mul, smul_mul_assoc]
  rw [Finset.sum_comm]
  exact hc'

end MPSTensor
