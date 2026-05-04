/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Basic

/-!
# Duplicate scalar-block obstruction to MPDO biCF

This module records the finite-dimensional obstruction showing that the
non-`biCF` fields of `HorizontalCFData` do not imply the biCF trace-separation
property. The example has two identical scalar blocks: each block is injective
and left-canonical and the weights are nonzero, but every finite word-entry
family has two equal rows, so no finite-length linear-independence witness can
exist.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Proposition IV.3]

## Tags

matrix product density operators, canonical form, block separation
-/

open scoped Matrix BigOperators

namespace MPSTensor

section DuplicateScalarBlocks

/-- Nonzero weights for the duplicate-block counterexample. -/
def duplicateScalarWeights : Fin 2 → ℂ
  | 0 => 1
  | 1 => 2

/-- Common block dimension for the duplicate-block counterexample. -/
abbrev duplicateScalarDim : Fin 2 → ℕ := fun _ => 1

/-- Two identical `1 × 1` blocks. This family is blockwise injective and
left-canonical, but it cannot admit any finite-length `wordEntryFamily`
linear-independence witness. -/
def duplicateScalarBlocks :
    (k : Fin 2) → MPSTensor 1 (duplicateScalarDim k)
  | _ => fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)

private theorem span_singleton_one_finOne_eq_top :
    (ℂ ∙ (1 : Matrix (Fin 1) (Fin 1) ℂ)) = ⊤ := by
  refine (Submodule.span_singleton_eq_top_iff ℂ
    (1 : Matrix (Fin 1) (Fin 1) ℂ)).2 ?_
  intro M
  refine ⟨M 0 0, ?_⟩
  ext i j
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  subst hi
  subst hj
  simp

/-- Each duplicate scalar block is injective. -/
theorem duplicateScalarBlocks_isInjective :
    ∀ k, IsInjective (duplicateScalarBlocks k) := by
  intro k
  simpa [duplicateScalarBlocks, duplicateScalarDim, IsInjective, Set.range_const] using
    span_singleton_one_finOne_eq_top

/-- The duplicate scalar blocks are left-canonical. -/
theorem duplicateScalarBlocks_leftCanonical :
    ∀ k, ∑ i : Fin 1, (duplicateScalarBlocks k i)ᴴ * duplicateScalarBlocks k i = 1 := by
  intro k
  simp [duplicateScalarBlocks]

/-- The counterexample weights are nonzero. -/
theorem duplicateScalarWeights_ne_zero :
    ∀ k, duplicateScalarWeights k ≠ 0 := by
  intro k
  fin_cases k <;> norm_num [duplicateScalarWeights]

/-- Duplicate blocks force repeated scalar word-entry functionals, so no blocking
length can make `wordEntryFamily` linearly independent. -/
theorem duplicateScalarBlocks_not_linearIndependent_wordEntryFamily (L : ℕ) :
    ¬ LinearIndependent ℂ (wordEntryFamily duplicateScalarBlocks L) := by
  intro hLI
  let x0 : BlockEntryIndex duplicateScalarDim := ⟨0, (0, 0)⟩
  let x1 : BlockEntryIndex duplicateScalarDim := ⟨1, (0, 0)⟩
  have hEq : wordEntryFamily duplicateScalarBlocks L x0 =
      wordEntryFamily duplicateScalarBlocks L x1 := by
    funext w
    simp [x0, x1, wordEntryFamily, blockEntryValue, wordTuple, duplicateScalarBlocks]
  have hx : x0 = x1 := hLI.injective hEq
  have h01 : (0 : Fin 2) = 1 := by
    simpa [x0, x1] using congrArg Sigma.fst hx
  exact Fin.zero_ne_one h01

/-- Concrete obstruction to the Issue-#822 target on the current hypotheses:
blockwise injectivity, left-canonicality, and nonzero weights do not by
themselves imply a finite-length `wordEntryFamily` witness. -/
theorem duplicateScalarBlocks_not_exists_linearIndependent_wordEntryFamily :
    ¬ ∃ L, LinearIndependent ℂ (wordEntryFamily duplicateScalarBlocks L) := by
  rintro ⟨L, hL⟩
  exact duplicateScalarBlocks_not_linearIndependent_wordEntryFamily L hL

/-- The duplicate scalar blocks do not satisfy the biCF trace-separation property. -/
theorem duplicateScalarBlocks_not_hasBiCF :
    ¬ HasBiCF duplicateScalarBlocks := by
  rintro ⟨L, hL⟩
  let Δ : (k : Fin 2) → Matrix (Fin (duplicateScalarDim k)) (Fin (duplicateScalarDim k)) ℂ :=
    fun k => if k = 0 then 1 else -1
  have hTrace :
      ∀ w : Fin L → Fin 1,
        (∑ k : Fin 2,
          Matrix.trace (Δ k * evalWord (duplicateScalarBlocks k) (List.ofFn w))) = 0 := by
    intro w
    simp [Δ, duplicateScalarBlocks, duplicateScalarDim, Matrix.trace_fin_one]
  have hzero := hL Δ hTrace 0
  have hentry := congrFun (congrFun hzero 0) 0
  simp [Δ] at hentry

/-- Counterexample to deriving finite-length block separation from the
other `HorizontalCFData` fields alone. -/
theorem duplicateScalarBlocks_counterexample :
    (∀ k, IsInjective (duplicateScalarBlocks k)) ∧
      (∀ k, ∑ i : Fin 1,
        (duplicateScalarBlocks k i)ᴴ * duplicateScalarBlocks k i = 1) ∧
      (∀ k, duplicateScalarWeights k ≠ 0) ∧
      ¬ HasBiCF duplicateScalarBlocks ∧
      ¬ ∃ L, LinearIndependent ℂ (wordEntryFamily duplicateScalarBlocks L) := by
  refine ⟨duplicateScalarBlocks_isInjective, duplicateScalarBlocks_leftCanonical,
    duplicateScalarWeights_ne_zero, duplicateScalarBlocks_not_hasBiCF,
    duplicateScalarBlocks_not_exists_linearIndependent_wordEntryFamily⟩

end DuplicateScalarBlocks

end MPSTensor
