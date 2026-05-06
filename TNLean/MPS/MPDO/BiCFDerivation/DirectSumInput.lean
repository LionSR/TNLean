/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.TracePairing
import TNLean.MPS.MPDO.BiCFDerivation.Core

/-!
# Direct-sum trace input for canonical-form block separation

This file formalizes the first algebraic step in the proof of
David--Perez-Garcia--Schuch--Wolf, Lemma `lem:direct-sum`
(`Papers/quant-ph_0608197/MPSarchive.tex`): from a homogeneous three-block
trace relation and the two-sided nonzero span lemma, every trace test on one
block has a matching trace test on the other block at the single-block length.

The remaining source step, not proved here, is the contradiction with equality
of the finite-chain image spaces using the injective parent-Hamiltonian
uniqueness theorem.

## References

* [David--Perez-Garcia--Schuch--Wolf 2006, Lemmas `lem1` and `lem:direct-sum`]

## Tags

matrix product states, canonical form, direct sum, block separation
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D₁ D₂ L : ℕ}

/-- **Three-block direct-sum input, left block.**

Assume the word products of `A` of length `L` span the full matrix algebra and
`ΔA` is nonzero. If a homogeneous trace relation holds on three consecutive
length-`L` blocks, then every matrix trace test against `A` at length `L` has a
matching matrix trace test against `B` at the same length.

This is the formal trace-dual version of the first `b = 2` step in
David--Perez-Garcia--Schuch--Wolf, Lemma `lem:direct-sum`, after applying
Lemma `lem1` to the nonzero middle matrix. -/
theorem exists_right_trace_test_of_three_block_trace_relation_left
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ΔA : Matrix (Fin D₁) (Fin D₁) ℂ}
    {ΔB : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsNBlkInjective A L) (hΔA : ΔA ≠ 0)
    (hRel : ∀ w : Fin (L + (L + L)) → Fin d,
      Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
        Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0)
    (Z : Matrix (Fin D₁) (Fin D₁) ℂ) :
    ∃ W : Matrix (Fin D₂) (Fin D₂) ℂ, ∀ t : Fin L → Fin d,
      Matrix.trace (Z * evalWord A (List.ofFn t)) +
        Matrix.trace (W * evalWord B (List.ofFn t)) = 0 := by
  classical
  let spanA : Submodule ℂ (Matrix (Fin D₁) (Fin D₁) ℂ) :=
    Submodule.span ℂ
      (Set.range fun uv : (Fin L → Fin d) × (Fin L → Fin d) =>
        evalWord A (List.ofFn uv.1) * ΔA * evalWord A (List.ofFn uv.2))
  have hZ : Z ∈ spanA := by
    change Z ∈ Submodule.span ℂ
      (Set.range fun uv : (Fin L → Fin d) × (Fin L → Fin d) =>
        evalWord A (List.ofFn uv.1) * ΔA * evalWord A (List.ofFn uv.2))
    rw [span_range_evalWord_mul_nonzero_mul_evalWord_eq_top hA hΔA]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun Y _ => ∃ W : Matrix (Fin D₂) (Fin D₂) ℂ, ∀ t : Fin L → Fin d,
      Matrix.trace (Y * evalWord A (List.ofFn t)) +
        Matrix.trace (W * evalWord B (List.ofFn t)) = 0)
    ?mem ?zero ?add ?smul hZ
  · rintro Y ⟨uv, rfl⟩
    rcases uv with ⟨u, v⟩
    refine ⟨evalWord B (List.ofFn u) * ΔB * evalWord B (List.ofFn v), ?_⟩
    intro t
    let Au := evalWord A (List.ofFn u)
    let Av := evalWord A (List.ofFn v)
    let At := evalWord A (List.ofFn t)
    let Bu := evalWord B (List.ofFn u)
    let Bv := evalWord B (List.ofFn v)
    let Bt := evalWord B (List.ofFn t)
    have hAcycle :
        Matrix.trace ((Au * ΔA * Av) * At) =
          Matrix.trace (ΔA * (Av * (At * Au))) := by
      simpa [Au, Av, At, Matrix.mul_assoc] using
        (Matrix.trace_mul_comm Au (ΔA * Av * At))
    have hBcycle :
        Matrix.trace ((Bu * ΔB * Bv) * Bt) =
          Matrix.trace (ΔB * (Bv * (Bt * Bu))) := by
      simpa [Bu, Bv, Bt, Matrix.mul_assoc] using
        (Matrix.trace_mul_comm Bu (ΔB * Bv * Bt))
    have hRel' := hRel (Fin.append v (Fin.append t u))
    rw [hAcycle, hBcycle]
    simpa [Au, Av, At, Bu, Bv, Bt, List.ofFn_fin_append, evalWord_append,
      Matrix.mul_assoc] using hRel'
  · refine ⟨0, ?_⟩
    intro t
    simp
  · intro Y₁ Y₂ _ _ hY₁ hY₂
    rcases hY₁ with ⟨W₁, hW₁⟩
    rcases hY₂ with ⟨W₂, hW₂⟩
    refine ⟨W₁ + W₂, ?_⟩
    intro t
    have h1 := hW₁ t
    have h2 := hW₂ t
    calc
      Matrix.trace ((Y₁ + Y₂) * evalWord A (List.ofFn t)) +
          Matrix.trace ((W₁ + W₂) * evalWord B (List.ofFn t))
          = (Matrix.trace (Y₁ * evalWord A (List.ofFn t)) +
              Matrix.trace (W₁ * evalWord B (List.ofFn t))) +
            (Matrix.trace (Y₂ * evalWord A (List.ofFn t)) +
              Matrix.trace (W₂ * evalWord B (List.ofFn t))) := by
              simp [Matrix.add_mul, Matrix.trace_add, add_assoc, add_left_comm]
      _ = 0 := by simp [h1, h2]
  · intro a Y _ hY
    rcases hY with ⟨W, hW⟩
    refine ⟨a • W, ?_⟩
    intro t
    calc
      Matrix.trace ((a • Y) * evalWord A (List.ofFn t)) +
          Matrix.trace ((a • W) * evalWord B (List.ofFn t))
          = a * (Matrix.trace (Y * evalWord A (List.ofFn t)) +
              Matrix.trace (W * evalWord B (List.ofFn t))) := by
              simp [Matrix.trace_smul, mul_add]
      _ = 0 := by simp [hW t]

/-- **Three-block direct-sum input, right block.**

This is the symmetric form of
`exists_right_trace_test_of_three_block_trace_relation_left`: a nonzero test
matrix on `B` lets every trace test against `B` be matched by a trace test
against `A`. -/
theorem exists_left_trace_test_of_three_block_trace_relation_right
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ΔA : Matrix (Fin D₁) (Fin D₁) ℂ}
    {ΔB : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hB : IsNBlkInjective B L) (hΔB : ΔB ≠ 0)
    (hRel : ∀ w : Fin (L + (L + L)) → Fin d,
      Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
        Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0)
    (W : Matrix (Fin D₂) (Fin D₂) ℂ) :
    ∃ Z : Matrix (Fin D₁) (Fin D₁) ℂ, ∀ t : Fin L → Fin d,
      Matrix.trace (Z * evalWord A (List.ofFn t)) +
        Matrix.trace (W * evalWord B (List.ofFn t)) = 0 := by
  classical
  obtain ⟨Z, hZ⟩ :=
    exists_right_trace_test_of_three_block_trace_relation_left
      (A := B) (B := A) (ΔA := ΔB) (ΔB := ΔA) hB hΔB
      (fun w => by
        simpa [add_comm] using hRel w) W
  exact ⟨Z, fun t => by
    simpa [add_comm] using hZ t⟩

end MPSTensor
