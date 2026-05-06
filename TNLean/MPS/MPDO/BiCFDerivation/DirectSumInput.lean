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

/-- The length-`L` trace-test map \(Z\mapsto(t\mapsto \operatorname{tr}(ZA_t))\).

This is the trace-dual coordinate form of the finite-chain image space
\(\mathcal G_L^A\) used in the direct-sum argument. -/
noncomputable def leftTraceWordMap (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin L → Fin d) → ℂ :=
  LinearMap.pi fun t : Fin L → Fin d =>
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulRight ℂ (evalWord A (List.ofFn t)))

@[simp]
lemma leftTraceWordMap_apply (A : MPSTensor d D) (L : ℕ)
    (Z : Matrix (Fin D) (Fin D) ℂ) (t : Fin L → Fin d) :
    leftTraceWordMap A L Z t =
      Matrix.trace (Z * evalWord A (List.ofFn t)) := by
  simp [leftTraceWordMap, Matrix.traceLinearMap_apply]

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
  induction hZ using Submodule.span_induction with
  | mem Y hY =>
    rcases hY with ⟨uv, rfl⟩
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
  | zero =>
    refine ⟨0, ?_⟩
    intro t
    simp
  | add Y₁ Y₂ _ _ hY₁ hY₂ =>
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
  | smul a Y _ hY =>
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

/-- The three-block relation gives inclusion of length-`L` trace-test images.

This is the formal image-space version of the first inclusion step in
David--Perez-Garcia--Schuch--Wolf, Lemma `lem:direct-sum`. -/
theorem leftTraceWordMap_range_le_of_three_block_trace_relation_left
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ΔA : Matrix (Fin D₁) (Fin D₁) ℂ}
    {ΔB : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsNBlkInjective A L) (hΔA : ΔA ≠ 0)
    (hRel : ∀ w : Fin (L + (L + L)) → Fin d,
      Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
        Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0) :
    (leftTraceWordMap A L).range ≤ (leftTraceWordMap B L).range := by
  rintro f ⟨Z, rfl⟩
  obtain ⟨W, hW⟩ :=
    exists_right_trace_test_of_three_block_trace_relation_left hA hΔA hRel Z
  refine ⟨-W, ?_⟩
  ext t
  calc
    leftTraceWordMap B L (-W) t =
        -Matrix.trace (W * evalWord B (List.ofFn t)) := by simp
    _ = Matrix.trace (Z * evalWord A (List.ofFn t)) := by
        simpa using neg_eq_of_add_eq_zero_left (hW t)
    _ = leftTraceWordMap A L Z t := by simp

/-- If both middle test matrices are nonzero, the three-block relation gives
equality of the two length-`L` trace-test images. -/
theorem leftTraceWordMap_range_eq_of_three_block_trace_relation
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ΔA : Matrix (Fin D₁) (Fin D₁) ℂ}
    {ΔB : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hΔA : ΔA ≠ 0) (hΔB : ΔB ≠ 0)
    (hRel : ∀ w : Fin (L + (L + L)) → Fin d,
      Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
        Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0) :
    (leftTraceWordMap A L).range = (leftTraceWordMap B L).range := by
  apply le_antisymm
  · exact leftTraceWordMap_range_le_of_three_block_trace_relation_left hA hΔA hRel
  · rintro f ⟨W, rfl⟩
    obtain ⟨Z, hZ⟩ :=
      exists_left_trace_test_of_three_block_trace_relation_right hB hΔB hRel W
    refine ⟨-Z, ?_⟩
    ext t
    calc
      leftTraceWordMap A L (-Z) t =
          -Matrix.trace (Z * evalWord A (List.ofFn t)) := by simp
      _ = Matrix.trace (W * evalWord B (List.ofFn t)) := by
          simpa using neg_eq_of_add_eq_zero_right (hZ t)
      _ = leftTraceWordMap B L W t := by simp

/-- Block injectivity makes the length-`L` trace-test map injective. -/
theorem leftTraceWordMap_injective_of_isNBlkInjective {A : MPSTensor d D}
    (hA : IsNBlkInjective A L) :
    Function.Injective (leftTraceWordMap A L) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply (LinearMap.ker_eq_bot').2
  intro Z hZ
  have hφ :
      (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulLeft ℂ Z) = 0 := by
    apply LinearMap.ext_on_range
      (v := fun t : Fin L → Fin d => evalWord A (List.ofFn t))
    · simpa [IsNBlkInjective] using hA
    · intro t
      simpa [leftTraceWordMap_apply, Matrix.traceLinearMap_apply] using
        congrArg (fun f => f t) hZ
  exact trace_mul_right_eq_zero fun N => by
    simpa [Matrix.traceLinearMap_apply] using congrArg (fun f => f N) hφ

/-- Under block injectivity, the trace-test image has the full boundary-matrix
dimension. -/
theorem leftTraceWordMap_range_finrank_eq_of_isNBlkInjective {A : MPSTensor d D}
    (hA : IsNBlkInjective A L) :
    Module.finrank ℂ ((leftTraceWordMap A L).range) = D ^ 2 := by
  rw [LinearMap.finrank_range_of_inj
    (leftTraceWordMap_injective_of_isNBlkInjective hA)]
  calc
    Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ)
        = (Fintype.card (Fin D) * Fintype.card (Fin D)) * Module.finrank ℂ ℂ := by
            simpa using (Module.finrank_matrix ℂ ℂ (Fin D) (Fin D))
    _ = D * D := by simp
    _ = D ^ 2 := by simp [pow_two]

/-- The paper's dimension step for the two-block direct-sum argument.

If the length-`L` trace-test image of the larger block is contained in that of
the smaller block, and both blocks are length-`L` block-injective, then their
bond dimensions are equal and the trace-test images are equal. -/
theorem leftTraceWordMap_range_eq_of_range_le_of_isNBlkInjective_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hD : D₂ ≤ D₁)
    (hLe : (leftTraceWordMap A L).range ≤ (leftTraceWordMap B L).range) :
    D₁ = D₂ ∧ (leftTraceWordMap A L).range = (leftTraceWordMap B L).range := by
  have hfinLe := Submodule.finrank_mono hLe
  have hfinA := leftTraceWordMap_range_finrank_eq_of_isNBlkInjective (A := A) hA
  have hfinB := leftTraceWordMap_range_finrank_eq_of_isNBlkInjective (A := B) hB
  have hsq_le : D₁ ^ 2 ≤ D₂ ^ 2 := by
    simpa [hfinA, hfinB] using hfinLe
  have hsq_ge : D₂ ^ 2 ≤ D₁ ^ 2 := Nat.pow_le_pow_left hD 2
  have hsq : D₁ ^ 2 = D₂ ^ 2 := le_antisymm hsq_le hsq_ge
  have hD_eq : D₁ = D₂ := by
    exact Nat.mul_self_inj.mp (by simpa [pow_two] using hsq)
  have hfinEq :
      Module.finrank ℂ ((leftTraceWordMap A L).range) =
        Module.finrank ℂ ((leftTraceWordMap B L).range) := by
    simpa [hfinA, hfinB] using hsq
  exact ⟨hD_eq, Submodule.eq_of_le_of_finrank_eq hLe hfinEq⟩

/-- The three-block relation plus the paper's size ordering gives equality of
the trace-test images in the two-block direct-sum argument. -/
theorem leftTraceWordMap_range_eq_of_three_block_trace_relation_left_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ΔA : Matrix (Fin D₁) (Fin D₁) ℂ}
    {ΔB : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hD : D₂ ≤ D₁) (hΔA : ΔA ≠ 0)
    (hRel : ∀ w : Fin (L + (L + L)) → Fin d,
      Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
        Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0) :
    D₁ = D₂ ∧ (leftTraceWordMap A L).range = (leftTraceWordMap B L).range := by
  exact leftTraceWordMap_range_eq_of_range_le_of_isNBlkInjective_of_dim_ge
    hA hB hD (leftTraceWordMap_range_le_of_three_block_trace_relation_left hA hΔA hRel)

end MPSTensor
