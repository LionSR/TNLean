/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.Entropy.MarkovChain
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Simple MPDO local structure

This file records the local entropy-theoretic part of the simple MPDO
renormalization fixed-point argument from Appendix C.2 of
arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete).

## Main declarations

- `MPOTensor.EtaStructure`: the quantum-Markov decomposition on the middle
  subsystem supplied by equality in strong subadditivity.
- `MPOTensor.sal_implies_eta_structure`: the Lean form of the entropy step in
  Lemma C.3.  We formalize the strong-area-law input locally as equality in
  strong subadditivity for a normalized three-site reduced state.
- `Matrix.HasRankOneFactorization`: a finite matrix factors as `vecMulVec a b`.
- `Matrix.TracePowersConstant`: all positive powers of a matrix have the same
  trace as the matrix itself.
- `Matrix.PrimitiveTracePowersConstantImpliesRankOne`: the provisional
  rank-one placeholder abstracted from Lemma C.4.
- `Matrix.primitiveTraceCounterexample`: an explicit primitive nonnegative
  matrix with constant trace powers that is not rank one.
- `MPOTensor.sal_zcl_implies_rank_one_T`: the scoped Lemma C.4 consequence,
  proved relative to that stronger placeholder input.

## Implementation note

In the paper, Lemma C.3 continues from equality in strong subadditivity to the
explicit operators `η_{k,h}` by applying local inverse maps coming from the
injectivity of the simple tensor. The current repository does not yet contain
that inverse-map layer for simple MPDOs, so we formalize the entropic core
exactly as the Hayashi / Ruskai / Hayden–Jozsa–Petz–Winter decomposition already
available through `Entropy.QuantumMarkovDecomposition`.

Lemma C.4 was initially isolated to the matrix claim that a primitive
nonnegative matrix with constant traces of all positive powers must be rank
one. The explicit declaration `Matrix.primitiveTraceCounterexample` shows that
this matrix statement is false in full generality. We therefore keep
`Matrix.PrimitiveTracePowersConstantImpliesRankOne` only as a provisional local
placeholder for the stronger input that must ultimately be extracted from the
full ZCL / local-`η` structure.

## References

- [CPGSV17] arXiv:1606.00608, Appendix C.2, Lemmas C.3–C.4
- Hayashi, J. Phys. A: Math. Gen. 37 (2004) L205–L208
- Ruskai, JMP 43, 4358 (2002)
- Hayden, Jozsa, Petz, Winter, Commun. Math. Phys. 246, 359–374 (2004)
-/

open scoped Matrix ComplexOrder BigOperators

namespace Matrix

variable {n : ℕ}

/-- A square real matrix has the rank-one factorization of Appendix C.2,
Lemma C.4 if it is an outer product `a bᵀ`, represented in Lean as
`Matrix.vecMulVec a b`. -/
def HasRankOneFactorization (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b

/-- The traces of all positive powers of `T` agree with the trace of `T`
itself.  This is the matrix-theoretic consequence of the ZCL step used in
Appendix C.2, Lemma C.4. -/
def TracePowersConstant (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → Matrix.trace (T ^ k) = Matrix.trace T

/-- A provisional rank-one placeholder for Appendix C.2, Lemma C.4.

The naive matrix statement “primitive + constant trace powers implies rank one”
is false in general; see `primitiveTraceCounterexample`. We nevertheless keep
this implication as a local placeholder because `sal_zcl_implies_rank_one_T`
only needs some stronger input at exactly this point. The eventual replacement
must come from additional structure in the full ZCL / local-`η` argument, not
from Perron–Frobenius theory alone. -/
def PrimitiveTracePowersConstantImpliesRankOne
    (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.IsPrimitive T → TracePowersConstant T → HasRankOneFactorization T

/-- A concrete primitive nonnegative matrix with constant trace powers but not a
rank-one factorization. This shows that
`PrimitiveTracePowersConstantImpliesRankOne` is not a valid global theorem for
arbitrary primitive real matrices. -/
noncomputable def primitiveTraceCounterexample : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    match i.1, j.1 with
    | 0, 0 => 0
    | 0, 1 => 0
    | 0, 2 => 1 / 2
    | 1, 0 => 1 / 2
    | 1, 1 => 1 / 2
    | 1, 2 => 0
    | 2, 0 => 1 / 2
    | 2, 1 => 1 / 2
    | 2, 2 => 1 / 2
    | _, _ => 0

theorem primitiveTraceCounterexample_sq :
    primitiveTraceCounterexample ^ 2 =
      Matrix.of fun i _ : Fin 3 => if i = 2 then (1 / 2 : ℝ) else (1 / 4 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primitiveTraceCounterexample, Matrix.of_apply, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two] <;> norm_num

theorem primitiveTraceCounterexample_sq_mul :
    primitiveTraceCounterexample ^ 2 * primitiveTraceCounterexample =
      primitiveTraceCounterexample ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primitiveTraceCounterexample, Matrix.of_apply, Matrix.mul_apply,
      Fin.sum_univ_three, pow_two] <;> norm_num

theorem primitiveTraceCounterexample_pow_add_two (m : ℕ) :
    primitiveTraceCounterexample ^ (m + 2) = primitiveTraceCounterexample ^ 2 := by
  induction m with
  | zero =>
      simp
  | succ m hm =>
      calc
        primitiveTraceCounterexample ^ (Nat.succ m + 2) =
            primitiveTraceCounterexample ^ (m + 2) * primitiveTraceCounterexample := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ]
        _ = primitiveTraceCounterexample ^ 2 * primitiveTraceCounterexample := by rw [hm]
        _ = primitiveTraceCounterexample ^ 2 := primitiveTraceCounterexample_sq_mul

theorem trace_primitiveTraceCounterexample :
    Matrix.trace primitiveTraceCounterexample = 1 := by
  simp [primitiveTraceCounterexample, Matrix.of_apply, Matrix.trace, Fin.sum_univ_three]
  norm_num

theorem trace_primitiveTraceCounterexample_sq :
    Matrix.trace (primitiveTraceCounterexample ^ 2) = 1 := by
  simp [primitiveTraceCounterexample_sq, Matrix.of_apply, Matrix.trace, Fin.sum_univ_three]
  norm_num

/-- The explicit matrix `primitiveTraceCounterexample` is primitive because its
square is entrywise strictly positive. -/
theorem primitiveTraceCounterexample_isPrimitive :
    Matrix.IsPrimitive primitiveTraceCounterexample := by
  refine ⟨?_, 2, by norm_num, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [primitiveTraceCounterexample, Matrix.of_apply]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [primitiveTraceCounterexample_sq, Matrix.of_apply]

/-- The explicit counterexample has constant trace on all positive powers. -/
theorem primitiveTraceCounterexample_tracePowersConstant :
    TracePowersConstant primitiveTraceCounterexample := by
  intro k hk
  cases k with
  | zero =>
      exact absurd hk (lt_irrefl 0)
  | succ k =>
      cases k with
      | zero =>
          simp
      | succ k =>
          calc
            Matrix.trace (primitiveTraceCounterexample ^ Nat.succ (Nat.succ k)) =
                Matrix.trace (primitiveTraceCounterexample ^ (k + 2)) := by
                  rfl
            _ = Matrix.trace (primitiveTraceCounterexample ^ 2) := by
                  rw [primitiveTraceCounterexample_pow_add_two]
            _ = 1 := trace_primitiveTraceCounterexample_sq
            _ = Matrix.trace primitiveTraceCounterexample :=
                  trace_primitiveTraceCounterexample.symm

/-- The explicit counterexample is not rank one. -/
theorem primitiveTraceCounterexample_not_hasRankOneFactorization :
    ¬ HasRankOneFactorization primitiveTraceCounterexample := by
  rintro ⟨a, b, hT⟩
  have h02 : a 0 * b 2 = (1 / 2 : ℝ) := by
    simpa [primitiveTraceCounterexample, Matrix.vecMulVec_apply] using
      (congrArg (fun M => M 0 2) hT).symm
  have ha0 : a 0 ≠ 0 := by
    intro ha0
    have : (1 / 2 : ℝ) = 0 := by simpa [ha0] using h02.symm
    norm_num at this
  have h00 : a 0 * b 0 = 0 := by
    simpa [primitiveTraceCounterexample, Matrix.vecMulVec_apply] using
      (congrArg (fun M => M 0 0) hT).symm
  have hb0 : b 0 = 0 := Or.resolve_left (mul_eq_zero.mp h00) ha0
  have h10 : a 1 * b 0 = (1 / 2 : ℝ) := by
    simpa [primitiveTraceCounterexample, Matrix.vecMulVec_apply] using
      (congrArg (fun M => M 1 0) hT).symm
  simp [hb0] at h10

/-- Hence the placeholder implication is false for the explicit counterexample. -/
theorem primitiveTraceCounterexample_not_pf_input :
    ¬ PrimitiveTracePowersConstantImpliesRankOne primitiveTraceCounterexample := by
  intro h
  exact primitiveTraceCounterexample_not_hasRankOneFactorization
    (h primitiveTraceCounterexample_isPrimitive
      primitiveTraceCounterexample_tracePowersConstant)

end Matrix

namespace MPOTensor

section LocalSAL

variable {dA dB dC : ℕ}

/-- The local `η`-structure used in the simple MPDO argument, formalized as the
quantum-Markov decomposition on the middle subsystem produced by equality in
strong subadditivity.

For the current repository state, this is the exact entropy-theoretic content of
Lemma C.3 that is already available through the sanctioned Hayashi equality
characterization. The further conversion from this decomposition to explicit
operators `η_{k,h}` requires the injective inverse-map layer for simple MPDOs
and is deferred to future work. -/
abbrev EtaStructure
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) : Type :=
  Entropy.QuantumMarkovDecomposition ρ_ABC

/-- **Lemma C.3, scoped entropy form**: strong area law implies the local
`η`-structure.

We formalize the SAL input at the exact local point where the paper invokes it:
for the normalized three-site reduced state `ρ_ABC`, SAL gives equality in
strong subadditivity. The Hayashi equality characterization then yields the
quantum-Markov decomposition on the middle subsystem. -/
theorem sal_implies_eta_structure
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSAL : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    Nonempty (EtaStructure ρ_ABC) :=
  Entropy.exists_quantumMarkovDecomposition_of_ssaEquality ρ_ABC hρ_dm hSAL

end LocalSAL

section RankOneT

variable {n : ℕ}

/-- **Lemma C.4, scoped matrix form**: once the matrix `T` attached to the
local `η`-structure is known to be primitive and to have constant trace on all
positive powers, any additional rank-one input available for that particular
`T` yields a rank-one factorization.

The normalization `a ⬝ᵥ b = 1` is then immediate from `trace T = 1` and the
identity `trace (vecMulVec a b) = a ⬝ᵥ b`. -/
theorem sal_zcl_implies_rank_one_T
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hTrace : Matrix.trace T = 1)
    (hZCL : Matrix.TracePowersConstant T)
    (hPF : Matrix.PrimitiveTracePowersConstantImpliesRankOne T) :
    ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 := by
  rcases hPF hPrimitive hZCL with ⟨a, b, hT⟩
  refine ⟨a, b, hT, ?_⟩
  calc
    a ⬝ᵥ b = Matrix.trace (Matrix.vecMulVec a b) := by
      symm
      exact Matrix.trace_vecMulVec a b
    _ = Matrix.trace T := by rw [← hT]
    _ = 1 := hTrace

end RankOneT

end MPOTensor
