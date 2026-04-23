/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.Entropy.MarkovChain
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

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
- `Matrix.PrimitiveTracePowersConstantImpliesRankOne`: the single missing
  Perron–Frobenius input isolated by Lemma C.4.
- `MPOTensor.sal_zcl_implies_rank_one_T`: the scoped Lemma C.4 consequence,
  proved relative to that Perron–Frobenius input.

## Implementation note

In the paper, Lemma C.3 continues from equality in strong subadditivity to the
explicit operators `η_{k,h}` by applying local inverse maps coming from the
injectivity of the simple tensor. The current repository does not yet contain
that inverse-map layer for simple MPDOs, so we formalize the entropic core
exactly as the Hayashi / Ruskai / Hayden–Jozsa–Petz–Winter decomposition already
available through `Entropy.QuantumMarkovDecomposition`.

Lemma C.4 is further isolated to the finite-dimensional Perron–Frobenius step:
for a primitive nonnegative matrix `T`, constant traces of positive powers are
*claimed* (in the paper) to force `T` to have rank one. We expose that step as
the single hypothesis `Matrix.PrimitiveTracePowersConstantImpliesRankOne`, so
the remaining gap is honestly localized and matches the paper one-to-one.

The universally quantified form of that claim is in fact false — see
`TNLean/Archive/PerronFrobeniusRankOneCounterexample.lean` for an explicit
3 × 3 witness. Callers of `MPOTensor.sal_zcl_implies_rank_one_T` must therefore
discharge the hypothesis using additional structure on the specific `T` coming
from the MPDO context (the η-operators are positive semidefinite in the paper's
construction, which supplies the missing diagonalizability).

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

/-- The missing Perron–Frobenius input for Appendix C.2, Lemma C.4:
for a primitive nonnegative matrix, constant traces of positive powers imply a
rank-one factorization.

This is intentionally packaged as a local hypothesis rather than a new global
assumption. Once a genuine proof is formalized, downstream callers can simply
supply that theorem here and the scoped result `MPOTensor.sal_zcl_implies_rank_one_T`
will become unconditional.

**Note.** As a universally quantified statement over primitive nonnegative real
matrices this implication is *false*: there exist primitive nonnegative
matrices with `trace (T ^ k) = trace T` for all `k ≥ 1` but rank greater than
one. An explicit machine-checked `3 × 3` witness is recorded in
`TNLean/Archive/PerronFrobeniusRankOneCounterexample.lean`. Discharging the
hypothesis in a specific MPDO context therefore requires additional structure
on `T` (for instance positive semidefiniteness or diagonalizability over `ℂ`)
that the caller must supply. -/
def PrimitiveTracePowersConstantImpliesRankOne
    (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.IsPrimitive T → TracePowersConstant T → HasRankOneFactorization T

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
positive powers, the remaining Perron–Frobenius input forces `T` to be rank one.

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
