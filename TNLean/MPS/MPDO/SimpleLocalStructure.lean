/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.Entropy.MarkovChain
import TNLean.MPS.Chain.VirtualInsertion
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Simple MPDO local structure

This file records the local entropy-theoretic part of the simple MPDO
renormalization fixed-point argument from Appendix C.2 of
arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete).

## Main declarations

- `MPOTensor.IsInjective`: injectivity of a simple MPO tensor, expressed via the
  doubled-index MPS tensor.
- `MPOTensor.inverseTensor`: a concrete right inverse `K⁻¹` for an injective
  simple MPO tensor.
- `MPOTensor.physRealize` / `MPOTensor.physRealizeLeft`: the physical
  realization maps for virtual insertions on an injective simple MPO tensor.
- `MPOTensor.EtaStructure`: the quantum-Markov decomposition on the middle
  subsystem supplied by equality in strong subadditivity.
- `MPOTensor.ExplicitEtaOperators`: the explicit neighboring operators
  `η_{k,h}` over a fixed Hayashi decomposition.
- `MPOTensor.etaOperators`: the underlying family of operators in an
  `ExplicitEtaOperators` witness.
- `Matrix.HasRankOneFactorization`: a finite matrix factors as `vecMulVec a b`.
- `Matrix.TracePowersConstant`: all positive powers of a matrix have the same
  trace as the matrix itself.
- `Matrix.PrimitiveTracePowersConstantImpliesRankOne`: the single missing
  Perron–Frobenius input isolated by Lemma C.4.
- `MPOTensor.sal_implies_eta_structure`: the Lean form of the entropy step in
  Lemma C.3. We formalize the strong-area-law input locally as equality in
  strong subadditivity for a normalized three-site reduced state.
- `MPOTensor.sal_zcl_implies_rank_one_T`: the scoped Lemma C.4 consequence,
  proved relative to that Perron–Frobenius input.

## Implementation note

In the paper, Lemma C.3 continues from equality in strong subadditivity to the
explicit operators `η_{k,h}` by applying local inverse maps coming from the
injectivity of the simple tensor. The present file now contains that
inverse-map layer for an injective simple MPO tensor, packaged by
`MPOTensor.inverseTensor`, `MPOTensor.physRealize`, and
`MPOTensor.physRealizeLeft`.

What remains to be formalized is the final bookkeeping theorem connecting those
inverse maps to the Hayashi decomposition blocks and thereby producing a term of
`MPOTensor.ExplicitEtaOperators`. We therefore record both the inverse-map
infrastructure and the target `η_{k,h}` family separately, so the residual gap
is isolated to a single local extraction statement.

Lemma C.4 is further isolated to the finite-dimensional Perron–Frobenius step:
for a primitive nonnegative matrix `T`, constant traces of positive powers force
`T` to have rank one. We expose that step as the single hypothesis
`Matrix.PrimitiveTracePowersConstantImpliesRankOne`, so the remaining gap is
honestly localized and matches the paper one-to-one.

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
itself. This is the matrix-theoretic consequence of the ZCL step used in
Appendix C.2, Lemma C.4. -/
def TracePowersConstant (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → Matrix.trace (T ^ k) = Matrix.trace T

/-- The missing Perron–Frobenius input for Appendix C.2, Lemma C.4:
for a primitive nonnegative matrix, constant traces of positive powers imply a
rank-one factorization.

This is intentionally packaged as a local hypothesis rather than a new global
assumption. Once a genuine proof is formalized, downstream callers can simply
supply that theorem here and the scoped result `MPOTensor.sal_zcl_implies_rank_one_T`
will become unconditional. -/
def PrimitiveTracePowersConstantImpliesRankOne
    (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.IsPrimitive T → TracePowersConstant T → HasRankOneFactorization T

end Matrix

namespace MPOTensor

section InjectiveInverseMaps

variable {d D : ℕ}

/-- A simple MPO tensor is injective when its doubled-index MPS tensor is
injective. This is the exact hypothesis needed for the local inverse-map layer
in Appendix C.2. -/
abbrev IsInjective (K : MPOTensor d D) : Prop :=
  MPSTensor.IsInjective K.toMPSTensor

/-- A concrete inverse tensor `K⁻¹` obtained from a right inverse to the linear
combination map of the doubled-index MPS tensor.

For each physical index `p : Fin (d * d)`, the matrix `inverseTensor K hK p`
collects the coefficients of the standard matrix basis under the chosen right
inverse. Equivalently, its `(α, β)` entry is the coefficient of `K p` in the
expansion of the matrix unit `|α⟩⟨β|`. -/
noncomputable def inverseTensor (K : MPOTensor d D) (hK : K.IsInjective) :
    Fin (d * d) → Matrix (Fin D) (Fin D) ℂ :=
  fun p => Matrix.of fun α β =>
    MPSTensor.decompositionMap (A := K.toMPSTensor) hK (Matrix.single α β (1 : ℂ)) p

/-- Contracting the chosen inverse tensor with the local MPO tensor recovers the
matrix units on the virtual bond space. This is the Lean form of the paper's
inverse-map identity for an injective simple tensor. -/
theorem inverseTensor_spec (K : MPOTensor d D) (hK : K.IsInjective)
    (α β : Fin D) :
    ∑ p : Fin (d * d), inverseTensor K hK p α β • K.toMPSTensor p =
      Matrix.single α β (1 : ℂ) := by
  simpa [inverseTensor] using
    (MPSTensor.decompositionMap_sum (A := K.toMPSTensor) hK
      (Matrix.single α β (1 : ℂ)))

/-- The physical realization map for a right virtual insertion on an injective
simple MPO tensor. This is the MPO wrapper around
`MPSTensor.physRealize` for the doubled-index tensor. -/
noncomputable def physRealize (K : MPOTensor d D) (hK : K.IsInjective)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  MPSTensor.physRealize K.toMPSTensor hK X

/-- Defining property of `MPOTensor.physRealize`. -/
theorem physRealize_spec (K : MPOTensor d D) (hK : K.IsInjective)
    (X : Matrix (Fin D) (Fin D) ℂ) (p : Fin (d * d)) :
    K.toMPSTensor p * X =
      ∑ q, (physRealize K hK X) p q • K.toMPSTensor q := by
  simpa [physRealize] using MPSTensor.physRealize_spec K.toMPSTensor hK X p

/-- `MPOTensor.physRealize` is multiplicative. -/
theorem physRealize_mul (K : MPOTensor d D) (hK : K.IsInjective)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physRealize K hK (X * Y) = physRealize K hK X * physRealize K hK Y := by
  simpa [physRealize] using MPSTensor.physRealize_mul K.toMPSTensor hK X Y

/-- The physical realization map for a left virtual insertion on an injective
simple MPO tensor. -/
noncomputable def physRealizeLeft (K : MPOTensor d D) (hK : K.IsInjective)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  MPSTensor.physRealizeLeft K.toMPSTensor hK X

/-- Defining property of `MPOTensor.physRealizeLeft`. -/
theorem physRealizeLeft_spec (K : MPOTensor d D) (hK : K.IsInjective)
    (X : Matrix (Fin D) (Fin D) ℂ) (p : Fin (d * d)) :
    X * K.toMPSTensor p =
      ∑ q, (physRealizeLeft K hK X) p q • K.toMPSTensor q := by
  simpa [physRealizeLeft] using
    MPSTensor.physRealizeLeft_spec K.toMPSTensor hK X p

end InjectiveInverseMaps

section LocalSAL

variable {dA dB dC : ℕ}

/-- The local `η`-structure used in the simple MPDO argument, formalized as the
quantum-Markov decomposition on the middle subsystem produced by equality in
strong subadditivity. -/
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

/-- Explicit neighboring operators `η_{k,h}` over a fixed Hayashi decomposition.

For each pair of sectors `(k, h)`, the operator `eta k h` acts on the
neighboring bond space `B_kᴿ ⊗ B_hᴸ`, represented in Lean as the matrix algebra
on `Fin (hη.dR k) × Fin (hη.dL h)`. Positivity matches the paper's
`η_{k,h} ≥ 0`. -/
structure ExplicitEtaOperators
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    (hη : EtaStructure ρ_ABC) where
  eta : (k h : Fin hη.m) →
    Matrix (Fin (hη.dR k) × Fin (hη.dL h))
      (Fin (hη.dR k) × Fin (hη.dL h)) ℂ
  eta_pos : ∀ k h, (eta k h).PosSemidef

/-- The underlying family of explicit neighboring operators in an
`ExplicitEtaOperators` witness. -/
abbrev etaOperators
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hη : EtaStructure ρ_ABC}
    (data : ExplicitEtaOperators hη) :=
  data.eta

namespace ExplicitEtaOperators

variable
  {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
    (Fin dA × Fin dB × Fin dC) ℂ}
  {hη : EtaStructure ρ_ABC}

/-- The trace matrix attached to an explicit `η_{k,h}` family. -/
noncomputable def traceMatrix (data : ExplicitEtaOperators hη) :
    Matrix (Fin hη.m) (Fin hη.m) ℂ :=
  fun k h => Matrix.trace (data.eta k h)

@[simp] theorem traceMatrix_apply (data : ExplicitEtaOperators hη)
    (k h : Fin hη.m) :
    data.traceMatrix k h = Matrix.trace (data.eta k h) := rfl

end ExplicitEtaOperators

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
