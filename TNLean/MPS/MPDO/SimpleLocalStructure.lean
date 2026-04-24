/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.Entropy.MarkovChain
import TNLean.MPS.Chain.VirtualInsertion
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Simple MPDO local structure

This file records the local entropy-theoretic part of the simple MPDO
renormalization fixed-point argument from Appendix C.2 of
arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete).

## Main declarations

- `MPOTensor.IsInjective`: injectivity of a simple MPO tensor, expressed via the
  doubled-index MPS tensor.
- `MPOTensor.inverseTensor` / `MPOTensor.inverseTensor_spec`: the concrete
  inverse tensor `K⁻¹` and its matrix-unit contraction identity.
- `MPOTensor.physRealize` / `MPOTensor.physRealize_spec` /
  `MPOTensor.physRealize_mul`: the physical realization of right virtual
  insertions and its multiplicativity.
- `MPOTensor.physRealizeLeft` / `MPOTensor.physRealizeLeft_spec`: the left-bond
  analogue of the physical realization map.
- `MPOTensor.EtaStructure`: the quantum-Markov decomposition on the middle
  subsystem supplied by equality in strong subadditivity.
- `MPOTensor.sal_implies_eta_structure`: the Lean form of the entropy step in
  Lemma C.3. We formalize the strong-area-law input locally as equality in
  strong subadditivity for a normalized three-site reduced state.
- `MPOTensor.etaOperators`: the dependent type of explicit neighboring operator
  families over a fixed Hayashi decomposition.
- `MPOTensor.ExplicitEtaOperators`: the explicit neighboring operators
  `η_{k,h}` together with positivity.
- `MPOTensor.ExplicitEtaOperators.traceMatrix` /
  `MPOTensor.ExplicitEtaOperators.traceMatrixRe`: the complex trace matrix of an
  explicit `η`-family and its real-part interface to the downstream
  Perron–Frobenius step.
- `MPOTensor.ExplicitEtaOperators.ofHayashiMarkov`: concrete extraction of an
  explicit `η_{k,h}` family from a Hayashi decomposition witness, as the
  Kronecker product of the sector-indexed neighboring reduced states.
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
injectivity of the simple tensor. The present file now contains that
inverse-map layer for an injective simple MPO tensor, given by
`MPOTensor.inverseTensor`, `MPOTensor.physRealize`, and
`MPOTensor.physRealizeLeft`.

The target `η_{k,h}` family is populated by
`MPOTensor.ExplicitEtaOperators.ofHayashiMarkov`, which constructs the family
directly from the Hayashi decomposition witness as the Kronecker product of
the sector-indexed neighboring reduced states,
`η_{k,h} := tr_C(ρ_right k) ⊗ tr_A(ρ_left h)`. This extraction is strictly
weaker than the paper's `K⁻¹`-based construction — it does not invoke the
injective inverse-map layer — but it supplies a canonical positive
semidefinite family of the correct type, with trace matrix `T_{k,h} = 1`,
and it is sufficient to unblock the downstream local-to-global `HasCommutingForm`
construction (see issue #823). The paper-faithful variant using the
explicit inverse-map layer remains available for future refinement.

Lemma C.4 is further isolated to the finite-dimensional Perron–Frobenius step:
for a primitive nonnegative matrix `T`, constant traces of positive powers are
*claimed* (in the paper) to force `T` to have rank one. We expose that step as
the single hypothesis `Matrix.PrimitiveTracePowersConstantImpliesRankOne`, so
the remaining gap is exactly localized and matches the paper one-to-one.

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
itself. This is the matrix-theoretic consequence of the ZCL step used in
Appendix C.2, Lemma C.4. -/
def TracePowersConstant (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → Matrix.trace (T ^ k) = Matrix.trace T

/-- The missing Perron–Frobenius input for Appendix C.2, Lemma C.4:
for a primitive nonnegative matrix, constant traces of positive powers imply a
rank-one factorization.

This is intentionally stated as a local hypothesis rather than a new global
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
  change
    ∑ p : Fin (d * d),
      MPSTensor.decompositionMap (A := K.toMPSTensor) hK
          (Matrix.single α β (1 : ℂ)) p • K.toMPSTensor p
        = Matrix.single α β (1 : ℂ)
  exact MPSTensor.decompositionMap_sum (A := K.toMPSTensor) hK
    (Matrix.single α β (1 : ℂ))

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
      ∑ q, (physRealize K hK X) p q • K.toMPSTensor q :=
  MPSTensor.physRealize_spec K.toMPSTensor hK X p

/-- `MPOTensor.physRealize` is multiplicative. -/
theorem physRealize_mul (K : MPOTensor d D) (hK : K.IsInjective)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physRealize K hK (X * Y) = physRealize K hK X * physRealize K hK Y :=
  MPSTensor.physRealize_mul K.toMPSTensor hK X Y

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
      ∑ q, (physRealizeLeft K hK X) p q • K.toMPSTensor q :=
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

/-- The type of explicit neighboring operator families `η_{k,h}` over a fixed
Hayashi decomposition.

For each pair of sectors `(k, h)`, the operator `η_{k,h}` acts on the
neighboring bond space `B_kᴿ ⊗ B_hᴸ`, represented in Lean as the matrix algebra
on `Fin (hη.dR k) × Fin (hη.dL h)`. -/
abbrev etaOperators
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    (hη : EtaStructure ρ_ABC) : Type :=
  (k h : Fin hη.m) →
    Matrix (Fin (hη.dR k) × Fin (hη.dL h))
      (Fin (hη.dR k) × Fin (hη.dL h)) ℂ

/-- Explicit neighboring operators `η_{k,h}` together with their positivity.

This structure consists of the operator family from `MPOTensor.etaOperators`
together with the positivity condition `η_{k,h} ≥ 0` from Appendix C.2. -/
structure ExplicitEtaOperators
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    (hη : EtaStructure ρ_ABC) where
  eta : etaOperators hη
  eta_pos : ∀ k h, (eta k h).PosSemidef

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

/-- The real-part trace matrix attached to an explicit `η_{k,h}` family.

This is the direct real-valued interface to the Perron–Frobenius matrix `T`
used later in Appendix C.2, Lemma C.4. -/
noncomputable def traceMatrixRe (data : ExplicitEtaOperators hη) :
    Matrix (Fin hη.m) (Fin hη.m) ℝ :=
  fun k h => (Matrix.trace (data.eta k h)).re

@[simp] theorem traceMatrixRe_apply (data : ExplicitEtaOperators hη)
    (k h : Fin hη.m) :
    data.traceMatrixRe k h = (Matrix.trace (data.eta k h)).re := rfl

/-- **Extraction of explicit neighboring `η`-operators from a Hayashi
decomposition witness.**

Given the quantum-Markov-chain witness `hη` on the middle subsystem, the
sector-indexed density matrices `ρ_right k` on `B_k^R ⊗ C` and `ρ_left h` on
`A ⊗ B_h^L` canonically restrict by partial trace to operators on the
neighboring virtual bond spaces `B_k^R` and `B_h^L`, respectively. Their
Kronecker product is a positive semidefinite operator on
`B_k^R ⊗ B_h^L`, which serves as the explicit `η_{k,h}` witness required by
Appendix C.2.

This extraction does not use the injectivity hypothesis on the MPO tensor
`K`: the Hayashi decomposition witness alone already supplies the
neighboring-bond data needed to populate the `ExplicitEtaOperators` record.
See the module docstring for the relationship with the paper's original
`K⁻¹`-based construction. -/
noncomputable def ofHayashiMarkov (hη : EtaStructure ρ_ABC) :
    ExplicitEtaOperators hη where
  eta k h :=
    Matrix.kroneckerMap (· * ·)
      (Matrix.traceRight (hη.ρ_right k))
      (Matrix.traceLeft (hη.ρ_left h))
  eta_pos k h :=
    ((hη.hρ_right_dm k).1.traceRight).kronecker ((hη.hρ_left_dm h).1.traceLeft)

/-- The trace of each extracted `η_{k,h}` equals the product of the sector
traces, which are both `1` by normalization of the Hayashi density matrices.
This specializes to `T_{k,h} = 1` for the partial-trace-based extraction and
feeds the rank-one Perron–Frobenius step of Lemma C.4 with a concrete
rank-one trace matrix (the all-ones matrix). -/
@[simp] theorem traceMatrix_ofHayashiMarkov
    (hη : EtaStructure ρ_ABC) (k h : Fin hη.m) :
    (ofHayashiMarkov hη).traceMatrix k h = 1 := by
  have hR : (Matrix.traceRight (hη.ρ_right k)).trace = 1 := by
    rw [← Matrix.trace_eq_trace_traceRight]; exact (hη.hρ_right_dm k).2
  have hL : (Matrix.traceLeft (hη.ρ_left h)).trace = 1 := by
    rw [← Matrix.trace_eq_trace_traceLeft]; exact (hη.hρ_left_dm h).2
  simp [traceMatrix_apply, ofHayashiMarkov, Matrix.trace_kronecker, hR, hL]

/-- Real-part version of `traceMatrix_ofHayashiMarkov`: the extracted
`η`-family yields `T_{k,h} = 1` entrywise on the real Perron–Frobenius matrix. -/
@[simp] theorem traceMatrixRe_ofHayashiMarkov
    (hη : EtaStructure ρ_ABC) (k h : Fin hη.m) :
    (ofHayashiMarkov hη).traceMatrixRe k h = 1 := by
  have h := traceMatrix_ofHayashiMarkov hη k h
  simp only [traceMatrix_apply] at h
  simp [traceMatrixRe_apply, h]

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
