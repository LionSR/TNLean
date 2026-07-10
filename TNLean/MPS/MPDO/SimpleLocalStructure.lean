/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.Entropy.MarkovChain
import TNLean.MPS.MPDO.MutualInfoMonotone
import TNLean.MPS.Chain.VirtualInsertion
import TNLean.Algebra.PerronFrobenius.RankOne
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Simple MPDO local structure

This file states the local entropy-theoretic part of the simple MPDO
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
- `MPOTensor.isSSAEquality_tripartite_of_isSAL` and
  `MPOTensor.isSSAEquality_threeSite_of_isSAL`: saturation of the area law gives
  equality in strong subadditivity for the marginal used in Lemma C.2 and for
  its three-site specialization.
- `MPOTensor.sal_implies_eta_structure`: equality in strong subadditivity gives
  the local structure by the Hayashi equality characterization.
- `MPOTensor.etaOperators`: the dependent type of explicit neighboring operator
  families over a fixed Hayashi decomposition.
- `MPOTensor.ExplicitEtaOperators`: the explicit neighboring operators
  `η_{k,h}` together with positivity.
- `MPOTensor.ExplicitEtaOperators.traceMatrix` /
  `MPOTensor.ExplicitEtaOperators.traceMatrixRe`: the complex trace matrix of an
  explicit `η`-family and its real-part input to the subsequent
  Perron–Frobenius step.
- `MPOTensor.ExplicitEtaOperators.ofHayashiMarkov`: concrete extraction of an
  explicit `η_{k,h}` family from a Hayashi decomposition witness, as the
  Kronecker product of the sector-indexed neighboring reduced states.
- `MPOTensor.ExplicitEtaOperators.traceMatrixRe_nonneg`: positivity of each
  neighboring operator gives entrywise nonnegativity of the real trace matrix.
- `MPOTensor.ExplicitEtaOperators.traceMatrixRe_ofHayashiMarkov_posSemidef`:
  the special sector-reduced extraction has the positive-semidefinite all-ones
  trace matrix.
- `MPOTensor.ExplicitEtaOperators.trace_traceMatrixRe_ofHayashiMarkov`: the
  trace of that all-ones matrix is the number of sectors.
- `MPOTensor.sal_zcl_implies_rank_one_T`: the conditional Lemma C.5 consequence,
  proved relative to the Perron–Frobenius rank-one input.
- `MPOTensor.sal_zcl_implies_rank_one_T_of_posSemidef`: the same consequence
  with the Perron–Frobenius input derived from positive semidefiniteness of `T`.
- `MPOTensor.SectorPairingData`: the sector tensors $|l_k)$ and functionals
  $(r_k|$ of arXiv:1606.00608, Appendix C.2, with the pairing
  $T_{k,h}=(r_k|l_h)$ and the displayed zero-correlation-length identity.
- `MPOTensor.SectorPairingData.mul_self_eq_self` /
  `MPOTensor.SectorPairingData.linearIndependent_l`: idempotence of the sector
  trace matrix from the zero-correlation-length identity, and linear
  independence of the sector tensors from primitivity and an independent
  family of subspaces containing each sector tensor.
- `MPOTensor.sal_zcl_implies_rank_one_T_of_pairing_idempotent` /
  `MPOTensor.sal_zcl_implies_rank_one_T_of_sector_supports`: the rank-one
  factorization at lines 1484--1499, derived from the zero-correlation-length
  identity through idempotence of $T$.

## Implementation note

In the paper, Lemma C.2 supplies the Markov direct-sum decomposition. Lemma C.4
then constructs the explicit operators `η_{k,h}` by applying local inverse maps
coming from the injectivity of the simple tensor. The present file now contains
that inverse-map layer for an injective simple MPO tensor, given by
`MPOTensor.inverseTensor`, `MPOTensor.physRealize`, and
`MPOTensor.physRealizeLeft`.

`MPOTensor.ExplicitEtaOperators.ofHayashiMarkov` constructs a canonical family
directly from the Hayashi decomposition witness as the Kronecker product of
the sector-indexed neighboring reduced states: the right reduced state in
sector k and the left reduced state in sector h. This extraction is strictly
weaker than
the paper's `K⁻¹`-based construction: it does not invoke the inverse-map layer
and its trace matrix is identically one. By contrast, the paper's neighboring
operators have the generally nonconstant primitive trace matrix whose kh-entry
is the trace of ηₖₕ. Consequently these two families cannot simply be
identified.

The earliest missing connection to Appendix C.2 is the conclusion of Lemma
propSN: the inverse-map calculation must produce a sector factorization of the
concrete tensor `K` satisfying, for every `N`,
\[
  \widetilde\sigma^{(N)}(K)
    = \bigoplus_{k_1,\ldots,k_N}\bigotimes_{n=1}^N \eta_{k_n,k_{n+1}}.
\]
Only after that identity is available can its sector operators be assembled
into the common two-site bond of Proposition 3to4.

Lemma C.5 is further isolated to the finite-dimensional Perron–Frobenius step:
for a primitive nonnegative matrix `T`, constant traces of positive powers are
*claimed* (in the paper) to force `T` to have rank one. The universally
quantified form of that claim is false — see
`TNLean/Archive/PerronFrobeniusRankOneCounterexample.lean` for an explicit
3 × 3 witness.

The corrected matrix theorem now available is
`Matrix.PosSemidef.trace_powers_constant_implies_rank_one`: positive
semidefiniteness of the concrete trace matrix, together with trace
normalization and constant trace powers, supplies the missing diagonalizability
and forces a rank-one factorization. The theorem
`MPOTensor.sal_zcl_implies_rank_one_T_of_posSemidef` connects this corrected
criterion to the Lemma C.5 structure. What remains on
the MPDO side is to prove that the sector trace matrix `T` from the paper's
inverse-map construction has additional structure excluding the nilpotent
zero-eigenspace. Positivity of the individual η-operators alone gives only
entrywise nonnegativity of the trace matrix. The special sector-reduced family
`ofHayashiMarkov` does have a positive-semidefinite all-ones trace matrix, but
its identification with the paper's inverse-map family is not available.

A second exclusion of the nilpotent zero-eigenspace goes through the pairing.
`MPOTensor.SectorPairingData` records the closed sector tensors $|l_k)$, the
functionals $(r_k|$, the pairing $T_{k,h}=(r_k|l_h)$, and the
zero-correlation-length identity at lines 1490--1493. The theorem
`MPOTensor.sal_zcl_implies_rank_one_T_of_pairing_idempotent` derives the
rank-one factorization once the closed sector tensors are linearly independent.
Three obligations remain: construct the sector families and their pairing from
the inverse-map factorization at lines 1407--1482, derive the operator identity
from zero correlation length, and prove linear independence. They are recorded in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemmas C.2, C.4, and C.5
- Hayashi, *Quantum Information: An Introduction*, Springer 2006, Theorem 5.24
- Ruskai, JMP 43, 4358 (2002)
- Hayden, Jozsa, Petz, Winter, Commun. Math. Phys. 246, 359–374 (2004)
-/

open scoped Matrix ComplexOrder BigOperators

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
simple MPO tensor. This is the MPO encoding of
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

section GlobalToLocalSAL

variable {d D : ℕ}

/-- Saturation of the area law gives equality in strong subadditivity for the
three-region marginal used in the proof of Lemma C.2.

The regions have lengths \(1\), \(1\), and \(N-3\). Thus the entropy identity is
\(S_{N-1} + S_1 = S_2 + S_{N-2}\), which is equivalent to \(I_1 = I_2\) after
cancelling the full-chain entropy \(S_N\).

Source: arXiv:1606.00608, Appendix C.2, Lemma Lsigma3. -/
theorem isSSAEquality_tripartite_of_isSAL (M : MPOTensor d D) (hSAL : IsSAL M)
    {N : ℕ} (hN : 4 ≤ N) :
    let hM : (mpo M N).PosSemidef := (Classical.choose hSAL) N
    let h3 : 1 + 1 + (N - 3) ≤ N := by omega
    let ρ_ABC := (M.reducedBlockState N (1 + 1 + (N - 3)) h3).submatrix
      (tripartiteSplitEquiv d 1 1 (N - 3)).symm
      (tripartiteSplitEquiv d 1 1 (N - 3)).symm
    IsSSAEquality ρ_ABC
      ((reducedBlockState_posSemidef M N (1 + 1 + (N - 3)) h3 hM).submatrix _).1 := by
  classical
  dsimp only
  rw [IsSSAEquality]
  let hMpdo : IsMPDO M := Classical.choose hSAL
  rcases Classical.choose_spec hSAL with ⟨_, hstep⟩
  have hEq := hstep N 1 (by omega) (by omega)
  simp only [mutualInfoChain] at hEq
  have hEABC := vonNeumannEntropy_tripartiteSplit_eq_blockEntropy M
    (N := N) (a := 1) (b := 1) (c := N - 3) (by omega) (hMpdo N)
  have hEC := vonNeumannEntropy_traceC_eq_blockEntropy M
    (N := N) (a := 1) (b := 1) (c := N - 3) (by omega) (hMpdo N)
  have hEAC := vonNeumannEntropy_traceAC_eq_blockEntropy M
    (N := N) (a := 1) (b := 1) (c := N - 3) (by omega) (hMpdo N)
  have hEA := vonNeumannEntropy_traceA_eq_blockEntropy M
    (N := N) (a := 1) (b := 1) (c := N - 3) (by omega) (hMpdo N)
  rw [hEABC, hEAC, hEC, hEA]
  rw [blockEntropy_congr M N (show 1 + 1 + (N - 3) = N - 1 by omega)
      (by omega) (Nat.sub_le N 1) (hMpdo N),
    blockEntropy_congr M N (show 1 + (N - 3) = N - (1 + 1) by omega)
      (by omega) (Nat.sub_le N (1 + 1)) (hMpdo N)]
  linarith [hEq]

/-- Saturation of the area law gives equality in strong subadditivity for the
three-site reduced state of the four-site periodic chain.

Source: arXiv:1606.00608, Appendix C.2, Lemma Lsigma3. -/
theorem isSSAEquality_threeSite_of_isSAL (M : MPOTensor d D) (hSAL : IsSAL M) :
    let hM : (mpo M 4).PosSemidef := (Classical.choose hSAL) 4
    let h3 : 1 + 1 + (4 - 3) ≤ 4 := by omega
    let ρ_ABC := (M.reducedBlockState 4 (1 + 1 + (4 - 3)) h3).submatrix
      (tripartiteSplitEquiv d 1 1 (4 - 3)).symm
      (tripartiteSplitEquiv d 1 1 (4 - 3)).symm
    IsSSAEquality ρ_ABC
      ((reducedBlockState_posSemidef M 4 (1 + 1 + (4 - 3)) h3 hM).submatrix _).1 := by
  simpa using isSSAEquality_tripartite_of_isSAL M hSAL (N := 4) (by omega)

end GlobalToLocalSAL

section LocalSAL

variable {dA dB dC : ℕ}

/-- The local `η`-structure used in the simple MPDO argument, formalized as the
quantum-Markov decomposition on the middle subsystem produced by equality in
strong subadditivity. -/
abbrev EtaStructure
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) : Type :=
  Entropy.QuantumMarkovDecomposition ρ_ABC

/-- **Lemma C.2, local entropy form**: strong area law implies the local
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
neighboring bond space `B_kᴿ ⊗ B_hᴸ`, the matrix algebra with row and column
indices `Fin (hη.dR k) × Fin (hη.dL h)`. -/
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

This is the direct real-valued input to the Perron–Frobenius matrix `T` used
later in Appendix C.2, Lemma C.5. -/
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
`B_k^R ⊗ B_h^L`, which provides the data for explicit `η_{k,h}` witnesses.

This extraction does not use the injectivity hypothesis on the MPO tensor
`K`: it is the sector-reduced layer supplied directly by the Hayashi
decomposition. See the module docstring for the remaining connection to the
Appendix C.2 `K⁻¹`-based construction. -/
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
feeds the rank-one Perron–Frobenius step of Lemma C.5 with a concrete
rank-one trace matrix (the all-ones matrix). -/
@[simp] theorem traceMatrix_ofHayashiMarkov
    (hη : EtaStructure ρ_ABC) (k h : Fin hη.m) :
    (ofHayashiMarkov hη).traceMatrix k h = 1 := by
  have hR : (Matrix.traceRight (hη.ρ_right k)).trace = 1 := by
    rw [Matrix.traceRight, Matrix.trace_partialTraceRight]
    exact (hη.hρ_right_dm k).2
  have hL : (Matrix.traceLeft (hη.ρ_left h)).trace = 1 := by
    rw [← Matrix.trace_eq_trace_traceLeft]
    exact (hη.hρ_left_dm h).2
  simp [traceMatrix_apply, ofHayashiMarkov, Matrix.trace_kronecker, hR, hL]

/-- Real-part version of `traceMatrix_ofHayashiMarkov`: the extracted
`η`-family yields `T_{k,h} = 1` entrywise on the real Perron–Frobenius matrix. -/
@[simp] theorem traceMatrixRe_ofHayashiMarkov
    (hη : EtaStructure ρ_ABC) (k h : Fin hη.m) :
    (ofHayashiMarkov hη).traceMatrixRe k h = 1 := by
  have h := traceMatrix_ofHayashiMarkov hη k h
  simp only [traceMatrix_apply] at h
  simp [traceMatrixRe_apply, h]

/-- The trace of the real all-ones matrix from the Hayashi--Markov extraction
is the number of sectors.

This concerns the sector-reduced family in `ofHayashiMarkov`, not yet the
inverse-map family of arXiv:1606.00608, Appendix C.2, lines 1413--1455. -/
@[simp] theorem trace_traceMatrixRe_ofHayashiMarkov
    (hη : EtaStructure ρ_ABC) :
    Matrix.trace (ofHayashiMarkov hη).traceMatrixRe = hη.m := by
  rw [Matrix.trace]
  change ∑ i, (ofHayashiMarkov hη).traceMatrixRe i i = _
  simp_rw [traceMatrixRe_ofHayashiMarkov]
  simp

/-- The real trace matrix of the Hayashi--Markov extraction is positive
semidefinite.

This is the positive-semidefinite all-ones matrix. It concerns the
sector-reduced family in `ofHayashiMarkov`; identifying that family with the
inverse-map construction of arXiv:1606.00608, Appendix C.2, lines 1413--1455,
is a separate question. -/
theorem traceMatrixRe_ofHayashiMarkov_posSemidef
    (hη : EtaStructure ρ_ABC) :
    (ofHayashiMarkov hη).traceMatrixRe.PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin hη.m => (1 : ℝ)) using 1
  ext k h
  rw [traceMatrixRe_ofHayashiMarkov]
  simp [Matrix.vecMulVec]

/-- Positivity of each neighboring operator makes the corresponding real trace
entry nonnegative.

This is the entrywise nonnegativity needed for the primitive-matrix hypothesis.
It is strictly weaker than the matrix-level positive semidefiniteness needed by
`Matrix.PosSemidef.trace_powers_constant_implies_rank_one`; proving that
stronger property for the sector trace matrix is the remaining MPDO-specific
evidence. -/
theorem traceMatrixRe_nonneg (data : ExplicitEtaOperators hη) (k h : Fin hη.m) :
    0 ≤ data.traceMatrixRe k h :=
  (RCLike.nonneg_iff.mp (data.eta_pos k h).trace_nonneg).1

end ExplicitEtaOperators

end LocalSAL

section RankOneT

variable {n : ℕ}

/-- **Lemma C.5, conditional matrix form**: once the matrix `T` attached to the
local `η`-structure is known to be primitive and to have constant trace on all
positive powers, the remaining Perron–Frobenius input forces `T` to be rank one.

The normalization `a ⬝ᵥ b = 1` is then immediate from `trace T = 1` and the
identity `trace (vecMulVec a b) = a ⬝ᵥ b`.

**Unfaithful:** relies on `hPF : PrimitiveTracePowersConstantImpliesRankOne T`,
which restates the conclusion and is false in general (counterexample in
`TNLean/Archive/PerronFrobeniusRankOneCounterexample.lean`); the source Lemma
C.5 (`SALZCL`, lines 1484--1502) instead derives the factorization from
Perron--Frobenius fixed-point theory. Documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. Elimination: discharge via the
PSD-corrected variant `sal_zcl_implies_rank_one_T_of_posSemidef` once
positive-semidefiniteness of `T` is available as a hypothesis; the open
follow-up is tracked in that note. -/
theorem sal_zcl_implies_rank_one_T
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hTrace : Matrix.trace T = 1)
    (hZCL : Matrix.TracePowersConstant T)
    (hPF : Matrix.PrimitiveTracePowersConstantImpliesRankOne T) :
    ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 := by
  rcases hPF hPrimitive hZCL with ⟨a, b, hT⟩
  refine ⟨a, b, hT, ?_⟩
  rw [← Matrix.trace_vecMulVec, ← hT]
  exact hTrace

/-- **Lemma C.5, PSD-corrected matrix form**: if the auxiliary trace matrix `T`
is positive semidefinite, then the corrected finite-dimensional theorem
`Matrix.PosSemidef.trace_powers_constant_implies_rank_one` supplies the
conditional Perron--Frobenius input used by `MPOTensor.sal_zcl_implies_rank_one_T`.

The primitivity hypothesis is kept in the statement because it is part of the
paper's construction of `T`, but the PSD rank-one criterion is stronger and does
not use primitivity once `trace T = 1` and constant trace powers are known. -/
theorem sal_zcl_implies_rank_one_T_of_posSemidef
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hPSD : T.PosSemidef)
    (hTrace : Matrix.trace T = 1)
    (hZCL : Matrix.TracePowersConstant T) :
    ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 :=
  sal_zcl_implies_rank_one_T T hPrimitive hTrace hZCL
    (Matrix.primitive_trace_powers_constant_implies_rank_one_of_posSemidef hPSD hTrace)

/-! ### Sector tensors and the pairing route to rank one

Appendix C.2 of arXiv:1606.00608 obtains the sector trace matrix by pairing
sector tensors. After the isometry $U$, the injective simple tensor splits as
a direct sum over sectors $k$ of pairs $l_k,r_k$ at lines 1436--1448. The
closed tensors $|l_k)$ and $(r_k|$ pair to $T_{k,h}=(r_k|l_h)$ at lines
1473--1482. The zero-correlation-length identity at lines 1490--1493 states
that the operator $\sum_k |l_k)(r_k|$ equals its own square. The declarations
below record this pairing and derive the rank-one factorization of $T$ through
`Matrix.mul_self_eq_self_of_pairing_idempotent`. -/

/-- The sector tensors of arXiv:1606.00608, Appendix C.2, paired into the
sector trace matrix $T$.

The vector space $V$ carries the closed sector tensors $|l_k)$ and the
functionals $(r_k|$ at lines 1473--1477. The recorded identities are the
pairing $T_{k,h}=(r_k|l_h)$ at lines 1478--1482 and the
zero-correlation-length identity at lines 1490--1493. Constructing these
families from the injective simple tensor factorization at lines 1436--1448
remains open; see the module docstring. -/
structure SectorPairingData (T : Matrix (Fin n) (Fin n) ℝ)
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The closed sector tensors $|l_k)$; arXiv:1606.00608, lines 1473--1477. -/
  l : Fin n → V
  /-- The closed sector functionals $(r_k|$; arXiv:1606.00608,
  lines 1473--1477. -/
  r : Fin n → Module.Dual ℝ V
  /-- The pairing identity $T_{k,h}=(r_k|l_h)$; arXiv:1606.00608,
  lines 1478--1482. -/
  pairing : ∀ k h, T k h = r k (l h)
  /-- The zero-correlation-length identity
  $\sum_k |l_k)(r_k|=\sum_{k,h}T_{k,h}|l_k)(r_h|$, evaluated on a vector;
  arXiv:1606.00608, lines 1490--1493. -/
  zcl : ∀ v : V, ∑ k, r k v • l k = ∑ k, ∑ h, (T k h * r h v) • l k

namespace SectorPairingData

variable {T : Matrix (Fin n) (Fin n) ℝ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The zero-correlation-length identity makes the pairing operator
$\sum_k |l_k)(r_k|$ equal to its own square. The right-hand side of the
identity at lines 1490--1493 expands to this square after replacing
$T_{k,h}$ by the pairing $(r_k|l_h)$ from lines 1478--1482 of
arXiv:1606.00608. -/
theorem pairing_operator_idempotent (data : SectorPairingData T V) (v : V) :
    ∑ k, data.r k (∑ j, data.r j v • data.l j) • data.l k
      = ∑ k, data.r k v • data.l k := by
  have hexpand : ∀ k, data.r k (∑ j, data.r j v • data.l j)
      = ∑ j, T k j * data.r j v := by
    intro k
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, data.pairing k j]
    ring
  calc ∑ k, data.r k (∑ j, data.r j v • data.l j) • data.l k
      = ∑ k, ∑ j, (T k j * data.r j v) • data.l k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hexpand k, Finset.sum_smul]
    _ = ∑ k, data.r k v • data.l k := (data.zcl v).symm

/-- **Idempotence of the sector trace matrix** for sector tensors satisfying
the zero-correlation-length identity: $T^2=T$.

**Scope restriction (linear independence):** the source argument at
arXiv:1606.00608, lines 1484--1499 neither assumes nor derives
linear independence of the sector tensors; see the marker on
`Matrix.mul_self_eq_self_of_pairing_idempotent` and
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.  The hypothesis `hl` is discharged
by `SectorPairingData.linearIndependent_l` once each sector tensor lies in the
corresponding member of an independent family of subspaces. -/
theorem mul_self_eq_self (data : SectorPairingData T V)
    (hl : LinearIndependent ℝ data.l) : T * T = T :=
  Matrix.mul_self_eq_self_of_pairing_idempotent data.pairing hl
    data.pairing_operator_idempotent

/-- The traces of all positive powers of the sector trace matrix agree with
its trace: $\operatorname{tr}(T^N)=\operatorname{tr}(T)$ for $N\geq 1$, as at
arXiv:1606.00608, lines 1494--1497, recovered from idempotence.

**Scope restriction (linear independence):** inherited from
`SectorPairingData.mul_self_eq_self`; documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
theorem tracePowersConstant (data : SectorPairingData T V)
    (hl : LinearIndependent ℝ data.l) : Matrix.TracePowersConstant T :=
  Matrix.tracePowersConstant_of_mul_self_eq_self (data.mul_self_eq_self hl)

/-- Primitivity of the sector trace matrix makes every closed sector tensor
$|l_k)$ nonzero: some entry of column $k$ of $T$ is positive, and that entry
is the pairing of $|l_k)$ against a functional (arXiv:1606.00608,
lines 1478--1482). -/
theorem l_ne_zero (data : SectorPairingData T V)
    (hPrimitive : Matrix.IsPrimitive T) (k : Fin n) : data.l k ≠ 0 := by
  intro hzero
  obtain ⟨j, hj⟩ := hPrimitive.exists_col_pos k
  rw [data.pairing j k, hzero, map_zero] at hj
  exact lt_irrefl 0 hj

/-- Linear independence of the closed sector tensors from an independent family
of subspaces: if each $|l_k)$ lies in the corresponding member of an independent
family of subspaces of $V$ and the sector trace matrix is primitive, then the
family $|l_k)$ is linearly independent.

**Scope restriction (independent subspaces):** the subspace family is not displayed
in arXiv:1606.00608. Lines 1436--1448 give a sector splitting of the physical
indices, but the closed tensors $|l_k)$ at lines 1473--1477 live in a common
bond space after the physical sector legs are contracted. Whether the
inverse-map construction supplies such supports, or proves independence by
another argument, remains open; documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
theorem linearIndependent_l (data : SectorPairingData T V)
    (support : Fin n → Submodule ℝ V)
    (hmem : ∀ k, data.l k ∈ support k)
    (hsupp : iSupIndep support)
    (hPrimitive : Matrix.IsPrimitive T) :
    LinearIndependent ℝ data.l :=
  hsupp.linearIndependent support hmem (data.l_ne_zero hPrimitive)

end SectorPairingData

/-- **Rank one from sector-pairing idempotence.**

For a sector trace matrix $T$ paired from sector tensors satisfying the
zero-correlation-length identity at arXiv:1606.00608, lines 1490--1493,
linear independence and trace normalization give
$T_{k,h}=a_kb_h$ with $\sum_k a_kb_k=1$, the conclusion at lines 1484--1499.
Unlike the positive-semidefinite variant
`MPOTensor.sal_zcl_implies_rank_one_T_of_posSemidef`, the constant trace
powers are derived, not assumed. Primitivity of $T$ is not needed once linear
independence is assumed. It enters the independent-subspace form
`MPOTensor.sal_zcl_implies_rank_one_T_of_sector_supports`, where it makes
the closed sector tensors nonzero.

**Scope restriction (linear independence):** the source lemma neither assumes
nor derives linear independence of the sector tensors; documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.  The hypothesis `hl` is discharged
by `SectorPairingData.linearIndependent_l` when each sector tensor lies in the
corresponding member of an independent family of subspaces. -/
theorem sal_zcl_implies_rank_one_T_of_pairing_idempotent
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : Matrix (Fin n) (Fin n) ℝ)
    (data : SectorPairingData T V)
    (hl : LinearIndependent ℝ data.l)
    (hTrace : Matrix.trace T = 1) :
    ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 := by
  obtain ⟨a, b, hT⟩ :=
    Matrix.hasRankOneFactorization_of_mul_self_eq_self
      (data.mul_self_eq_self hl) hTrace
  refine ⟨a, b, hT, ?_⟩
  rw [← Matrix.trace_vecMulVec, ← hT]
  exact hTrace

/-- **Rank one from independent sector supports.**

This is the rank-one conclusion at arXiv:1606.00608, lines 1484--1499, with
linear independence of the closed sector tensors derived from primitivity and
an independent family of subspaces containing the respective sector tensors.

**Scope restriction (independent subspaces):** the subspace family carrying the
closed sector tensors is not displayed in arXiv:1606.00608; documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
theorem sal_zcl_implies_rank_one_T_of_sector_supports
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : Matrix (Fin n) (Fin n) ℝ)
    (data : SectorPairingData T V)
    (support : Fin n → Submodule ℝ V)
    (hmem : ∀ k, data.l k ∈ support k)
    (hsupp : iSupIndep support)
    (hPrimitive : Matrix.IsPrimitive T)
    (hTrace : Matrix.trace T = 1) :
    ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 :=
  sal_zcl_implies_rank_one_T_of_pairing_idempotent T data
    (data.linearIndependent_l support hmem hsupp hPrimitive) hTrace

end RankOneT

end MPOTensor
