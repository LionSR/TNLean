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
- `MPOTensor.inverseMapThreeSiteContraction` /
  `MPOTensor.inverseMapThreeSiteContraction_eq`: the double inverse-map
  contraction used in the proof of Lemma C.4.
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

The raw double inverse-map contraction in the proof of Lemma propSN is
`MPOTensor.inverseMapThreeSiteContraction_eq`. The earliest missing connection
to Appendix C.2 is the comparison of that contraction with the conjugated,
reindexed Hayashi decomposition. This comparison must produce a sector
factorization of the concrete tensor `K` satisfying, for every `N`,
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

/-- The contraction obtained by applying the inverse tensor to the first and
third sites of a three-site MPO word.

Here `R` is the virtual matrix obtained by contracting the remaining sites.
With $X_{\alpha,\beta}$ denoting the corresponding component of
${\cal K}^{-1}$, this is the left-hand side of the calculation following
Equation Qketc in the proof of Lemma propSN.

Source: arXiv:1606.00608, Appendix C.2, Lemma propSN, lines 1415--1438. -/
noncomputable def inverseMapThreeSiteContraction
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (α₁ β₁ α₃ β₃ : Fin D) (p₂ : Fin (d * d)) : ℂ :=
  ∑ p₁ : Fin (d * d), ∑ p₃ : Fin (d * d),
    inverseTensor K hK p₁ α₁ β₁ * inverseTensor K hK p₃ α₃ β₃ *
      Matrix.trace
        (K.toMPSTensor p₁ * K.toMPSTensor p₂ * K.toMPSTensor p₃ * R)

/-- Applying ${\cal K}^{-1}$ to the two end sites leaves one entry of the
middle tensor and the complementary entry of the virtual tail:

\[
  \sum_{p_1,p_3} ({\cal K}^{-1})^{\alpha_1,\beta_1}_{p_1}
    ({\cal K}^{-1})^{\alpha_3,\beta_3}_{p_3}
    \tr({\cal K}^{p_1}{\cal K}^{p_2}{\cal K}^{p_3}R)
  = {\cal K}^{p_2}_{\beta_1,\alpha_3}R_{\beta_3,\alpha_1}.
\]

This is the inverse-map calculation immediately before Equation formK in
the proof of Lemma propSN.

**Local fix (tail index):** the source display following Equation Qketc
writes $m_{\beta_3,\alpha_3}$. Direct contraction of the two matrix units
gives $m_{\beta_3,\alpha_1}$, as shown by the formula above. The correction
is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, Lemma propSN, lines 1422--1438. -/
theorem inverseMapThreeSiteContraction_eq
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (α₁ β₁ α₃ β₃ : Fin D) (p₂ : Fin (d * d)) :
    inverseMapThreeSiteContraction K hK R α₁ β₁ α₃ β₃ p₂ =
      K.toMPSTensor p₂ β₁ α₃ * R β₃ α₁ := by
  classical
  let a : Fin (d * d) → ℂ := fun p ↦ inverseTensor K hK p α₁ β₁
  let b : Fin (d * d) → ℂ := fun p ↦ inverseTensor K hK p α₃ β₃
  let C : Fin (d * d) → Matrix (Fin D) (Fin D) ℂ := K.toMPSTensor
  change
    (∑ p₁ : Fin (d * d), ∑ p₃ : Fin (d * d),
      (a p₁ * b p₃) • Matrix.trace (C p₁ * C p₂ * C p₃ * R)) =
        C p₂ β₁ α₃ * R β₃ α₁
  simp_rw [← Matrix.trace_smul]
  simp_rw [← Matrix.trace_sum Finset.univ]
  have hmat :
      (∑ i, ∑ j, (a i * b j) • (C i * C p₂ * C j * R)) =
        (∑ i, a i • C i) * C p₂ * (∑ j, b j • C j) * R := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp [Matrix.mul_assoc, smul_smul, mul_comm]
  have ha : ∑ i, a i • C i = Matrix.single α₁ β₁ (1 : ℂ) := by
    simpa [a, C] using inverseTensor_spec K hK α₁ β₁
  have hb : ∑ i, b i • C i = Matrix.single α₃ β₃ (1 : ℂ) := by
    simpa [b, C] using inverseTensor_spec K hK α₃ β₃
  rw [hmat, ha, hb, Matrix.single_mul_mul_single, Matrix.trace_single_mul]
  simp

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

end RankOneT

end MPOTensor
