/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.MPDO.ZCL
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
- `MPOTensor.normalizedFourSiteTail` /
  `MPOTensor.reducedBlockState_four_three_apply`: the normalized one-site
  virtual tail closing the three-site marginal of the four-site MPO.
- `MPOTensor.normalizedFourSiteTail_ne_zero` /
  `MPOTensor.exists_normalizedFourSiteTail_entry_ne_zero`: nonvanishing of the
  tail and selection of a nonzero virtual entry.
- `MPOTensor.inverseMapThreeSiteContraction` /
  `MPOTensor.inverseMapThreeSiteContraction_eq`: the double inverse-map
  contraction at lines 1415--1438 of Appendix C.2 in arXiv:1606.00608.
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
- `MPOTensor.exists_etaStructure_reducedBlockState_three_of_isSAL`: the
  first-three-site marginal of every chain of length at least four has this
  local structure.
- `MPOTensor.exists_etaStructure_reducedBlockState_of_isSAL`: the four-site
  specialization retained for subsequent arguments.
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
- `MPOTensor.sal_zcl_implies_rank_one_T_of_posSemidef`: the same consequence
  derived from positive semidefiniteness of `T` and constant trace powers.
- `MPOTensor.SectorPairingData`: the sector tensors $|l_k)$ and functionals
  $(r_k|$ of arXiv:1606.00608, Appendix C.2, with the pairing
  $T_{k,h}=(r_k|l_h)$ and the displayed zero-correlation-length identity.
- `MPOTensor.SectorPairingData.mul_self_eq_self` /
  `MPOTensor.SectorPairingData.linearIndependent_l`: idempotence of the sector
  trace matrix from the zero-correlation-length identity, and linear
  independence of the sector tensors from primitivity and an independent
  family of subspaces containing each sector tensor.
- `MPOTensor.SectorPairingData.pairing_sq_eq_pairing_cube` /
  `MPOTensor.SectorPairingData.tracePowersConstant`: the unconditional matrix
  identity $T^2=T^3$ and the resulting constant trace powers of $T$, with no
  independence hypothesis on the sector tensors.
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

The raw double inverse-map contraction (arXiv:1606.00608, Appendix C.2,
lines 1415--1438) is `MPOTensor.inverseMapThreeSiteContraction_eq`. The
Hayashi-sector comparison then gives a factorization of the concrete tensor
`K` whose neighboring operators satisfy, for every `N`,
\[
  \widetilde\sigma^{(N)}(K)
    = \bigoplus_{k_1,\ldots,k_N}\bigotimes_{n=1}^N \eta_{k_n,k_{n+1}}.
\]
The inverse-map factorization has a coherently positive choice, and
`MPOTensor.nonempty_etaLocalStructureData_of_isSAL` assembles its neighboring
operators into the common two-site bond of Proposition C.8 from injectivity and
SAL alone.

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
For the concrete inverse-map sector families,
`MPOTensor.closedSectorTraceMatrix_normalized_relations` proves the normalized
square--cube and trace-power identities from source zero correlation length.
The remaining problem is to exclude the nilpotent generalized zero-eigenspace
of the concrete trace matrix without an additional hypothesis absent from
Lemma C.5. It is recorded in
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

/-- The virtual matrix obtained by tracing the fourth physical site of the
normalized four-site MPO:

\[
  R_4 = \operatorname{tr}(\rho^{(4)}(K))^{-1}
    \sum_i K^{i,i}.
\]

The scalar is the normalization of the full four-site state. This matrix is
the one-site specialization of the virtual tail in the three-site marginal
formula at lines 1343--1348, later denoted by $m$ at lines 1430--1433.

Source: arXiv:1606.00608, lines 792--793 and Appendix C.2, lines 1343--1348.
The later inverse-map contraction at lines 1415--1438 uses this tail but is not
part of the definition. -/
noncomputable def normalizedFourSiteTail (K : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ :=
  (Matrix.trace (mpo K 4))⁻¹ • physTraceTransfer K

/-- The normalized three-site marginal of the four-site MPO is the product of
the first three local tensors closed against `normalizedFourSiteTail`:

\[
  \bigl(\sigma^{(4)}_3(K)\bigr)_{u,v}
    = \operatorname{tr}\!\left(K^{u_1,v_1}K^{u_2,v_2}K^{u_3,v_3}R_4\right).
\]

This is the four-site instance of the three-site marginal formula at lines
1343--1348. It supplies the normalized tail occurring in the inverse-map
calculation at lines 1415--1438; it does not make the subsequent comparison
with the Hayashi decomposition.

Source: arXiv:1606.00608, lines 792--793 and Appendix C.2, lines 1343--1348;
compare lines 1415--1438. -/
theorem reducedBlockState_four_three_apply
    (K : MPOTensor d D) (u v : Fin 3 → Fin d) :
    K.reducedBlockState 4 3 (by omega) u v =
      Matrix.trace
        (K.evalWord (List.ofFn u) (List.ofFn v) * normalizedFourSiteTail K) := by
  rw [reducedBlockState_eq_sum]
  rw [normalizedMPO, normalizedFourSiteTail, physTraceTransfer]
  simp only [Matrix.smul_apply, mpo_apply, mpoMatrixEntry]
  have hwords (a : Fin 3 → Fin d) (x : Fin 1 → Fin d) :
      List.ofFn (Fin.append a x ∘ Fin.cast (show 4 = 3 + 1 by omega)) =
        List.ofFn a ++ List.ofFn x := by
    rw [← List.ofFn_fin_append]
    congr 1
  simp_rw [hwords]
  have heval (x : Fin 1 → Fin d) :
      K.evalWord (List.ofFn u ++ List.ofFn x) (List.ofFn v ++ List.ofFn x) =
        K.evalWord (List.ofFn u) (List.ofFn v) *
          K.evalWord (List.ofFn x) (List.ofFn x) := by
    exact evalWord_append K _ _ _ _ (by simp)
  simp_rw [heval]
  let z : Fin 1 := 0
  have hone (x : Fin 1 → Fin d) :
      K.evalWord (List.ofFn x) (List.ofFn x) = K (x z) (x z) := by
    simp [z]
  simp_rw [hone]
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin d)).symm
    (fun x : Fin 1 → Fin d ↦
      (K.mpo 4).trace⁻¹ •
        Matrix.trace
          (K.evalWord (List.ofFn u) (List.ofFn v) * K (x z) (x z)))]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  simp_rw [← Matrix.trace_smul]
  rw [← Matrix.trace_sum]
  congr 1
  rw [← Finset.smul_sum]
  rw [← Finset.mul_sum]
  rw [Matrix.mul_smul]

/-- The normalized one-site tail is nonzero whenever the four-site MPO has
nonzero trace. Equivalently, the normalized three-site marginal cannot be
closed against the zero virtual matrix.

This is the four-site instance of the observation that the matrix $m$ in
Appendix C.2 has a nonzero entry; the source uses such an entry in the next
sector-factorization step.

Source: arXiv:1606.00608, Appendix C.2, lines 1431--1434, with the
normalization convention at lines 792--793. -/
theorem normalizedFourSiteTail_ne_zero
    (K : MPOTensor d D) (htrace : (mpo K 4).trace ≠ 0) :
    normalizedFourSiteTail K ≠ 0 := by
  intro htail
  have hred : K.reducedBlockState 4 3 (by omega) = 0 := by
    ext u v
    rw [reducedBlockState_four_three_apply, htail]
    simp
  have hunit := reducedBlockState_trace K 4 3 (by omega) htrace
  rw [hred] at hunit
  simp at hunit

/-- A nonzero four-site trace supplies virtual indices at which the normalized
one-site tail does not vanish:

\[
  \exists\,\beta,\alpha,\qquad (R_4)_{\beta,\alpha}\ne 0.
\]

These are precisely the indices selected at line 1434 before the sector
factorization at lines 1435--1437; no SAL or injectivity hypothesis is needed
for this selection once the four-site state has nonzero trace.

Source: arXiv:1606.00608, Appendix C.2, lines 1431--1437. -/
theorem exists_normalizedFourSiteTail_entry_ne_zero
    (K : MPOTensor d D) (htrace : (mpo K 4).trace ≠ 0) :
    ∃ β α : Fin D, normalizedFourSiteTail K β α ≠ 0 := by
  by_contra h
  push Not at h
  apply normalizedFourSiteTail_ne_zero K htrace
  ext β α
  exact h β α

/-- The contraction obtained by applying the inverse tensor to the first and
third sites of a three-site MPO word.

Here `R` is the virtual matrix obtained by contracting the remaining sites.
With $X_{\alpha,\beta}$ denoting the corresponding component of
${\cal K}^{-1}$, this is the left-hand side of the double-sum contraction
identity at lines 1415--1438 of arXiv:1606.00608.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1438. -/
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

This is the contraction-collapse step at lines 1422--1438 of arXiv:1606.00608,
immediately before the sector-factorization equation.

**Local fix (tail index):** the source display at lines 1422--1438
writes $m_{\beta_3,\alpha_3}$. Direct contraction of the two matrix units
gives $m_{\beta_3,\alpha_1}$, as shown by the formula above. The correction
is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1422--1438. -/
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
    let hM : (mpo M N).PosSemidef := (Classical.choose hSAL) N (by omega)
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
  have hNpos : 0 < N := by omega
  rcases Classical.choose_spec hSAL with ⟨_, hstep⟩
  have hEq := hstep N 1 (by omega) (by omega)
  simp only [mutualInfoChain] at hEq
  have hEABC := vonNeumannEntropy_tripartiteSplit_eq_blockEntropy M
    (N := N) (a := 1) (b := 1) (c := N - 3) (by omega) (hMpdo N hNpos)
  have hEC := vonNeumannEntropy_traceC_eq_blockEntropy M
    (N := N) (a := 1) (b := 1) (c := N - 3) (by omega) (hMpdo N hNpos)
  have hEAC := vonNeumannEntropy_traceAC_eq_blockEntropy M
    (N := N) (a := 1) (b := 1) (c := N - 3) (by omega) (hMpdo N hNpos)
  have hEA := vonNeumannEntropy_traceA_eq_blockEntropy M
    (N := N) (a := 1) (b := 1) (c := N - 3) (by omega) (hMpdo N hNpos)
  rw [hEABC, hEAC, hEC, hEA]
  rw [blockEntropy_congr M N (show 1 + 1 + (N - 3) = N - 1 by omega)
      (by omega) (Nat.sub_le N 1) (hMpdo N hNpos),
    blockEntropy_congr M N (show 1 + (N - 3) = N - (1 + 1) by omega)
      (by omega) (Nat.sub_le N (1 + 1)) (hMpdo N hNpos)]
  linarith [hEq]

/-- Saturation of the area law gives equality in strong subadditivity for the
three-site reduced state of the four-site periodic chain.

Source: arXiv:1606.00608, Appendix C.2, Lemma Lsigma3. -/
theorem isSSAEquality_threeSite_of_isSAL (M : MPOTensor d D) (hSAL : IsSAL M) :
    let hM : (mpo M 4).PosSemidef := (Classical.choose hSAL) 4 (by omega)
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

/-- **Lemma Lsigma3.** If `K` satisfies the strong area law, then the first-three-site
marginal of every periodic chain of length at least four admits a quantum Markov
decomposition on the middle site.

The decomposition is obtained first for the marginal on the first (N-1) sites,
with consecutive regions of lengths (1), (1), and (N-3), and is then
preserved while the last (N-4) sites of the third region are traced out.

Source: arXiv:1606.00608, Appendix C.2, Lemma Lsigma3, lines 1351--1371. -/
theorem exists_etaStructure_reducedBlockState_three_of_isSAL
    {d D : ℕ} (K : MPOTensor d D) (hSAL : IsSAL K) {N : ℕ} (hN : 4 ≤ N) :
    Nonempty
      (EtaStructure
        ((K.reducedBlockState N 3 (by omega)).submatrix
          (fun p : Fin d × Fin d × Fin d ↦ ![p.1, p.2.1, p.2.2])
          (fun p : Fin d × Fin d × Fin d ↦ ![p.1, p.2.1, p.2.2]))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  let N := 4 + n
  let hM : (mpo K N).PosSemidef := (Classical.choose hSAL) N (by omega)
  let hNm1 : 1 + 1 + (N - 3) ≤ N := by omega
  let ρflat :=
    (K.reducedBlockState N (1 + 1 + (N - 3)) hNm1).submatrix
      (tripartiteSplitEquiv d 1 1 (N - 3)).symm
      (tripartiteSplitEquiv d 1 1 (N - 3)).symm
  let eSite : Fin d ≃ Fin (d ^ 1) :=
    (Equiv.funUnique (Fin 1) (Fin d)).symm.trans finFunctionFinEquiv
  let E := eSite.prodCongr (eSite.prodCongr (Equiv.refl (Fin (d ^ (N - 3)))))
  have hρflatPos : ρflat.PosSemidef := by
    exact (reducedBlockState_posSemidef K N (1 + 1 + (N - 3)) hNm1 hM).submatrix _
  have hρflatTrace : ρflat.trace = 1 := by
    dsimp only [ρflat]
    rw [Matrix.trace_submatrix_equiv]
    exact reducedBlockState_trace K N (1 + 1 + (N - 3)) hNm1
      ((Classical.choose_spec hSAL).1 N (by omega))
  have hEqFlat : IsSSAEquality ρflat hρflatPos.isHermitian := by
    simpa [ρflat, hM] using isSSAEquality_tripartite_of_isSAL K hSAL hN
  have hEqSite :
      IsSSAEquality (ρflat.submatrix E E) (hρflatPos.isHermitian.submatrix E) :=
    isSSAEquality_submatrix_prodEquiv ρflat hρflatPos.isHermitian
      eSite eSite (Equiv.refl _) hEqFlat
  have hρsiteTrace : (ρflat.submatrix E E).trace = 1 := by
    rw [Matrix.trace_submatrix_equiv]
    exact hρflatTrace
  have hηLarge : Nonempty (EtaStructure (ρflat.submatrix E E)) :=
    sal_implies_eta_structure (ρflat.submatrix E E)
      ⟨hρflatPos.submatrix E, hρsiteTrace⟩ hEqSite
  let eC : Fin (d ^ (N - 3)) ≃ Fin d × (Fin (N - 4) → Fin d) :=
    finFunctionFinEquiv.symm |>.trans
      (Equiv.arrowCongr (finCongr (show N - 3 = 1 + (N - 4) by omega)) (Equiv.refl _)) |>.trans
      (blockSplitEquiv d 1 (N - 4)) |>.trans
      (finFunctionFinEquiv.prodCongr (Equiv.refl _)) |>.trans
      (eSite.symm.prodCongr (Equiv.refl _))
  have hηSmall := Entropy.exists_quantumMarkovDecomposition_rightMarginalAlong
    eC (ρflat.submatrix E E) hηLarge
  have hstate : Entropy.rightMarginalAlong eC (ρflat.submatrix E E) =
      (K.reducedBlockState N 3 (by omega)).submatrix
        (fun p : Fin d × Fin d × Fin d ↦ ![p.1, p.2.1, p.2.2])
        (fun p : Fin d × Fin d × Fin d ↦ ![p.1, p.2.1, p.2.2]) := by
    ext p q
    simp only [Entropy.rightMarginalAlong, Matrix.submatrix_apply]
    simp only [ρflat, Matrix.submatrix_apply]
    have hconfig (r : Fin d × Fin d × Fin d) (x : Fin (N - 4) → Fin d) :
        (tripartiteSplitEquiv d 1 1 (N - 3)).symm
              (E (r.1, r.2.1, eC.symm (r.2.2, x))) ∘
            Fin.cast (show 3 + (N - 4) = 1 + 1 + (N - 3) by omega) =
          Fin.append ![r.1, r.2.1, r.2.2] x := by
      dsimp only [tripartiteSplitEquiv, E, eC, eSite, N]
      simp only [Equiv.symm_trans, Equiv.prodCongr_symm, Equiv.refl_symm,
        Equiv.prodCongr_apply, Equiv.coe_trans, Equiv.funUnique_symm_apply,
        Equiv.trans_apply, Equiv.prodAssoc_symm_apply, Function.comp_apply,
        Equiv.symm_apply_apply, Equiv.symm_symm, Equiv.coe_refl, Prod.map_apply,
        id_eq, Nat.succ_eq_add_one]
      rw [blockSplitEquiv_symm_apply, blockSplitEquiv_symm_apply,
        blockSplitEquiv_symm_apply]
      funext i
      refine Fin.addCases (fun j : Fin 3 ↦ ?_) (fun j : Fin (N - 4) ↦ ?_) i
      · fin_cases j <;>
          simp [Fin.append, Fin.addCases, Equiv.arrowCongr, Function.comp_def]
      · simp only [Nat.reduceAdd, Fin.append, Equiv.arrowCongr, Equiv.coe_refl,
          finCongr_symm, Function.comp_def, finCongr_apply,
          Equiv.refl_symm, Equiv.symm_mk, Equiv.coe_fn_mk, Fin.addCases,
          Fin.val_cast, Order.lt_one_iff, uniqueElim_const, Fin.cast_cast,
          eq_rec_constant, Function.comp_apply, Fin.val_natAdd, Order.lt_two_iff,
          Fin.val_castLT, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
          ↓reduceDIte, Fin.cast_eq_self, Fin.val_subNat, add_lt_iff_neg_left,
          not_lt_zero, Fin.cast_natAdd, Fin.subNat_addNat]
        split
        · omega
        · split
          · omega
          · apply congrArg x
            apply Fin.ext
            simp only [Fin.val_subNat, Fin.val_cast, Fin.val_natAdd]
            omega
    simp_rw [reducedBlockState_cast K
      (show 3 + (N - 4) = 1 + 1 + (N - 3) by omega) hNm1]
    simp_rw [hconfig]
    simpa only [Nat.add_zero] using
      (collapse_last K (N := N) (a := 3) (b := 0) (c := N - 4)
        (show 3 + 0 + (N - 4) ≤ N by omega)
        ![p.1, p.2.1, p.2.2] ![q.1, q.2.1, q.2.2])
  rwa [hstate] at hηSmall

/-- **Four-site specialization of Lemma Lsigma3.** If `K` satisfies the strong
area law, then the three-site marginal of its normalized four-site periodic
state admits a quantum Markov decomposition on the middle site.

Source: arXiv:1606.00608, Appendix C.2, Lemma Lsigma3, lines 1351--1363;
normalization convention at lines 792--793.

This is the (N=4) specialization of
`exists_etaStructure_reducedBlockState_three_of_isSAL`. -/
theorem exists_etaStructure_reducedBlockState_of_isSAL
    {d D : ℕ} (K : MPOTensor d D) (hSAL : IsSAL K) :
    Nonempty
      (EtaStructure
        ((K.reducedBlockState 4 3 (by omega)).submatrix
          (fun p : Fin d × Fin d × Fin d ↦ ![p.1, p.2.1, p.2.2])
          (fun p : Fin d × Fin d × Fin d ↦ ![p.1, p.2.1, p.2.2]))) := by
  exact exists_etaStructure_reducedBlockState_three_of_isSAL K hSAL (N := 4) (by omega)

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

/-- **Lemma C.5, PSD-corrected matrix form**: if the auxiliary trace matrix `T`
is positive semidefinite, then
`Matrix.PosSemidef.trace_powers_constant_implies_rank_one` gives its rank-one
factorization directly.

The primitivity hypothesis is kept in the statement because it is part of the
paper's construction of `T`, but the PSD rank-one criterion is stronger and does
not use primitivity once `trace T = 1` and constant trace powers are known.

**Scope restriction (positive-semidefinite trace matrix):** Positive
semidefiniteness is absent from arXiv:1606.00608, Appendix C.2, Lemma
`SALZCL` (Lemma C.5), lines 1484--1499. The primitivity hypothesis is retained
for comparison with the source but is unused by this corrected argument.
Documented in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
theorem sal_zcl_implies_rank_one_T_of_posSemidef
    (T : Matrix (Fin n) (Fin n) ℝ)
    (_hPrimitive : Matrix.IsPrimitive T)
    (hPSD : T.PosSemidef)
    (hTrace : Matrix.trace T = 1)
    (hZCL : Matrix.TracePowersConstant T) :
    ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 := by
  rcases hPSD.trace_powers_constant_implies_rank_one hTrace hZCL with ⟨a, b, hT⟩
  refine ⟨a, b, hT, ?_⟩
  rw [← Matrix.trace_vecMulVec, ← hT]
  exact hTrace

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

/-- **Unconditional `T^2=T^3`** for sector tensors satisfying the
zero-correlation-length identity, with no independence hypothesis on the
closed sector tensors $|l_k)$ or the functionals $(r_k|$: pairing the
identity with $(r_j|$ and $|l_i)$ gives this matrix identity directly.

Source: arXiv:1606.00608, lines 1494--1497. This is the pairing computation
of `docs/paper-gaps/cpgsv17_pf_rank_one.tex`, §3 ("What the operator-valued
ZCL identity implies"). -/
theorem pairing_sq_eq_pairing_cube (data : SectorPairingData T V) : T ^ 2 = T ^ 3 :=
  Matrix.pow_two_eq_pow_three_of_pairing_idempotent data.pairing data.pairing_operator_idempotent

/-- **Unconditional constant trace powers of the sector trace matrix.** The
traces of all positive powers of the sector trace matrix agree with its
trace: $\operatorname{tr}(T^N)=\operatorname{tr}(T)$ for $N\geq 1$, with no
independence hypothesis on the closed sector tensors $|l_k)$ or the
functionals $(r_k|$.

Source: arXiv:1606.00608, lines 1494--1497. -/
theorem tracePowersConstant (data : SectorPairingData T V) : Matrix.TracePowersConstant T :=
  Matrix.tracePowersConstant_of_pairing_idempotent data.pairing data.pairing_operator_idempotent

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
