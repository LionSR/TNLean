/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.Analysis.Entropy

/-!
# Saturation of the area law for MPDO and MPS tensors

This file formalizes the **saturation of the area law** (SAL) predicate for
matrix product density operators and the pure matrix product state analogue,
following arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete), Section 4.4
("Mutual information. Saturation of the area law", line 789) and Section 3
("Saturation of the area law", line 593).

For a chain of `N` spins in a normalized state `σ^{(N)}(M)`, the mutual
information between a block of `L` neighboring spins and the rest is

  `I_L = S_L + S_{N-L} - S_N`

(arXiv:1606.00608, eq. line 797), where `S_L` is the von Neumann entropy of the
reduced state of `L` neighboring spins. A tensor `M` generating MPDO **verifies
SAL** when `I_1 = I_2 = ⋯` (Definition 4.6, line 811). Equivalently
(line 815), `I_L = I_{L+1}` whenever `L + 1 < ⌊N/2⌋`. The pure analogue
(Definition 3.13, line 600) asks the block von Neumann entropies
`S_1^{(N)} = S_2^{(N)} = ⋯` of the pure state to coincide.

## Main definitions

* `Matrix.partialTraceRight`: partial trace over the second factor of a general
  product index `α × β`.
* `blockReducedState`: the reduced state of the first `L` of `L + K` contiguous
  spins.
* `MPOTensor.normalizedMPO`: the normalized density operator
  `σ^{(N)}(M) = ρ^{(N)}(M) / tr[ρ^{(N)}(M)]`.
* `MPOTensor.reducedBlockState`: the reduced state of the first `L` spins of
  `σ^{(N)}(M)`.
* `MPOTensor.blockEntropy`: the block entropy `S_L`.
* `MPOTensor.mutualInfoChain`: the mutual information `I_L = S_L + S_{N-L} - S_N`.
* `MPOTensor.IsSAL`: the saturation-of-the-area-law predicate for MPDO.
* `MPSTensor.normalizedPureState`, `MPSTensor.pureBlockEntropy`,
  `MPSTensor.IsSAL`: the pure-state analogues.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Definition 4.6
  (line 811), Definition 3.13 (line 600), eq. line 797.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

/-! ## General partial trace over the second factor -/

namespace Matrix

variable {α β : Type*} [Fintype β]

/-- **Partial trace over the second factor** of a product index `α × β`.

For a matrix `X` indexed by `α × β`, this produces the `α × α` matrix

  `(partialTraceRight X) i j = ∑ k : β, X (i, k) (j, k)`.

This generalizes `Matrix.traceRight` (specialized to `Fin d × Fin d'`) to an
arbitrary product index, as needed for contiguous-block reduced states indexed
by function types `Fin L → Fin d`. -/
noncomputable def partialTraceRight (X : Matrix (α × β) (α × β) ℂ) :
    Matrix α α ℂ :=
  fun i j => ∑ k : β, X (i, k) (j, k)

@[simp]
theorem partialTraceRight_apply (X : Matrix (α × β) (α × β) ℂ) (i j : α) :
    partialTraceRight X i j = ∑ k : β, X (i, k) (j, k) := rfl

/-- The partial trace over the second factor preserves Hermiticity. -/
theorem partialTraceRight_isHermitian {X : Matrix (α × β) (α × β) ℂ}
    (hX : X.IsHermitian) : (partialTraceRight X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [partialTraceRight_apply, star_sum]
  exact Finset.sum_congr rfl fun k _ => hX.apply (i, k) (j, k)

/-- The partial trace over the second factor preserves positive semidefiniteness.
The reduced state is a sum of submatrices of `X`, one per traced-out index. -/
theorem PosSemidef.partialTraceRight [Finite α] {X : Matrix (α × β) (α × β) ℂ}
    (hX : X.PosSemidef) : (Matrix.partialTraceRight X).PosSemidef := by
  cases nonempty_fintype α
  have h_eq : (Matrix.partialTraceRight X : Matrix α α ℂ)
      = ∑ k : β, X.submatrix (fun a => (a, k)) (fun a => (a, k)) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.submatrix_apply]
    rfl
  rw [h_eq]
  exact Matrix.posSemidef_sum _ fun _ _ => hX.submatrix _

/-- The trace is invariant under the partial trace over the second factor. -/
theorem trace_partialTraceRight [Fintype α] (X : Matrix (α × β) (α × β) ℂ) :
    (partialTraceRight X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTraceRight_apply]
  rw [Fintype.sum_prod_type]

end Matrix

/-! ## Contiguous-block reduced state -/

/-- The identification splitting a configuration on `L + K` contiguous spins into
its first `L` and last `K` parts:
`(Fin (L + K) → Fin d) ≃ (Fin L → Fin d) × (Fin K → Fin d)`. -/
def blockSplitEquiv (d L K : ℕ) :
    (Fin (L + K) → Fin d) ≃ (Fin L → Fin d) × (Fin K → Fin d) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin d))).trans
    (Equiv.sumArrowEquivProdArrow (Fin L) (Fin K) (Fin d))

/-- The reduced state of the first `L` of `L + K` contiguous spins, obtained by
tracing out the last `K` spins after splitting the index via `blockSplitEquiv`. -/
noncomputable def blockReducedState (d L K : ℕ)
    (ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  Matrix.partialTraceRight
    (ρ.submatrix (blockSplitEquiv d L K).symm (blockSplitEquiv d L K).symm)

/-- The block reduced state preserves Hermiticity. -/
theorem blockReducedState_isHermitian {d L K : ℕ}
    {ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ}
    (hρ : ρ.IsHermitian) : (blockReducedState d L K ρ).IsHermitian :=
  Matrix.partialTraceRight_isHermitian (hρ.submatrix _)

/-- The block reduced state preserves positive semidefiniteness. -/
theorem blockReducedState_posSemidef {d L K : ℕ}
    {ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ}
    (hρ : ρ.PosSemidef) : (blockReducedState d L K ρ).PosSemidef :=
  (hρ.submatrix _).partialTraceRight

/-- The block reduced state preserves the trace. -/
theorem blockReducedState_trace {d L K : ℕ}
    (ρ : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ) :
    (blockReducedState d L K ρ).trace = ρ.trace := by
  rw [blockReducedState, Matrix.trace_partialTraceRight]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact (blockSplitEquiv d L K).symm.sum_comp (fun p => ρ p p)

/-! ## Normalized MPO and block entropies -/

namespace MPOTensor

variable {d D : ℕ}

/-- The **normalized density operator** of the MPO for system size `N`:

  `σ^{(N)}(M) = ρ^{(N)}(M) / tr[ρ^{(N)}(M)]`.

This is the convention of arXiv:1606.00608, line 792: entropic quantities are
always taken on the normalized state. -/
noncomputable def normalizedMPO (M : MPOTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (Matrix.trace (mpo M N))⁻¹ • mpo M N

/-- The normalized MPO is positive semidefinite when `M` generates an MPDO: the
normalizing scalar `(tr ρ)⁻¹` is a nonnegative real, so it preserves positive
semidefiniteness. -/
theorem normalizedMPO_posSemidef (M : MPOTensor d D) (N : ℕ)
    (hM : (mpo M N).PosSemidef) : (normalizedMPO M N).PosSemidef := by
  rw [normalizedMPO]
  have htr_nonneg : (0 : ℂ) ≤ (mpo M N).trace := hM.trace_nonneg
  have hre : 0 ≤ (mpo M N).trace.re := htr_nonneg.1
  have him : (mpo M N).trace.im = 0 := (Complex.le_def.mp htr_nonneg).2.symm
  set r : ℝ := (mpo M N).trace.re with hr
  have htr_eq : (mpo M N).trace = (r : ℂ) := Complex.ext rfl (by simp [him, hr])
  have hinv_eq : ((mpo M N).trace)⁻¹ = ((r⁻¹ : ℝ) : ℂ) := by
    rw [htr_eq, Complex.ofReal_inv]
  rw [hinv_eq]
  exact hM.smul (a := ((r⁻¹ : ℝ) : ℂ)) (by exact_mod_cast inv_nonneg.mpr hre)

/-- The normalized MPO is Hermitian when `M` generates an MPDO. -/
theorem normalizedMPO_isHermitian (M : MPOTensor d D) (N : ℕ)
    (hM : (mpo M N).PosSemidef) : (normalizedMPO M N).IsHermitian :=
  (normalizedMPO_posSemidef M N hM).isHermitian

/-- The normalized MPO has unit trace when the unnormalized trace is nonzero. -/
theorem normalizedMPO_trace (M : MPOTensor d D) (N : ℕ)
    (hN : (mpo M N).trace ≠ 0) : (normalizedMPO M N).trace = 1 := by
  rw [normalizedMPO, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hN]

/-- The reindexing equiv that views a configuration on `N = L + (N - L)` spins as
one on `L + (N - L)` spins, used to feed `normalizedMPO M N` into the
contiguous-block reduced state. -/
def blockReindexEquiv (d N L : ℕ) (hL : L ≤ N) :
    (Fin N → Fin d) ≃ (Fin (L + (N - L)) → Fin d) :=
  Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' hL).symm) (Equiv.refl (Fin d))

/-- The **reduced state of the first `L` spins** of the normalized state
`σ^{(N)}(M)`, for `L ≤ N`. -/
noncomputable def reducedBlockState (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  blockReducedState d L (N - L)
    ((normalizedMPO M N).submatrix (blockReindexEquiv d N L hL).symm
      (blockReindexEquiv d N L hL).symm)

/-- The reduced block state is Hermitian when `M` generates an MPDO. -/
theorem reducedBlockState_isHermitian (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) : (reducedBlockState M N L hL).IsHermitian :=
  blockReducedState_isHermitian ((normalizedMPO_isHermitian M N hM).submatrix _)

/-- The reduced block state is positive semidefinite when `M` generates an MPDO. -/
theorem reducedBlockState_posSemidef (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) : (reducedBlockState M N L hL).PosSemidef :=
  blockReducedState_posSemidef ((normalizedMPO_posSemidef M N hM).submatrix _)

/-- The **block entropy** `S_L`: the von Neumann entropy of the reduced state of
the first `L` spins of the normalized state `σ^{(N)}(M)`.

Source: arXiv:1606.00608, line 797 (`S_L` is the von Neumann entropy of the
reduced state of `L` neighboring spins). -/
noncomputable def blockEntropy (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) : ℝ :=
  vonNeumannEntropy (reducedBlockState M N L hL)
    (reducedBlockState_isHermitian M N L hL hM)

/-- The **mutual information** `I_L = S_L + S_{N-L} - S_N` between a block of `L`
spins and the rest of the chain, for the normalized state `σ^{(N)}(M)`.

Source: arXiv:1606.00608, eq. line 797. -/
noncomputable def mutualInfoChain (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) : ℝ :=
  blockEntropy M N L hL hM
    + blockEntropy M N (N - L) (Nat.sub_le N L) hM
    - blockEntropy M N N (le_refl N) hM

/-- The mutual information equals `S_L + S_{N-L} - S_N`, the source formula
(arXiv:1606.00608, eq. line 797). This holds by definition. -/
theorem mutualInfoChain_eq (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) :
    mutualInfoChain M N L hL hM
      = blockEntropy M N L hL hM
        + blockEntropy M N (N - L) (Nat.sub_le N L) hM
        - blockEntropy M N N (le_refl N) hM :=
  rfl

/-- A tensor `M` **verifies saturation of the area law** (SAL) if it generates
MPDO, every system-size density operator has nonzero trace (so the normalized
state is well defined), and the mutual information is constant in the block size:
`I_L = I_{L+1}` for all `L` with `L + 1 < ⌊N/2⌋`, for all `N`.

Source: arXiv:1606.00608, Definition 4.6 (line 811), with the equivalent
form `I_L = I_{L+1}` for `L + 1 < ⌊N/2⌋` (line 815). -/
def IsSAL (M : MPOTensor d D) : Prop :=
  ∃ hMpdo : IsMPDO M, (∀ N, (mpo M N).trace ≠ 0) ∧
    ∀ N L : ℕ, (h : L + 1 < N / 2) →
      mutualInfoChain M N L (by omega) (hMpdo N)
        = mutualInfoChain M N (L + 1) (by omega) (hMpdo N)

end MPOTensor

/-! ## Pure-state analogue -/

namespace MPSTensor

variable {d D : ℕ}

/-- The (unnormalized) pure-state density operator `|V^{(N)}(A)⟩⟨V^{(N)}(A)|` for
system size `N`, with matrix elements
`(σ, τ) ↦ mpv A σ * conj (mpv A τ)`.

Source: arXiv:1606.00608, Section 3 (the state `|V^{(N)}(A)⟩`), line 595. -/
noncomputable def pureState (A : MPSTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  Matrix.vecMulVec (fun σ => mpv A σ) (star fun σ => mpv A σ)

/-- The pure-state density operator is positive semidefinite (it is a rank-one
projector up to normalization). -/
theorem pureState_posSemidef (A : MPSTensor d D) (N : ℕ) :
    (pureState A N).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

/-- The pure-state density operator is Hermitian. -/
theorem pureState_isHermitian (A : MPSTensor d D) (N : ℕ) :
    (pureState A N).IsHermitian :=
  (pureState_posSemidef A N).isHermitian

/-- The **normalized pure state** `σ^{(N)}(A) = |V⟩⟨V| / tr[|V⟩⟨V|]`. -/
noncomputable def normalizedPureState (A : MPSTensor d D) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  (Matrix.trace (pureState A N))⁻¹ • pureState A N

/-- The normalized pure state is positive semidefinite. -/
theorem normalizedPureState_posSemidef (A : MPSTensor d D) (N : ℕ) :
    (normalizedPureState A N).PosSemidef := by
  rw [normalizedPureState]
  have hP := pureState_posSemidef A N
  have htr_nonneg : (0 : ℂ) ≤ (pureState A N).trace := hP.trace_nonneg
  have hre : 0 ≤ (pureState A N).trace.re := htr_nonneg.1
  have him : (pureState A N).trace.im = 0 := (Complex.le_def.mp htr_nonneg).2.symm
  set r : ℝ := (pureState A N).trace.re with hr
  have htr_eq : (pureState A N).trace = (r : ℂ) := Complex.ext rfl (by simp [him, hr])
  have hinv_eq : ((pureState A N).trace)⁻¹ = ((r⁻¹ : ℝ) : ℂ) := by
    rw [htr_eq, Complex.ofReal_inv]
  rw [hinv_eq]
  exact hP.smul (a := ((r⁻¹ : ℝ) : ℂ)) (by exact_mod_cast inv_nonneg.mpr hre)

/-- The normalized pure state is Hermitian. -/
theorem normalizedPureState_isHermitian (A : MPSTensor d D) (N : ℕ) :
    (normalizedPureState A N).IsHermitian :=
  (normalizedPureState_posSemidef A N).isHermitian

/-- The reduced state of the first `L` spins of the normalized pure state
`σ^{(N)}(A)`, for `L ≤ N`. -/
noncomputable def reducedPureBlockState (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  blockReducedState d L (N - L)
    ((normalizedPureState A N).submatrix
      (MPOTensor.blockReindexEquiv d N L hL).symm
      (MPOTensor.blockReindexEquiv d N L hL).symm)

/-- The reduced pure block state is Hermitian. -/
theorem reducedPureBlockState_isHermitian (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) :
    (reducedPureBlockState A N L hL).IsHermitian :=
  blockReducedState_isHermitian ((normalizedPureState_isHermitian A N).submatrix _)

/-- The **pure block entropy** `S_L^{(N)}(A)`: the von Neumann entropy of the
reduced state of the first `L` spins of the normalized pure state `σ^{(N)}(A)`.

Source: arXiv:1606.00608, eq. line 597. -/
noncomputable def pureBlockEntropy (A : MPSTensor d D) (N L : ℕ) (hL : L ≤ N) : ℝ :=
  vonNeumannEntropy (reducedPureBlockState A N L hL)
    (reducedPureBlockState_isHermitian A N L hL)

/-- A tensor `A` **saturates the area law** (SAL) if the block entropies of the
generated pure state are constant in the block size:
`S_L^{(N)}(A) = S_{L+1}^{(N)}(A)` for all `L` with `L + 1 < ⌊N/2⌋`, for all `N`.

Source: arXiv:1606.00608, Definition 3.13 (line 600):
`S_1^{(N)}(A) = S_2^{(N)}(A) = ⋯ = S_{N/2}^{(N)}(A)`. -/
def IsSAL (A : MPSTensor d D) : Prop :=
  ∀ N L : ℕ, (h : L + 1 < N / 2) →
    pureBlockEntropy A N L (by omega)
      = pureBlockEntropy A N (L + 1) (by omega)

end MPSTensor
