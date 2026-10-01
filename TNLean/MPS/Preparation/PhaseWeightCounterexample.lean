/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrthogonalBlockSum
import TNLean.MPS.Preparation.RepeatedBlockCounterexample

/-!
# The approximating state fails for weights with a phase

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") write a tensor as `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ`
with complex weights `|μ_{j,k}| ≤ 1`, at least one of modulus one (eq. (S2)), assert that the
positive part of the blocked tensor is `P = ⊕ⱼ diag(μ_{j,1}^q, …, μ_{j,m_j}^q) ⊗ P_j`
(eq. (S5)), and approximate the state on `N = qM` sites by `V^{⊗M} ∑ⱼ βⱼ |Ω_j⟩` (eq. (S7)),
with `βⱼ = ∑ₖ μ_{j,k}^N` (eq. (S4)). Lemma 1'(ii) bounds the error of this state by
`O((N/q) e^{-γ q/ξ_diag})` for `q = o(N)`.

The positive part is positive semidefinite, so it cannot carry the phases of the weights; they
sit in the isometry `V`, which already supplies the phase `(μⱼ/|μⱼ|)^N` to the `j`-th block, and
`βⱼ = μⱼ^N` counts this phase a second time. This file evaluates the construction for the two
one-dimensional normal blocks `A_1 = (1, 0)` and `A_2 = (0, 1)`, of multiplicity one, with
weights `1` and `μ`, `|μ| = 1`, so that `A⁰ = diag(1, 0)` and `A¹ = diag(0, μ)`
(`phaseBlockTensor`). The states of the two blocks are orthogonal for every `q ≥ 1`, so the overlap
of blocks plays no role. For every block length `q ≥ 1` and every number of blocks `M ≥ 1`, with
`N = qM`, the overlap of the approximating state with the target is `(1 + conj(μ)^N)/2`
(`nonNormalApproxOverlap_phaseBlockTensor`), while with `βⱼ = |μⱼ|^N` the approximating state is
the target itself (`nonNormalApproxOverlap_phaseBlockTensor_norm`). For `μ = -1` and odd `N` the
approximating state is orthogonal to the target, and the error is `1`
(`one_sub_norm_nonNormalApproxOverlap_phaseBlockTensor_neg_one`).

The tensor lies in the domain of Lemma 1'(ii): after ordering its bond coordinates it is the
canonical form of eq. (S2) of a basis of normal tensors in canonical form II with weights
`(1, μ)` (`isBNTCanonicalForm_phaseBlockSector`, `reindex_toTensor_phaseBlockSector`), and it is
the direct sum `⊕ⱼ μⱼ A_j` (`blockSum_phaseBlock`). Both blocks are one-dimensional, so their
transfer maps have no eigenvalue other than `1`, and the hypothesis on the subleading eigenvalue
that defines `ξ_diag` holds for every `λ₂`. For `μ = -1` and every `λ₂` with `0 < |λ₂| < 1`,
along `q = M` odd (`N = q²`, so `q = o(N)`) the error stays `1` while
`(N/q) e^{-γ q/ξ_diag}` tends to zero (`not_approximationError_le_phaseBlockTensor`).

**False source (eqs. (S5)–(S7), complex weights):** for weights that are not nonnegative real
numbers the approximating state of eq. (S7), with the coefficients `βⱼ = ∑ₖ μ_{j,k}^N` of
eq. (S4), does not approximate `|φ_N⟩`, and the bound of Lemma 1'(ii) fails, already for
orthogonal blocks of multiplicity one. The coefficients of eq. (S4) are correct in the expansion
of eq. (S3); the false steps are the block form of eq. (S5), which places the phase in the
positive part, and its use in eqs. (S6) and (S7), where `V^{⊗M}` already carries the phase.
Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.phaseBlockTensor` — the tensor `A⁰ = diag(1, 0)`, `A¹ = diag(0, μ)`.
* `MPSTensor.nonNormalApproxOverlap_phaseBlockTensor` — the overlap `(1 + conj(μ)^N)/2`.
* `MPSTensor.nonNormalApproxOverlap_phaseBlockTensor_norm` — with `βⱼ = |μⱼ|^N` the overlap is
  one.
* `MPSTensor.one_sub_norm_nonNormalApproxOverlap_phaseBlockTensor_neg_one`,
  `MPSTensor.not_approximationError_le_phaseBlockTensor` — for `μ = -1` the error is `1` at odd
  `N`, and the bound of Lemma 1'(ii) fails.
* `MPSTensor.phaseBlockSector`, `MPSTensor.isBNTCanonicalForm_phaseBlockSector`,
  `MPSTensor.reindex_toTensor_phaseBlockSector` — the tensor is, after ordering its bond
  coordinates, the canonical form of eq. (S2) of a basis of normal tensors.
* `MPSTensor.isBNTCanonicalForm_and_not_approximationError_le_phaseBlock` — for `μ = -1` the
  tensor satisfies every hypothesis of Lemma 1'(ii), and the bound fails for it.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7) and Lemma 1'(ii).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix Filter Topology Complex

namespace MPSTensor

/-- The diagonal entries of `A⁰ = diag(1, 0)` and `A¹ = diag(0, μ)`. -/
def phaseBlockDiag (μ : ℂ) : Fin 2 → Fin 2 → ℂ := ![![1, 0], ![0, μ]]

/-- The tensor `A⁰ = diag(1, 0)`, `A¹ = diag(0, μ)`: the canonical form of arXiv:2307.01696,
eq. (S2), with the one-dimensional normal blocks `A_1 = (1, 0)` and `A_2 = (0, 1)`, each of
multiplicity one, with weights `1` and `μ`. -/
abbrev phaseBlockTensor (μ : ℂ) : MPSTensor 2 2 := fun i => diagonal (phaseBlockDiag μ i)

/-- The weights `(1, μ)`, one copy of each block. -/
def phaseBlockWeight (μ : ℂ) : (j : Fin 2) → Fin 1 → ℂ := fun j _ => ![1, μ] j

/-- `phaseBlockTensor μ` is the direct sum `⊕ⱼ μⱼ A_j` of arXiv:2307.01696, eq. (S2), for
`m_j = 1`, of the blocks `A_1 = (1, 0)` and `A_2 = (0, 1)` placed on the bond coordinates `0` and
`1`, with weights `(1, μ)`. -/
theorem blockSum_phaseBlock (μ : ℂ) :
    blockSum repeatedBlockBasis (fun j _ => j) ![1, μ] = phaseBlockTensor μ := by
  funext i
  ext x y
  fin_cases i <;> fin_cases x <;> fin_cases y <;>
    simp [blockSum, coordEmbedding, repeatedBlockBasis, phaseBlockDiag, Fin.sum_univ_two,
      mul_apply, conjTranspose_apply]

/-- The weights `βⱼ = ∑ₖ μ_{j,k}^N = (1, μ^N)` of arXiv:2307.01696, eq. (S4). -/
theorem bntWeight_phaseBlockWeight (μ : ℂ) (N : ℕ) :
    bntWeight (m := fun _ => 1) (phaseBlockWeight μ) N = ![1, μ ^ N] := by
  funext j
  fin_cases j <;> simp [bntWeight, phaseBlockWeight]

private lemma sum_norm_sq_one_vec {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ l, ‖(![1, z] : Fin 2 → ℂ) l‖ ^ 2) = 2 := by
  simp [Fin.sum_univ_two, hz]; norm_num

/-- The normalized weights `α^{(N)} = (1, z)/√2` of weights `(1, z)` with `|z| = 1`. -/
theorem ghzAmplitude_one_vec {z : ℂ} (hz : ‖z‖ = 1) :
    ghzAmplitude ![1, z] = ![invSqrtTwo, invSqrtTwo * z] := by
  funext j
  rw [ghzAmplitude, sum_norm_sq_one_vec hz]
  fin_cases j <;> simp [invSqrtTwo, div_eq_inv_mul]

/-- For `q ≥ 1` the Gram matrix of the blocked tensor is the identity: the `q`-site states of
the two blocks are orthogonal and normalized. -/
theorem diagGram_phaseBlockDiag {μ : ℂ} (hμ : ‖μ‖ = 1) {q : ℕ} (hq : q ≠ 0) :
    diagGram (phaseBlockDiag μ) q = 1 := by
  have h : starRingEnd ℂ μ * μ = 1 := by
    rw [Complex.conj_mul', hμ]; norm_num
  ext e e'
  fin_cases e <;> fin_cases e' <;>
    simp [diagGram, phaseBlockDiag, Fin.sum_univ_two, zero_pow hq, h]

/-- The positive part of the `q`-site blocked tensor is `J Jᴴ`, for `q ≥ 1`. -/
theorem polarPos_phaseBlockTensor {μ : ℂ} (hμ : ‖μ‖ = 1) {q : ℕ} (hq : q ≠ 0) :
    polarPos (physicalMatrix (blockTensor (phaseBlockTensor μ) q)) =
      diagPairEmbedding (Fin 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        (diagPairEmbedding (Fin 2))ᴴ :=
  polarPos_physicalMatrix_blockTensor_diagonal (phaseBlockDiag μ) q PosSemidef.one
    (by rw [Matrix.one_mul, diagGram_phaseBlockDiag hμ hq])

/-- The support projector of the `q`-site blocked tensor is `J Jᴴ`, for `q ≥ 1`. -/
theorem polarSupport_phaseBlockTensor {μ : ℂ} (hμ : ‖μ‖ = 1) {q : ℕ} (hq : q ≠ 0) :
    polarSupport (physicalMatrix (blockTensor (phaseBlockTensor μ) q)) =
      diagPairEmbedding (Fin 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        (diagPairEmbedding (Fin 2))ᴴ :=
  polarSupport_physicalMatrix_blockTensor_diagonal (phaseBlockDiag μ) q PosSemidef.one
    (by rw [Matrix.one_mul, diagGram_phaseBlockDiag hμ hq]) isHermitian_one (Matrix.one_mul 1)
    (Matrix.one_mul _) (R := 1) (Matrix.one_mul 1)

/-- **The overlap for any normalized coefficients.** For `|μ| = 1`, the fixed-point pairs of
the two one-dimensional blocks, coefficients `α` with `|α₁|² + |α₂|² = 1`, every block length
`q ≥ 1`, and every number of blocks `M ≥ 1`, the overlap of the approximating state of
arXiv:2307.01696, eq. (S7), with the target is `(conj(α₁) + conj(α₂))/√2`. -/
theorem nonNormalApproxOverlap_phaseBlockTensor_of_norm {μ : ℂ} (hμ : ‖μ‖ = 1) {q M : ℕ}
    (hq : q ≠ 0) (hM : M ≠ 0) {α : Fin 2 → ℂ} (hα : ‖α 0‖ ^ 2 + ‖α 1‖ ^ 2 = 1) :
    nonNormalApproxOverlap (phaseBlockTensor μ) q M α
        (fun j => embedPair (fun _ : Fin 1 => j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ))) =
      (star (α 0) + star (α 1)) * invSqrtTwo := by
  simp only [embedPair_fixedPointPair_one]
  rw [nonNormalApproxOverlap_diagonal (phaseBlockDiag μ) q M α (fun j => j) (X := 1) (Y := 2)]
  · rw [polarPos_phaseBlockTensor hμ hq]
    simp only [diagPairEmbedding_mul_mul_conjTranspose_apply, Fin.sum_univ_two]
    simp [zero_pow hM, invSqrtTwo]
    ring
  · rw [polarSupport_phaseBlockTensor hμ hq]
    simp only [diagPairEmbedding_mul_mul_conjTranspose_apply, Fin.sum_univ_two]
    have h0 : star (α 0) * α 0 = ((‖α 0‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    have h1 : star (α 1) * α 1 = ((‖α 1‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    simp only [one_apply_eq, one_pow, mul_one, Fin.isValue, ne_eq, zero_ne_one,
      not_false_eq_true, one_apply_ne, zero_pow hM, mul_zero, add_zero, one_ne_zero, zero_add,
      h0, h1]
    exact_mod_cast hα.symm
  · rw [diagGram_phaseBlockDiag hμ hq]
    simp [Fin.sum_univ_two, zero_pow hM]
    norm_num

/-- **The overlap with the printed coefficients** (arXiv:2307.01696, eqs. (S4) and (S7)). For
`|μ| = 1`, the fixed-point pairs of the two blocks, the coefficients `α^{(N)}` of the weights
`βⱼ = μⱼ^N = (1, μ^N)`, every block length `q ≥ 1`, and every number of blocks `M ≥ 1`, with
`N = qM`, `⟨φ~_N|φ_N⟩ = (1 + conj(μ)^N)/2`. -/
theorem nonNormalApproxOverlap_phaseBlockTensor {μ : ℂ} (hμ : ‖μ‖ = 1) {q M : ℕ}
    (hq : q ≠ 0) (hM : M ≠ 0) :
    nonNormalApproxOverlap (phaseBlockTensor μ) q M
        (ghzAmplitude (bntWeight (m := fun _ => 1) (phaseBlockWeight μ) (M * q)))
        (fun j => embedPair (fun _ : Fin 1 => j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ))) =
      (1 + star μ ^ (M * q)) / 2 := by
  have hμN : ‖μ ^ (M * q)‖ = 1 := by rw [norm_pow, hμ, one_pow]
  rw [bntWeight_phaseBlockWeight, ghzAmplitude_one_vec hμN,
    nonNormalApproxOverlap_phaseBlockTensor_of_norm hμ hq hM]
  · simp only [Fin.isValue, cons_val_zero, cons_val_one, star_mul', star_pow]
    have hs : star invSqrtTwo = invSqrtTwo := star_invSqrtTwo
    rw [hs]
    linear_combination (1 + star μ ^ (M * q)) * invSqrtTwo_mul_self
  · simp [hμN, invSqrtTwo]
    norm_num

/-- **With `βⱼ = |μⱼ|^N` the approximating state is exact.** For `|μ| = 1`, the coefficients
`α^{(N)}` of the weights `|μⱼ|^N = (1, 1)`, every block length `q ≥ 1`, and every number of
blocks `M ≥ 1`, the overlap of the approximating state of arXiv:2307.01696, eq. (S7), with the
target is `1`. -/
theorem nonNormalApproxOverlap_phaseBlockTensor_norm {μ : ℂ} (hμ : ‖μ‖ = 1) {q M : ℕ}
    (hq : q ≠ 0) (hM : M ≠ 0) :
    nonNormalApproxOverlap (phaseBlockTensor μ) q M
        (ghzAmplitude fun j => (‖(![1, μ] : Fin 2 → ℂ) j‖ : ℂ) ^ (M * q))
        (fun j => embedPair (fun _ : Fin 1 => j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ))) = 1 := by
  have hβ : (fun j => (‖(![1, μ] : Fin 2 → ℂ) j‖ : ℂ) ^ (M * q)) = ![1, 1] := by
    funext j
    fin_cases j <;> simp [hμ]
  rw [hβ, ghzAmplitude_one_vec norm_one, nonNormalApproxOverlap_phaseBlockTensor_of_norm hμ hq hM]
  · simp only [Fin.isValue, cons_val_zero, cons_val_one, mul_one, star_invSqrtTwo]
    linear_combination 2 * invSqrtTwo_mul_self
  · simp [invSqrtTwo]
    norm_num

/-- **For `μ = -1` and odd `N` the error is `1`.** For odd block length `q` and odd number of
blocks `M`, the approximating state of arXiv:2307.01696, eq. (S7), with the printed coefficients
`βⱼ = μⱼ^N` of eq. (S4), is orthogonal to the target `|0⋯0⟩ - |1⋯1⟩`. -/
theorem one_sub_norm_nonNormalApproxOverlap_phaseBlockTensor_neg_one {q M : ℕ} (hq : Odd q)
    (hM : Odd M) :
    1 - ‖nonNormalApproxOverlap (phaseBlockTensor (-1)) q M
        (ghzAmplitude (bntWeight (m := fun _ => 1) (phaseBlockWeight (-1)) (M * q)))
        (fun j => embedPair (fun _ : Fin 1 => j)
          (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)))‖ = 1 := by
  rw [nonNormalApproxOverlap_phaseBlockTensor (by simp) hq.pos.ne'
    hM.pos.ne', star_neg, star_one, (hM.mul hq).neg_one_pow]
  simp

/-- **Lemma 1'(ii) fails for weights with a phase** (arXiv:2307.01696, Supplemental Material,
Lemma 1'(ii), eq. (S12)). The transfer maps of the one-dimensional blocks of
`phaseBlockTensor (-1)` have no eigenvalue other than `1`
(`norm_le_of_hasEigenvalue_transferMap_repeatedBlockBasis`), so every `λ₂` with
`0 < |λ₂| < 1` bounds their subleading eigenvalues. For every such `λ₂`, every `γ > 0`, and
every constant `C` there is an odd `M ≥ 1` such that, with block length `q = M` (`N = M²`, so
`q = o(N)` along this sequence) and `y = (N/q) e^{-γ q/ξ_diag}`, the error of the approximating
state of eq. (S7) with `βⱼ = μⱼ^N` exceeds `C y e^{C y}`, and in particular exceeds `C y`. -/
theorem not_approximationError_le_phaseBlockTensor {lam₂ : ℂ} (h0 : 0 < ‖lam₂‖)
    (h1 : ‖lam₂‖ < 1) {γ : ℝ} (hγ : 0 < γ) (C : ℝ) :
    ∃ M : ℕ, Odd M ∧
      C * (M * Real.exp (-γ * M / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * M / correlationLength lam₂))) <
        1 - ‖nonNormalApproxOverlap (phaseBlockTensor (-1)) M M
          (ghzAmplitude (bntWeight (m := fun _ => 1) (phaseBlockWeight (-1)) (M * M)))
          (fun j => embedPair (fun _ : Fin 1 => j)
            (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)))‖ := by
  set r := Real.exp (-γ / correlationLength lam₂)
  have hξ := correlationLength_pos h0 h1
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hξ)
  have hxq : ∀ M : ℕ, Real.exp (-γ * M / correlationLength lam₂) = r ^ M := fun M => by
    rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1
    (eventually_mul_pow_mul_exp_lt (Real.exp_pos _).le hr1 le_rfl C 1 one_pos)
  have hodd : Odd (2 * M₀ + 1) := odd_two_mul_add_one M₀
  refine ⟨2 * M₀ + 1, hodd, ?_⟩
  rw [hxq, one_sub_norm_nonNormalApproxOverlap_phaseBlockTensor_neg_one hodd hodd]
  simpa using hM₀ (2 * M₀ + 1) (by omega)

/-! ## The tensor satisfies the hypotheses of Lemma 1'(ii) -/

/-- The canonical form of arXiv:2307.01696, eq. (S2), of `phaseBlockTensor μ` for `μ ≠ 0`: the
basis of the two one-dimensional normal blocks `A_1 = (1, 0)` and `A_2 = (0, 1)`, each of
multiplicity one, with weights `μ_{1,1} = 1` and `μ_{2,1} = μ`. -/
abbrev phaseBlockSector {μ : ℂ} (hμ : μ ≠ 0) : SectorDecomposition 2 :=
  repeatedBlockBasisSector (fun _ => 1) (fun _ => Nat.one_pos) (phaseBlockWeight μ)
    (fun j _ => by
      fin_cases j
      · exact one_ne_zero
      · exact hμ)

/-- The coefficients `βⱼ = ∑ₖ μ_{j,k}^N` of the canonical form (arXiv:2307.01696, eq. (S4)). -/
theorem coeff_phaseBlockSector {μ : ℂ} (hμ : μ ≠ 0) (N : ℕ) :
    (phaseBlockSector hμ).coeff N = bntWeight (m := fun _ => 1) (phaseBlockWeight μ) N :=
  rfl

/-- **The canonical form of `phaseBlockTensor μ` is a basis of normal tensors** for `|μ| = 1`
(arXiv:2307.01696, eq. (S2)): the blocks are irreducible, left-canonical, with normalized
self-overlap, their states are linearly independent, they are not related by a gauge
transformation and a phase, and the weights `1` and `μ` have modulus one. -/
theorem isBNTCanonicalForm_phaseBlockSector {μ : ℂ} (hμ : ‖μ‖ = 1) :
    IsBNTCanonicalForm (phaseBlockSector (norm_ne_zero_iff.1 (hμ.trans_ne one_ne_zero))) :=
  isBNTCanonicalForm_repeatedBlockBasisSector _ _ _ _
    (fun j _ => by
      change ‖(![1, μ] : Fin 2 → ℂ) j‖ ≤ 1
      fin_cases j <;> simp [hμ])
    ⟨(0 : Fin 2), ⟨0, Nat.one_pos⟩, by change ‖(![1, μ] : Fin 2 → ℂ) 0‖ = 1; simp⟩

/-- The bond coordinates of the two blocks in the canonical form. -/
noncomputable def phaseBlockCopyCoord {μ : ℂ} (hμ : μ ≠ 0) :
    Fin 2 → Fin (phaseBlockSector hμ).totalDim :=
  ![(phaseBlockSector hμ).copyCoord 0 ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩,
    (phaseBlockSector hμ).copyCoord 1 ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩]

/-- The canonical form has bond dimension two, the sum `∑ⱼ m_j D_j` of arXiv:2307.01696,
eq. (S2). -/
theorem totalDim_phaseBlockSector {μ : ℂ} (hμ : μ ≠ 0) : (phaseBlockSector hμ).totalDim = 2 := by
  have h : (phaseBlockSector hμ).totalCopies = 2 := by
    simp [SectorDecomposition.totalCopies, SectorDecomposition.copies]
  simp only [SectorDecomposition.totalDim, SectorDecomposition.flatDim, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, h]

/-- The bond coordinates of the copies of the blocks exhaust the bond coordinates of the
canonical form of arXiv:2307.01696, eq. (S2), each exactly once. -/
theorem bijective_phaseBlockCopyCoord {μ : ℂ} (hμ : μ ≠ 0) :
    Function.Bijective (phaseBlockCopyCoord hμ) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun x y hxy => ?_, by
    simp [totalDim_phaseBlockSector]⟩
  fin_cases x <;> fin_cases y <;>
    first
    | rfl
    | (exfalso
       exact absurd (congrArg Sigma.fst ((phaseBlockSector hμ).sigma_eq_of_copyCoord_eq hxy))
         (by simp))

/-- The ordering of the bond coordinates of the canonical form under which its assembled tensor
is `phaseBlockTensor μ`: a permutation of the bond basis, which is a gauge transformation. -/
noncomputable def phaseBlockEquiv {μ : ℂ} (hμ : μ ≠ 0) :
    Fin (phaseBlockSector hμ).totalDim ≃ Fin 2 :=
  (Equiv.ofBijective _ (bijective_phaseBlockCopyCoord hμ)).symm

/-- The ordering of the bond coordinates sends the coordinate `x` to the bond coordinate of the
`x`-th copy. -/
theorem phaseBlockEquiv_symm_apply {μ : ℂ} (hμ : μ ≠ 0) (x : Fin 2) :
    (phaseBlockEquiv hμ).symm x = phaseBlockCopyCoord hμ x :=
  rfl

/-- **`phaseBlockTensor μ` is the canonical form** `⊕ⱼ μ_{j,1} A_j` of arXiv:2307.01696,
eq. (S2), of `phaseBlockSector`, after ordering the bond coordinates. -/
theorem reindex_toTensor_phaseBlockSector {μ : ℂ} (hμ : μ ≠ 0) (i : Fin 2) :
    reindex (phaseBlockEquiv hμ) (phaseBlockEquiv hμ) ((phaseBlockSector hμ).toTensor i) =
      phaseBlockTensor μ i := by
  ext x y
  rw [reindex_apply, submatrix_apply, phaseBlockEquiv_symm_apply, phaseBlockEquiv_symm_apply]
  fin_cases x <;> fin_cases y <;>
    simp only [phaseBlockCopyCoord, Fin.zero_eta, Fin.mk_one, cons_val_zero, cons_val_one] <;>
    first
    | (rw [SectorDecomposition.toTensor_copyCoord]
       fin_cases i <;> simp [SectorDecomposition.weight, phaseBlockWeight, repeatedBlockBasis,
         phaseBlockDiag])
    | (rw [SectorDecomposition.toTensor_copyCoord_of_ne _ _ (by simp)]
       fin_cases i <;> simp)

/-- The fixed-point pairs of the blocks of the canonical form
(`SectorDecomposition.embeddedFixedPointPair`, with the fixed point `σ_j = 1` of the
one-dimensional block) are the pairs placed on the coordinate `j`. -/
theorem embeddedFixedPointPair_phaseBlockSector {μ : ℂ} (hμ : μ ≠ 0) (j : Fin 2)
    (p : Fin 2 × Fin 2) :
    (phaseBlockSector hμ).embeddedFixedPointPair (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (fun j => ⟨0, (phaseBlockSector hμ).copies_pos j⟩) j
        ((phaseBlockEquiv hμ).symm p.1, (phaseBlockEquiv hμ).symm p.2) =
      embedPair (fun _ : Fin 1 => j) (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)) p := by
  have hc : (phaseBlockSector hμ).copyCoord j ⟨0, (phaseBlockSector hμ).copies_pos j⟩ =
      fun _ : Fin 1 => (phaseBlockEquiv hμ).symm j := by
    funext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rw [phaseBlockEquiv_symm_apply]
    fin_cases j <;> rfl
  rw [SectorDecomposition.embeddedFixedPointPair, hc, embedPair_symm_comp]
  simp

/-- **Lemma 1'(ii) of arXiv:2307.01696 fails for a tensor satisfying all its hypotheses, with
weights of modulus one.** The tensor `A⁰ = diag(1, 0)`, `A¹ = diag(0, -1)` is, after ordering
its bond coordinates, the canonical form `⊕ⱼ μ_{j,1} A_j` of eq. (S2) of a basis of two normal
blocks in canonical form II, with weights `μ_{1,1} = 1` and `μ_{2,1} = -1` (`IsBNTCanonicalForm`,
normality, and the diagonal positive-definite fixed point `1` of each block), whose states
"produce orthogonal vectors in the thermodynamic limit" (arXiv:2307.01696, line 973). The
transfer maps of the blocks have no eigenvalue other than `1`, so every `λ₂` bounds their
subleading eigenvalues. For every `λ₂` with `0 < |λ₂| < 1`, every `γ > 0`, and every constant
`C`, for the approximating state of eq. (S7), built from the coefficients `βⱼ = ∑ₖ μ_{j,k}^N`
and the pairs of that same fixed point `1`, there is an odd `M` such that, with `q = M` and
`N = M²` (so `q = o(N)` along this sequence) and `y = (N/q) e^{-γ q/ξ_diag}`, the error exceeds
`C y e^{C y}`. -/
theorem isBNTCanonicalForm_and_not_approximationError_le_phaseBlock :
    IsBNTCanonicalForm (phaseBlockSector (neg_ne_zero.2 one_ne_zero)) ∧
      (∀ j k, j ≠ k → Tendsto (fun N : ℕ =>
        mpvOverlap ((phaseBlockSector (neg_ne_zero.2 one_ne_zero)).basis j)
          ((phaseBlockSector (neg_ne_zero.2 one_ne_zero)).basis k) N) atTop (𝓝 0)) ∧
      (∀ j, IsNormalTensor ((phaseBlockSector (neg_ne_zero.2 one_ne_zero)).basis j)) ∧
      (∀ j, (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef ∧ (1 : Matrix (Fin 1) (Fin 1) ℂ).IsDiag ∧
        Kraus.transferMap ((phaseBlockSector (neg_ne_zero.2 one_ne_zero)).basis j) 1 = 1) ∧
      (∀ i, reindex (phaseBlockEquiv (neg_ne_zero.2 one_ne_zero))
        (phaseBlockEquiv (neg_ne_zero.2 one_ne_zero))
        ((phaseBlockSector (neg_ne_zero.2 one_ne_zero)).toTensor i) = phaseBlockTensor (-1) i) ∧
      (∀ j (lam₂ μ : ℂ), Module.End.HasEigenvalue
          (Kraus.transferMap ((phaseBlockSector (neg_ne_zero.2 one_ne_zero)).basis j)) μ →
          μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖) ∧
      ∀ {lam₂ : ℂ}, 0 < ‖lam₂‖ → ‖lam₂‖ < 1 → ∀ {γ : ℝ}, 0 < γ → ∀ C : ℝ,
        ∃ M : ℕ, Odd M ∧
          C * (M * Real.exp (-γ * M / correlationLength lam₂)) *
              Real.exp (C * (M * Real.exp (-γ * M / correlationLength lam₂))) <
            1 - ‖nonNormalApproxOverlap (phaseBlockTensor (-1)) M M
              (ghzAmplitude ((phaseBlockSector (neg_ne_zero.2 one_ne_zero)).coeff (M * M)))
              (fun j p => (phaseBlockSector (neg_ne_zero.2 one_ne_zero)).embeddedFixedPointPair
                (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
                (fun j => ⟨0, (phaseBlockSector (neg_ne_zero.2 one_ne_zero)).copies_pos j⟩) j
                ((phaseBlockEquiv (neg_ne_zero.2 one_ne_zero)).symm p.1,
                  (phaseBlockEquiv (neg_ne_zero.2 one_ne_zero)).symm p.2))‖ := by
  have hBNT : IsBNTCanonicalForm (phaseBlockSector (neg_ne_zero.2 (one_ne_zero (α := ℂ)))) :=
    isBNTCanonicalForm_phaseBlockSector (by simp)
  refine ⟨hBNT, fun _ _ hjk => hBNT.cross_overlap_basis_tendsto_zero hjk,
    fun j => isNormalTensor_of_dim_one _ (repeatedBlockBasis_norm j),
    fun j => posDef_isDiag_transferMap_one_of_dim_one _ (repeatedBlockBasis_norm j),
    reindex_toTensor_phaseBlockSector _,
    norm_le_of_hasEigenvalue_transferMap_repeatedBlockBasis, fun h0 h1 γ hγ C => ?_⟩
  simp only [embeddedFixedPointPair_phaseBlockSector, coeff_phaseBlockSector]
  exact not_approximationError_le_phaseBlockTensor h0 h1 hγ C

end MPSTensor
