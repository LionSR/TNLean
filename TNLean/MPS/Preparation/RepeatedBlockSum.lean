/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrthogonalBlockSum

/-!
# Direct sums of blocks with multiplicities

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") write a tensor that is not normal as
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S2)), assert that the positive part of the
`q`-site blocked tensor is `⊕ⱼ diag(μ_{j,1}^q, …, μ_{j,m_j}^q) ⊗ P_j` (eq. (S5)), and approximate
the state by `V^{⊗M} ∑ⱼ βⱼ |Ω_j⟩` with `βⱼ = ∑ₖ μ_{j,k}^N` and products of nearest-neighbour
pairs `|Ω_j⟩` (eq. (S7)). For `m_j ≥ 2` both the block form and the approximating state fail
(`docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`).

This file computes the correct block form when the `q`-site states of distinct blocks are
orthogonal. With the copy `k` of block `j` placed on the bond coordinates `ι_{j,k}` and
`K_{j,k} = E_{j,k} ⊗ E_{j,k}` the isometry placing its bond pairs, the blocked tensor is
`B = ∑ⱼ cⱼ B_j L_jᴴ` (`physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry`), where

  `cⱼ = (∑ₖ |μ_{j,k}|^{2q})^{1/2}`,  `L_j = ∑ₖ (conj(μ_{j,k}^q) / cⱼ) K_{j,k}`

(`copyNorm`, `copyIsometry`). The `L_j` are isometries with orthogonal ranges, so the positive
part is `P = ∑ⱼ cⱼ L_j P_j L_jᴴ`: on the copy index of block `j` it has rank one, rather than the
diagonal `diag(μ_{j,1}^q, …, μ_{j,m_j}^q)` of eq. (S5). The partial isometry is
`V = ∑ⱼ V_j L_jᴴ` (`polarIso_blockTensor_repeatedBlockSum`).

Replacing `P_j` by its fixed point in this block form gives the corrected fixed-point state
`∑ⱼ βⱼ L_j^{⊗M} |Ω_j⟩` (`copyFixedPointState`), where `|Ω_j⟩` is the product of the pairs of
block `j` in its own bond space: the isometry `L_j` acts on the two legs `L_k R_k` of each site,
so the state is not a product of nearest-neighbour pairs of the full bond space when `m_j ≥ 2`.
Since `V L_j = V_j`, applying `V^{⊗M}` gives `∑ⱼ βⱼ |φ_M(V_j P_{j,∞})⟩`, the combination of the
approximating states of the normal case (`copyApproxVector_repeatedBlockSum`).

**Local fix (corrected fixed-point state):** eq. (S7) of the source is replaced by
`V^{⊗M} ∑ⱼ βⱼ L_j^{⊗M} |Ω_j⟩`, the fixed-point state of the corrected block form of the positive
part. For `m_j = 1` and `μⱼ > 0` it is the source's state. Documented in
`docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

**Scope restriction (orthogonal blocks):** the block form is proved under the orthogonality
`B_jᴴ B_{j'} = 0` of the `q`-site states of distinct blocks, which the source does not assume
and without which the block form fails. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.repeatedBlockSum` — the direct sum `⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_j`.
* `MPSTensor.mpv_repeatedBlockSum` — its state is `∑ⱼ βⱼ |φ_N(A_j)⟩`.
* `MPSTensor.copyNorm`, `MPSTensor.copyIsometry` — `cⱼ` and `L_j`.
* `MPSTensor.physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry` — `B = ∑ⱼ cⱼ B_j L_jᴴ`.
* `MPSTensor.polarIso_blockTensor_repeatedBlockSum`,
  `MPSTensor.polarPos_blockTensor_repeatedBlockSum` — the corrected block form of eq. (S5).
* `MPSTensor.copyFixedPointState`, `MPSTensor.copyApproxVector` — the corrected state of
  eq. (S7), before and after `V^{⊗M}`.
* `MPSTensor.copyApproxVector_repeatedBlockSum` — `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M}|Ω_j⟩` is
  `∑ⱼ αⱼ |φ_M(V_j P_{j,∞})⟩`.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7).
-/

open scoped BigOperators Matrix ComplexOrder Kronecker
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}

/-- The direct sum `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` of arXiv:2307.01696,
Supplemental Material, eq. (S2): the copy `k` of block `j` is placed on the bond coordinates
`ι_{j,k}` with the weight `μ_{j,k}`. -/
def repeatedBlockSum (Aj : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D) (μ : (j : Fin b) → Fin (m j) → ℂ) :
    MPSTensor d D :=
  fun i => ∑ j, ∑ k, μ j k • (coordEmbedding (ι j k) * Aj j i * (coordEmbedding (ι j k))ᴴ)

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- The copies of all blocks, listed along `finSigmaFinEquiv`. -/
local notation "flat" => (finSigmaFinEquiv (m := b) (n := m)).symm

/-- The direct sum with multiplicities is the direct sum of all copies, each of multiplicity
one. -/
theorem repeatedBlockSum_eq_blockSum (μ : (j : Fin b) → Fin (m j) → ℂ) :
    repeatedBlockSum Aj ι μ =
      blockSum (Dj := fun p => Dj (flat p).1) (fun p => Aj (flat p).1)
        (fun p => ι (flat p).1 (flat p).2) (fun p => μ (flat p).1 (flat p).2) := by
  funext i
  simp only [repeatedBlockSum, blockSum]
  rw [Equiv.sum_comp flat
    (fun s => μ s.1 s.2 • (coordEmbedding (ι s.1 s.2) * Aj s.1 i * (coordEmbedding (ι s.1 s.2))ᴴ)),
    Fintype.sum_sigma]

theorem flat_disjoint_coord
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a') :
    ∀ p p', p ≠ p' → ∀ a a', ι (flat p).1 (flat p).2 a ≠ ι (flat p').1 (flat p').2 a' :=
  fun p p' h => hdisj (flat p) (flat p') (flat.injective.ne h)

/-- The periodic state of the direct sum on `N ≥ 1` sites is `∑ⱼ βⱼ |φ_N(A_j)⟩` with
`βⱼ = ∑ₖ μ_{j,k}^N`: arXiv:2307.01696, Supplemental Material, eqs. (S3) and (S4). -/
theorem mpv_repeatedBlockSum (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : (j : Fin b) → Fin (m j) → ℂ) {N : ℕ} (hN : N ≠ 0) (s : Fin N → Fin d) :
    mpv (repeatedBlockSum Aj ι μ) s = ∑ j, bntWeight μ N j * mpv (Aj j) s := by
  rw [repeatedBlockSum_eq_blockSum,
    mpv_blockSum (fun p => hι _ _) (flat_disjoint_coord hdisj) _ hN,
    Equiv.sum_comp flat (fun p => μ p.1 p.2 ^ N * mpv (Aj p.1) s), Fintype.sum_sigma]
  simp only [bntWeight, Finset.sum_mul]

/-- The physical matrix of the `q`-site blocked tensor of the direct sum, for `q ≥ 1`:
`B = ∑ⱼ ∑ₖ μ_{j,k}^q B_j K_{j,k}ᴴ`. -/
theorem physicalMatrix_blockTensor_repeatedBlockSum (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : (j : Fin b) → Fin (m j) → ℂ) {q : ℕ} (hq : q ≠ 0) :
    physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q) =
      ∑ j, ∑ k, μ j k ^ q •
        (physicalMatrix (blockTensor (Aj j) q) * (pairEmbedding (ι j k))ᴴ) := by
  rw [repeatedBlockSum_eq_blockSum,
    physicalMatrix_blockTensor_blockSum (fun p => hι _ _) (flat_disjoint_coord hdisj) _ hq,
    Equiv.sum_comp flat (fun p => μ p.1 p.2 ^ q •
      (physicalMatrix (blockTensor (Aj p.1) q) * (pairEmbedding (ι p.1 p.2))ᴴ)),
    Fintype.sum_sigma]

/-! ### The copy isometries -/

/-- The norm `cⱼ = (∑ₖ |μ_{j,k}|^{2q})^{1/2}` of the weights of the copies of block `j` on `q`
sites. -/
noncomputable def copyNorm (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ) (j : Fin b) : ℝ :=
  Real.sqrt (∑ k, ‖μ j k‖ ^ (2 * q))

/-- The isometry `L_j = ∑ₖ (conj(μ_{j,k}^q) / cⱼ) K_{j,k}` from the bond pairs of block `j` to the
bond pairs of the direct sum: it places a bond pair on all copies of the block at once, with the
weights of the copies on `q` sites. -/
noncomputable def copyIsometry (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D)
    (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ) (j : Fin b) :
    Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ :=
  ∑ k, (star (μ j k ^ q) / (copyNorm μ q j : ℂ)) • pairEmbedding (ι j k)

theorem copyNorm_sq (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ) (j : Fin b) :
    copyNorm μ q j ^ 2 = ∑ k, ‖μ j k‖ ^ (2 * q) :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)

/-- A block with some nonzero weight has `cⱼ > 0`. -/
theorem copyNorm_pos {μ : (j : Fin b) → Fin (m j) → ℂ} {j : Fin b} (hμ : μ j ≠ 0) (q : ℕ) :
    0 < copyNorm μ q j := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hμ
  refine Real.sqrt_pos.2 (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hk) _) ?_)
  exact Finset.single_le_sum (f := fun k => ‖μ j k‖ ^ (2 * q)) (fun _ _ => by positivity)
    (Finset.mem_univ k)

theorem conjTranspose_copyIsometry (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ) (j : Fin b) :
    (copyIsometry ι μ q j)ᴴ = ∑ k, (μ j k ^ q / (copyNorm μ q j : ℂ)) •
      (pairEmbedding (ι j k))ᴴ := by
  simp only [copyIsometry, conjTranspose_sum, conjTranspose_smul, star_div₀, star_star,
    Complex.star_def, Complex.conj_ofReal]

/-- `K_{j,k}ᴴ K_{j',k'}` is `1` for the same copy and `0` for distinct copies. -/
theorem conjTranspose_pairEmbedding_mul_copy (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {j j' : Fin b} (k : Fin (m j)) (k' : Fin (m j')) (h : (⟨j, k⟩ : (j : Fin b) × Fin (m j)) ≠
      ⟨j', k'⟩) : (pairEmbedding (ι j k))ᴴ * pairEmbedding (ι j' k') = 0 :=
  conjTranspose_pairEmbedding_mul_eq_zero (hdisj _ _ h)

/-- `L_j` is an isometry, `L_jᴴ L_j = 1`, when some weight of block `j` is nonzero. -/
theorem conjTranspose_copyIsometry_mul_self (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : (j : Fin b) → Fin (m j) → ℂ} {j : Fin b} (hμ : μ j ≠ 0) (q : ℕ) :
    (copyIsometry ι μ q j)ᴴ * copyIsometry ι μ q j = 1 := by
  have hc := copyNorm_pos hμ q
  have hc0 : (copyNorm μ q j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  rw [conjTranspose_copyIsometry, copyIsometry, Matrix.sum_mul]
  have hterm : ∀ k, (μ j k ^ q / (copyNorm μ q j : ℂ)) • (pairEmbedding (ι j k))ᴴ *
      ∑ k', (star (μ j k' ^ q) / (copyNorm μ q j : ℂ)) • pairEmbedding (ι j k') =
      ((‖μ j k‖ ^ (2 * q) / copyNorm μ q j ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := fun k => by
    rw [Matrix.mul_sum, Finset.sum_eq_single k]
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        conjTranspose_pairEmbedding_mul_self (hι j k)]
      congr 1
      rw [div_mul_div_comm, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← sq,
        mul_comm (μ j k ^ q), ← Complex.normSq_eq_conj_mul_self.symm.trans rfl]
      push_cast
      rw [Complex.star_def, ← map_pow, Complex.conj_mul', norm_pow, ← pow_mul, mul_comm q 2]
    · intro k' _ hk'
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_pairEmbedding_mul_copy hι
        hdisj k k' (fun h => hk' (eq_of_heq (Sigma.mk.inj h).2).symm), smul_zero]
    · simp
  simp_rw [hterm, ← Finset.sum_smul, ← Complex.ofReal_sum, ← Finset.sum_div, ← copyNorm_sq,
    div_self (pow_pos hc 2).ne', Complex.ofReal_one, one_smul]

/-- The isometries of distinct blocks have orthogonal ranges, `L_jᴴ L_{j'} = 0`. -/
theorem conjTranspose_copyIsometry_mul_eq_zero (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ) {j j' : Fin b} (h : j ≠ j') :
    (copyIsometry ι μ q j)ᴴ * copyIsometry ι μ q j' = 0 := by
  rw [conjTranspose_copyIsometry, copyIsometry, Matrix.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_pairEmbedding_mul_copy hι hdisj
    k k' (fun h' => h (Sigma.mk.inj h').1), smul_zero]

/-- The physical matrix of the `q`-site blocked tensor of the direct sum, for `q ≥ 1` and blocks
with some nonzero weight: `B = ∑ⱼ cⱼ B_j L_jᴴ`. -/
theorem physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : (j : Fin b) → Fin (m j) → ℂ} (hμ : ∀ j, μ j ≠ 0) {q : ℕ} (hq : q ≠ 0) :
    physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q) =
      ∑ j, (copyNorm μ q j : ℂ) •
        (physicalMatrix (blockTensor (Aj j) q) * (copyIsometry ι μ q j)ᴴ) := by
  rw [physicalMatrix_blockTensor_repeatedBlockSum hι hdisj μ hq]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc0 : (copyNorm μ q j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (copyNorm_pos (hμ j) q).ne'
  rw [conjTranspose_copyIsometry, Matrix.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, smul_smul, mul_div_cancel₀ _ hc0]

/-! ### The corrected block form -/

/-- **The partial isometry of the blocked direct sum.** For blocks with some nonzero weight whose
`q`-site states are orthogonal, `B_jᴴ B_{j'} = 0` for `j ≠ j'`, the partial isometry of the
`q`-site blocked tensor is `V = ∑ⱼ V_j L_jᴴ`: the corrected form of arXiv:2307.01696,
Supplemental Material, eq. (S5), for blocks with multiplicities. -/
theorem polarIso_blockTensor_repeatedBlockSum (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : (j : Fin b) → Fin (m j) → ℂ} (hμ : ∀ j, μ j ≠ 0) {q : ℕ} (hq : q ≠ 0)
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) :
    polarIso (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) =
      ∑ j, polarIso (physicalMatrix (blockTensor (Aj j) q)) * (copyIsometry ι μ q j)ᴴ := by
  rw [physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry hι hdisj hμ hq]
  exact (polarIso_sum_of_orthogonal horth (fun j => copyNorm_pos (hμ j) q)
    (fun j => conjTranspose_copyIsometry_mul_self hι hdisj (hμ j) q)
    (fun j j' h => conjTranspose_copyIsometry_mul_eq_zero hι hdisj μ q h)).1

/-- **The positive part of the blocked direct sum.** In the setting of
`polarIso_blockTensor_repeatedBlockSum`, the positive part is `P = ∑ⱼ cⱼ L_j P_j L_jᴴ`. On the
copies of block `j` it is `cⱼ w_j w_jᴴ ⊗ P_j` with the unit vector `w_{j,k} = conj(μ_{j,k}^q)/cⱼ`,
of rank one in the copy index, where arXiv:2307.01696, Supplemental Material, eq. (S5), prints
`diag(μ_{j,1}^q, …, μ_{j,m_j}^q) ⊗ P_j`. -/
theorem polarPos_blockTensor_repeatedBlockSum (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : (j : Fin b) → Fin (m j) → ℂ} (hμ : ∀ j, μ j ≠ 0) {q : ℕ} (hq : q ≠ 0)
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) :
    polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) =
      ∑ j, (copyNorm μ q j : ℂ) • (copyIsometry ι μ q j *
        polarPos (physicalMatrix (blockTensor (Aj j) q)) * (copyIsometry ι μ q j)ᴴ) := by
  rw [physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry hι hdisj hμ hq]
  exact (polarIso_sum_of_orthogonal horth (fun j => copyNorm_pos (hμ j) q)
    (fun j => conjTranspose_copyIsometry_mul_self hι hdisj (hμ j) q)
    (fun j j' h => conjTranspose_copyIsometry_mul_eq_zero hι hdisj μ q h)).2

/-! ### The corrected approximating state -/

/-- The corrected fixed-point state `∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` on a ring of `M` sites with legs
`L_k ⊗ R_k`, where `|Ω_j⟩ = ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` is the product of the pairs of `σ_j` in the
bond space of block `j` and `L_j` maps the two legs of each site into the bond pairs of the full
tensor. With `L_j = copyIsometry ι μ q j` this replaces `∑ⱼ βⱼ |Ω_j⟩` in arXiv:2307.01696,
Supplemental Material, eq. (S7), by the fixed point of the corrected block form
`P = ∑ⱼ cⱼ L_j P_j L_jᴴ` (`polarPos_blockTensor_repeatedBlockSum`). -/
noncomputable def copyFixedPointState {M : ℕ} (α : Fin b → ℂ)
    (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) : (Fin M → Fin D × Fin D) → ℂ :=
  ∑ j, α j • (tensorPower M (L j) *ᵥ pairProductState (fixedPointPair (σ j)))

/-- The unnormalized corrected approximating state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`, with `V` the
partial isometry of the `q`-site blocked tensor of `A`; the analogue of
`MPSTensor.nonNormalApproxVector` for the corrected fixed-point state (arXiv:2307.01696,
Supplemental Material, eq. (S7), corrected as in the module docstring). -/
noncomputable def copyApproxVector (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    (Fin M → Fin (blockPhysDim d q)) → ℂ :=
  tensorPower M (polarIso (physicalMatrix (blockTensor A q))) *ᵥ copyFixedPointState α L σ

/-- **The corrected approximating state of a direct sum with multiplicities.** For blocks with
some nonzero weight whose `q`-site states are orthogonal, `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` is
`∑ⱼ αⱼ |φ_M(V_j P_{j,∞})⟩`, the combination of the approximating states of the normal case for
the blocks (arXiv:2307.01696, eqs. (9), (10) and Supplemental Material, eq. (S7), corrected as in
the module docstring). -/
theorem copyApproxVector_repeatedBlockSum (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : (j : Fin b) → Fin (m j) → ℂ} (hμ : ∀ j, μ j ≠ 0) {q : ℕ} (hq : q ≠ 0)
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (M : ℕ) [NeZero M] (α : Fin b → ℂ)
    (τ : Fin M → Fin (blockPhysDim d q)) :
    copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ τ =
      ∑ j, α j * mpv (approximatingTensor (blockTensor (Aj j) q) (σ j)) τ := by
  have hV := polarIso_blockTensor_repeatedBlockSum hι hdisj hμ hq horth
  have hVL : ∀ j, polarIso (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) *
      copyIsometry ι μ q j = polarIso (physicalMatrix (blockTensor (Aj j) q)) := fun j => by
    rw [hV, Matrix.sum_mul, Finset.sum_eq_single j]
    · rw [Matrix.mul_assoc, conjTranspose_copyIsometry_mul_self hι hdisj (hμ j), Matrix.mul_one]
    · intro j' _ hj'
      rw [Matrix.mul_assoc, conjTranspose_copyIsometry_mul_eq_zero hι hdisj μ q hj',
        Matrix.mul_zero]
    · simp
  rw [copyApproxVector, copyFixedPointState, mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, mulVec_mulVec, tensorPower_mul, hVL,
    tensorPower_polarIso_mulVec_pairProductState]

end MPSTensor
