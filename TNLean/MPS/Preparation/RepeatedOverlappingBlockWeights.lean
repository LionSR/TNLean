/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RelativePositivePart
import TNLean.MPS.Preparation.RepeatedOverlappingBlockError

/-!
# The approximation error for repeated overlapping blocks with weights of any size

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound the
error of the approximating state of eq. (S7) for a tensor
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` that is not normal by
`ε = O((N/q) e^{-γ q/ξ_diag})`, with no factor depending on the weights. This file proves the bound
`ε ≤ C y e^{C y}`, `y = M e^{-γ q/ξ}`, for the corrected approximating state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` (`TNLean.MPS.Preparation.RepeatedBlockSum`) of blocks with
multiplicities whose `q`-site states may overlap, with `C` independent of the weights, for all
nonzero complex weights (`exists_approximationError_le_repeatedOverlappingBlockSum`). The sums
`βⱼ = ∑ₖ μ_{j,k}^N` may cancel and `b = ∑ⱼ |βⱼ|²` may be arbitrarily small.

The overlaps `zⱼ = ⟨Ω_j|φ_M(L_jᴴ P)⟩` are estimated relative to the weights. The tensor read from
`L_jᴴ P` is the direct sum over the copies `(j', k)` of the tensors read from the blocks
`L_jᴴ P C⁻¹ L_{j'}` with the weights `μ_{j',k}^q` (`ofPhysicalMatrixLM_conjTranspose_copyIsometry_mul_polarPos`),
so

  `zⱼ = ∑_{j'} β_{j'} w_{jj'}`,  `w_{jj'} = ⟨Ω_j|φ_M(L_jᴴ P C⁻¹ L_{j'})⟩`

(`mpvOverlap_conjTranspose_copyIsometry_mul_polarPos`). The blocks `L_jᴴ P C⁻¹ L_{j'}` are
`δ_{jj'} ((√σ_j)ᵀ ⊗ 1)` up to `K e^{-γ q/ξ}` uniformly in the weights
(`exists_norm_relativeRow_sub_le`), so `w_{jj'} = δ_{jj'}` up to `C y e^{C y}`
(`exists_norm_mpvOverlap_sub_ite_le`). Hence `∑ⱼ conj(βⱼ) zⱼ = b (1 + O(y e^{O(y)}))`, and the
factor `min(1, b)^{-1/2}` of the absolute estimate disappears.

**Local fix (corrected fixed-point state):** the approximating state is the corrected state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`, not the state of eq. (S7), which fails for `m_j ≥ 2`. Documented
in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

**Local fix (rate of the overlapping blocks):** the rate `e^{-γ q/ξ_diag}` of the source is
replaced by `e^{-γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.CopyWeights.pow` — the weights `μ_{j,k}^q` of the copies on `q` sites.
* `MPSTensor.ofPhysicalMatrixLM_mul_conjTranspose_pairEmbedding` — the letters of a row placed
  on one copy.
* `MPSTensor.mpvOverlap_conjTranspose_copyIsometry_mul_polarPos` — `zⱼ = ∑_{j'} β_{j'} w_{jj'}`.
* `MPSTensor.exists_norm_mpvOverlap_sub_ite_le` — `w_{jj'} = δ_{jj'}` up to `C y e^{C y}`.
* `MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum`,
  `MPSTensor.exists_approximationError_le_mul_repeatedOverlappingBlockSum` — Lemma 1'(ii) for
  repeated blocks whose states may overlap, for the corrected state at the corrected rate, for all
  nonzero complex weights.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S12) and Lemma 1'(ii)
  (`eq:fid_err_gen_non_normal`).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}
  {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-! ### The tensor read from a row -/

/-- The weights `μ_{j,k}^q` of the copies of the blocks on `q` sites: the weights of the copies in
the `q`-site blocked tensor (arXiv:2307.01696, Supplemental Material, eq. (S2) blocked). -/
def CopyWeights.pow (μ : CopyWeights b m) (q : ℕ) : CopyWeights b m where
  weight j k := μ j k ^ q
  mult_pos := μ.mult_pos
  weight_ne_zero j k := pow_ne_zero q (μ.weight_ne_zero j k)

/-- The letters of the tensor read from `Y K_ιᴴ` are the letters of the tensor read from `Y`,
placed on the bond coordinates `ι`: `E_ι Yⁱ E_ιᴴ`. -/
theorem ofPhysicalMatrixLM_mul_conjTranspose_pairEmbedding {D₂ D' : ℕ} (ι' : Fin D' → Fin D)
    (Y : Matrix (Fin D₂ × Fin D₂) (Fin D' × Fin D') ℂ) (i : Fin (D₂ * D₂)) :
    ofPhysicalMatrixLM (Y * (pairEmbedding ι')ᴴ) i =
      coordEmbedding ι' * ofPhysicalMatrixLM Y i * (coordEmbedding ι')ᴴ := by
  ext x y
  change (Y * (pairEmbedding ι')ᴴ) (virtualPairEquiv D₂ i) (x, y) = _
  simp only [mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [conjTranspose_apply, pairEmbedding_apply, coordEmbedding, of_apply, Prod.mk.injEq]
  by_cases h1 : x = ι' a <;> by_cases h2 : y = ι' c
  all_goals simp [h1, h2]
  rfl

section Rows

variable (hι : ∀ j k, Function.Injective (ι j k))
  (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
include hι hdisj

/-- The positive part vanishes off the ranges of the copy isometries: `P ∑ⱼ L_j L_jᴴ = P`. -/
private theorem polarPos_mul_sum_copyIsometry {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0) :
    Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) *
        ∑ j, copyIsometry ι μ q j * (copyIsometry ι μ q j)ᴴ =
      Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) := by
  have hiso := fun j => conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q
  have horth := fun j k (h : j ≠ k) => conjTranspose_copyIsometry_mul_eq_zero hdisj μ q h
  have hB : physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q) *
      ∑ j, copyIsometry ι μ q j * (copyIsometry ι μ q j)ᴴ =
      physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q) := by
    rw [physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry hι hdisj hq, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_assoc,
      conjTranspose_mul_sum_of_isometry hiso horth (fun k => (copyIsometry ι μ q k)ᴴ) j]
  rw [← Matrix.conjTranspose_polarIso_mul_self, Matrix.mul_assoc, hB]

/-- **The row of the positive part.** For `q ≥ 1`,
`L_jᴴ P = ∑_{j'} ∑ₖ μ_{j',k}^q (L_jᴴ P C⁻¹ L_{j'}) K_{j',k}ᴴ`. -/
theorem conjTranspose_copyIsometry_mul_polarPos_eq_sum {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0) (j : Fin b) :
    (copyIsometry ι μ q j)ᴴ *
        Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) =
      ∑ j', ∑ k, μ j' k ^ q • (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j' *
        (pairEmbedding (ι j' k))ᴴ) := by
  set P := Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q))
  have hterm : ∀ j', ∑ k, μ j' k ^ q • (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j' *
      (pairEmbedding (ι j' k))ᴴ) =
      (copyIsometry ι μ q j)ᴴ * P * (copyIsometry ι μ q j' * (copyIsometry ι μ q j')ᴴ) :=
    fun j' => by
      have hc0 : (copyNorm μ q j' : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (copyNorm_pos (μ.weight_fun_ne_zero j') q).ne'
      have hL : (copyNorm μ q j' : ℂ) • (copyIsometry ι μ q j')ᴴ =
          ∑ k, μ j' k ^ q • (pairEmbedding (ι j' k))ᴴ := by
        rw [conjTranspose_copyIsometry, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, mul_div_cancel₀ _ hc0]
      calc ∑ k, μ j' k ^ q • (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j' *
            (pairEmbedding (ι j' k))ᴴ)
          = relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j' *
              ∑ k, μ j' k ^ q • (pairEmbedding (ι j' k))ᴴ := by
            rw [Matrix.mul_sum]; simp only [Matrix.mul_smul]
        _ = relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j' *
              ((copyNorm μ q j' : ℂ) • (copyIsometry ι μ q j')ᴴ) := by rw [hL]
        _ = _ := by
            rw [relativeRow_eq_smul hι hdisj, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
              inv_mul_cancel₀ hc0, one_smul]
            simp only [Matrix.mul_assoc, P]
  simp_rw [hterm]
  rw [← Matrix.mul_sum, Matrix.mul_assoc, polarPos_mul_sum_copyIsometry hι hdisj μ hq]

/-- **The tensor read from a row is a direct sum over the copies.** For `q ≥ 1`, the tensor read
from `L_jᴴ P` is the direct sum, over the copies `(j', k)` with the weights `μ_{j',k}^q`, of the
tensors read from the blocks `L_jᴴ P C⁻¹ L_{j'}`. -/
theorem ofPhysicalMatrixLM_conjTranspose_copyIsometry_mul_polarPos
    {Aj : (j : Fin b) → MPSTensor d (Dj j)} (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0)
    (j : Fin b) :
    ofPhysicalMatrixLM ((copyIsometry ι μ q j)ᴴ *
        Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q))) =
      repeatedBlockSum (fun j' => ofPhysicalMatrixLM
        (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j')) ι (μ.pow q) := by
  funext i
  rw [conjTranspose_copyIsometry_mul_polarPos_eq_sum hι hdisj μ hq, repeatedBlockSum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    ofPhysicalMatrixLM_mul_conjTranspose_pairEmbedding]
  rfl

/-- **The overlap of a row is a combination of the blocks.** For `q ≥ 1` and `M ≥ 1`, the
overlap of the tensor read from `L_jᴴ P` with any tensor `F` on `M` sites is
`∑_{j'} β_{j'} ⟨φ_M(F)|φ_M(L_jᴴ P C⁻¹ L_{j'})⟩` with `β_{j'} = ∑ₖ μ_{j',k}^{qM}`
(arXiv:2307.01696, Supplemental Material, eq. (S4)). -/
theorem mpvOverlap_conjTranspose_copyIsometry_mul_polarPos
    {Aj : (j : Fin b) → MPSTensor d (Dj j)} (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0)
    (j : Fin b) {D' : ℕ} (F : MPSTensor (Dj j * Dj j) D') (M : ℕ) [NeZero M] :
    mpvOverlap (ofPhysicalMatrixLM ((copyIsometry ι μ q j)ᴴ *
        Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)))) F M =
      ∑ j', bntWeight μ (M * q) j' * mpvOverlap (ofPhysicalMatrixLM
        (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j')) F M := by
  rw [ofPhysicalMatrixLM_conjTranspose_copyIsometry_mul_polarPos hι hdisj μ hq, mpvOverlap]
  simp_rw [mpv_repeatedBlockSum hι hdisj (μ.pow q) (NeZero.ne M), Finset.sum_mul, mpvOverlap,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun s _ => ?_
  have hw : bntWeight (μ.pow q) M j' = bntWeight μ (M * q) j' := by
    simp only [bntWeight, CopyWeights.pow, ← pow_mul, mul_comm q M]
  rw [hw, mul_assoc]

open scoped Matrix.Norms.L2Operator in
/-- **The overlaps of the blocks.** For positive semidefinite `σ_j` of trace one and blocks
`j, j'`, there is `C > 0` such that for all nonzero weights, all `q`, all `G` with
`‖G - L_jᴴ P_∞ C⁻¹ L_{j'}‖ ≤ δ`, and all `M ≥ 1`, the overlap of the tensor read from `G` with
the fixed-point tensor of `σ_j` on `M` sites is `δ_{jj'}` up to `C (M δ) e^{C M δ}`.

The limit is `(√σ_j)ᵀ ⊗ 1` for `j = j'`, read as the fixed-point tensor itself, whose mixed
transfer map against itself is the idempotent `ρ ↦ Tr(ρ) σ_j` of trace one, and `0` otherwise;
the telescoping estimate `exists_norm_mpvOverlap_sub_trace_pow_le` applies. -/
theorem exists_norm_mpvOverlap_sub_ite_le
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) (j j' : Fin b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (q : ℕ)
      (G : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j') × Fin (Dj j')) ℂ) (δ : ℝ) (M : ℕ)
      [NeZero M], ‖G - relativeRowLimit ι μ q σ j j'‖ ≤ δ →
      ‖mpvOverlap (ofPhysicalMatrixLM G) (fixedPointTensor (σ j)) M -
          (if j = j' then 1 else 0)‖ ≤ C * (M * δ) * Real.exp (C * (M * δ)) := by
  have : NeZero (Dj j) := Matrix.neZero_of_trace_eq_one (htr j)
  have : NeZero (Dj j') := Matrix.neZero_of_trace_eq_one (htr j')
  set F := fixedPointTensor (σ j)
  set R : Module.End ℂ (Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) := Kraus.mixedMapLM F F
  have hR : ∀ ρ, R ρ = ((1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) * ρ).trace • σ j := fun ρ => by
    rw [Matrix.one_mul]
    exact (congrArg (fun T => T ρ) (Kraus.mixedMapLM_self F)).trans
      (transferMap_fixedPointTensor_apply (hσ j) ρ)
  have h1 : ((1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) * σ j).trace = 1 := by
    rw [Matrix.one_mul, htr j]
  have hidem : IsIdempotentElem R := isIdempotentElem_of_apply_eq_trace_smul hR h1
  have htr1 : LinearMap.trace ℂ _ R = 1 := (trace_of_apply_eq_trace_smul hR).trans h1
  set c : ℝ := 1 + ‖LinearMap.toContinuousLinearMap R‖
  have hc : 0 ≤ c := by positivity
  obtain ⟨C, hC, hgen⟩ := exists_norm_mpvOverlap_sub_trace_pow_le (D₁ := Dj j') F hc
  refine ⟨C, hC, fun μ q G δ M _ hG => ?_⟩
  by_cases hjj : j = j'
  · subst hjj
    rw [relativeRowLimit_self hι hdisj] at hG
    have hT : Kraus.mixedMapLM (ofPhysicalMatrixLM
        ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ))) F = R := by
      change Kraus.mixedMapLM (ofPhysicalMatrix (((CFC.sqrt (σ j))ᵀ ⊗ₖ
        (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)).submatrix (virtualPairEquiv (Dj j)) id)) F = R
      rw [ofPhysicalMatrix_sqrt_transpose_kronecker_one]
    have hpow : ∀ (k : ℕ) (ρ : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ),
        ‖(Kraus.mixedMapLM (ofPhysicalMatrixLM
          ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ))) F ^ k) ρ‖ ≤
          c * ‖ρ‖ := fun k ρ => by
      rw [hT]
      rcases k with _ | k
      · rw [pow_zero, Module.End.one_apply]
        exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _))
      · rw [hidem.pow_succ_eq]
        exact ((LinearMap.toContinuousLinearMap R).le_opNorm ρ).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
    have htrace : LinearMap.trace ℂ _ (Kraus.mixedMapLM (ofPhysicalMatrixLM
        ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ))) F ^ M) = 1 := by
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
      rw [hT, hn, hidem.pow_succ_eq, htr1]
    have h := hgen G _ δ M hpow hG
    rw [htrace] at h
    simpa using h
  · rw [relativeRowLimit_of_ne hι hdisj μ q σ hjj] at hG
    have hT : Kraus.mixedMapLM (ofPhysicalMatrixLM
        (0 : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j') × Fin (Dj j')) ℂ)) F = 0 := by
      change mixedMapLMLeft (D₁ := Dj j') F (ofPhysicalMatrixLM 0) = 0
      rw [map_zero, map_zero]
    have hpow : ∀ (k : ℕ) (ρ : Matrix (Fin (Dj j')) (Fin (Dj j)) ℂ),
        ‖(Kraus.mixedMapLM (ofPhysicalMatrixLM
          (0 : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j') × Fin (Dj j')) ℂ)) F ^ k) ρ‖ ≤
          c * ‖ρ‖ := fun k ρ => by
      rw [hT]
      rcases k with _ | k
      · rw [pow_zero, Module.End.one_apply]
        exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _))
      · rw [zero_pow (Nat.succ_ne_zero k), LinearMap.zero_apply, norm_zero]
        positivity
    have htrace : LinearMap.trace ℂ _ (Kraus.mixedMapLM (ofPhysicalMatrixLM
        (0 : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j') × Fin (Dj j')) ℂ)) F ^ M) = 0 := by
      rw [hT, zero_pow (NeZero.ne M), map_zero]
    have h := hgen G _ δ M hpow hG
    rw [htrace] at h
    simpa [hjj] using h

end Rows

/-! ### The approximation error -/

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)}

open scoped Matrix.Norms.L2Operator in
/-- **Approximation error for repeated blocks with overlapping states** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected approximating state at the
corrected rate, in the scope of the module docstring). Let
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S2)), the copy `k` of block `j` placed on the
bond coordinates `ι_{j,k}` with a nonzero complex weight, let every block `A_j` be normal in the
gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let `λ₂` bound
the moduli of the eigenvalues other than `1` of every transfer map `E_{A_j}` and the moduli of all
eigenvalues of the mixed transfer maps `E_{jj'}(X) = ∑ᵢ A_jⁱ X (A_{j'}ⁱ)†` of distinct blocks, so
that `ξ = -1/log|λ₂|` bounds `ξ_diag` and `ξ_off-diag`, and let `0 < γ < 1/2`. There is `C > 0`
such that for all weights, every block length `q`, and every number of blocks `M ≥ 1` with
`N = qM` and `βⱼ = ∑ₖ μ_{j,k}^N` not all zero (eq. (S4)), the error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the
corrected approximating state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` satisfies `ε ≤ C y e^{C y}` with
`y = M e^{-γ q/ξ}`.

The `q`-site states of distinct blocks need not be orthogonal, no condition `q = o(N)` is needed,
and `C` does not depend on the weights: the sums `βⱼ` may cancel and `∑ⱼ |βⱼ|²` may be arbitrarily
small. The normalization `|μ_{j,k}| ≤ 1` of the source is not needed. -/
theorem exists_approximationError_le_repeatedOverlappingBlockSum
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : CopyWeights b m, ∀ (q M : ℕ) [NeZero M],
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
            Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  set x := Real.exp (-γ / correlationLength lam₂) with hx_def
  have hx0 : 0 < x := Real.exp_pos _
  have hxq : ∀ q : ℕ, Real.exp (-γ * q / correlationLength lam₂) = x ^ q := fun q =>
    Real.exp_neg_mul_div_eq_pow _ _ q
  simp_rw [hxq]
  -- The trivial bound `ε ≤ 1`, which suffices whenever `C M x^q ≥ 1`.
  have htriv : ∀ (C : ℝ), 1 ≤ C → ∀ (μ : CopyWeights b m) (q M : ℕ) [NeZero M],
      1 ≤ C * ((M : ℝ) * x ^ q) →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * x ^ q) * Real.exp (C * (M * x ^ q)) := fun C hC μ q M _ hu => by
    have h2 : 1 ≤ Real.exp (C * (M * x ^ q)) := Real.one_le_exp (by linarith)
    have h3 : 0 ≤ ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
        (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ := norm_nonneg _
    nlinarith
  rcases le_or_gt 1 x with hx1 | hx1
  · -- For `e^{-γ/ξ} ≥ 1` the rate is at least `1` and the bound is trivial.
    refine ⟨1, one_pos, fun μ q M _ _ => htriv 1 le_rfl μ q M ?_⟩
    have := one_le_pow₀ hx1 (n := q)
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
    nlinarith
  have hl : ‖lam₂‖ < 1 := by
    rw [hx_def, neg_div_correlationLength, Real.exp_lt_one_iff] at hx1
    have hlog : Real.log ‖lam₂‖ < 0 := by
      by_contra h
      nlinarith [not_lt.1 h]
    rcases (norm_nonneg lam₂).lt_or_eq with hpos | h0
    · exact (Real.log_neg_iff hpos).1 hlog
    · rw [← h0, Real.log_zero] at hlog; exact absurd hlog (lt_irrefl 0)
  obtain ⟨K₁, hK₁, q₀, hrow⟩ := exists_norm_relativeRow_sub_le hι hdisj hN hA hσ htr hfix hl hlam
    hmix hγ0 (by linarith) hx1
  have hz : ∀ j j', ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (q : ℕ)
      (G : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j') × Fin (Dj j')) ℂ) (δ : ℝ) (M : ℕ)
      [NeZero M], ‖G - relativeRowLimit ι μ q σ j j'‖ ≤ δ →
      ‖mpvOverlap (ofPhysicalMatrixLM G) (fixedPointTensor (σ j)) M -
          (if j = j' then 1 else 0)‖ ≤ C * (M * δ) * Real.exp (C * (M * δ)) := fun j j' =>
    exists_norm_mpvOverlap_sub_ite_le hι hdisj (fun j => (hσ j).posSemidef) htr j j'
  choose C₀ hC₀ hgen using hz
  obtain ⟨Kt, hKt, hnorm⟩ := exists_abs_sum_norm_sq_sum_mpv_sub_le hN hA hσ htr hfix hl hlam hmix
    hγ0 hγ
  set Cz : Fin b × Fin b → ℝ := fun p => C₀ p.1 p.2 * K₁ + 1
  have hCz : ∀ p, 0 < Cz p := fun p =>
    add_pos_of_nonneg_of_pos (mul_nonneg (hC₀ p.1 p.2).le hK₁) one_pos
  set S := ∑ p, Cz p
  have hS : 0 ≤ S := Finset.sum_nonneg fun p _ => (hCz p).le
  have hxq₀ : 0 < x ^ q₀ := pow_pos hx0 q₀
  refine ⟨S + Kt + 1 + (x ^ q₀)⁻¹, by positivity, fun μ q M _ hβ => ?_⟩
  set Cf := S + Kt + 1 + (x ^ q₀)⁻¹
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  set u := (M : ℝ) * x ^ q
  have hu : 0 ≤ u := by positivity
  -- Short blocks: the trivial bound.
  by_cases hshort : q = 0 ∨ q < q₀
  · refine htriv Cf (by simp only [Cf]; linarith [inv_nonneg.2 hxq₀.le]) μ q M ?_
    have hxle : x ^ q₀ ≤ x ^ q := by
      rcases hshort with h | h
      · subst h; exact pow_le_one₀ hx0.le hx1.le
      · exact pow_le_pow_of_le_one hx0.le hx1.le h.le
    have h1 : 1 ≤ (x ^ q₀)⁻¹ * x ^ q := by
      rw [inv_mul_eq_div, le_div_iff₀ hxq₀, one_mul]; exact hxle
    have h2 : (x ^ q₀)⁻¹ * x ^ q ≤ Cf * u := by
      have : (x ^ q₀)⁻¹ ≤ Cf := by simp only [Cf]; linarith
      calc (x ^ q₀)⁻¹ * x ^ q ≤ Cf * x ^ q := by gcongr
        _ ≤ Cf * u := by
            simp only [u]; gcongr; exact le_mul_of_one_le_left (by positivity) hM
    linarith
  rw [not_or, not_lt] at hshort
  obtain ⟨hq0, hq⟩ := hshort
  have hD : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  -- The ingredients.
  set A := repeatedBlockSum Aj ι μ
  set β := bntWeight μ (M * q)
  set bb : ℝ := ∑ l, ‖β l‖ ^ 2
  have hbb : 0 < bb := sum_norm_sq_pos_of_ne_zero hβ
  have hsb : 0 < Real.sqrt bb := Real.sqrt_pos.2 hbb
  have hβle : ∀ j, ‖β j‖ ≤ Real.sqrt bb := fun j =>
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖β j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j))
  set P := Matrix.polarPos (physicalMatrix (blockTensor A q))
  set w : Fin b → Fin b → ℂ := fun j j' =>
    mpvOverlap (ofPhysicalMatrixLM (relativeRow A ι μ q j j')) (fixedPointTensor (σ j)) M
  set z : Fin b → ℂ := fun j => mpvOverlap (ofPhysicalMatrixLM ((copyIsometry ι μ q j)ᴴ * P))
    (fixedPointTensor (σ j)) M
  have hzw : ∀ j, z j = ∑ j', β j' * w j j' := fun j =>
    mpvOverlap_conjTranspose_copyIsometry_mul_polarPos hι hdisj μ hq0 j
      _ M
  set v := copyApproxVector A q M (ghzAmplitude β) (copyIsometry ι μ q) σ
  set num := ∑ τ, star (v τ) * mpv A (blockedConfigEquiv d M q τ)
  set Sz := ∑ j, star (β j) * z j
  have hnum : num = ((Real.sqrt bb : ℝ) : ℂ)⁻¹ * Sz := by
    simp only [num, v, sum_star_copyApproxVector_mul_mpv, Sz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ghzAmplitude, star_div₀, Complex.star_def, Complex.conj_ofReal, bb]
    ring
  set t := ‖mpvState A (M * q)‖
  have hov : t⁻¹ * ‖num‖ ≤ ‖copyApproxOverlap A q M (ghzAmplitude β) (copyIsometry ι μ q) σ‖ := by
    rw [copyApproxOverlap_eq]
    exact inv_mul_norm_le_norm_of_sum_norm_sq_le_one v _
      (sum_norm_sq_copyApproxVector_le A q M hβ
        (fun j => conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q)
        (fun j k h => conjTranspose_copyIsometry_mul_eq_zero hdisj μ q h)
        (fun j => (hσ j).posSemidef) htr) (norm_nonneg _)
  -- The overlaps of the blocks, relative to the weights.
  have hwj : ∀ p : Fin b × Fin b, ‖w p.1 p.2 - (if p.1 = p.2 then 1 else 0)‖ ≤
      Cz p * u * Real.exp (Cz p * u) := fun p => by
    have hG := (hrow μ q hq hq0).2 p.1 p.2
    have h := hgen p.1 p.2 μ q _ (K₁ * x ^ q) M hG
    have hre : C₀ p.1 p.2 * (M * (K₁ * x ^ q)) = C₀ p.1 p.2 * K₁ * u := by simp only [u]; ring
    calc _ ≤ C₀ p.1 p.2 * (M * (K₁ * x ^ q)) * Real.exp (C₀ p.1 p.2 * (M * (K₁ * x ^ q))) := h
      _ = C₀ p.1 p.2 * K₁ * u * Real.exp (C₀ p.1 p.2 * K₁ * u) := by rw [hre]
      _ ≤ Cz p * u * Real.exp (Cz p * u) := by
          have : C₀ p.1 p.2 * K₁ ≤ Cz p := by simp only [Cz]; linarith
          have h0 : 0 ≤ C₀ p.1 p.2 * K₁ := mul_nonneg (hC₀ p.1 p.2).le hK₁
          gcongr
  -- The rescaled overlap: `∑ⱼ conj(βⱼ) zⱼ = b (1 + O(∑ |w - δ|))`.
  set δ' := ∑ p : Fin b × Fin b, ‖w p.1 p.2 - (if p.1 = p.2 then 1 else 0)‖
  have hSz : ‖Sz / (bb : ℂ) - 1‖ ≤ δ' := by
    have hbbC : (bb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hbb.ne'
    have hrw : Sz / (bb : ℂ) - 1 = (∑ p : Fin b × Fin b, star (β p.1) * β p.2 *
        (w p.1 p.2 - (if p.1 = p.2 then 1 else 0))) / (bb : ℂ) := by
      rw [eq_div_iff hbbC, sub_mul, div_mul_cancel₀ _ hbbC, one_mul]
      simp only [Sz, hzw, bb, Complex.ofReal_sum, Fintype.sum_prod_type, mul_sub,
        Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
        ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        ring
    rw [hrw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbb, div_le_iff₀ hbb]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [norm_mul, norm_mul, norm_star, mul_comm _ bb]
    gcongr
    calc ‖β p.1‖ * ‖β p.2‖ ≤ Real.sqrt bb * Real.sqrt bb := by
          gcongr
          · exact hβle p.1
          · exact hβle p.2
      _ = bb := Real.mul_self_sqrt hbb.le
  have hNq : M * q ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) hq0
  have ht2 : |(t / Real.sqrt bb) ^ 2 - 1| ≤ Kt * x ^ (M * q) := by
    have h := hnorm (Real.sqrt bb) β hβle (M * q)
    have hT : t ^ 2 = ∑ s : Fin (M * q) → Fin d, ‖∑ j, β j * mpv (Aj j) s‖ ^ 2 := by
      simp only [t, EuclideanSpace.norm_sq_eq, mpvState_apply, A,
        mpv_repeatedBlockSum hι hdisj μ hNq]
      rfl
    rw [← hT, Real.sq_sqrt hbb.le] at h
    have he : (t / Real.sqrt bb) ^ 2 - 1 = (t ^ 2 - bb) / bb := by
      rw [div_pow, Real.sq_sqrt hbb.le]
      field_simp
    rw [he, abs_div, abs_of_pos hbb, div_le_iff₀ hbb]
    linarith [h]
  have hmain := one_sub_norm_div_le_of_norm_sub_le (b := 1) le_rfl
    (div_nonneg (norm_nonneg _) hsb.le) (by simpa using hSz) (by simpa using ht2)
  have hkey : (t / Real.sqrt bb)⁻¹ * (‖Sz / (bb : ℂ)‖ / Real.sqrt 1) = t⁻¹ * ‖num‖ := by
    rw [hnum, Real.sqrt_one, div_one, norm_mul, norm_div, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsb, abs_of_pos hbb,
      inv_div]
    rcases eq_or_ne t 0 with ht | ht
    · simp [ht]
    · field_simp
      rw [Real.sq_sqrt hbb.le, mul_comm]
  rw [hkey] at hmain
  -- Combine.
  have hfin := one_sub_le_mul_mul_exp_div_of_sum_le
    (r := ‖copyApproxOverlap A q M (ghzAmplitude β) (copyIsometry ι μ q) σ‖)
    (fun p => (hCz p).le) hwj hKt hx0.le hx1.le
    (NeZero.ne M) one_pos le_rfl (by rw [div_one]; change _ ≤ δ' + _; linarith)
  rw [div_one] at hfin
  refine hfin.trans ?_
  have hCf : S + Kt + 1 ≤ Cf := by simp only [Cf]; linarith [inv_nonneg.2 hxq₀.le]
  gcongr

open scoped Matrix.Norms.L2Operator in
/-- **Approximation error for repeated blocks with overlapping states, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected
approximating state at the corrected rate): in the setting of
`exists_approximationError_le_repeatedOverlappingBlockSum`, there is `C` with
`ε ≤ C M e^{-γ q/ξ}`, which is `C (N/q) e^{-γ q/ξ}` for `q ≥ 1`, for all nonzero complex weights
with `βⱼ = ∑ₖ μ_{j,k}^N` not all zero. -/
theorem exists_approximationError_le_mul_repeatedOverlappingBlockSum
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : CopyWeights b m, ∀ (q M : ℕ) [NeZero M],
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedOverlappingBlockSum hι hdisj hN hA
    hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun μ q M _ hβ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h μ q M hβ) ?_
  linarith [norm_nonneg (copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
    (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ)]

end MPSTensor
