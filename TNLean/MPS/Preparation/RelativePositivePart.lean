/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixSylvesterBound
import TNLean.MPS.Preparation.RepeatedOverlappingBlockOverlap

/-!
# The positive part relative to the block weights

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7)) write a
tensor that is not normal as `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ`. Its `q`-site blocked
map is `B = ∑ⱼ cⱼ B_j L_jᴴ = B̃ C`, with `B̃ = ∑ⱼ B_j L_jᴴ`, `C = ∑ⱼ cⱼ L_j L_jᴴ`, the copy norms
`cⱼ = (∑ₖ |μ_{j,k}|^{2q})^{1/2}`, and the copy isometries `L_j`
(`TNLean.MPS.Preparation.RepeatedBlockSum`). The positive part `P` of `B` is close to
`P_∞ = ∑ⱼ cⱼ L_j ((√σ_j)ᵀ ⊗ 1) L_jᴴ` in absolute terms
(`exists_norm_polarPos_blockTensor_repeatedBlockSum_sub_le`). This file proves that it is close
relative to each weight:

  `‖(P - P_∞) C⁻¹‖ ≤ K e^{-γ q/ξ}`,  `C⁻¹ = ∑ⱼ cⱼ⁻¹ L_j L_jᴴ`,

for `0 < γ < 1` and all `q` beyond a threshold, uniformly in the weights, which may be arbitrarily
small and need not satisfy `|μ_{j,k}| ≤ 1`
(`exists_norm_polarPos_blockTensor_repeatedBlockSum_sub_mul_le`). Hence the blocks
`L_jᴴ P L_{j'} / c_{j'}` are `δ_{jj'} ((√σ_j)ᵀ ⊗ 1)` up to `K e^{-γ q/ξ}`
(`exists_norm_relativeRow_sub_le`).

The proof: `X = (P - P_∞) C⁻¹` solves the Sylvester equation `P X + X P_∞ = C Δ Π` with
`Δ = B̃ᴴ B̃ - ∑ⱼ L_j (σ_jᵀ ⊗ 1) L_jᴴ` and `Π = ∑ⱼ L_j L_jᴴ`, and `P² = C B̃ᴴ B̃ C ≥ (λ/2) C²` once
`‖Δ‖ ≤ λ/2`, where `λ > 0` bounds every `σ_jᵀ ⊗ 1` from below
(`norm_polarPos_sub_mul_sum_le`); the entrywise bound for such Sylvester equations
(`Matrix.norm_le_of_mul_add_mul_eq_mul`) and the Gram estimate `exists_norm_gram_sum_sub_le` at unit
weights finish the proof. Unlike the absolute estimate, this one does not pass through the Hölder
bound of the square root, because `B̃ᴴ B̃` is bounded below on the range of `C`.

## Main declarations

* `MPSTensor.norm_polarPos_sub_mul_sum_le` — the relative bound for `B = B̃ C`.
* `MPSTensor.copyScaleInv`, `MPSTensor.relativeRow`, `MPSTensor.relativeRowLimit` — `C⁻¹`, the
  blocks `L_jᴴ P C⁻¹ L_{j'}` and their limits.
* `MPSTensor.exists_norm_polarPos_blockTensor_repeatedBlockSum_sub_mul_le`,
  `MPSTensor.exists_norm_relativeRow_sub_le` — the rate for blocks with multiplicities.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7) and the proof of Lemma 1'(ii).
* [Li97] R.-C. Li, *Relative perturbation bounds for the unitary polar factor*,
  BIT Numerical Mathematics 37 (1997), 67–75.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators
open Matrix

namespace MPSTensor

/-! ### Sums along isometries with orthogonal ranges -/

section Generic

variable {b : ℕ} {κ : Fin b → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
  {n : Type*} [Fintype n] [DecidableEq n] {L : (j : Fin b) → Matrix n (κ j) ℂ}

/-- The block-diagonal operator `∑ⱼ L_j F_j L_jᴴ`. -/
private noncomputable def isoSum (L : (j : Fin b) → Matrix n (κ j) ℂ)
    (F : (j : Fin b) → Matrix (κ j) (κ j) ℂ) : Matrix n n ℂ :=
  ∑ j, L j * F j * (L j)ᴴ

omit [DecidableEq n] in
private theorem isoSum_mul_isoSum (hiso : ∀ j, (L j)ᴴ * L j = 1)
    (horth : ∀ j k, j ≠ k → (L j)ᴴ * L k = 0) (F G : (j : Fin b) → Matrix (κ j) (κ j) ℂ) :
    isoSum L F * isoSum L G = isoSum L fun j => F j * G j :=
  sum_mul_conjTranspose_mul_sum_of_isometry hiso horth F G

omit [∀ j, DecidableEq (κ j)] [Fintype n] [DecidableEq n] in
private theorem conjTranspose_isoSum (F : (j : Fin b) → Matrix (κ j) (κ j) ℂ) :
    (isoSum L F)ᴴ = isoSum L fun j => (F j)ᴴ := by
  simp only [isoSum, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

omit [∀ j, DecidableEq (κ j)] [DecidableEq n] in
private theorem posSemidef_isoSum {F : (j : Fin b) → Matrix (κ j) (κ j) ℂ}
    (hF : ∀ j, (F j).PosSemidef) : (isoSum L F).PosSemidef :=
  posSemidef_sum _ fun j _ => (hF j).mul_mul_conjTranspose_same (L j)

omit [Fintype n] [DecidableEq n] in
private theorem isoSum_smul_one (t : Fin b → ℂ) :
    isoSum L (fun j => t j • (1 : Matrix (κ j) (κ j) ℂ)) = ∑ j, t j • (L j * (L j)ᴴ) := by
  simp only [isoSum, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

omit [∀ j, DecidableEq (κ j)] [Fintype n] [DecidableEq n] in
private theorem isoSum_smul (t : Fin b → ℂ) (F : (j : Fin b) → Matrix (κ j) (κ j) ℂ) :
    isoSum L (fun j => t j • F j) = ∑ j, t j • (L j * F j * (L j)ᴴ) := by
  simp only [isoSum, Matrix.mul_smul, Matrix.smul_mul]

open scoped Matrix.Norms.L2Operator in
/-- An orthogonal projector has operator norm at most one. -/
private theorem norm_le_one_of_isHermitian_of_mul_self {Q : Matrix n n ℂ} (hQ : Qᴴ = Q)
    (hQQ : Q * Q = Q) : ‖Q‖ ≤ 1 := by
  have h : ‖Q‖ * ‖Q‖ = ‖Q‖ := by
    rw [← CStarRing.norm_star_mul_self, star_eq_conjTranspose, hQ, hQQ]
  rcases (norm_nonneg Q).lt_or_eq with hpos | h0
  · nlinarith
  · rw [← h0]; exact zero_le_one

open scoped Matrix.Norms.L2Operator in
/-- **The positive part relative to the block weights.** Let `L_j` be isometries with orthogonal
ranges, `cⱼ > 0`, `C = ∑ⱼ cⱼ L_j L_jᴴ` and `C⁻¹ = ∑ⱼ cⱼ⁻¹ L_j L_jᴴ`, let `h_j ≥ 0` with
`h_j² = g_j ≥ λ > 0`, and let `M = B̃ C`. If `Δ = B̃ᴴ B̃ - ∑ⱼ L_j g_j L_jᴴ` has `‖Δ‖ ≤ λ/2`, then
the positive part `P` of `M` satisfies `‖(P - S) C⁻¹‖ ≤ n² (λ/2)^{-1/2} ‖Δ‖` with
`S = ∑ⱼ cⱼ L_j h_j L_jᴴ`, in dimension `n`: the bound does not depend on the weights `cⱼ`.

`X = (P - S) C⁻¹` solves `P X + X S = C Δ Π` with `Π = C C⁻¹`, and `P² = C B̃ᴴ B̃ C ≥ (λ/2) C²`;
`Matrix.norm_le_of_mul_add_mul_eq_mul` applies. -/
theorem norm_polarPos_sub_mul_sum_le (hiso : ∀ j, (L j)ᴴ * L j = 1)
    (horth : ∀ j k, j ≠ k → (L j)ᴴ * L k = 0) {c : Fin b → ℝ} (hc : ∀ j, 0 < c j)
    {h g : (j : Fin b) → Matrix (κ j) (κ j) ℂ} (hh : ∀ j, (h j).PosSemidef)
    (hhg : ∀ j, h j * h j = g j) {l : ℝ} (hl : 0 < l)
    (hg : ∀ j, (g j - (l : ℂ) • (1 : Matrix (κ j) (κ j) ℂ)).PosSemidef)
    {ι' : Type*} [Fintype ι'] (Bt : Matrix ι' n ℂ) {M : Matrix ι' n ℂ}
    (hM : M = Bt * ∑ j, (c j : ℂ) • (L j * (L j)ᴴ))
    (hΔ : ‖Btᴴ * Bt - ∑ j, L j * g j * (L j)ᴴ‖ ≤ l / 2) :
    ‖(polarPos M - ∑ j, (c j : ℂ) • (L j * h j * (L j)ᴴ)) *
        ∑ j, ((c j : ℂ)⁻¹) • (L j * (L j)ᴴ)‖ ≤
      (Fintype.card n : ℝ) ^ 2 * ((Real.sqrt (l / 2))⁻¹ *
        ‖Btᴴ * Bt - ∑ j, L j * g j * (L j)ᴴ‖) := by
  have hc0 : ∀ j, (c j : ℂ) ≠ 0 := fun j => Complex.ofReal_ne_zero.2 (hc j).ne'
  have hreal : ∀ j, star (c j : ℂ) = c j := fun j => Complex.conj_ofReal _
  rw [← isoSum_smul_one (L := L) fun j => (c j : ℂ)] at hM
  rw [← isoSum_smul_one (L := L) fun j => ((c j : ℂ))⁻¹, ← isoSum_smul (L := L) (fun j => (c j : ℂ)) h]
  change ‖(polarPos M - isoSum L fun j => (c j : ℂ) • h j) *
      (isoSum L fun j => ((c j : ℂ))⁻¹ • (1 : Matrix (κ j) (κ j) ℂ))‖ ≤
    _ * (_ * ‖Btᴴ * Bt - isoSum L g‖)
  change ‖Btᴴ * Bt - isoSum L g‖ ≤ l / 2 at hΔ
  -- The algebra of the block sums.
  have hCC : (isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ))ᴴ =
      isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ) := by
    rw [conjTranspose_isoSum]
    congr 1
    funext j
    rw [conjTranspose_smul, conjTranspose_one, hreal]
  have hCCi : (isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ)) *
      (isoSum L fun j => ((c j : ℂ))⁻¹ • (1 : Matrix (κ j) (κ j) ℂ)) =
      isoSum L fun j => (1 : Matrix (κ j) (κ j) ℂ) := by
    rw [isoSum_mul_isoSum hiso horth]
    congr 1
    funext j
    rw [smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ (hc0 j), one_smul]
  have hSCi : (isoSum L fun j => (c j : ℂ) • h j) *
      (isoSum L fun j => ((c j : ℂ))⁻¹ • (1 : Matrix (κ j) (κ j) ℂ)) =
      (isoSum L fun j => ((c j : ℂ))⁻¹ • (1 : Matrix (κ j) (κ j) ℂ)) *
        isoSum L fun j => (c j : ℂ) • h j := by
    rw [isoSum_mul_isoSum hiso horth, isoSum_mul_isoSum hiso horth]
    congr 1
    funext j
    rw [smul_mul_smul_comm, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, mul_comm]
  have hSS : (isoSum L fun j => (c j : ℂ) • h j) * (isoSum L fun j => (c j : ℂ) • h j) =
      (isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ)) * isoSum L g *
        isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ) := by
    rw [isoSum_mul_isoSum hiso horth, isoSum_mul_isoSum hiso horth, isoSum_mul_isoSum hiso horth]
    congr 1
    funext j
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, hhg]
  have hblock : (isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ)) * isoSum L g *
      (isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ)) -
      (l : ℂ) • ((isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ)) *
        isoSum L fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ)) =
      isoSum L fun j => ((c j : ℂ) * c j) • (g j - (l : ℂ) • 1) := by
    rw [isoSum_mul_isoSum hiso horth, isoSum_mul_isoSum hiso horth, isoSum_mul_isoSum hiso horth]
    simp only [isoSum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub, Matrix.mul_sub, Matrix.sub_mul, smul_smul, mul_comm (l : ℂ)]
  have hPr : (isoSum L fun j => (1 : Matrix (κ j) (κ j) ℂ))ᴴ =
      isoSum L fun j => (1 : Matrix (κ j) (κ j) ℂ) := by
    rw [conjTranspose_isoSum]; simp only [conjTranspose_one]
  have hPrPr : (isoSum L fun j => (1 : Matrix (κ j) (κ j) ℂ)) *
      (isoSum L fun j => (1 : Matrix (κ j) (κ j) ℂ)) =
      isoSum L fun j => (1 : Matrix (κ j) (κ j) ℂ) := by
    rw [isoSum_mul_isoSum hiso horth]; simp only [Matrix.one_mul]
  have hG₀h : (isoSum L g).IsHermitian := by
    change (isoSum L g)ᴴ = isoSum L g
    rw [conjTranspose_isoSum]
    congr 1
    funext j
    rw [← hhg j, conjTranspose_mul, (hh j).1.eq]
  have hSpsd : (isoSum L fun j => (c j : ℂ) • h j).PosSemidef :=
    posSemidef_isoSum fun j => (hh j).smul (Complex.zero_le_real.2 (hc j).le)
  have hblockpsd : (isoSum L fun j => ((c j : ℂ) * c j) • (g j - (l : ℂ) • 1)).PosSemidef :=
    posSemidef_isoSum fun j => (hg j).smul (by
      rw [← Complex.ofReal_mul]; exact Complex.zero_le_real.2 (mul_self_nonneg _))
  -- Forget the block structure.
  generalize isoSum L (fun j => (c j : ℂ) • (1 : Matrix (κ j) (κ j) ℂ)) = C at *
  generalize isoSum L (fun j => ((c j : ℂ))⁻¹ • (1 : Matrix (κ j) (κ j) ℂ)) = Ci at *
  generalize isoSum L (fun j => (c j : ℂ) • h j) = S at *
  generalize isoSum L (fun j => ((c j : ℂ) * c j) • (g j - (l : ℂ) • 1)) = Q at *
  generalize isoSum L (fun j => (1 : Matrix (κ j) (κ j) ℂ)) = Pr at *
  generalize isoSum L g = G₀ at *
  subst hM
  set P := polarPos (Bt * C)
  set Δ := Btᴴ * Bt - G₀
  have hPP : P * P = C * (G₀ + Δ) * C := by
    rw [polarPos_mul_polarPos, conjTranspose_mul, hCC, add_sub_cancel]
    simp only [Matrix.mul_assoc]
  -- The Sylvester equation `P X + X S = C (Δ Π)`.
  have hsyl : P * (P * Ci + (-Ci) * S) + (P * Ci + (-Ci) * S) * S = C * (Δ * Pr) := by
    have h1 : P * (P * Ci + (-Ci) * S) + (P * Ci + (-Ci) * S) * S =
        P * P * Ci - S * S * Ci := by
      have e : Ci * S * S = S * S * Ci := by
        rw [← hSCi, Matrix.mul_assoc, ← hSCi, ← Matrix.mul_assoc]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc,
        e]
      abel
    rw [h1, hPP, hSS, ← Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, add_sub_cancel_left,
      Matrix.mul_assoc, Matrix.mul_assoc, hCCi]
  -- The lower bound `P² ≥ (λ/2) C²`.
  have hΔh : IsSelfAdjoint Δ :=
    ((isHermitian_conjTranspose_mul_self Bt).sub hG₀h).isSelfAdjoint
  have hΔpos : (Δ + (‖Δ‖ : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
    have h := hΔh.neg_algebraMap_norm_le_self
    rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one, sub_neg_eq_add] at h
    simpa only [Complex.coe_smul] using h
  have hlow : (P * P - ((l / 2 : ℝ) : ℂ) • (C * Cᴴ)).PosSemidef := by
    have hsplit : P * P - ((l / 2 : ℝ) : ℂ) • (C * Cᴴ) =
        Q + Cᴴ * (Δ + (‖Δ‖ : ℂ) • 1) * C + ((l / 2 - ‖Δ‖ : ℝ) : ℂ) • (Cᴴ * C) := by
      rw [← hblock, hPP, hCC]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Complex.ofReal_sub, Complex.ofReal_div]
      push_cast
      module
    rw [hsplit]
    exact (hblockpsd.add (hΔpos.conjTranspose_mul_mul_same C)).add
      ((posSemidef_conjTranspose_mul_self C).smul
        (Complex.zero_le_real.2 (by linarith)))
  have hX : (P - S) * Ci = P * Ci + (-Ci) * S := by
    rw [Matrix.sub_mul, hSCi, Matrix.neg_mul, sub_eq_add_neg]
  have hPrn : ‖Pr‖ ≤ 1 := norm_le_one_of_isHermitian_of_mul_self hPr hPrPr
  rw [hX]
  refine (Matrix.norm_le_of_mul_add_mul_eq_mul (posSemidef_polarPos (Bt * C)) hSpsd
    (by positivity) hlow hsyl).trans ?_
  gcongr
  calc ‖Δ * Pr‖ ≤ ‖Δ‖ * ‖Pr‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Δ‖ * 1 := by gcongr
    _ = ‖Δ‖ := mul_one _

end Generic

/-! ### Blocks with multiplicities -/

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}
  {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- The inverse `C⁻¹ = ∑ⱼ cⱼ⁻¹ L_j L_jᴴ` of the weights `cⱼ = (∑ₖ |μ_{j,k}|^{2q})^{1/2}` on the
ranges of the copy isometries `L_j` (arXiv:2307.01696, Supplemental Material, eq. (S5), corrected
as in `TNLean.MPS.Preparation.RepeatedBlockSum`). -/
noncomputable def copyScaleInv (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D)
    (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ) : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ∑ j, ((copyNorm μ q j : ℂ)⁻¹) • (copyIsometry ι μ q j * (copyIsometry ι μ q j)ᴴ)

/-- The block `L_jᴴ P C⁻¹ L_{j'} = L_jᴴ P L_{j'} / c_{j'}` of the positive part `P` of the
`q`-site blocked tensor of `A`, relative to the weight of block `j'`
(`relativeRow_eq_smul`). -/
noncomputable def relativeRow (A : MPSTensor d D)
    (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D) (μ : (j : Fin b) → Fin (m j) → ℂ)
    (q : ℕ) (j j' : Fin b) : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j') × Fin (Dj j')) ℂ :=
  (copyIsometry ι μ q j)ᴴ * Matrix.polarPos (physicalMatrix (blockTensor A q)) *
    copyScaleInv ι μ q * copyIsometry ι μ q j'

/-- The block `L_jᴴ P_∞ C⁻¹ L_{j'}` of the limit `P_∞` of the positive parts: `(√σ_j)ᵀ ⊗ 1` for
`j = j'` (`relativeRowLimit_self`) and `0` otherwise (`relativeRowLimit_of_ne`). -/
noncomputable def relativeRowLimit (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D)
    (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (j j' : Fin b) :
    Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j') × Fin (Dj j')) ℂ :=
  (copyIsometry ι μ q j)ᴴ * copyPosLimit ι μ q σ * copyScaleInv ι μ q * copyIsometry ι μ q j'

section Multiplicities

variable (hι : ∀ j k, Function.Injective (ι j k))
  (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
include hι hdisj

/-- `C⁻¹ L_j = cⱼ⁻¹ L_j`. -/
theorem copyScaleInv_mul_copyIsometry (μ : CopyWeights b m) (q : ℕ) (j : Fin b) :
    copyScaleInv ι μ q * copyIsometry ι μ q j =
      ((copyNorm μ q j : ℂ)⁻¹) • copyIsometry ι μ q j := by
  rw [copyScaleInv, Matrix.sum_mul, Finset.sum_eq_single j]
  · rw [Matrix.smul_mul, Matrix.mul_assoc,
      conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q, Matrix.mul_one]
  · intro l _ hl
    rw [Matrix.smul_mul, Matrix.mul_assoc, conjTranspose_copyIsometry_mul_eq_zero hdisj μ q hl,
      Matrix.mul_zero, smul_zero]
  · simp

/-- `L_jᴴ P C⁻¹ L_{j'} = c_{j'}⁻¹ L_jᴴ P L_{j'}`. -/
theorem relativeRow_eq_smul (A : MPSTensor d D) (μ : CopyWeights b m) (q : ℕ) (j j' : Fin b) :
    relativeRow A ι μ q j j' = ((copyNorm μ q j' : ℂ)⁻¹) •
      ((copyIsometry ι μ q j)ᴴ * Matrix.polarPos (physicalMatrix (blockTensor A q)) *
        copyIsometry ι μ q j') := by
  rw [relativeRow, Matrix.mul_assoc _ (copyScaleInv ι μ q), copyScaleInv_mul_copyIsometry hι hdisj,
    Matrix.mul_smul]

/-- `L_jᴴ P_∞ = cⱼ ((√σ_j)ᵀ ⊗ 1) L_jᴴ`. -/
private theorem conjTranspose_copyIsometry_mul_copyPosLimit_eq_smul (μ : CopyWeights b m)
    (q : ℕ) (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (j : Fin b) :
    (copyIsometry ι μ q j)ᴴ * copyPosLimit ι μ q σ = (copyNorm μ q j : ℂ) •
      (((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) *
        (copyIsometry ι μ q j)ᴴ) := by
  have h := conjTranspose_mul_sum_of_isometry
    (fun j => conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q)
    (fun j k (h : j ≠ k) => conjTranspose_copyIsometry_mul_eq_zero hdisj μ q h)
    (fun l => (copyNorm μ q l : ℂ) •
      (((CFC.sqrt (σ l))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj l)) (Fin (Dj l)) ℂ)) *
        (copyIsometry ι μ q l)ᴴ)) j
  rw [← h, copyPosLimit]
  simp only [Matrix.mul_smul, Matrix.mul_assoc]

/-- `L_jᴴ P_∞ C⁻¹ L_{j'} = c_{j'}⁻¹ cⱼ ((√σ_j)ᵀ ⊗ 1) L_jᴴ L_{j'}`. -/
private theorem relativeRowLimit_eq (μ : CopyWeights b m) (q : ℕ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (j j' : Fin b) :
    relativeRowLimit ι μ q σ j j' = ((copyNorm μ q j' : ℂ)⁻¹ * copyNorm μ q j) •
      (((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) *
        ((copyIsometry ι μ q j)ᴴ * copyIsometry ι μ q j')) := by
  rw [relativeRowLimit, Matrix.mul_assoc _ (copyScaleInv ι μ q),
    copyScaleInv_mul_copyIsometry hι hdisj, Matrix.mul_smul,
    conjTranspose_copyIsometry_mul_copyPosLimit_eq_smul hι hdisj, Matrix.smul_mul, smul_smul,
    Matrix.mul_assoc]

/-- The diagonal block of the limit is `(√σ_j)ᵀ ⊗ 1`. -/
theorem relativeRowLimit_self (μ : CopyWeights b m) (q : ℕ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (j : Fin b) :
    relativeRowLimit ι μ q σ j j =
      (CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) := by
  rw [relativeRowLimit_eq hι hdisj,
    conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q, Matrix.mul_one,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (copyNorm_pos (μ.weight_fun_ne_zero j) q).ne'),
    one_smul]

/-- The blocks of the limit off the diagonal vanish. -/
theorem relativeRowLimit_of_ne (μ : CopyWeights b m) (q : ℕ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) {j j' : Fin b} (h : j ≠ j') :
    relativeRowLimit ι μ q σ j j' = 0 := by
  rw [relativeRowLimit_eq hι hdisj, conjTranspose_copyIsometry_mul_eq_zero hdisj μ q h,
    Matrix.mul_zero, smul_zero]

end Multiplicities

/-- Some `λ > 0` bounds every `σ_jᵀ ⊗ 1` from below when every `σ_j` is positive definite. -/
private theorem exists_pos_transpose_kronecker_one_sub
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) :
    ∃ l : ℝ, 0 < l ∧ ∀ j, ((σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) -
      (l : ℂ) • (1 : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j) × Fin (Dj j)) ℂ)).PosSemidef := by
  have hc : ∀ j, ∃ c : ℝ, 0 < c ∧
      algebraMap ℝ (Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) c ≤ σ j := fun j => by
    have := Matrix.neZero_of_trace_eq_one (htr j)
    have hsp : IsStrictlyPositive (σ j) := (hσ j).isStrictlyPositive
    obtain ⟨c, hc, hcb⟩ := (CFC.exists_pos_algebraMap_le_iff (σ j)
      hsp.nonneg.isSelfAdjoint).2 fun x hx => hsp.spectrum_pos hx
    exact ⟨c, hc, hcb⟩
  choose c hc0 hcσ using hc
  set c₀ : ℝ := 1 / (1 + ∑ j, 1 / c j)
  have hS : 0 ≤ ∑ j, 1 / c j := Finset.sum_nonneg fun j _ => (one_div_pos.2 (hc0 j)).le
  have hc₀ : 0 < c₀ := by positivity
  have hc₀j : ∀ j, c₀ ≤ c j := fun j => by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / c j ≤ ∑ j, 1 / c j :=
      Finset.single_le_sum (f := fun j => 1 / c j) (fun j _ => (one_div_pos.2 (hc0 j)).le)
        (Finset.mem_univ j)
    have h1 : c j * (1 / c j) = 1 := mul_one_div_cancel (hc0 j).ne'
    nlinarith [hc0 j]
  refine ⟨c₀, hc₀, fun j => ?_⟩
  have hblock : (σ j - (c₀ : ℂ) • (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)).PosSemidef := by
    have h := (algebraMap_mono (Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (hc₀j j)).trans (hcσ j)
    rwa [Matrix.le_iff, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at h
  have hkron : (σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) - (c₀ : ℂ) • 1 =
      (σ j - (c₀ : ℂ) • 1)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_eq_add_neg,
      sub_eq_add_neg, Matrix.add_kronecker, ← neg_smul, ← neg_smul, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  rw [hkron]
  exact (Matrix.posSemidef_transpose_iff.2 hblock).kronecker Matrix.PosSemidef.one

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)}

open scoped Matrix.Norms.L2Operator in
/-- **Rate of the positive part relative to the block weights.** Let the blocks `A_j` be normal
in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`, let `λ₂` with
`|λ₂| < 1` bound the moduli of the eigenvalues other than `1` of every `E_{A_j}` and of all
eigenvalues of the mixed transfer maps `E_{jj'}` of distinct blocks, and let `0 < γ < 1` with
`e^{-γ/ξ} < 1`. There are `K` and `q₀` such that for all nonzero weights `μ_{j,k}` and all
`q ≥ q₀`, `q ≥ 1`, the positive part `P` of the `q`-site blocked direct sum
`⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_j` satisfies `‖(P - P_∞) C⁻¹‖ ≤ K e^{-γ q/ξ}`, so that
every block satisfies `‖L_jᴴ P L_{j'} / c_{j'} - δ_{jj'} ((√σ_j)ᵀ ⊗ 1)‖ ≤ K e^{-γ q/ξ}`
(arXiv:2307.01696, Supplemental Material, eq. (S5), corrected as in
`TNLean.MPS.Preparation.RepeatedBlockSum`, relative to each weight).

The Gram estimate `exists_norm_gram_sum_sub_le` at unit weights bounds `Δ`, and
`norm_polarPos_sub_mul_sum_le` gives the relative bound once `‖Δ‖ ≤ λ/2`. -/
theorem exists_norm_relativeRow_sub_le
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) (hx1 : Real.exp (-γ / correlationLength lam₂) < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ q₀ : ℕ, ∀ μ : CopyWeights b m, ∀ q : ℕ, q₀ ≤ q → q ≠ 0 →
      ‖(Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) -
          copyPosLimit ι μ q σ) * copyScaleInv ι μ q‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q ∧
      ∀ j j', ‖relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j' -
          relativeRowLimit ι μ q σ j j'‖ ≤ K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  obtain ⟨Kg, hKg, hG⟩ := exists_norm_gram_sum_sub_le (D := D) hN hA hσ htr hfix hl hlam hmix
    hγ0 hγ
  obtain ⟨l, hl0, hg⟩ := exists_pos_transpose_kronecker_one_sub hσ htr
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx0 : 0 < x := Real.exp_pos _
  obtain ⟨q₀, hq₀⟩ := exists_pow_lt_of_lt_one (show 0 < l / 2 / (Kg + 1) by positivity) hx1
  set n := Fintype.card (Fin D × Fin D)
  set K := (n : ℝ) ^ 2 * (Real.sqrt (l / 2))⁻¹ * Kg
  refine ⟨K, by positivity, q₀, fun μ q hq hq0 => ?_⟩
  have hxq : x ^ q ≤ x ^ q₀ := pow_le_pow_of_le_one hx0.le hx1.le hq
  set L := copyIsometry ι μ q
  have hiso : ∀ j, (L j)ᴴ * L j = 1 := fun j =>
    conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q
  have horth : ∀ j k, j ≠ k → (L j)ᴴ * L k = 0 := fun j k h =>
    conjTranspose_copyIsometry_mul_eq_zero hdisj μ q h
  have hLn : ∀ j, ‖L j‖ ≤ 1 := fun j => Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
    (hiso j)
  set Bt := ∑ j, physicalMatrix (blockTensor (Aj j) q) * (L j)ᴴ
  have hΔ := hG 1 (fun _ => 1) L (fun _ => by simp) hLn q
  simp only [one_smul, norm_one, one_pow, Complex.ofReal_one, one_mul] at hΔ
  change ‖Btᴴ * Bt - ∑ j, L j * ((σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) *
    (L j)ᴴ‖ ≤ Kg * x ^ q at hΔ
  have hsmall : Kg * x ^ q ≤ l / 2 := by
    have h1 : (Kg + 1) * x ^ q₀ < l / 2 := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < Kg + 1)] at hq₀; linarith
    nlinarith [pow_nonneg hx0.le q]
  have hM : physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q) =
      Bt * ∑ j, (copyNorm μ q j : ℂ) • (L j * (L j)ᴴ) := by
    rw [physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry hι hdisj hq0, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := conjTranspose_mul_sum_of_isometry hiso horth
      (fun k => (copyNorm μ q k : ℂ) • (L k)ᴴ) j
    have h' : (L j)ᴴ * ∑ k, (copyNorm μ q k : ℂ) • (L k * (L k)ᴴ) =
        (copyNorm μ q j : ℂ) • (L j)ᴴ := by
      rw [← h]; simp only [Matrix.mul_smul]
    rw [Matrix.mul_assoc, h', Matrix.mul_smul]
  have hh : ∀ j, ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)).PosSemidef :=
    fun j => (Matrix.posSemidef_transpose_iff.2
      (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (σ j)))).kronecker Matrix.PosSemidef.one
  have hhg : ∀ j, ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) *
      ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) =
      (σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) := fun j => by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Matrix.transpose_mul,
      CFC.sqrt_mul_sqrt_self (σ j) (hσ j).posSemidef.nonneg]
  have key := norm_polarPos_sub_mul_sum_le hiso horth
    (fun j => copyNorm_pos (μ.weight_fun_ne_zero j) q) hh hhg hl0 hg Bt hM (hΔ.trans hsmall)
  have hX : ‖(Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) -
      copyPosLimit ι μ q σ) * copyScaleInv ι μ q‖ ≤ K * x ^ q := by
    calc _ ≤ (n : ℝ) ^ 2 * ((Real.sqrt (l / 2))⁻¹ * (Kg * x ^ q)) := key.trans (by gcongr)
      _ = K * x ^ q := by simp only [K]; ring
  refine ⟨hX, fun j j' => ?_⟩
  have hdiff : relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j' - relativeRowLimit ι μ q σ j j' =
      (L j)ᴴ * ((Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) -
        copyPosLimit ι μ q σ) * copyScaleInv ι μ q) * L j' := by
    simp only [relativeRow, relativeRowLimit, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, L]
  rw [hdiff]
  calc _ ≤ ‖(L j)ᴴ‖ * ‖(Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) -
        copyPosLimit ι μ q σ) * copyScaleInv ι μ q‖ * ‖L j'‖ :=
        (Matrix.l2_opNorm_mul _ _).trans (by gcongr; exact Matrix.l2_opNorm_mul _ _)
    _ ≤ 1 * (K * x ^ q) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
        exacts [hLn j, hLn j']
    _ = K * x ^ q := by ring

end MPSTensor
