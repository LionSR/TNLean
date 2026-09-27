/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Overlap of a subspace with a finite sum of subspaces

Nachtergaele's Lemma 9 bounds the overlap with a sum of subspaces in terms
of the pairwise overlaps. If \(B\) is the matrix of off-diagonal overlap bounds
and \(a\) bounds the overlaps with a distinguished subspace, the bound is
\(\|a\|/\sqrt{1-\|B\|}\), provided \(\|B\|<1\).

## References

* Nachtergaele, arXiv:cond-mat/9410110, Lemma 9, `overlapestimate`,
  equations `overlapineq` and `defB` (local source lines 2109--2175).
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Submodule

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype ι] [DecidableEq ι]

private theorem overlapMatrix_bilinear_le (B : Matrix ι ι ℝ)
    (v w : EuclideanSpace ℝ ι) :
    ∑ i, ∑ j, B i j * v i * w j ≤ ‖B‖ * ‖v‖ * ‖w‖ := by
  have h := (real_inner_le_norm v (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B w)).trans
    (mul_le_mul_of_nonneg_left
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B).le_opNorm w) (norm_nonneg v))
  simpa [Matrix.inner_toEuclideanCLM, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Matrix.l2_opNorm_toEuclideanCLM, mul_assoc, mul_left_comm] using h

/-- The quadratic form of a real matrix is bounded by its operator norm:
\(\sum_{i,j}B_{ij}w_iw_j\leq\|B\|\,\|w\|^2\), by Cauchy--Schwarz. -/
private theorem overlapMatrix_quadratic_le (B : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι) :
    ∑ i, ∑ j, B i j * w i * w j ≤ ‖B‖ * ‖w‖ ^ 2 := by
  simpa only [pow_two, mul_assoc] using overlapMatrix_bilinear_le B w w

omit [DecidableEq ι] in
/-- The pairwise overlap bounds give the lower Gram estimate in the proof of
Nachtergaele, arXiv:cond-mat/9410110, Lemma 9, equation `overlapineq`.
The matrix \(B\) has zero diagonal and bounds the off-diagonal inner products. -/
private theorem sum_norm_sq_le_norm_sum_sq_add_overlapMatrix (v : ι → E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0)
    (hpair : ∀ i j, i ≠ j → ‖⟪v i, v j⟫_ℂ‖ ≤ B i j * ‖v i‖ * ‖v j‖) :
    (∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, v i‖ ^ 2 + ∑ i, ∑ j, B i j * ‖v i‖ * ‖v j‖ := by
  classical
  have hEntry (i j : ι) :
      (if i = j then ‖v i‖ ^ 2 else 0) ≤
        (⟪v i, v j⟫_ℂ).re + B i j * ‖v i‖ * ‖v j‖ := by
    by_cases hij : i = j
    all_goals simp [hij, hdiag, ← Complex.ofReal_pow]
    linarith [hpair i j hij, (abs_le.mp (Complex.abs_re_le_norm ⟪v i, v j⟫_ℂ)).1]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ hEntry i j
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hsum
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (∑ i, v i), sum_inner]
  simpa only [inner_sum, map_sum, RCLike.re_eq_complex_re] using hsum

/-- The lower Gram estimate from Nachtergaele, arXiv:cond-mat/9410110,
Lemma 9: a matrix of pairwise overlap bounds controls the norm of a sum. -/
theorem norm_sum_sq_ge_of_overlapMatrix (v : ι → E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0)
    (hpair : ∀ i j, i ≠ j → ‖⟪v i, v j⟫_ℂ‖ ≤ B i j * ‖v i‖ * ‖v j‖) :
    (1 - ‖B‖) * (∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, v i‖ ^ 2 := by
  have hB : (∑ i, ∑ j, B i j * ‖v i‖ * ‖v j‖) ≤ ‖B‖ * ∑ i, ‖v i‖ ^ 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_toLp] using
      overlapMatrix_quadratic_le B (WithLp.toLp 2 fun i ↦ ‖v i‖)
  linarith [sum_norm_sq_le_norm_sum_sq_add_overlapMatrix v B hdiag hpair]

omit [DecidableEq ι] [InnerProductSpace ℂ E] in
private theorem norm_norms_le_of_lower_bound (v : ι → E) {b : ℝ} (hb : b < 1)
    (hLower : (1 - b) * (∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, v i‖ ^ 2) :
    ‖(WithLp.toLp 2 (fun i ↦ ‖v i‖) : EuclideanSpace ℝ ι)‖ ≤
      ‖∑ i, v i‖ / Real.sqrt (1 - b) := by
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ ‖v i‖
  have hSq : (‖w‖ * Real.sqrt (1 - b)) ^ 2 ≤ ‖∑ i, v i‖ ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt (sub_pos.mpr hb).le,
      EuclideanSpace.real_norm_sq_eq, w, WithLp.ofLp_toLp, mul_comm] using hLower
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (sub_pos.mpr hb))).mpr
    ((sq_le_sq₀ (mul_nonneg (norm_nonneg w) (Real.sqrt_nonneg _))
      (norm_nonneg _)).mp hSq)

omit [DecidableEq ι] in
/-- The final Cauchy--Schwarz step of Nachtergaele, arXiv:cond-mat/9410110,
Lemma 9: overlap bounds \(a_i\) with each summand and the lower Gram estimate
\((1-b)\sum_i\|v_i\|^2\leq\|\sum_i v_i\|^2\) give the bound
\(\|a\|/\sqrt{1-b}\) on the overlap of \(x\) with \(\sum_i v_i\). -/
private theorem norm_inner_sum_le_of_lower_bound (x : E) (v : ι → E)
    (a : EuclideanSpace ℝ ι) {b : ℝ} (hb : b < 1)
    (hLower : (1 - b) * (∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, v i‖ ^ 2)
    (hCross : ∀ i, ‖⟪x, v i⟫_ℂ‖ ≤ a i * ‖x‖ * ‖v i‖) :
    ‖⟪x, ∑ i, v i⟫_ℂ‖ ≤ ‖a‖ / Real.sqrt (1 - b) * ‖x‖ * ‖∑ i, v i‖ := by
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ ‖v i‖
  have hw : ‖w‖ ≤ ‖∑ i, v i‖ / Real.sqrt (1 - b) :=
    norm_norms_le_of_lower_bound v hb hLower
  have hCauchy : ∑ i, a i * ‖v i‖ ≤ ‖a‖ * ‖w‖ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, w, mul_comm] using
      real_inner_le_norm a w
  have htri : ‖⟪x, ∑ i, v i⟫_ℂ‖ ≤ ‖x‖ * ∑ i, a i * ‖v i‖ := by
    simpa only [inner_sum, Finset.mul_sum, mul_assoc, mul_left_comm] using
      (norm_sum_le Finset.univ (fun i ↦ ⟪x, v i⟫_ℂ)).trans
        (Finset.sum_le_sum fun i _ ↦ hCross i)
  have hbound := htri.trans (mul_le_mul_of_nonneg_left
    (hCauchy.trans (mul_le_mul_of_nonneg_left hw (norm_nonneg a))) (norm_nonneg x))
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- Nachtergaele, arXiv:cond-mat/9410110, Lemma 9 (`overlapestimate`):
the overlap of \(U\) with the sum of the \(V_i\) is bounded by
\(\|a\|/\sqrt{1-\|B\|}\). The entries of \(a\) bound the overlaps with
\(U\), and the zero-diagonal matrix \(B\) bounds the pairwise overlaps
among the \(V_i\). -/
theorem norm_inner_le_iSup_of_overlapMatrix (U : Submodule ℂ E)
    (V : ι → Submodule ℂ E) (a : EuclideanSpace ℝ ι) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1)
    (hpair : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖)
    (hCross : ∀ i, ∀ x ∈ U, ∀ v ∈ V i,
      ‖⟪x, v⟫_ℂ‖ ≤ a i * ‖x‖ * ‖v‖)
    {x y : E} (hx : x ∈ U) (hy : y ∈ ⨆ i, V i) :
    ‖⟪x, y⟫_ℂ‖ ≤ ‖a‖ / Real.sqrt (1 - ‖B‖) * ‖x‖ * ‖y‖ := by
  obtain ⟨v, rfl⟩ := (mem_iSup_finset_iff_exists_sum (s := Finset.univ) V y).mp
    (by simpa using hy)
  exact norm_inner_sum_le_of_lower_bound x (fun i ↦ (v i : E)) a hB
    (norm_sum_sq_ge_of_overlapMatrix _ B hdiag
      (fun i j hij ↦ hpair i j hij _ (v i).property _ (v j).property))
    (fun i ↦ hCross i x hx _ (v i).property)

omit [DecidableEq ι] in
/-- The lower Gram estimate for uniform pairwise overlaps at most \(\varepsilon\)
among \(m\) vectors: \((1-\varepsilon(m-1))\sum_i\|v_i\|^2\leq\|\sum_i v_i\|^2\),
by Cauchy--Schwarz \((\sum_i\|v_i\|)^2\leq m\sum_i\|v_i\|^2\). -/
private theorem norm_sum_sq_ge_of_uniform_overlap (v : ι → E) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hpair : ∀ i j, i ≠ j → ‖⟪v i, v j⟫_ℂ‖ ≤ ε * ‖v i‖ * ‖v j‖) :
    (1 - ε * ((Fintype.card ι : ℝ) - 1)) * (∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, v i‖ ^ 2 := by
  classical
  have hsum := sum_norm_sq_le_norm_sum_sq_add_overlapMatrix v
    (fun i j ↦ ε - if i = j then ε else 0) (by simp)
    (fun i j hij ↦ by simpa [hij] using hpair i j hij)
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Fintype.sum_ite_eq, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ← pow_two] at hsum
  have hCS : (∑ i, ‖v i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun _ ↦ (1 : ℝ)) (fun i ↦ ‖v i‖)
  nlinarith [mul_le_mul_of_nonneg_left hCS hε]

omit [DecidableEq ι] in
/-- The uniform-overlap conclusion of Nachtergaele, arXiv:cond-mat/9410110,
Lemma 9. For \(m\) subspaces with pairwise overlaps at most \(\varepsilon\),
and the same bound on their overlaps with \(U\), the overlap with their sum
is at most \(\varepsilon\sqrt m/\sqrt{1-\varepsilon(m-1)}\). If
\(0\leq\varepsilon\) and \(\varepsilon m\leq1\), this coefficient is at most one. -/
theorem iSup_overlap_bound_of_uniform (U : Submodule ℂ E)
    (V : ι → Submodule ℂ E) {ε : ℝ} (hε : 0 ≤ ε)
    (hεcard : ε * (Fintype.card ι : ℝ) ≤ 1)
    (hpair : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ ε * ‖u‖ * ‖v‖)
    (hCross : ∀ i, ∀ x ∈ U, ∀ v ∈ V i, ‖⟪x, v⟫_ℂ‖ ≤ ε * ‖x‖ * ‖v‖) :
    let η := ε * Real.sqrt (Fintype.card ι) /
      Real.sqrt (1 - ε * ((Fintype.card ι : ℝ) - 1))
    η ≤ 1 ∧ ∀ x ∈ U, ∀ y ∈ ⨆ i, V i, ‖⟪x, y⟫_ℂ‖ ≤ η * ‖x‖ * ‖y‖ := by
  have hβ : ε * ((Fintype.card ι : ℝ) - 1) < 1 := by
    nlinarith
  have hcoefSq : (ε * Real.sqrt (Fintype.card ι)) ^ 2 ≤
      1 - ε * ((Fintype.card ι : ℝ) - 1) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι))]
    nlinarith [mul_le_mul_of_nonneg_left hεcard hε]
  refine ⟨(div_le_one₀ (Real.sqrt_pos.mpr (sub_pos.mpr hβ))).mpr
    (Real.le_sqrt_of_sq_le hcoefSq), ?_⟩
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 fun _ ↦ ε
  have ha : ‖a‖ = ε * Real.sqrt (Fintype.card ι) := by
    simp [a, EuclideanSpace.norm_eq, Real.norm_eq_abs, abs_of_nonneg hε,
      Real.sqrt_mul (Nat.cast_nonneg (Fintype.card ι)), Real.sqrt_sq hε, mul_comm]
  intro x hx y hy
  obtain ⟨v, rfl⟩ := (mem_iSup_finset_iff_exists_sum (s := Finset.univ) V y).mp
    (by simpa using hy)
  simpa only [ha] using norm_inner_sum_le_of_lower_bound x (fun i ↦ (v i : E)) a hβ
    (norm_sum_sq_ge_of_uniform_overlap _ hε
      (fun i j hij ↦ hpair i j hij _ (v i).property _ (v j).property))
    (fun i ↦ hCross i x hx _ (v i).property)

/-- The off-diagonal pairing estimate in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation`, equation `5d`
(local source lines 2465--2500). The same matrix bounds the internal
overlaps of both families and their off-diagonal cross overlaps. -/
theorem sum_offDiagonal_norm_inner_le_of_overlapMatrix
    (v w : ι → E) (B : Matrix ι ι ℝ) (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1)
    (hv : ∀ i j, i ≠ j → ‖⟪v i, v j⟫_ℂ‖ ≤ B i j * ‖v i‖ * ‖v j‖)
    (hw : ∀ i j, i ≠ j → ‖⟪w i, w j⟫_ℂ‖ ≤ B i j * ‖w i‖ * ‖w j‖)
    (hcross : ∀ i j, i ≠ j → ‖⟪v i, w j⟫_ℂ‖ ≤ B i j * ‖v i‖ * ‖w j‖) :
    (∑ i, ∑ j, if i = j then 0 else ‖⟪v i, w j⟫_ℂ‖) ≤
      ‖B‖ / (1 - ‖B‖) * ‖∑ i, v i‖ * ‖∑ i, w i‖ := by
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ ‖v i‖
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ ‖w i‖
  have hab : (∑ i, ∑ j, if i = j then 0 else ‖⟪v i, w j⟫_ℂ‖) ≤
      ‖B‖ * ‖a‖ * ‖b‖ := by
    apply le_trans _ (overlapMatrix_bilinear_le B a b)
    apply Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
    by_cases hij : i = j
    · simp [hij, hdiag]
    · simpa [hij, a, b] using hcross i j hij
  have ha : ‖a‖ ≤ ‖∑ i, v i‖ / Real.sqrt (1 - ‖B‖) :=
    norm_norms_le_of_lower_bound v hB (norm_sum_sq_ge_of_overlapMatrix v B hdiag hv)
  have hb : ‖b‖ ≤ ‖∑ i, w i‖ / Real.sqrt (1 - ‖B‖) :=
    norm_norms_le_of_lower_bound w hB (norm_sum_sq_ge_of_overlapMatrix w B hdiag hw)
  calc
    _ ≤ ‖B‖ * ‖a‖ * ‖b‖ := hab
    _ ≤ ‖B‖ * (‖∑ i, v i‖ / Real.sqrt (1 - ‖B‖)) *
        (‖∑ i, w i‖ / Real.sqrt (1 - ‖B‖)) := by gcongr
    _ = _ := by
      field_simp
      rw [Real.sq_sqrt (sub_pos.mpr hB).le]

end Submodule
