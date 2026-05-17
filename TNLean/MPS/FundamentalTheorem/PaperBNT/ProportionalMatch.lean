/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.StrongMatch

/-!
# Proportional sector matching for two BNT canonical forms

The main theorem `MPSTensor.ft_paper_bnt_proportional_sector_match`
delivers the basis-count identity $g_P = g_Q$, a basis bijection
$\beta : \{1,\dots,g_Q\} \to \{1,\dots,g_P\}$, per-block bond-dimension
equality $D_P^{(\beta k)} = D_Q^{(k)}$, and per-block gauge-phase
equivalence $B_k = \zeta_k X_k A_{\beta k} X_k^{-1}$, from the hypotheses

* both decompositions are `IsBNTCanonicalForm`,
* every basis sector on each side carries a unit-modulus copy weight,
* eventual nonzero proportionality $V^{(N)}(P) = c_N V^{(N)}(Q)$
  (`EventuallyNonzeroProportionalMPV₂`).

The proof mirrors the equal-MPV chain in `DominantMatch` and `StrongMatch`,
but keeps the per-$N$ proportionality scalar $c_N$ inside the projection
identity.  The novel analytic input is the joint Cesàro non-decay of
$P.\mathrm{coeff}(N,j)\cdot Q.\mathrm{coeff}(N,k)$, which expands as
$\sum_{q,p}(\mu_{j,q}^P\,\mu_{k,p}^Q)^N$ — a single sum of $N$-th powers
with a unit-modulus pair — to which
`CesaroNonDecay.sum_pow_not_tendsto_zero_of_unit_modulus` applies.

The per-block matching at a fixed sector $k_0$ of $Q$ projects the
proportionality identity onto $V^{(N)}(B_{k_0})$ and onto
$V^{(N)}(A_{j^*})$, multiplies the two equations to eliminate $c_N$, and
contradicts the joint non-decay.  Dimension equality and gauge-phase
equivalence then follow as in the equal case, and the full bijection
comes from running the per-block matching in both directions.

## References

* CPSV16: arXiv:1606.00608, lines 349–352 (theorem `thm1`), 1167–1170
  (restatement), 1182–1188 (proof).
* CPSV21: arXiv:2011.12127, lines 1891–1894 (proportional target).
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **Joint Cesàro non-decay** of the product of two unit-block sector
coefficients.

For sectors $j$ on side $P$ and $k$ on side $Q$ with unit-modulus copy
witnesses $q^*$ and $p^*$, the product
$P.\mathrm{coeff}(N,j)\cdot Q.\mathrm{coeff}(N,k)
  = \sum_{q,p}(\mu_{j,q}^P\,\mu_{k,p}^Q)^N$
has a unit-modulus summand at $(q^*,p^*)$.  By
`CesaroNonDecay.sum_pow_not_tendsto_zero_of_unit_modulus` the sum does not
tend to zero.  Paper anchor: CPSV16 §II.A line 246 and §II.C lines
1181–1188. -/
lemma joint_coeff_not_tendsto_zero
    {P Q : SectorDecomposition d}
    (j : Fin P.basisCount) (k : Fin Q.basisCount)
    (hUnitP : ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∃ p : Fin (Q.copies k), ‖Q.weight k p‖ = 1)
    (hLeP : ∀ q : Fin (P.copies j), ‖P.weight j q‖ ≤ 1)
    (hLeQ : ∀ p : Fin (Q.copies k), ‖Q.weight k p‖ ≤ 1) :
    ¬ Tendsto (fun N : ℕ => P.coeff N j * Q.coeff N k) atTop (𝓝 0) := by
  classical
  -- Re-express the product as a single sum of `N`-th powers over the
  -- product index `Fin (P.copies j) × Fin (Q.copies k)`, then transport to
  -- `Fin (P.copies j * Q.copies k)` via `finProdFinEquiv` so that the
  -- pure-analytic Cesàro lemma applies.
  set r : ℕ := P.copies j * Q.copies k with hr_def
  let e : Fin (P.copies j) × Fin (Q.copies k) ≃ Fin r := finProdFinEquiv
  let μ : Fin r → ℂ := fun s =>
    P.weight j (e.symm s).1 * Q.weight k (e.symm s).2
  -- Modulus bound on `μ`.
  have hμ_le : ∀ s : Fin r, ‖μ s‖ ≤ 1 := by
    intro s
    have h1 : ‖P.weight j (e.symm s).1‖ ≤ 1 := hLeP _
    have h2 : ‖Q.weight k (e.symm s).2‖ ≤ 1 := hLeQ _
    have hp_nn : (0 : ℝ) ≤ ‖P.weight j (e.symm s).1‖ := norm_nonneg _
    have hq_nn : (0 : ℝ) ≤ ‖Q.weight k (e.symm s).2‖ := norm_nonneg _
    have hμs_eq : ‖μ s‖ =
        ‖P.weight j (e.symm s).1‖ * ‖Q.weight k (e.symm s).2‖ := by
      simp [μ]
    rw [hμs_eq]
    calc ‖P.weight j (e.symm s).1‖ * ‖Q.weight k (e.symm s).2‖
        ≤ 1 * 1 := mul_le_mul h1 h2 hq_nn (by norm_num : (0:ℝ) ≤ 1)
      _ = 1 := by norm_num
  -- A unit-modulus pair exists.
  have hμ_unit : ∃ s : Fin r, ‖μ s‖ = 1 := by
    rcases hUnitP with ⟨q_star, hq_star⟩
    rcases hUnitQ with ⟨p_star, hp_star⟩
    refine ⟨e (q_star, p_star), ?_⟩
    simp [μ, e, hq_star, hp_star]
  -- The Cesàro non-decay theorem provides the per-sequence non-decay.
  have hCesaro :
      ¬ Tendsto (fun N : ℕ => ∑ s : Fin r, (μ s) ^ N) atTop (𝓝 0) :=
    CesaroNonDecay.sum_pow_not_tendsto_zero_of_unit_modulus μ hμ_le hμ_unit
  -- Identify the sum `∑ s, (μ s)^N` with `P.coeff N j * Q.coeff N k`.
  intro hT
  apply hCesaro
  refine hT.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro N
  -- `∑_{s : Fin r} (μ s)^N = ∑_{(q,p)} (P.weight j q · Q.weight k p)^N
  --   = (∑_q (P.weight j q)^N) * (∑_p (Q.weight k p)^N)`.
  have hSum :
      (∑ s : Fin r, (μ s) ^ N)
        = ∑ pq : Fin (P.copies j) × Fin (Q.copies k),
            (P.weight j pq.1 * Q.weight k pq.2) ^ N := by
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl ?_
    intro pq _
    simp [μ, e]
  have hProd :
      (∑ pq : Fin (P.copies j) × Fin (Q.copies k),
          (P.weight j pq.1 * Q.weight k pq.2) ^ N)
        = (∑ q : Fin (P.copies j), (P.weight j q) ^ N) *
            (∑ p : Fin (Q.copies k), (Q.weight k p) ^ N) := by
    rw [Finset.sum_mul_sum]
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl ?_
    intro pq _
    rw [mul_pow]
  -- The two sums of `N`-th powers are precisely the sector coefficients.
  have hPc : (∑ q : Fin (P.copies j), (P.weight j q) ^ N) = P.coeff N j := rfl
  have hQc : (∑ p : Fin (Q.copies k), (Q.weight k p) ^ N) = Q.coeff N k := rfl
  calc (P.coeff N j * Q.coeff N k)
      = (∑ q : Fin (P.copies j), (P.weight j q) ^ N) *
          (∑ p : Fin (Q.copies k), (Q.weight k p) ^ N) := by
        rw [hPc, hQc]
    _ = ∑ pq : Fin (P.copies j) × Fin (Q.copies k),
            (P.weight j pq.1 * Q.weight k pq.2) ^ N := hProd.symm
    _ = ∑ s : Fin r, (μ s) ^ N := hSum.symm

/-- For a basis block $j_0$ of a BNT canonical form satisfying `IsBNTCanonicalForm`, the
overlap $\langle V^{(N)}(\text{toTensor})|V^{(N)}(\text{basis}_{j_0})\rangle$
differs from the sector coefficient $P.\mathrm{coeff}(N,j_0)$ by a sequence
tending to zero: the diagonal "self-overlap $-\,1$" and the off-diagonal
$P$-cross summands both vanish under the basis self-overlap normalization
and the cross-decay lemma. -/
private lemma mpvOverlap_total_basis_diff_tendsto_zero
    {P : SectorDecomposition d} (hP : IsBNTCanonicalForm P)
    (j₀ : Fin P.basisCount) :
    Tendsto
      (fun N : ℕ =>
        mpvOverlap (d := d) P.toTensor (P.basis j₀) N - P.coeff N j₀)
      atTop (𝓝 0) := by
  classical
  have hP_weight_le := hP.weight_norm_le_one
  -- Diagonal: P.coeff j₀ · (overlap(P_j₀, P_j₀) - 1) → 0.
  have hSelfMinusOne :
      Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)
        atTop (𝓝 0) := by
    have := (hP.basis_normalized_self_overlap j₀).sub_const (1 : ℂ)
    simpa using this
  have hDiagTermZero :
      Tendsto (fun N : ℕ =>
          P.coeff N j₀ *
            (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1))
        atTop (𝓝 0) := by
    have hBound :
        Tendsto (fun N : ℕ =>
            (P.copies j₀ : ℝ) *
            ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖)
          atTop (𝓝 0) := by
      have := hSelfMinusOne.norm.const_mul ((P.copies j₀ : ℝ))
      simpa using this
    refine squeeze_zero_norm (fun N => ?_) hBound
    have hC :=
      P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j₀)
        (hWeightLe := hP_weight_le j₀)
    calc
      ‖P.coeff N j₀ *
          (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)‖
          = ‖P.coeff N j₀‖ *
            ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖ :=
          norm_mul _ _
      _ ≤ (P.copies j₀ : ℝ) *
            ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖ :=
          mul_le_mul_of_nonneg_right hC (norm_nonneg _)
  -- Off-diagonal: ∑_{j ≠ j₀} P.coeff · overlap(P_j, P_j₀) → 0.
  have hCrossEach :
      ∀ j : Fin P.basisCount, j ≠ j₀ →
        Tendsto (fun N : ℕ =>
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
          atTop (𝓝 0) := by
    intro j hj
    have hOverlap :
        Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j) (P.basis j₀) N) atTop (𝓝 0) :=
      hP.cross_overlap_basis_tendsto_zero hj
    have hBound :
        Tendsto (fun N : ℕ =>
            (P.copies j : ℝ) *
            ‖mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖)
          atTop (𝓝 0) := by
      have := hOverlap.norm.const_mul ((P.copies j : ℝ))
      simpa using this
    refine squeeze_zero_norm (fun N => ?_) hBound
    have hC :=
      P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j)
        (hWeightLe := hP_weight_le j)
    calc
      ‖P.coeff N j * mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖
          = ‖P.coeff N j‖ *
            ‖mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖ := norm_mul _ _
      _ ≤ (P.copies j : ℝ) *
            ‖mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖ :=
          mul_le_mul_of_nonneg_right hC (norm_nonneg _)
  have hCrossSum :
      Tendsto (fun N : ℕ =>
          ∑ j ∈ (Finset.univ : Finset (Fin P.basisCount)).erase j₀,
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
        atTop (𝓝 0) := by
    have := tendsto_finset_sum
      ((Finset.univ : Finset (Fin P.basisCount)).erase j₀)
      (fun (j : Fin P.basisCount) hj =>
        hCrossEach j (Finset.ne_of_mem_erase hj))
    simpa using this
  -- Combine: the full overlap minus the coefficient equals the diag + off-diag.
  have hCombined :
      Tendsto (fun N : ℕ =>
          P.coeff N j₀ *
            (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)
          + ∑ j ∈ (Finset.univ : Finset (Fin P.basisCount)).erase j₀,
              P.coeff N j *
                mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
        atTop (𝓝 0) := by
    have h := hDiagTermZero.add hCrossSum
    simpa using h
  refine hCombined.congr ?_
  intro N
  -- Algebraic identity: ∑_j P.coeff · o(j, j₀) - P.coeff j₀
  --   = P.coeff j₀ · (o(j₀, j₀) - 1) + ∑_{j ≠ j₀} P.coeff · o(j, j₀).
  have hOverlapExpand :
      mpvOverlap (d := d) P.toTensor (P.basis j₀) N
        = ∑ j : Fin P.basisCount,
            P.coeff N j *
              mpvOverlap (d := d) (P.basis j) (P.basis j₀) N :=
    mpvOverlap_eq_sum_of_decomp_left (d := d) (g := P.basisCount)
      (dim := P.basisDim) (A_total := P.toTensor) (A := P.basis)
      (N := N) (c := fun j => P.coeff N j)
      (hdecomp := fun σ => P.mpv_toTensor_eq_sum_coeff (N := N) σ)
      (B := P.basis j₀)
  have hSplit :
      (∑ j : Fin P.basisCount,
          P.coeff N j *
            mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
        = P.coeff N j₀ *
            mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N
          + ∑ j ∈ (Finset.univ : Finset (Fin P.basisCount)).erase j₀,
              P.coeff N j *
                mpvOverlap (d := d) (P.basis j) (P.basis j₀) N := by
    rw [← Finset.add_sum_erase
      (Finset.univ : Finset (Fin P.basisCount))
      (fun j => P.coeff N j *
        mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
      (Finset.mem_univ j₀)]
  rw [hOverlapExpand, hSplit]
  ring

/-- The AM–GM inequality
$|x\bar y| \le \tfrac{1}{2}(|x|^2+|y|^2)$ applied to each configuration $\sigma$
gives the bound
$\|\langle V^{(N)}(A)|V^{(N)}(B)\rangle\| \le
  \tfrac{1}{2}(\|\langle V^{(N)}(A)|V^{(N)}(A)\rangle\|
  + \|\langle V^{(N)}(B)|V^{(N)}(B)\rangle\|)$,
which is eventually $\le 2$ for basis blocks with self-overlaps converging
to $1$. -/
private lemma norm_mpvOverlap_le_self_arith_mean
    {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) (N : ℕ) :
    ‖mpvOverlap (d := d) A B N‖ ≤
      (‖mpvOverlap (d := d) A A N‖ + ‖mpvOverlap (d := d) B B N‖) / 2 := by
  classical
  -- Bound by the triangle inequality + AM–GM on each `σ`.
  have hTri :
      ‖mpvOverlap (d := d) A B N‖
        ≤ ∑ σ : Cfg d N, ‖mpv A σ * star (mpv B σ)‖ := by
    unfold mpvOverlap
    exact norm_sum_le _ _
  have hSplit :
      ∀ σ : Cfg d N,
        ‖mpv A σ * star (mpv B σ)‖
          ≤ (‖mpv A σ‖ ^ 2 + ‖mpv B σ‖ ^ 2) / 2 := by
    intro σ
    rw [norm_mul, norm_star]
    -- AM–GM: 2|x||y| ≤ |x|² + |y|².
    have h := sq_nonneg (‖mpv A σ‖ - ‖mpv B σ‖)
    nlinarith [sq_nonneg (‖mpv A σ‖ - ‖mpv B σ‖), sq_nonneg (‖mpv A σ‖),
      sq_nonneg (‖mpv B σ‖), norm_nonneg (mpv A σ), norm_nonneg (mpv B σ)]
  have hSumSplit :
      (∑ σ : Cfg d N, ‖mpv A σ * star (mpv B σ)‖)
        ≤ ∑ σ : Cfg d N, (‖mpv A σ‖ ^ 2 + ‖mpv B σ‖ ^ 2) / 2 :=
    Finset.sum_le_sum (fun σ _ => hSplit σ)
  have selfEq : ∀ (z : ℂ), z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq]
  have hSelfA :
      (∑ σ : Cfg d N, ‖mpv A σ‖ ^ 2)
        = ‖mpvOverlap (d := d) A A N‖ := by
    have hAux :
        (∑ σ : Cfg d N, mpv A σ * star (mpv A σ))
          = (((∑ σ : Cfg d N, ‖mpv A σ‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl ?_
      intro σ _
      have := selfEq (mpv A σ); push_cast at this ⊢; exact this
    have hSumNN : (0 : ℝ) ≤ ∑ σ : Cfg d N, ‖mpv A σ‖ ^ 2 :=
      Finset.sum_nonneg (fun σ _ => sq_nonneg _)
    unfold mpvOverlap
    rw [hAux]
    rw [show ‖((∑ σ : Cfg d N, ‖mpv A σ‖ ^ 2 : ℝ) : ℂ)‖
            = |(∑ σ : Cfg d N, ‖mpv A σ‖ ^ 2 : ℝ)| from Complex.norm_real _]
    exact (abs_of_nonneg hSumNN).symm
  have hSelfB :
      (∑ σ : Cfg d N, ‖mpv B σ‖ ^ 2)
        = ‖mpvOverlap (d := d) B B N‖ := by
    have hAux :
        (∑ σ : Cfg d N, mpv B σ * star (mpv B σ))
          = (((∑ σ : Cfg d N, ‖mpv B σ‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl ?_
      intro σ _
      have := selfEq (mpv B σ); push_cast at this ⊢; exact this
    have hSumNN : (0 : ℝ) ≤ ∑ σ : Cfg d N, ‖mpv B σ‖ ^ 2 :=
      Finset.sum_nonneg (fun σ _ => sq_nonneg _)
    unfold mpvOverlap
    rw [hAux]
    rw [show ‖((∑ σ : Cfg d N, ‖mpv B σ‖ ^ 2 : ℝ) : ℂ)‖
            = |(∑ σ : Cfg d N, ‖mpv B σ‖ ^ 2 : ℝ)| from Complex.norm_real _]
    exact (abs_of_nonneg hSumNN).symm
  have hRewrite :
      (∑ σ : Cfg d N, (‖mpv A σ‖ ^ 2 + ‖mpv B σ‖ ^ 2) / 2)
        = ((∑ σ : Cfg d N, ‖mpv A σ‖ ^ 2)
            + ∑ σ : Cfg d N, ‖mpv B σ‖ ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_div]
  rw [hRewrite, hSelfA, hSelfB] at hSumSplit
  linarith [hTri, hSumSplit]

/-- **Per-block proportional matching at a $Q$-sector $k_0$.**  Under
eventual nonzero proportionality and unit-modulus copy weights at $Q$-sector
$k_0$ and auxiliary $P$-sector $j_0$, some $P$-block $j_1$ has matched bond
dimension, cast-compatible gauge-phase equivalence, and non-decaying
cross-overlap with $Q.\mathrm{basis}\,k_0$.  Paper anchor: CPSV16 §II.C
lines 349–352, 1167–1170, 1182–1188. -/
theorem exists_block_match_at_Q_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (k₀ : Fin Q.basisCount)
    (hUnitQ_at_k₀ : ∃ q : Fin (Q.copies k₀), ‖Q.weight k₀ q‖ = 1)
    (j₀ : Fin P.basisCount)
    (hUnitP_at_j₀ : ∃ q : Fin (P.copies j₀), ‖P.weight j₀ q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ j₁ : Fin P.basisCount,
      ∃ h : P.basisDim j₁ = Q.basisDim k₀,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis j₁))
            (Q.basis k₀) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j₁) (Q.basis k₀) N)
          atTop (𝓝 0) := by
  classical
  have hP_weight_le := hP.weight_norm_le_one
  have hQ_weight_le := hQ.weight_norm_le_one
  -- Joint Cesàro non-decay of `P.coeff N j₀ * Q.coeff N k₀`.
  have hJointNonDecay :
      ¬ Tendsto (fun N : ℕ => P.coeff N j₀ * Q.coeff N k₀) atTop (𝓝 0) :=
    joint_coeff_not_tendsto_zero (P := P) (Q := Q) j₀ k₀
      hUnitP_at_j₀ hUnitQ_at_k₀ (hP_weight_le j₀) (hQ_weight_le k₀)
  -- Step 1: extract some `j₁` with non-decaying cross-overlap to `Q.basis k₀`.
  suffices hExists_j :
      ∃ j₁ : Fin P.basisCount,
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j₁) (Q.basis k₀) N) atTop (𝓝 0) by
    -- Step 2: dimension equality + gauge-phase from the chosen `j₁`.
    obtain ⟨j₁, hj₁⟩ := hExists_j
    haveI hj₁dim : NeZero (P.basisDim j₁) := ⟨(hP.basis_dim_pos j₁).ne'⟩
    haveI hk₀dim : NeZero (Q.basisDim k₀) := ⟨(hQ.basis_dim_pos k₀).ne'⟩
    have hDim : P.basisDim j₁ = Q.basisDim k₀ := by
      by_contra hne
      exact hj₁ <|
        mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
          (P.basis j₁) (Q.basis k₀)
          (hP.basis_irreducible j₁) (hQ.basis_irreducible k₀)
          (hP.basis_left_canonical j₁) (hQ.basis_left_canonical k₀) hne
    have hGPE :
        GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) hDim) (P.basis j₁)) (Q.basis k₀) := by
      by_contra hNot
      exact hj₁ <|
        mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
          (hdim := hDim) (A := P.basis j₁) (B := Q.basis k₀)
          (hA_irr := hP.basis_irreducible j₁)
          (hB_irr := hQ.basis_irreducible k₀)
          (hA_norm := hP.basis_left_canonical j₁)
          (hB_norm := hQ.basis_left_canonical k₀)
          (hNot := hNot)
    exact ⟨j₁, hDim, hGPE, hj₁⟩
  -- Establish Step 1 by contradiction.
  by_contra hAll
  push Not at hAll
  -- `hAll : ∀ j, Tendsto (mpvOverlap (P.basis j) (Q.basis k₀)) atTop (𝓝 0)`.
  -- Eventually proportional projection identity (dual projection eliminates `c_N`):
  --   mpvOverlap P (Q_k₀) · mpvOverlap Q (P_j₀)
  --     = mpvOverlap P (P_j₀) · mpvOverlap Q (Q_k₀).
  have hCrossId :
      ∀ᶠ N in atTop,
        mpvOverlap (d := d) P.toTensor (Q.basis k₀) N *
            mpvOverlap (d := d) Q.toTensor (P.basis j₀) N
          = mpvOverlap (d := d) P.toTensor (P.basis j₀) N *
              mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N := by
    refine hProp.mono ?_
    intro N hN
    rcases hN with ⟨c, _hc_ne, hEq⟩
    have h1 : mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
            = c * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N :=
      mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
        (A := P.toTensor) (B := Q.toTensor) (c := c) hEq (Q.basis k₀)
    have h2 : mpvOverlap (d := d) P.toTensor (P.basis j₀) N
            = c * mpvOverlap (d := d) Q.toTensor (P.basis j₀) N :=
      mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
        (A := P.toTensor) (B := Q.toTensor) (c := c) hEq (P.basis j₀)
    rw [h1, h2]; ring
  -- Step 2: `mpvOverlap P (Q_k₀)` tends to zero (each summand vanishes).
  have hOverlapPQ_zero :
      Tendsto (fun N : ℕ => mpvOverlap (d := d) P.toTensor (Q.basis k₀) N)
        atTop (𝓝 0) := by
    have hExpand : ∀ N : ℕ,
        mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
          = ∑ j : Fin P.basisCount,
              P.coeff N j *
                mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N := by
      intro N
      exact mpvOverlap_eq_sum_of_decomp_left (d := d) (g := P.basisCount)
        (dim := P.basisDim) (A_total := P.toTensor) (A := P.basis)
        (N := N) (c := fun j => P.coeff N j)
        (hdecomp := fun σ => P.mpv_toTensor_eq_sum_coeff (N := N) σ)
        (B := Q.basis k₀)
    have hEach : ∀ j : Fin P.basisCount,
        Tendsto (fun N : ℕ =>
            P.coeff N j *
              mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
          atTop (𝓝 0) := by
      intro j
      have hOverlap := hAll j
      have hBound :
          Tendsto (fun N : ℕ =>
              (P.copies j : ℝ) *
              ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖)
            atTop (𝓝 0) := by
        have := hOverlap.norm.const_mul ((P.copies j : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBound
      have hC :=
        P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j)
          (hWeightLe := hP_weight_le j)
      calc
        ‖P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖
            = ‖P.coeff N j‖ *
              ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖ :=
            norm_mul _ _
        _ ≤ (P.copies j : ℝ) *
              ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖ :=
            mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    have hSum :
        Tendsto (fun N : ℕ =>
            ∑ j : Fin P.basisCount,
              P.coeff N j *
                mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
          atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin P.basisCount))
        (fun (j : Fin P.basisCount) _ => hEach j)
      simpa using this
    refine hSum.congr ?_
    intro N
    exact (hExpand N).symm
  -- Step 3: basis self-overlaps eventually ≤ 3/2, then AM–GM bounds cross
  -- overlaps `(Q.basis k, P.basis j₀)` by 3/2 eventually.
  have hEvSelfBoundP : ∀ j : Fin P.basisCount,
      ∀ᶠ N in atTop,
        ‖mpvOverlap (d := d) (P.basis j) (P.basis j) N‖ ≤ (3 : ℝ) / 2 := by
    intro j
    have h := ((hP.basis_normalized_self_overlap j).norm).eventually_lt_const
      (show ‖(1 : ℂ)‖ < 3/2 by simp; norm_num)
    filter_upwards [h] with N hN using le_of_lt hN
  have hEvSelfBoundQ : ∀ k : Fin Q.basisCount,
      ∀ᶠ N in atTop,
        ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k) N‖ ≤ (3 : ℝ) / 2 := by
    intro k
    have h := ((hQ.basis_normalized_self_overlap k).norm).eventually_lt_const
      (show ‖(1 : ℂ)‖ < 3/2 by simp; norm_num)
    filter_upwards [h] with N hN using le_of_lt hN
  -- AM–GM bound for `(Q.basis k, P.basis j₀)` cross overlap.
  have hQbasis_Pj₀_bound : ∀ k : Fin Q.basisCount,
      ∀ᶠ N in atTop,
        ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖ ≤ (3 : ℝ) / 2 := by
    intro k
    filter_upwards [hEvSelfBoundQ k, hEvSelfBoundP j₀] with N hQ_self hP_self
    calc ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖
        ≤ (‖mpvOverlap (d := d) (Q.basis k) (Q.basis k) N‖ +
            ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N‖) / 2 :=
          norm_mpvOverlap_le_self_arith_mean (Q.basis k) (P.basis j₀) N
      _ ≤ ((3 : ℝ) / 2 + (3 : ℝ) / 2) / 2 := by linarith
      _ = (3 : ℝ) / 2 := by norm_num
  -- Step 4: `mpvOverlap Q (P_j₀) N` is bounded under by a constant eventually.
  set M_Q : ℝ := ∑ k : Fin Q.basisCount, (Q.copies k : ℝ) * (3 / 2) with hMQ_def
  have hOverlapQPj₀_bound :
      ∀ᶠ N in atTop,
        ‖mpvOverlap (d := d) Q.toTensor (P.basis j₀) N‖ ≤ M_Q := by
    -- Expand and bound each summand.
    have hExpand : ∀ N : ℕ,
        mpvOverlap (d := d) Q.toTensor (P.basis j₀) N
          = ∑ k : Fin Q.basisCount,
              Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N := by
      intro N
      exact mpvOverlap_eq_sum_of_decomp_left (d := d) (g := Q.basisCount)
        (dim := Q.basisDim) (A_total := Q.toTensor) (A := Q.basis)
        (N := N) (c := fun k => Q.coeff N k)
        (hdecomp := fun σ => Q.mpv_toTensor_eq_sum_coeff (N := N) σ)
        (B := P.basis j₀)
    have hAllBound :
        ∀ᶠ N in atTop, ∀ k : Fin Q.basisCount,
          ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖ ≤ (3 : ℝ) / 2 := by
      rw [Filter.eventually_all]
      exact hQbasis_Pj₀_bound
    filter_upwards [hAllBound] with N hN
    rw [hExpand]
    calc ‖∑ k : Fin Q.basisCount,
              Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖
        ≤ ∑ k : Fin Q.basisCount,
            ‖Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k : Fin Q.basisCount, (Q.copies k : ℝ) * (3 / 2) := by
          refine Finset.sum_le_sum ?_
          intro k _
          have hC :=
            Q.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := k)
              (hWeightLe := hQ_weight_le k)
          calc ‖Q.coeff N k *
                  mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖
              = ‖Q.coeff N k‖ *
                  ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖ :=
                norm_mul _ _
            _ ≤ (Q.copies k : ℝ) *
                  ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖ :=
                mul_le_mul_of_nonneg_right hC (norm_nonneg _)
            _ ≤ (Q.copies k : ℝ) * (3 / 2) := by
                apply mul_le_mul_of_nonneg_left (hN k) (by positivity)
      _ = M_Q := rfl
  -- Step 5: LHS = mpvOverlap P (Q_k₀) · mpvOverlap Q (P_j₀) → 0.
  have hLHS_tendsto_zero :
      Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) P.toTensor (Q.basis k₀) N *
            mpvOverlap (d := d) Q.toTensor (P.basis j₀) N)
        atTop (𝓝 0) := by
    refine Filter.Tendsto.zero_mul_isBoundedUnder_le hOverlapPQ_zero ?_
    refine ⟨M_Q, ?_⟩
    rw [Filter.eventually_map]
    exact hOverlapQPj₀_bound
  -- Step 6: `mpvOverlap P (P_j₀) - P.coeff j₀ → 0` and same for Q-side.
  have hOverlapPP_diff :
      Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) P.toTensor (P.basis j₀) N - P.coeff N j₀)
        atTop (𝓝 0) :=
    mpvOverlap_total_basis_diff_tendsto_zero hP j₀
  have hOverlapQQ_diff :
      Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N - Q.coeff N k₀)
        atTop (𝓝 0) :=
    mpvOverlap_total_basis_diff_tendsto_zero hQ k₀
  -- Step 7: RHS - P.coeff j₀ · Q.coeff k₀ → 0 via the algebraic identity
  -- a·b - α·β = (a - α)·b + α·(b - β) with (a - α) → 0, b bounded,
  -- α bounded, (b - β) → 0.
  have hOverlapQQ_bounded : ∀ᶠ N in atTop,
      ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ ≤
        ‖Q.coeff N k₀‖ + 1 := by
    have hSmall :
        Tendsto (fun N : ℕ =>
            ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N - Q.coeff N k₀‖)
          atTop (𝓝 0) := by
      have := hOverlapQQ_diff.norm
      simpa using this
    have hEv1 := hSmall.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [hEv1] with N hN
    calc ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖
        = ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N - Q.coeff N k₀ +
            Q.coeff N k₀‖ := by ring_nf
      _ ≤ ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N - Q.coeff N k₀‖
          + ‖Q.coeff N k₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖Q.coeff N k₀‖ := by linarith [le_of_lt hN]
      _ = ‖Q.coeff N k₀‖ + 1 := by ring
  -- The RHS minus the target product tends to zero.
  have hRHS_diff :
      Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) P.toTensor (P.basis j₀) N *
              mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
            - P.coeff N j₀ * Q.coeff N k₀)
        atTop (𝓝 0) := by
    -- Decompose: a·b - α·β = (a - α)·b + α·(b - β).
    have hRewrite : ∀ N : ℕ,
        mpvOverlap (d := d) P.toTensor (P.basis j₀) N *
            mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
          - P.coeff N j₀ * Q.coeff N k₀
        = (mpvOverlap (d := d) P.toTensor (P.basis j₀) N - P.coeff N j₀) *
            mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
          + P.coeff N j₀ *
            (mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N - Q.coeff N k₀) := by
      intro N; ring
    -- The first summand → 0 via `hOverlapPP_diff` (→ 0) and `‖Q-side‖` bounded.
    have hT1 :
        Tendsto (fun N : ℕ =>
            (mpvOverlap (d := d) P.toTensor (P.basis j₀) N - P.coeff N j₀) *
              mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
          atTop (𝓝 0) := by
      refine Filter.Tendsto.zero_mul_isBoundedUnder_le hOverlapPP_diff ?_
      -- Q-side overlap bounded by `Q.copies k₀ + 1` eventually (the
      -- bounded-coefficient version of `hOverlapQQ_bounded`, with the
      -- constant `‖Q.coeff k₀‖` further bounded by `Q.copies k₀`).
      refine ⟨((Q.copies k₀ : ℝ)) + 1, ?_⟩
      rw [Filter.eventually_map]
      filter_upwards [hOverlapQQ_bounded] with N hN
      have hCb :
          ‖Q.coeff N k₀‖ ≤ (Q.copies k₀ : ℝ) :=
        Q.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := k₀)
          (hWeightLe := hQ_weight_le k₀)
      simp only [Function.comp_apply]
      linarith
    -- The second summand → 0 via `hOverlapQQ_diff` (→ 0) and `P.coeff j₀` bounded.
    have hT2 :
        Tendsto (fun N : ℕ =>
            P.coeff N j₀ *
              (mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N - Q.coeff N k₀))
          atTop (𝓝 0) := by
      refine Filter.isBoundedUnder_le_mul_tendsto_zero ?_ hOverlapQQ_diff
      refine ⟨((P.copies j₀ : ℝ)), ?_⟩
      rw [Filter.eventually_map]
      refine Filter.Eventually.of_forall (fun N => ?_)
      exact P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j₀)
        (hWeightLe := hP_weight_le j₀)
    have hSum := hT1.add hT2
    have hSum' :
        Tendsto (fun N : ℕ =>
            (mpvOverlap (d := d) P.toTensor (P.basis j₀) N - P.coeff N j₀) *
              mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
            + P.coeff N j₀ *
              (mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N - Q.coeff N k₀))
          atTop (𝓝 0) := by
      simpa using hSum
    refine hSum'.congr ?_
    intro N
    exact (hRewrite N).symm
  -- Step 8: combine LHS → 0 and LHS = RHS eventually to get
  -- RHS → 0, then with hRHS_diff get P.coeff j₀ · Q.coeff k₀ → 0,
  -- contradicting joint Cesàro non-decay.
  have hRHS_zero :
      Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) P.toTensor (P.basis j₀) N *
            mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
        atTop (𝓝 0) := by
    refine hLHS_tendsto_zero.congr' ?_
    refine hCrossId.mono ?_
    intro N hN
    exact hN
  -- The target product = (a · b) - (a · b - α · β).
  have hCoeffProd_zero :
      Tendsto (fun N : ℕ => P.coeff N j₀ * Q.coeff N k₀) atTop (𝓝 0) := by
    have hDiff := hRHS_zero.sub hRHS_diff
    have hDiff' :
        Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) P.toTensor (P.basis j₀) N *
              mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
            - (mpvOverlap (d := d) P.toTensor (P.basis j₀) N *
                mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
              - P.coeff N j₀ * Q.coeff N k₀))
          atTop (𝓝 0) := by
      simpa using hDiff
    refine hDiff'.congr ?_
    intro N
    ring
  exact hJointNonDecay hCoeffProd_zero

/-! ### Full-basis proportional matching (Q → P direction)

For every sector `k` of `Q`, there exists a sector `j` of `P` of equal
bond dimension, gauge-phase equivalent in the cast-compatible shape, and
with non-decaying cross-overlap.  This is the proportional analogue of
`StrongMatch.forall_k_exists_j_nondecaying_overlap_of_sameMPV`.

Paper anchor: CPSV16 §II.C lines 349–352 / 1167–1170 / 1182–1188. -/
theorem forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∀ k : Fin Q.basisCount,
      ∃ (j : Fin P.basisCount) (h : P.basisDim j = Q.basisDim k),
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis j))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
          atTop (𝓝 0) := by
  classical
  intro k
  obtain ⟨j_w, q_w, hq_w⟩ := hP.weight_unit_exists
  obtain ⟨j₁, hDim, hGE, hNonDecay⟩ :=
    exists_block_match_at_Q_of_eventuallyProportional
      hP hQ k (hUnitQ k) j_w ⟨q_w, hq_w⟩ hProp
  exact ⟨j₁, hDim, hGE, hNonDecay⟩

/-! ### Bijective matching from per-block existentials in both directions

The bijection construction composes two gauge-phase equivalences through a
common centre.  The cast-aware symmetry and transitivity lemmas
(`gaugePhaseEquiv_symm_same_dim`, `gaugePhaseEquiv_swap_cast`,
`gaugePhaseEquiv_trans_same_dim`, `gaugePhaseEquiv_cast_compose_via_centre`)
are shared with the equal-MPV variant in
`PaperBNT/StrongMatch.lean`. -/

/-- **Bijective proportional matching.**

Applying the per-block matching in both the $Q \to P$ and $P \to Q$
directions gives two injective maps; finite cardinality comparison turns
the forward one into an equivalence $\beta : \{1,\dots,g_Q\} \to
\{1,\dots,g_P\}$, carrying the matched bond-dimension equality,
gauge-phase equivalence, and non-decaying overlap for every sector of $Q$.

Paper anchor: CPSV16 §II.C lines 1184–1186, the symmetry step
"$g_A \ge g_B$ and $g_B \ge g_A$". -/
theorem bijective_match_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ β : Fin Q.basisCount ≃ Fin P.basisCount,
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (β k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (β k)) (Q.basis k) N)
          atTop (𝓝 0) := by
  classical
  have hFwd :=
    forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional
      hP hQ hUnitQ hProp
  have hProp_symm : EventuallyNonzeroProportionalMPV₂ Q.toTensor P.toTensor :=
    hProp.symm
  have hBwd :=
    forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional
      hQ hP hUnitP hProp_symm
  let φ₀ : Fin Q.basisCount → Fin P.basisCount := fun k => (hFwd k).choose
  have φ₀_spec : ∀ k : Fin Q.basisCount,
      ∃ h : P.basisDim (φ₀ k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (φ₀ k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (φ₀ k)) (Q.basis k) N)
          atTop (𝓝 0) := fun k => (hFwd k).choose_spec
  have rebase_centre_P :
      ∀ (j j' : Fin P.basisCount) (_hj : j = j')
        {kv : Fin Q.basisCount}
        (h_t : P.basisDim j' = Q.basisDim kv)
        (_GE : GaugePhaseEquiv
                  (cast (congr_arg (MPSTensor d) h_t) (P.basis j'))
                  (Q.basis kv)),
        ∃ h_t' : P.basisDim j = Q.basisDim kv,
          GaugePhaseEquiv
              (cast (congr_arg (MPSTensor d) h_t') (P.basis j))
              (Q.basis kv) := by
    rintro _ _ rfl _ h_t GE
    exact ⟨h_t, GE⟩
  have hφ₀_inj : Function.Injective φ₀ := by
    intro k₁ k₂ hjEq
    obtain ⟨h₁, GE₁, _⟩ := φ₀_spec k₁
    obtain ⟨h₂, GE₂, _⟩ := φ₀_spec k₂
    by_contra hne
    obtain ⟨h₂', GE₂'⟩ :=
      rebase_centre_P (φ₀ k₁) (φ₀ k₂) hjEq h₂ GE₂
    have hQdim : Q.basisDim k₁ = Q.basisDim k₂ := h₁.symm.trans h₂'
    have hQGE :
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hQdim) (Q.basis k₁))
            (Q.basis k₂) :=
      gaugePhaseEquiv_cast_compose_via_centre
        (A := P.basis (φ₀ k₁))
        (B := Q.basis k₁) (C := Q.basis k₂) h₁ h₂' GE₁ GE₂'
    exact hQ.basis_distinct k₁ k₂ hne hQdim hQGE
  let ψ₀ : Fin P.basisCount → Fin Q.basisCount := fun j => (hBwd j).choose
  have ψ₀_spec : ∀ j : Fin P.basisCount,
      ∃ h : Q.basisDim (ψ₀ j) = P.basisDim j,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (Q.basis (ψ₀ j)))
            (P.basis j) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (Q.basis (ψ₀ j)) (P.basis j) N)
          atTop (𝓝 0) := fun j => (hBwd j).choose_spec
  have rebase_centre_Q :
      ∀ (k k' : Fin Q.basisCount) (_hk : k = k')
        {jv : Fin P.basisCount}
        (h_t : Q.basisDim k' = P.basisDim jv)
        (_GE : GaugePhaseEquiv
                  (cast (congr_arg (MPSTensor d) h_t) (Q.basis k'))
                  (P.basis jv)),
        ∃ h_t' : Q.basisDim k = P.basisDim jv,
          GaugePhaseEquiv
              (cast (congr_arg (MPSTensor d) h_t') (Q.basis k))
              (P.basis jv) := by
    rintro _ _ rfl _ h_t GE
    exact ⟨h_t, GE⟩
  have hψ₀_inj : Function.Injective ψ₀ := by
    intro j₁ j₂ hkEq
    obtain ⟨h₁, GE₁, _⟩ := ψ₀_spec j₁
    obtain ⟨h₂, GE₂, _⟩ := ψ₀_spec j₂
    by_contra hne
    obtain ⟨h₂', GE₂'⟩ :=
      rebase_centre_Q (ψ₀ j₁) (ψ₀ j₂) hkEq h₂ GE₂
    have hPdim : P.basisDim j₁ = P.basisDim j₂ := h₁.symm.trans h₂'
    have hPGE :
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hPdim) (P.basis j₁))
            (P.basis j₂) :=
      gaugePhaseEquiv_cast_compose_via_centre
        (A := Q.basis (ψ₀ j₁))
        (B := P.basis j₁) (C := P.basis j₂) h₁ h₂' GE₁ GE₂'
    exact hP.basis_distinct j₁ j₂ hne hPdim hPGE
  have hCardQP :
      Fintype.card (Fin Q.basisCount) ≤ Fintype.card (Fin P.basisCount) :=
    Fintype.card_le_of_injective φ₀ hφ₀_inj
  have hCardPQ :
      Fintype.card (Fin P.basisCount) ≤ Fintype.card (Fin Q.basisCount) :=
    Fintype.card_le_of_injective ψ₀ hψ₀_inj
  have hCard :
      Fintype.card (Fin Q.basisCount) = Fintype.card (Fin P.basisCount) :=
    le_antisymm hCardQP hCardPQ
  have hφ₀_bij : Function.Bijective φ₀ :=
    (Fintype.bijective_iff_injective_and_card φ₀).2 ⟨hφ₀_inj, hCard⟩
  let β : Fin Q.basisCount ≃ Fin P.basisCount := Equiv.ofBijective φ₀ hφ₀_bij
  refine ⟨β, ?_⟩
  intro k
  simpa [β] using φ₀_spec k

/-! ### Final theorem: proportional sector matching with basis-count equality -/

/-- **Proportional sector matching for two BNT canonical forms.**

If two BNT canonical sector decompositions have eventually proportional
assembled tensors with nonzero per-$N$ scalar, and each basis sector on both
sides carries a unit-modulus copy weight, then the basis counts agree and
there is a basis bijection carrying matched bond-dimension equality and
per-block gauge-phase equivalence.

Paper anchor: CPSV16 §II.C lines 349–352 (theorem `thm1`), lines 1167–1170
(theorem statement), lines 1182–1188 (proof); CPSV21 lines 1891–1894
(proportional-MPV theorem-level target).  This is the proportional analogue
of `ft_paper_bnt_equal_mps_gaugeEquiv_witnesses` (`PaperBNT/FundamentalCoord.lean`)
in the matching layer; the global-gauge upgrade further requires the
per-block coefficient identification, which lies in the next module of the
proof chain. -/
theorem ft_paper_bnt_proportional_sector_match
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    P.basisCount = Q.basisCount ∧
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount),
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k) := by
  classical
  obtain ⟨β, hβ⟩ :=
    bijective_match_of_eventuallyProportional hP hQ hUnitP hUnitQ hProp
  refine ⟨?_, β, ?_⟩
  · have hCard := Fintype.card_congr β
    simpa using hCard.symm
  · intro k
    obtain ⟨h, hGE, _⟩ := hβ k
    exact ⟨h, hGE⟩

end MPSTensor
