/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.Lattice.RegionalEntropyBridge
import QICLean.Entropy.BufferDiscount
import QICLean.Analysis.HarmonicWeights
import TNLean.Algebra.TailRadiusWeights

/-!
# Conditional entropy in a buffered rectangle

The integer-clearance specialization of Lemma 3.2 of the area-law manuscript: for a gapped
ground vector of a finite-range lattice Hamiltonian, a cut `A`, a safe rectangle `Q` and a
rectangle `Q₀` of size at most `r` whose
padding `Q₀^{+C_pad r}` lies in `Q`, the region `X = A ∩ Q₀` and its buffer
`T = (A ∩ Q₀^{+C_pad r}) \ X` satisfy `S(X | T) ≤ S(X)/2 + C_buf r`, with `C_pad` and `C_buf`
depending only on `q, R, J, Δ`.

The finite-dimensional argument (optimized filters, stationarity, the energy estimate, the
prefix norm comparison and Schmidt pinning) is `Entropy.two_mul_condEntropy_le` in QICLean.
This module supplies its lattice hypotheses: the nested contours
`X_j = A ∩ Q₀^{+d_j}`, `d_j = r + j D`, `D = R + 1`, the single-split property, the crossing
budgets `≤ C (r + d_j)`, the harmonic weights `a_j = 2/(Z_r (r + d_j))` of total mass two, and
the choice of `C_pad` making `Z_r` large uniformly in `r`.

The full statement for real clearance is proved by
`exists_condEntropy_le_initialBuffer_real` in `InitialBufferReal`.

## Main results

* `condEntropy_le_initialBufferConst`: the integer-clearance specialization at the named
  constants `initialPaddingScale`, `initialPaddingConst` and `initialBufferConst`.
* `exists_condEntropy_le_initialBuffer`: the integer-clearance specialization of
  Lemma 3.2 (`lem:initial-buffer`).

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 3.2 (`lem:initial-buffer`), `02-initial.tex`, lines 240–256, and its proof,
  lines 258–568.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- Shifting the index of a finite sum from `0, …, m-1` to `1, …, m`. -/
theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ j ∈ Finset.range m, f (j + 1) = ∑ j ∈ Finset.Icc 1 m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- The dimension `q^{|X|}` of an admissible support is at most `q^{v_R}`,
`v_R = 1 + 2 R (R + 1)`. -/
theorem supportDim_le {Λ : Finset (ℤ × ℤ)} {q R : ℕ} (hq : 1 ≤ q) (X : AdmissibleSupport Λ R) :
    Entropy.supportDim (fun _ : Site Λ ↦ q) X.1 ≤ q ^ (1 + 2 * R * (R + 1)) := by
  rw [Entropy.supportDim, Finset.prod_const]
  exact Nat.pow_le_pow_right hq (card_support_le_diamond (G := domainGraph Λ) Subtype.val
    Subtype.val_injective (fun _ _ h ↦ latticeL1Distance_le_one_of_adj h) X.1 R X.2.2)

/-- Every admissible support has positive Hilbert-space dimension when the local
dimension is positive. -/
theorem one_le_supportDim {Λ : Finset (ℤ × ℤ)} {q R : ℕ} (hq : 1 ≤ q)
    (X : AdmissibleSupport Λ R) : 1 ≤ Entropy.supportDim (fun _ : Site Λ ↦ q) X.1 := by
  rw [Entropy.supportDim, Finset.prod_const]
  exact Nat.one_le_pow _ _ hq

/-- The cut parameter of Lemma 3.1 grows at most linearly with the number of crossing
supports: `ℬ ≤ 1 + |𝒞| log² (e q^{v_R})`. -/
theorem cutLogBudget_le_card {Λ : Finset (ℤ × ℤ)} {q R : ℕ} (hq : 1 ≤ q)
    (Cr : Finset (AdmissibleSupport Λ R)) :
    Entropy.cutLogBudget Cr (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ fun X ↦ X.1) ≤
      1 + Cr.card * Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2 := by
  have hbound : ∀ X ∈ Cr,
      Real.log (Real.exp 1 * ((Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ fun X ↦ X.1) X : ℝ)) ^ 2
        ≤ Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2 := by
    intro X _
    have h1 : (1 : ℝ) ≤ Entropy.supportDim (fun _ : Site Λ ↦ q) X.1 := by
      exact_mod_cast one_le_supportDim hq X
    have h2 : (Entropy.supportDim (fun _ : Site Λ ↦ q) X.1 : ℝ) ≤
        (q : ℝ) ^ (1 + 2 * R * (R + 1)) := by
      exact_mod_cast supportDim_le hq X
    have he : 1 ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hl : 0 ≤ Real.log (Real.exp 1 * Entropy.supportDim (fun _ : Site Λ ↦ q) X.1) :=
      Real.log_nonneg (by nlinarith)
    simp only [Function.comp_apply]
    have := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le)
    exact pow_le_pow_left₀ hl this 2
  have hsum := Finset.sum_le_card_nsmul Cr _ _ hbound
  rw [nsmul_eq_mul] at hsum
  rw [Entropy.cutLogBudget]
  linarith

/-- The constant `8 (R + 1) μ_R` of the crossing count, `μ_R = 2^{v_R - 1}`. -/
noncomputable def bufferCrossConst (R : ℕ) : ℝ :=
  8 * (R + 1) * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)

/-- The constant `K' = 1 + K log² (e q^{v_R})` bounding `ℬ_j ≤ K' (r + d_j)`. -/
noncomputable def bufferBudgetConst (q R : ℕ) : ℝ :=
  1 + bufferCrossConst R * Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2

/-- The coefficient in the contour crossing bound is nonnegative. -/
theorem bufferCrossConst_nonneg (R : ℕ) : 0 ≤ bufferCrossConst R := by
  unfold bufferCrossConst; positivity

/-- The contour logarithmic budget coefficient is at least one. -/
theorem one_le_bufferBudgetConst (q R : ℕ) : 1 ≤ bufferBudgetConst q R := by
  unfold bufferBudgetConst
  have := mul_nonneg (bufferCrossConst_nonneg R)
    (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1)))))
  linarith

/-! ### The discount at fixed constants -/

/-- **Lemma 3.2 at explicit constants.** Let `Zmin ≥ 4` dominate the energy and tail
thresholds, and let the padding `C_pad > R + 2` satisfy `(R + 3) e^{(R+1) Zmin} ≤ C_pad + 1`.
Then for a gapped ground vector, a safe rectangle `Q` with `R < D₀`, `r ≥ 1` and
`Q₀^{+C_pad r} ⊆ Q` with `size Q₀ ≤ r`,
`S(X | T) ≤ S(X)/2 + (1024 e (J/Δ) K' + C_pad) r / 2`. The contours are `d_j = r + (j+1)(R+1)`,
`0 ≤ j < m`, with `m = ⌊(C_pad - 1) r/(R + 1)⌋`. Source: `02-initial.tex`, lines 258–568. -/
theorem condEntropy_le_initialBuffer_of_constants {q R : ℕ} (hq : 1 ≤ q) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) {Zmin : ℝ} (hZ4 : 4 ≤ Zmin)
    (hZE : 32 * bufferCrossConst R * (q : ℝ) ^ (2 * (1 + 2 * R * (R + 1))) * J / Δ ≤ Zmin)
    (hZT : 128 * Real.sqrt ((1 + J / Δ) * bufferBudgetConst q R) ≤ Zmin) {Cpad : ℕ}
    (hCR : R + 2 < Cpad)
    (hCZ : (2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin) ≤ Cpad + 1)
    {D₀ : ℕ} (hRD₀ : R < D₀) {Λ : Finset (ℤ × ℤ)} (h : LocalHamiltonian Λ q R J) {E₀ : ℝ}
    {Ω : StateSpace Λ q} (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ)
    {A : Finset (Site Λ)} {Q : IntRect} (hsafe : IsSafe Λ A D₀ Q) {r : ℕ} (hr : 1 ≤ r)
    {Q₀ : IntRect} (hQ₀ : Q₀.size ≤ r) (hpad : (Q₀.dilate (Cpad * r)).toFinset ⊆ Q.toFinset) :
    regionalEntropy Λ q Ω (rectRegion A Q₀ ∪
        (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀)) -
      regionalEntropy Λ q Ω (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀) ≤
    regionalEntropy Λ q Ω (rectRegion A Q₀) / 2 +
      (1024 * Real.exp 1 * (J / Δ) * bufferBudgetConst q R + Cpad) / 2 * r := by
  classical
  obtain ⟨hΩ, heig, hgap⟩ := hgs
  replace heig : toEuclideanLin h.operator Ω = (E₀ : ℂ) • Ω := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin]; exact heig
  set K := bufferCrossConst R
  set K' := bufferBudgetConst q R
  set v : ℕ := 1 + 2 * R * (R + 1)
  have hK : 0 ≤ K := bufferCrossConst_nonneg R
  have hK' : 1 ≤ K' := one_le_bufferBudgetConst q R
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  -- the contours
  set D : ℕ := R + 1 with hDdef
  set m : ℕ := (Cpad - 1) * r / D
  set d : ℕ → ℕ := fun j ↦ r + (j + 1) * D
  set c : ℕ → ℝ := fun j ↦ 2 * r + (j + 1) * D
  set X : Finset (Site Λ) := rectRegion A Q₀
  set T : ℕ → Finset (Site Λ) := fun j ↦
    if j < m then rectRegion A (Q₀.dilate (d j)) \ X else Finset.univ \ X
  set Tbuf : Finset (Site Λ) := rectRegion A (Q₀.dilate (Cpad * r)) \ X
  have hD : 0 < D := Nat.succ_pos R
  have hm1 : 1 ≤ m := by
    refine (Nat.le_div_iff_mul_le hD).mpr ?_
    have : D ≤ Cpad - 1 := by omega
    nlinarith
  have hmD : m * D ≤ (Cpad - 1) * r := Nat.div_mul_le_self _ _
  have hdle : ∀ j < m, d j ≤ Cpad * r := by
    intro j hj
    have : (j + 1) * D ≤ m * D := Nat.mul_le_mul_right _ hj
    have : (Cpad - 1) * r + r = Cpad * r := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    simp only [d]; omega
  have hc : ∀ j, (d j : ℝ) + r = c j := fun j ↦ by simp only [d, c]; push_cast; ring
  have hc1 : ∀ j, (1 : ℝ) ≤ c j := fun j ↦ by
    simp only [c]
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ (j + 1) * D := by positivity
    linarith
  have hcpos : ∀ j, 0 < c j := fun j ↦ lt_of_lt_of_le one_pos (hc1 j)
  have hXd : ∀ j, X ⊆ rectRegion A (Q₀.dilate (d j)) := fun j ↦ by
    have := rectRegion_dilate_mono A Q₀ (Nat.zero_le (d j))
    rwa [IntRect.dilate_zero] at this
  have hXT : ∀ j < m, X ∪ T j = rectRegion A (Q₀.dilate (d j)) := fun j hj ↦ by
    simp only [T, hj, ↓reduceIte]
    exact Finset.union_sdiff_of_subset (hXd j)
  have hXT' : ∀ j, m ≤ j → X ∪ T j = Finset.univ := fun j hj ↦ by
    simp only [T, not_lt.mpr hj, ↓reduceIte]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ X)
  -- the harmonic weights
  set Z : ℝ := ∑ i ∈ Finset.range m, 1 / c i
  set a : ℕ → ℝ := Entropy.harmonicWeight (Finset.range m) c
  have hrange : (Finset.range m).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have hZ : Zmin ≤ Z := by
    have hlow := Entropy.log_div_le_sum_inv_contour_of_le (r := r) (D := D) (P := Cpad)
      (by exact_mod_cast hr) (by exact_mod_cast hD) (by exact_mod_cast (by omega : 1 ≤ Cpad))
      (m := m) (by
        have h1 := Nat.lt_mul_div_succ ((Cpad - 1) * r) hD
        have h3 : (((Cpad - 1) * r : ℕ) : ℝ) ≤ D * (m + 1) := by
          exact_mod_cast h1.le
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one] at h3
        linarith)
    have hsum : ∑ j ∈ Finset.Icc 1 m, 1 / (2 * (r : ℝ) + j * D) = Z := by
      rw [← sum_range_succ_eq_sum_Icc (fun j : ℕ ↦ 1 / (2 * (r : ℝ) + j * D))]
      simp only [Z, c]; push_cast; rfl
    rw [hsum] at hlow
    refine le_trans ?_ hlow
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    rw [le_div_iff₀ hDpos]
    have := Real.log_le_log (by positivity) hCZ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at this
    rw [Real.log_div (by positivity) (by positivity)]
    linarith
  have hZpos : 0 < Z := by linarith
  have ha_eq : ∀ j, a j = 2 / (Z * c j) := fun j ↦ rfl
  have hZ4' : 4 ≤ Z := hZ4.trans hZ
  have ha0 : ∀ j, 0 < a j := fun j ↦ by
    rw [ha_eq]; exact div_pos two_pos (mul_pos hZpos (hcpos j))
  have ha2 : ∀ j, a j ≤ 1 / 2 := fun j ↦ by
    rw [ha_eq]; exact Entropy.harmonic_weight_le_half hZ4' (hc1 j)
  have hmass : ∑ j ∈ Finset.range m, a j = 2 :=
    Entropy.sum_harmonicWeight hrange fun j _ ↦ hcpos j
  have hcost : ∑ j ∈ Finset.range m, c j * a j ^ 2 = 4 / Z :=
    Entropy.sum_mul_harmonicWeight_sq hrange fun j _ ↦ hcpos j
  have hcost1 : 4 / Z ≤ 1 := by rw [div_le_one hZpos]; linarith
  -- crossing budgets
  set S : AdmissibleSupport Λ R → Finset (Site Λ) := fun X ↦ X.1
  have hcross : ∀ j < m,
      ((Entropy.crossingTerms S (X ∪ T j)).card : ℝ) ≤ K * c j := fun j hj ↦ by
    rw [hXT j hj]
    have hdR : R + 1 ≤ d j := by
      have : D ≤ (j + 1) * D := Nat.le_mul_of_pos_left D (by omega)
      simp only [d]; omega
    have hQ : (Q₀.dilate (d j)).toFinset ⊆ Q.toFinset :=
      (Q₀.toFinset_dilate_mono (hdle j hj)).trans hpad
    have := card_crossingTerms_rectRegion_le hsafe hRD₀ hdR hQ
    have h' : ((Entropy.crossingTerms S (rectRegion A (Q₀.dilate (d j)))).card : ℝ) ≤
        K * ((Q₀.size : ℝ) + d j) := by
      simp only [K, bufferCrossConst]; exact_mod_cast this
    refine h'.trans (mul_le_mul_of_nonneg_left ?_ hK)
    have : (Q₀.size : ℝ) ≤ r := by exact_mod_cast hQ₀
    linarith [hc j]
  have hB : ∀ j < m,
      Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S) ≤ K' * c j := fun j hj ↦ by
    refine (cutLogBudget_le_card hq _).trans ?_
    have := mul_le_mul_of_nonneg_right (hcross j hj)
      (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ v)))
    have hKL := mul_nonneg hK (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ v)))
    simp only [K', bufferBudgetConst]
    nlinarith [hc1 j]
  -- the hypotheses of the finite-dimensional discount
  have hT : ∀ i j, i ≤ j → T i ⊆ T j := by
    intro i j hij
    by_cases hj : j < m
    · have hi : i < m := lt_of_le_of_lt hij hj
      simp only [T, hi, hj, ↓reduceIte]
      exact Finset.sdiff_subset_sdiff
        (rectRegion_dilate_mono A Q₀ (Nat.add_le_add_left (Nat.mul_le_mul_right _
          (Nat.succ_le_succ hij)) r)) le_rfl
    · simp only [T, hj, ↓reduceIte]
      split_ifs
      · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl
      · exact le_rfl
  have hdisj : ∀ j, Disjoint X (T j) := fun j ↦ by
    simp only [T]; split_ifs <;> exact Finset.disjoint_sdiff
  have hsingle : ∀ i j j', ((∃ v ∈ S i, v ∈ X ∪ T j) ∧ ∃ v ∈ S i, v ∉ X ∪ T j) →
      ((∃ v ∈ S i, v ∈ X ∪ T j') ∧ ∃ v ∈ S i, v ∉ X ∪ T j') → j = j' := by
    intro i j j' h1 h2
    have hlt : ∀ k, ((∃ v ∈ S i, v ∈ X ∪ T k) ∧ ∃ v ∈ S i, v ∉ X ∪ T k) → k < m := by
      intro k hk
      by_contra hkm
      obtain ⟨-, w, -, hw⟩ := hk
      exact hw (by rw [hXT' k (not_lt.mp hkm)]; exact Finset.mem_univ w)
    have hj := hlt j h1
    have hj' := hlt j' h2
    rw [hXT j hj] at h1
    rw [hXT j' hj'] at h2
    have key : ∀ k k', k < k' → k' < m →
        Splits (rectRegion A (Q₀.dilate (d k))) (S i) →
        Splits (rectRegion A (Q₀.dilate (d k'))) (S i) → False := by
      intro k k' hkk hk' s1 s2
      refine not_splits_two_contours hsafe hRD₀ (d := d k) (d' := d k') ?_
        ((Q₀.toFinset_dilate_mono (hdle k' hk')).trans hpad) i.2 s1 s2
      have : (k + 1) * D + D ≤ (k' + 1) * D := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      simp only [d]; omega
    rcases lt_trichotomy j j' with hjj | hjj | hjj
    · exact (key j j' hjj hj' h1 h2).elim
    · exact hjj
    · exact (key j' j hjj hj h2 h1).elim
  have hE : ∑ j ∈ Finset.range m, 4 * a j ^ 2 *
      ∑ i ∈ Entropy.crossingTerms S (X ∪ T j),
        (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J ≤ Δ / 2 := by
    have hqJ : 0 ≤ (q : ℝ) ^ (2 * v) * J := by positivity
    have hterm : ∀ j ∈ Finset.range m, 4 * a j ^ 2 *
        ∑ i ∈ Entropy.crossingTerms S (X ∪ T j),
          (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J ≤
        4 * K * ((q : ℝ) ^ (2 * v) * J) * (c j * a j ^ 2) := by
      intro j hj
      have hj := Finset.mem_range.mp hj
      have hsum : ∑ i ∈ Entropy.crossingTerms S (X ∪ T j),
          (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J ≤
          (Entropy.crossingTerms S (X ∪ T j)).card * ((q : ℝ) ^ (2 * v) * J) := by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
        have h2 : (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ≤ (q : ℝ) ^ v := by
          exact_mod_cast supportDim_le hq i
        have h0 : (0 : ℝ) ≤ Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) := by positivity
        calc (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J ≤
            ((q : ℝ) ^ v) ^ 2 * J := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h2 2) hJ
          _ = (q : ℝ) ^ (2 * v) * J := by rw [← pow_mul, mul_comm v 2]
      calc 4 * a j ^ 2 * ∑ i ∈ Entropy.crossingTerms S (X ∪ T j),
            (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J
          ≤ 4 * a j ^ 2 * ((Entropy.crossingTerms S (X ∪ T j)).card *
              ((q : ℝ) ^ (2 * v) * J)) := by gcongr
        _ ≤ 4 * a j ^ 2 * (K * c j * ((q : ℝ) ^ (2 * v) * J)) := by
            gcongr; exact hcross j hj
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, hcost]
    have hnum : 0 ≤ 4 * K * ((q : ℝ) ^ (2 * v) * J) := by positivity
    have h1 : 32 * K * (q : ℝ) ^ (2 * v) * J ≤ Zmin * Δ := (div_le_iff₀ hΔ).mp hZE
    rw [mul_div_assoc', div_le_div_iff₀ hZpos two_pos]
    nlinarith
  have hu : ∀ j < m, a j / (1 - a j) ≤ Entropy.tailRadius (J / Δ)
      (Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S)) := fun j hj ↦ by
    rw [ha_eq]
    exact (Entropy.harmonic_weight_ratio_le hZ4' (hc1 j)).trans
      (Entropy.le_tailRadius_of_le (hZT.trans hZ) hZpos (hc1 j) hϑ
        (Entropy.one_le_cutLogBudget _ _) (hB j hj))
  have hTbuf : ∀ j < m, T j ⊆ Tbuf := fun j hj ↦ by
    simp only [T, hj, ↓reduceIte, Tbuf]
    exact Finset.sdiff_subset_sdiff (rectRegion_dilate_mono A Q₀ (hdle j hj)) le_rfl
  -- the finite-dimensional discount
  have key := Entropy.two_mul_condEntropy_le (n := fun _ : Site Λ ↦ q) X T hT hdisj a ha0 ha2
    hΩ h.term S (fun i ↦ QuantumCircuit.isSupportedOn_of_mem_supportedOperators (h.supported i))
    h.hermitian hJ h.norm_le hsingle hΔ heig hgap (by linarith) hE hu hmass
    Finset.disjoint_sdiff hTbuf
  -- the error terms
  have herr : ∑ j ∈ Finset.range m, 1024 * Real.exp 1 * (J / Δ) *
      Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S) * a j ^ 2 ≤
      1024 * Real.exp 1 * (J / Δ) * K' := by
    have h0 : 0 ≤ 1024 * Real.exp 1 * (J / Δ) := by positivity
    have hterm : ∀ j ∈ Finset.range m, 1024 * Real.exp 1 * (J / Δ) *
        Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
          (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S) * a j ^ 2 ≤
        1024 * Real.exp 1 * (J / Δ) * K' * (c j * a j ^ 2) := by
      intro j hj
      have := hB j (Finset.mem_range.mp hj)
      calc _ = 1024 * Real.exp 1 * (J / Δ) * (Entropy.cutLogBudget
              (Entropy.crossingTerms S (X ∪ T j))
              (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S) * a j ^ 2) := by ring
        _ ≤ 1024 * Real.exp 1 * (J / Δ) * (K' * c j * a j ^ 2) := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, hcost]
    have h0' : 0 ≤ 1024 * Real.exp 1 * (J / Δ) * K' := by positivity
    calc 1024 * Real.exp 1 * (J / Δ) * K' * (4 / Z) ≤ 1024 * Real.exp 1 * (J / Δ) * K' * 1 :=
          mul_le_mul_of_nonneg_left hcost1 h0'
      _ = _ := mul_one _
  have hmr : (m : ℝ) ≤ Cpad * r := by
    have : m * D ≤ Cpad * r := hmD.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    have : m ≤ Cpad * r := le_trans (Nat.le_mul_of_pos_right m hD) this
    exact_mod_cast this
  have hlog : -((m : ℝ) * Real.log (1 - Δ / 2 / Δ)) ≤ Cpad * r := by
    have h12 : 1 - Δ / 2 / Δ = (2 : ℝ)⁻¹ := by field_simp; norm_num
    rw [h12, Real.log_inv, mul_neg, neg_neg]
    have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  -- conclusion
  simp only [regionalEntropy_eq_regionEntropy]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hE1 : 0 ≤ 1024 * Real.exp 1 * (J / Δ) * K' := by positivity
  have hE1r : 1024 * Real.exp 1 * (J / Δ) * K' ≤ 1024 * Real.exp 1 * (J / Δ) * K' * r :=
    le_mul_of_one_le_right hE1 hr1
  change 2 * (Entropy.regionEntropy (X ∪ Tbuf) Ω - Entropy.regionEntropy Tbuf Ω) ≤
    Entropy.regionEntropy X Ω + _ - _ at key
  rw [sub_eq_add_neg] at key
  have := add_le_add herr hlog
  linarith

/-! ### The constants of Lemma 3.2 -/

/-- **The padding scale** `Z = max {4, 32 B_× q^{2 v_R} J/Δ, 128 √((1 + J/Δ) K_b)}`, with
`B_× = bufferCrossConst R = 8 (R + 1) μ_R`, `μ_R = 2^{v_R - 1}`, `v_R = 1 + 2 R (R + 1)` and
`K_b = bufferBudgetConst q R = 1 + B_× log² (e q^{v_R})`. The harmonic weights must have
`Z_r ≥ Z`. The second entry makes the energy of the optimized vector small against the gap and
grows linearly in `J/Δ`. The third entry is the weight range for the marginal tail, which
grows like `√(J/Δ)`. Source: `02-initial.tex`, lines 444–459 (`eq initial-weight-range`), with
the uniform lower bound `eq initial-harmonic-lower` of lines 322–331. -/
noncomputable def initialPaddingScale (q R : ℕ) (J Δ : ℝ) : ℝ :=
  max 4 (max
    (32 * bufferCrossConst R * (q : ℝ) ^ (2 * (1 + 2 * R * (R + 1))) * J / Δ)
    (128 * Real.sqrt ((1 + J / Δ) * bufferBudgetConst q R)))

/-- **The padding constant** `C_pad = ⌈(R + 3) e^{(R+1) Z}⌉ + R + 3`, with
`Z = initialPaddingScale q R J Δ`. It makes `(1/D) log ((C_pad + 1)/(2 + D)) ≥ Z` for
`D = R + 1`, so `C_pad` is exponential in `Z`, and hence in `J/Δ`. Source: `02-initial.tex`,
lines 322–333 and 444–459. -/
noncomputable def initialPaddingConst (q R : ℕ) (J Δ : ℝ) : ℕ :=
  ⌈(2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * initialPaddingScale q R J Δ)⌉₊ + R + 3

/-- **The buffer constant** `C_buf = (1024 e (J/Δ) K_b + C_pad) / 2`, with
`K_b = bufferBudgetConst q R` and `C_pad = initialPaddingConst q R J Δ`. It bounds the error
`C (m + 1) ℰ` of the two norm comparisons by `C_buf r`, using `m ≤ C_pad r / D`. Through `K_b`
it is linear in `J/Δ`, and through `C_pad` exponential in `J/Δ`.
Source: `02-initial.tex`, lines 574–585. -/
noncomputable def initialBufferConst (q R : ℕ) (J Δ : ℝ) : ℝ :=
  (1024 * Real.exp 1 * (J / Δ) * bufferBudgetConst q R + initialPaddingConst q R J Δ) / 2

/-- The padding constant is at least one. Source: `02-initial.tex`, lines 322–333. -/
theorem one_le_initialPaddingConst (q R : ℕ) (J Δ : ℝ) :
    1 ≤ initialPaddingConst q R J Δ := by
  unfold initialPaddingConst; omega

/-- The buffer constant is nonnegative. Source: `02-initial.tex`, lines 574–585. -/
theorem initialBufferConst_nonneg (q R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    0 ≤ initialBufferConst q R J Δ := by
  have hK : 0 ≤ bufferBudgetConst q R := zero_le_one.trans (one_le_bufferBudgetConst q R)
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  unfold initialBufferConst; positivity

/-- **Lemma 3.2 at the named constants** (integer clearance). For a gapped ground vector, a
safe rectangle `Q` with `D₀ > 2R + 10`, `r ≥ 1` and a rectangle `Q₀` of size at most `r` with
`Q₀^{+C_pad r} ⊆ Q`, `S(X | T) ≤ S(X)/2 + C_buf r`, where `C_pad = initialPaddingConst q R J Δ`
and `C_buf = initialBufferConst q R J Δ`. Source: `02-initial.tex`, lines 240–256 and
258–585. -/
theorem condEntropy_le_initialBufferConst (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) {D₀ : ℕ} (hD₀ : 2 * R + 10 < D₀) {Λ : Finset (ℤ × ℤ)}
    (h : LocalHamiltonian Λ q R J) {E₀ : ℝ} {Ω : StateSpace Λ q}
    (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ) {A : Finset (Site Λ)} {Q : IntRect}
    (hsafe : IsSafe Λ A D₀ Q) {r : ℕ} (hr : 1 ≤ r) {Q₀ : IntRect} (hQ₀ : Q₀.size ≤ r)
    (hpad : (Q₀.dilate (initialPaddingConst q R J Δ * r)).toFinset ⊆ Q.toFinset) :
    regionalEntropy Λ q Ω (rectRegion A Q₀ ∪
        (rectRegion A (Q₀.dilate (initialPaddingConst q R J Δ * r)) \ rectRegion A Q₀)) -
      regionalEntropy Λ q Ω
        (rectRegion A (Q₀.dilate (initialPaddingConst q R J Δ * r)) \ rectRegion A Q₀) ≤
    regionalEntropy Λ q Ω (rectRegion A Q₀) / 2 + initialBufferConst q R J Δ * r := by
  set Zmin := initialPaddingScale q R J Δ
  set Cpad := initialPaddingConst q R J Δ
  have hCZ : (2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin) ≤ Cpad + 1 := by
    have := Nat.le_ceil ((2 + ((R + 1 : ℕ) : ℝ)) * Real.exp ((R + 1 : ℕ) * Zmin))
    have h0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    simp only [Cpad, initialPaddingConst]
    push_cast at this ⊢
    linarith
  have hCR : R + 2 < Cpad := by simp only [Cpad, initialPaddingConst]; omega
  exact condEntropy_le_initialBuffer_of_constants hq hJ hΔ (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    hCR hCZ (by omega) h hgs hsafe hr hQ₀ hpad

/-- **Integer-clearance specialization of Lemma 3.2: conditional entropy in a buffered
rectangle** (area-law manuscript,
`lem:initial-buffer`, `02-initial.tex`, lines 240–256). For local dimension `q ≥ 1`, range
`R`, term norm bound `J ≥ 0` and gap `Δ > 0` there are an integer `C_pad ≥ 1` and a constant
`C_buf ≥ 0` with the following property, for every natural safety parameter `D₀ > 2R + 10`.
Let `Ω` be a gapped ground vector of a finite-range Hamiltonian on a finite domain, `A` a cut,
`Q` a safe rectangle, `r ≥ 1`, and `Q₀` a rectangle of size at most `r` with `Q₀^{+C_pad r} ⊆ Q`.
Then for `X = A ∩ Q₀` and `T = (A ∩ Q₀^{+C_pad r}) \ X`,
`S(X | T) = S(X ∪ T) - S(T) ≤ S(X)/2 + C_buf r`. -/
theorem exists_condEntropy_le_initialBuffer (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) :
    ∃ Cpad : ℕ, 1 ≤ Cpad ∧ ∃ Cbuf : ℝ, 0 ≤ Cbuf ∧
      ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J) (E₀ : ℝ) (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
      ∀ (A : Finset (Site Λ)) (Q : IntRect), IsSafe Λ A D₀ Q →
      ∀ r : ℕ, 1 ≤ r → ∀ Q₀ : IntRect, Q₀.size ≤ r →
        (Q₀.dilate (Cpad * r)).toFinset ⊆ Q.toFinset →
        regionalEntropy Λ q Ω (rectRegion A Q₀ ∪
            (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀)) -
          regionalEntropy Λ q Ω (rectRegion A (Q₀.dilate (Cpad * r)) \ rectRegion A Q₀) ≤
        regionalEntropy Λ q Ω (rectRegion A Q₀) / 2 + Cbuf * r :=
  ⟨initialPaddingConst q R J Δ, one_le_initialPaddingConst q R J Δ, initialBufferConst q R J Δ,
    initialBufferConst_nonneg q R hJ hΔ, fun _ hD₀ _ h _ _ hgs _ _ hsafe _ hr _ hQ₀ hpad ↦
      condEntropy_le_initialBufferConst q R hq hJ hΔ hD₀ h hgs hsafe hr hQ₀ hpad⟩

end TNLean.PEPS.AreaLaw
