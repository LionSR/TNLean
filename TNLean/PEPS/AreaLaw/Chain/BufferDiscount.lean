/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Chain.Domain

/-!
# The buffered discount with a constant-width buffer

For an interval `X = [l, r]` of a one-row domain and the buffer `T = X^{+m(R+1)} \ X` of
constant width, the conditional entropy of a gapped ground vector satisfies
`2 S(X | T) ≤ S(X) + C`, with `m` and `C` explicit functions of the local dimension `q`,
the range `R`, the term norm `J` and the gap `Δ`, linear in `1 + J/Δ`.

The finite-dimensional argument (optimized filters, stationarity, the energy estimate, the
prefix norm comparison and Schmidt pinning) is `Entropy.two_mul_condEntropy_le` in QICLean,
exactly as for the two-dimensional buffer lemma. This module supplies its hypotheses on a
chain: the nested shells `X_j = X^{+(j+1)(R+1)}`, which are intervals, the single-split
property, the constant crossing budget `N_R` and cut budget `B_R` of
`TNLean.PEPS.AreaLaw.Chain.Domain`, and the uniform weights `a_j = 2/m` of total mass two.

## Main results

* `chainShellCount`: the number of shells `m`.
* `chainDiscountConst`: the constant `4096 e (J/Δ) B_R / m + m log 2`.
* `two_mul_condEntropy_interval_le`: the discount `2 S(X | T) ≤ S(X) + C`.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), Section 4, Lemma 4.2 (`lem:buffer`),
  with the shells of width `R + 1` and the energy threshold `Δ/2` of the formal
  finite-dimensional lemma in place of the note's width `R` and threshold `Δ/4`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw.Chain

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}

/-- The energy threshold `32 N_R q^{2 v_R} J / Δ` for the number of shells. -/
noncomputable def chainEnergyThreshold (q R : ℕ) (J Δ : ℝ) : ℝ :=
  32 * chainCrossConst R * (q : ℝ) ^ (2 * (1 + 2 * R * (R + 1))) * J / Δ

/-- The tail threshold `128 √((1 + J/Δ) B_R)` for the number of shells. -/
noncomputable def chainTailThreshold (q R : ℕ) (J Δ : ℝ) : ℝ :=
  128 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)

/-- The number of shells `m = ⌈max {4, 32 N_R q^{2 v_R} J/Δ, 128 √((1 + J/Δ) B_R)}⌉`. -/
noncomputable def chainShellCount (q R : ℕ) (J Δ : ℝ) : ℕ :=
  ⌈max (max 4 (chainEnergyThreshold q R J Δ)) (chainTailThreshold q R J Δ)⌉₊

/-- There are at least four shells. -/
theorem four_le_chainShellCount (q R : ℕ) (J Δ : ℝ) : 4 ≤ chainShellCount q R J Δ := by
  have h : (4 : ℝ) ≤ max (max 4 (chainEnergyThreshold q R J Δ)) (chainTailThreshold q R J Δ) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have := Nat.le_ceil (max (max 4 (chainEnergyThreshold q R J Δ)) (chainTailThreshold q R J Δ))
  exact_mod_cast h.trans this

/-- The number of shells dominates the energy threshold. -/
theorem chainEnergyThreshold_le_chainShellCount (q R : ℕ) (J Δ : ℝ) :
    chainEnergyThreshold q R J Δ ≤ chainShellCount q R J Δ :=
  ((le_max_right _ _).trans (le_max_left _ _)).trans (Nat.le_ceil _)

/-- The number of shells dominates the tail threshold. -/
theorem chainTailThreshold_le_chainShellCount (q R : ℕ) (J Δ : ℝ) :
    chainTailThreshold q R J Δ ≤ chainShellCount q R J Δ :=
  (le_max_right _ _).trans (Nat.le_ceil _)

/-- The discount constant `4096 e (J/Δ) B_R / m + m log 2`. -/
noncomputable def chainDiscountConst (q R : ℕ) (J Δ : ℝ) : ℝ :=
  4096 * Real.exp 1 * (J / Δ) * chainBudgetConst q R / chainShellCount q R J Δ +
    chainShellCount q R J Δ * Real.log 2

/-- The buffer `T = X^{+m(R+1)} \ X` of the interval `X = [l, r]`: the sites within
distance `m (R + 1)` of the interval that are not in it. -/
noncomputable def chainBuffer (Λ : Finset (ℤ × ℤ)) (q R : ℕ) (J Δ : ℝ) (l r : ℤ) :
    Finset (Site Λ) :=
  interval Λ (l - chainShellCount q R J Δ * (R + 1)) (r + chainShellCount q R J Δ * (R + 1)) \
    interval Λ l r

/-- The buffer is disjoint from the interval. -/
theorem disjoint_interval_chainBuffer (Λ : Finset (ℤ × ℤ)) (q R : ℕ) (J Δ : ℝ) (l r : ℤ) :
    Disjoint (interval Λ l r) (chainBuffer Λ q R J Δ l r) :=
  Finset.disjoint_sdiff

/-- The buffer of a one-row domain has at most `2 m (R + 1)` sites. -/
theorem card_chainBuffer_le (hΛ : IsOneRow Λ) (q R : ℕ) (J Δ : ℝ) (l r : ℤ) :
    (chainBuffer Λ q R J Δ l r).card ≤ 2 * (chainShellCount q R J Δ * (R + 1)) := by
  set w : ℕ := chainShellCount q R J Δ * (R + 1) with hwdef
  have hw : (w : ℤ) = (chainShellCount q R J Δ : ℤ) * ((R : ℤ) + 1) := by
    rw [hwdef]; push_cast; ring
  have hsub : chainBuffer Λ q R J Δ l r ⊆
      interval Λ (l - w) (l - 1) ∪ interval Λ (r + 1) (r + w) := by
    intro v hv
    simp only [chainBuffer, Finset.mem_sdiff, mem_interval, not_and, not_le] at hv
    rw [Finset.mem_union, mem_interval, mem_interval]
    omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 := card_interval_le hΛ (l - w) (l - 1)
  have h2 := card_interval_le hΛ (r + 1) (r + w)
  have e1 : (l - 1 + 1 - (l - w)).toNat = w := by omega
  have e2 : (r + w + 1 - (r + 1)).toNat = w := by omega
  rw [e1] at h1
  rw [e2] at h2
  omega

/-- **The buffered discount on a chain.** For a gapped ground vector `Ω` of a finite-range
Hamiltonian on a one-row domain and an interval `X = [l, r]` with buffer
`T = X^{+m(R+1)} \ X`, `2 (S(X ∪ T) - S(T)) ≤ S(X) + 4096 e (J/Δ) B_R / m + m log 2`.
The shells are `X_j = X^{+(j+1)(R+1)}`, `0 ≤ j < m`, with the uniform weights `2/m`. -/
theorem two_mul_condEntropy_interval_le (hΛ : IsOneRow Λ) (hq : 1 ≤ q) (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) (h : LocalHamiltonian Λ q R J) {E₀ : ℝ} {Ω : StateSpace Λ q}
    (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ) {l r : ℤ} (hlr : l ≤ r) :
    2 * (regionalEntropy Λ q Ω (interval Λ l r ∪ chainBuffer Λ q R J Δ l r) -
        regionalEntropy Λ q Ω (chainBuffer Λ q R J Δ l r)) ≤
      regionalEntropy Λ q Ω (interval Λ l r) + chainDiscountConst q R J Δ := by
  classical
  obtain ⟨hΩ, heig, hgap⟩ := hgs
  replace heig : toEuclideanLin h.operator Ω = (E₀ : ℂ) • Ω := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin]; exact heig
  set N : ℕ := chainCrossConst R
  set K' : ℝ := chainBudgetConst q R
  set v : ℕ := 1 + 2 * R * (R + 1)
  have hK' : 1 ≤ K' := one_le_chainBudgetConst q R
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  -- the shells
  set m : ℕ := chainShellCount q R J Δ
  have hm4 : 4 ≤ m := four_le_chainShellCount q R J Δ
  have hm4' : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hmpos : (0 : ℝ) < m := by linarith
  have hmE : chainEnergyThreshold q R J Δ ≤ m := chainEnergyThreshold_le_chainShellCount q R J Δ
  have hmT : chainTailThreshold q R J Δ ≤ m := chainTailThreshold_le_chainShellCount q R J Δ
  set D : ℕ := R + 1 with hDdef
  set d : ℕ → ℕ := fun j ↦ (j + 1) * D
  set Q₀ : IntRect := rowRect l r hlr
  set X : Finset (Site Λ) := interval Λ l r
  set T : ℕ → Finset (Site Λ) := fun j ↦
    if j < m then rectRegion Finset.univ (Q₀.dilate (d j)) \ X else Finset.univ \ X
  set Tbuf : Finset (Site Λ) := chainBuffer Λ q R J Δ l r
  have hX0 : rectRegion (Finset.univ : Finset (Site Λ)) (Q₀.dilate 0) = X := by
    rw [rectRegion_rowRect_dilate hΛ hlr 0]
    simp [X]
  have hXd : ∀ j, X ⊆ rectRegion Finset.univ (Q₀.dilate (d j)) := fun j ↦ by
    rw [← hX0]
    exact rectRegion_dilate_mono _ _ (Nat.zero_le _)
  have hXT : ∀ j < m, X ∪ T j = rectRegion Finset.univ (Q₀.dilate (d j)) := fun j hj ↦ by
    simp only [T, hj, ↓reduceIte]
    exact Finset.union_sdiff_of_subset (hXd j)
  have hXT' : ∀ j, m ≤ j → X ∪ T j = Finset.univ := fun j hj ↦ by
    simp only [T, not_lt.mpr hj, ↓reduceIte]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ X)
  have hXTint : ∀ j < m, X ∪ T j = interval Λ (l - d j) (r + d j) := fun j hj ↦ by
    rw [hXT j hj, rectRegion_rowRect_dilate hΛ hlr]
  have hTbuf_eq : Tbuf = rectRegion Finset.univ (Q₀.dilate (d (m - 1))) \ X := by
    rw [rectRegion_rowRect_dilate hΛ hlr]
    have : d (m - 1) = m * D := by
      simp only [d]
      rw [Nat.sub_add_cancel (by omega)]
    rw [this]
    simp only [Tbuf, chainBuffer, X, D]
    push_cast
    rfl
  -- the uniform weights
  set a : ℕ → ℝ := fun _ ↦ 2 / m
  have ha0 : ∀ j, 0 < a j := fun _ ↦ by positivity
  have ha2 : ∀ j, a j ≤ 1 / 2 := fun _ ↦ by
    simp only [a]
    rw [div_le_div_iff₀ hmpos two_pos]
    linarith
  have hmass : ∑ j ∈ Finset.range m, a j = 2 := by
    simp only [a, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  -- crossing budgets
  set S : AdmissibleSupport Λ R → Finset (Site Λ) := fun X ↦ X.1
  have hcross : ∀ j < m, ((Entropy.crossingTerms S (X ∪ T j)).card : ℝ) ≤ N := fun j hj ↦ by
    rw [hXTint j hj]
    exact_mod_cast card_crossingTerms_interval_le hΛ (l - d j) (r + d j)
  have hB : ∀ j < m,
      Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S) ≤ K' := fun j hj ↦ by
    rw [hXTint j hj]
    exact cutLogBudget_interval_le hΛ hq (l - d j) (r + d j)
  -- the hypotheses of the finite-dimensional discount
  have hT : ∀ i j, i ≤ j → T i ⊆ T j := by
    intro i j hij
    by_cases hj : j < m
    · have hi : i < m := lt_of_le_of_lt hij hj
      simp only [T, hi, hj, ↓reduceIte]
      exact Finset.sdiff_subset_sdiff
        (rectRegion_dilate_mono _ _ (Nat.mul_le_mul_right _ (Nat.succ_le_succ hij))) le_rfl
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
    have key : ∀ k k', k < k' →
        Splits (rectRegion Finset.univ (Q₀.dilate (d k))) (S i) →
        Splits (rectRegion Finset.univ (Q₀.dilate (d k'))) (S i) → False := by
      intro k k' hkk s1 s2
      refine not_splits_two_contours (isSafe_univ (R + 1) (Q₀.dilate (d k')))
        (Nat.lt_succ_self R) (d := d k) (d' := d k') ?_ subset_rfl i.2 s1 s2
      have : (k + 1) * D + D ≤ (k' + 1) * D := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      simp only [d]; omega
    rcases lt_trichotomy j j' with hjj | hjj | hjj
    · exact (key j j' hjj h1 h2).elim
    · exact hjj
    · exact (key j' j hjj h2 h1).elim
  have hE : ∑ j ∈ Finset.range m, 4 * a j ^ 2 *
      ∑ i ∈ Entropy.crossingTerms S (X ∪ T j),
        (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J ≤ Δ / 2 := by
    have hqJ : 0 ≤ (q : ℝ) ^ (2 * v) * J := by positivity
    have hterm : ∀ j ∈ Finset.range m, 4 * a j ^ 2 *
        ∑ i ∈ Entropy.crossingTerms S (X ∪ T j),
          (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J ≤
        16 * N * ((q : ℝ) ^ (2 * v) * J) / (m : ℝ) ^ 2 := by
      intro j hj
      have hj := Finset.mem_range.mp hj
      have hsum : ∑ i ∈ Entropy.crossingTerms S (X ∪ T j),
          (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J ≤
          (Entropy.crossingTerms S (X ∪ T j)).card * ((q : ℝ) ^ (2 * v) * J) := by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
        have h2 := supportDim_le_real (R := R) hq i
        have h0 : (0 : ℝ) ≤ Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) := by positivity
        calc (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J ≤
            ((q : ℝ) ^ v) ^ 2 * J := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h2 2) hJ
          _ = (q : ℝ) ^ (2 * v) * J := by rw [← pow_mul, mul_comm v 2]
      have hcard := hcross j hj
      have ha : a j ^ 2 = 4 / (m : ℝ) ^ 2 := by norm_num [a, div_pow]
      calc 4 * a j ^ 2 * ∑ i ∈ Entropy.crossingTerms S (X ∪ T j),
            (Entropy.supportDim (fun _ : Site Λ ↦ q) (S i) : ℝ) ^ 2 * J
          ≤ 4 * a j ^ 2 * ((Entropy.crossingTerms S (X ∪ T j)).card *
              ((q : ℝ) ^ (2 * v) * J)) := by gcongr
        _ ≤ 4 * a j ^ 2 * (N * ((q : ℝ) ^ (2 * v) * J)) := by gcongr
        _ = 16 * N * ((q : ℝ) ^ (2 * v) * J) / (m : ℝ) ^ 2 := by rw [ha]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hthr : 32 * N * (q : ℝ) ^ (2 * v) * J / Δ ≤ m := hmE
    rw [div_le_iff₀ hΔ] at hthr
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [show (m : ℝ) * (16 * N * ((q : ℝ) ^ (2 * v) * J) / (m : ℝ) ^ 2) =
      16 * N * ((q : ℝ) ^ (2 * v) * J) / m by field_simp]
    rw [div_le_div_iff₀ hmpos two_pos]
    nlinarith
  have hu : ∀ j < m, a j / (1 - a j) ≤ Entropy.tailRadius (J / Δ)
      (Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S)) := fun j hj ↦ by
    have h1 := harmonic_weight_ratio_le hm4' (le_refl (1 : ℝ))
    have h2 := le_tailRadius_of_le (Z := m) (c := 1) (ϑ := J / Δ) (K' := K')
      (B := Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S)) hmT hmpos le_rfl hϑ
      (Entropy.one_le_cutLogBudget _ _) (by rw [mul_one]; exact hB j hj)
    rw [mul_one] at h1 h2
    exact h1.trans h2
  have hTbuf : ∀ j < m, T j ⊆ Tbuf := fun j hj ↦ by
    rw [hTbuf_eq]
    simp only [T, hj, ↓reduceIte]
    exact Finset.sdiff_subset_sdiff
      (rectRegion_dilate_mono _ _ (Nat.mul_le_mul_right _ (by omega))) le_rfl
  -- the finite-dimensional discount
  have key := Entropy.two_mul_condEntropy_le (n := fun _ : Site Λ ↦ q) X T hT hdisj a ha0 ha2
    hΩ h.term S (fun i ↦ QuantumCircuit.isSupportedOn_of_mem_supportedOperators (h.supported i))
    h.hermitian hJ h.norm_le hsingle hΔ heig hgap (E := Δ / 2) (by linarith) hE hu hmass
    (disjoint_interval_chainBuffer Λ q R J Δ l r) hTbuf
  -- the error terms
  have herr : ∑ j ∈ Finset.range m, 1024 * Real.exp 1 * (J / Δ) *
      Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S) * a j ^ 2 ≤
      4096 * Real.exp 1 * (J / Δ) * K' / m := by
    have h0 : 0 ≤ 1024 * Real.exp 1 * (J / Δ) := by positivity
    have hterm : ∀ j ∈ Finset.range m, 1024 * Real.exp 1 * (J / Δ) *
        Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
          (Entropy.supportDim (fun _ : Site Λ ↦ q) ∘ S) * a j ^ 2 ≤
        1024 * Real.exp 1 * (J / Δ) * K' * (4 / (m : ℝ) ^ 2) := by
      intro j hj
      have := hB j (Finset.mem_range.mp hj)
      have ha : a j ^ 2 = 4 / (m : ℝ) ^ 2 := by norm_num [a, div_pow]
      rw [ha]
      gcongr
    refine (Finset.sum_le_sum hterm).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [show (m : ℝ) * (1024 * Real.exp 1 * (J / Δ) * K' * (4 / (m : ℝ) ^ 2)) =
      4096 * Real.exp 1 * (J / Δ) * K' / m by field_simp; ring]
  have hlog : (m : ℝ) * Real.log (1 - Δ / 2 / Δ) = -(m * Real.log 2) := by
    have h12 : 1 - Δ / 2 / Δ = (2 : ℝ)⁻¹ := by field_simp; norm_num
    rw [h12, Real.log_inv, mul_neg]
  -- conclusion
  simp only [regionalEntropy_eq_regionEntropy]
  change 2 * (Entropy.regionEntropy (X ∪ Tbuf) Ω - Entropy.regionEntropy Tbuf Ω) ≤
    Entropy.regionEntropy X Ω + _ - _ at key
  rw [hlog] at key
  simp only [chainDiscountConst]
  linarith

end TNLean.PEPS.AreaLaw.Chain
