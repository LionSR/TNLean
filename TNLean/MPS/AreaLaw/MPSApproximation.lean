/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AreaLaw
import TNLean.MPS.AreaLaw.OpenMPSRank
import TNLean.MPS.AreaLaw.SequentialTruncation

/-!
# Polynomial matrix product state approximation on a chain

The ground vector of a gapped finite-range Hamiltonian on the chain of `L` sites is within
`1/L` of a normalized open-boundary matrix product state whose bond dimension is an explicit
polynomial in `L`. The proof is the two-line route of the note: the marginal tail bound gives,
at every cut, a spectral projector of rank at most `exp(S + w)` discarding mass at most the
tail, the area law bounds `S` by a constant, and the sequential truncation across the cuts
produces the matrix product state.

## Main results

* `chainBondDimension`: the bond dimension `⌊exp(C_int + w(L))⌋`.
* `exists_isOpenMPS_norm_sub_le`: Theorem B.
* `chainBondDimension_le_mul_rpow`: the bond dimension is at most `C L^c`.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), Theorem B, Section 7 (the two-line route),
  Proposition 7.1 and Theorem 7.2.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

variable {q R : ℕ} {J Δ : ℝ}

/-- The left block of `k` sites is the interval `[0, k)`. -/
theorem leftBlock_eq_interval (L k : ℕ) : leftBlock L k = interval L 0 k := by
  ext i
  simp

/-- Scaling a matrix product state multiplies its scalar endpoint cap. -/
theorem IsOpenMPS.smul {L q D : ℕ} {ψ : (Fin L → Fin q) → ℂ} (h : IsOpenMPS L q D ψ) (c : ℂ) :
    IsOpenMPS L q D fun x ↦ c * ψ x := by
  obtain ⟨A, a, hA, hψ⟩ := h
  refine ⟨A, c * a, hA, fun x ↦ ?_⟩
  change c * ψ x = _
  rw [hψ x, mul_assoc]

/-- The square root `√(2 e^{e/2})` of the prefactor of the marginal tail bound. -/
noncomputable def tailPrefactorRoot : ℝ := Real.sqrt (2 * Real.exp (Real.exp 1 / 2))

/-- The prefactor root is positive. -/
theorem tailPrefactorRoot_pos : 0 < tailPrefactorRoot :=
  Real.sqrt_pos.mpr (by positivity)

/-- The square of the prefactor root is the prefactor. -/
theorem tailPrefactorRoot_sq : tailPrefactorRoot ^ 2 = 2 * Real.exp (Real.exp 1 / 2) :=
  Real.sq_sqrt (by positivity)

/-- The truncation width `w(L) = 64 √((1 + J/Δ) B_R) log (2 L² √(2 e^{e/2}))`. -/
noncomputable def chainTruncationWidth (q R : ℕ) (J Δ : ℝ) (L : ℕ) : ℝ :=
  64 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R) *
    Real.log (2 * (L : ℝ) ^ 2 * tailPrefactorRoot)

/-- The bond dimension `⌊exp (C_int + w(L))⌋`. -/
noncomputable def chainBondDimension (q R : ℕ) (J Δ : ℝ) (L : ℕ) : ℕ :=
  ⌊Real.exp (chainIntervalEntropyBound q R J Δ + chainTruncationWidth q R J Δ L)⌋₊

/-- The prefactor root exceeds one. -/
theorem one_lt_tailPrefactorRoot : 1 < tailPrefactorRoot := by
  rw [tailPrefactorRoot, Real.lt_sqrt zero_le_one]
  have := Real.exp_pos (Real.exp 1 / 2)
  have h1 : 1 ≤ Real.exp (Real.exp 1 / 2) := Real.one_le_exp (by positivity)
  linarith

/-- For `L ≥ 1` the truncation width is nonnegative. -/
theorem chainTruncationWidth_nonneg (hJ : 0 ≤ J) (hΔ : 0 < Δ) {L : ℕ} (hL : 1 ≤ L) :
    0 ≤ chainTruncationWidth q R J Δ L := by
  unfold chainTruncationWidth
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hroot := one_lt_tailPrefactorRoot
  have h1 : 1 ≤ 2 * (L : ℝ) ^ 2 * tailPrefactorRoot := by nlinarith
  have := Real.log_nonneg h1
  positivity

/-- The exponential of the truncation width at the tail rate: `exp(-w/(32 s)) = 1/(2 L² c)²`
with `s = √((1 + J/Δ) B_R)` and `c` the prefactor root. -/
theorem exp_neg_chainTruncationWidth (hJ : 0 ≤ J) (hΔ : 0 < Δ) {L : ℕ} (hL : 1 ≤ L) :
    Real.exp (-(chainTruncationWidth q R J Δ L /
        (32 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)))) =
      (2 * (L : ℝ) ^ 2 * tailPrefactorRoot)⁻¹ ^ 2 := by
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hK := one_le_chainBudgetConst q R
  have hs : 0 < Real.sqrt ((1 + J / Δ) * chainBudgetConst q R) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hroot := tailPrefactorRoot_pos
  have hy : 0 < 2 * (L : ℝ) ^ 2 * tailPrefactorRoot := by positivity
  have hw : chainTruncationWidth q R J Δ L /
      (32 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)) =
      2 * Real.log (2 * (L : ℝ) ^ 2 * tailPrefactorRoot) := by
    unfold chainTruncationWidth
    field_simp
    ring
  rw [hw, show -(2 * Real.log (2 * (L : ℝ) ^ 2 * tailPrefactorRoot)) =
      Real.log ((2 * (L : ℝ) ^ 2 * tailPrefactorRoot)⁻¹ ^ 2) by
        rw [Real.log_pow, Real.log_inv]; push_cast; ring,
    Real.exp_log (by positivity)]

/-- **Theorem B: polynomial matrix product state approximation on a chain.** For a gapped
ground vector `Ω` of a finite-range Hamiltonian on the chain of `L ≥ 1` sites there is a
normalized open-boundary matrix product state `Φ` of bond dimension at most
`⌊exp (C_int(q, R, J, Δ) + w(L))⌋` within `1/L` of `Ω`. TNLean note, Theorem B, by the
two-line route of Section 7. -/
theorem exists_isOpenMPS_norm_sub_le (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ) {L : ℕ}
    (hL : 1 ≤ L) (h : ChainHamiltonian L q R J) {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) :
    ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
      IsOpenMPS L q (chainBondDimension q R J Δ L) (fun x ↦ Φ x) ∧ ‖Φ - Ω‖ ≤ 1 / L := by
  classical
  have hΩ : ‖Ω‖ = 1 := hgs.1
  set w : ℝ := chainTruncationWidth q R J Δ L
  set s : ℝ := Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hK := one_le_chainBudgetConst q R
  have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hw0 : 0 ≤ w := chainTruncationWidth_nonneg hJ hΔ hL
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  set Cint := chainIntervalEntropyBound q R J Δ
  have hCint : 0 ≤ Cint := chainIntervalEntropyBound_nonneg hq hJ hΔ
  -- entropy and tail bounds at every cut
  have hS : ∀ k, Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω ≤ Cint := by
    intro k
    rw [leftBlock_eq_interval]
    exact regionEntropy_interval_le hq hJ hΔ h hgs _ _
  have htail : ∀ k, Entropy.surprisalTail
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω).eigenvalues
      (Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω) w ≤
      2 * Real.exp (Real.exp 1 / 2) * Real.exp (-(w / (32 * s))) := by
    intro k
    refine (h.surprisalTail_regionState_le hJ hΔ hgs _ w).trans ((min_le_right _ _).trans ?_)
    have hB : cutLogBudget L q R (leftBlock L k) ≤ chainBudgetConst q R := by
      rw [leftBlock_eq_interval]; exact cutLogBudget_interval_le hq 0 k
    have hB1 := one_le_cutLogBudget L q R (leftBlock L k)
    have hsA : 0 < Real.sqrt ((1 + J / Δ) * cutLogBudget L q R (leftBlock L k)) :=
      Real.sqrt_pos.mpr (by nlinarith)
    have hsle : Real.sqrt ((1 + J / Δ) * cutLogBudget L q R (leftBlock L k)) ≤ s :=
      Real.sqrt_le_sqrt (by gcongr)
    gcongr
  -- the sequential truncation
  obtain ⟨Φ₀, hrank, hdist⟩ := exists_sequentialTruncation Ω hΩ w
  -- the distance
  have hsum : ∑ k ∈ Finset.Ico 1 L, Real.sqrt (Entropy.surprisalTail
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω).eigenvalues
      (Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω) w) ≤
      ((L : ℝ) - 1) * (1 / (2 * (L : ℝ) ^ 2)) := by
    have hone : Real.sqrt (2 * Real.exp (Real.exp 1 / 2) * Real.exp (-(w / (32 * s)))) =
        1 / (2 * (L : ℝ) ^ 2) := by
      rw [exp_neg_chainTruncationWidth hJ hΔ hL, ← tailPrefactorRoot_sq]
      have hroot := tailPrefactorRoot_pos
      have : tailPrefactorRoot ^ 2 * (2 * (L : ℝ) ^ 2 * tailPrefactorRoot)⁻¹ ^ 2 =
          (1 / (2 * (L : ℝ) ^ 2)) ^ 2 := by
        field_simp
      rw [this, Real.sqrt_sq (by positivity)]
    have hterm : ∀ k ∈ Finset.Ico 1 L, Real.sqrt (Entropy.surprisalTail
        (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω).eigenvalues
        (Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω) w) ≤
        1 / (2 * (L : ℝ) ^ 2) := fun k _ ↦ by
      rw [← hone]
      exact Real.sqrt_le_sqrt (htail k)
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hL, Nat.cast_one]
  have hε : ‖Ω - Φ₀‖ ≤ 1 / (2 * L) := by
    refine hdist.trans (hsum.trans ?_)
    rw [show ((L : ℝ) - 1) * (1 / (2 * (L : ℝ) ^ 2)) = ((L : ℝ) - 1) / (2 * (L : ℝ) ^ 2) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hε' : 1 / (2 * (L : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]; linarith
  -- normalization
  have hΦ₀norm : 1 - 1 / (2 * (L : ℝ)) ≤ ‖Φ₀‖ := by
    have := norm_sub_norm_le Ω Φ₀
    linarith
  have hΦ₀pos : 0 < ‖Φ₀‖ := by linarith
  set c : ℂ := ((‖Φ₀‖⁻¹ : ℝ) : ℂ)
  set Φ₁ : EuclideanSpace ℂ (Fin L → Fin q) := c • Φ₀ with hΦ₁def
  have hΦ₁norm : ‖Φ₁‖ = 1 := by
    rw [hΦ₁def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΦ₀pos),
      inv_mul_cancel₀ hΦ₀pos.ne']
  have hΦ₁dist : ‖Φ₁ - Ω‖ ≤ 1 / L := by
    have h1 : ‖Φ₁ - Φ₀‖ = |1 - ‖Φ₀‖| := by
      have hsub : Φ₁ - Φ₀ = ((‖Φ₀‖⁻¹ - 1 : ℝ) : ℂ) • Φ₀ := by
        rw [hΦ₁def, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      rw [hsub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        show |‖Φ₀‖⁻¹ - 1| * ‖Φ₀‖ = |(‖Φ₀‖⁻¹ - 1) * ‖Φ₀‖| by
          rw [abs_mul, abs_of_pos hΦ₀pos]]
      congr 1
      field_simp
    have h2 : |1 - ‖Φ₀‖| ≤ 1 / (2 * (L : ℝ)) := by
      rw [abs_le]
      have := norm_sub_norm_le Φ₀ Ω
      rw [norm_sub_rev] at this
      constructor <;> linarith
    calc ‖Φ₁ - Ω‖ = ‖(Φ₁ - Φ₀) + (Φ₀ - Ω)‖ := by congr 1; abel
      _ ≤ ‖Φ₁ - Φ₀‖ + ‖Φ₀ - Ω‖ := norm_add_le _ _
      _ ≤ 1 / (2 * (L : ℝ)) + 1 / (2 * (L : ℝ)) := by
          rw [h1, norm_sub_rev]; exact add_le_add h2 hε
      _ = 1 / L := by field_simp; ring
  -- the matrix product structure
  have hD : ∀ k, (cutMatrix Φ₀ k).rank ≤ chainBondDimension q R J Δ L := by
    intro k
    apply Nat.le_floor
    refine (hrank k).trans (max_le ?_ ?_)
    · exact Real.one_le_exp (by linarith)
    · exact Real.exp_le_exp.mpr (by linarith [hS k])
  have hmps₀ := isOpenMPS_of_cutMatrix_rank_le Φ₀ hD
  refine ⟨Φ₁, hΦ₁norm, ?_, hΦ₁dist⟩
  have := hmps₀.smul c
  convert this using 2 with x
  simp [hΦ₁def]

/-- **The bond dimension is polynomial in the length.** For `L ≥ 1`,
`D(L) ≤ e^{C_int} (2 √(2 e^{e/2}))^{64 s} L^{128 s}` with `s = √((1 + J/Δ) B_R)`. -/
theorem chainBondDimension_le_mul_rpow {L : ℕ} (hL : 1 ≤ L) :
    (chainBondDimension q R J Δ L : ℝ) ≤
      Real.exp (chainIntervalEntropyBound q R J Δ) *
        (2 * tailPrefactorRoot) ^ (64 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)) *
        (L : ℝ) ^ (128 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hroot := tailPrefactorRoot_pos
  have hy : 0 < 2 * (L : ℝ) ^ 2 * tailPrefactorRoot := by positivity
  have hexpw : Real.exp (chainTruncationWidth q R J Δ L) =
      (2 * tailPrefactorRoot) ^ (64 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)) *
        (L : ℝ) ^ (128 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)) := by
    unfold chainTruncationWidth
    rw [show 64 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R) *
        Real.log (2 * (L : ℝ) ^ 2 * tailPrefactorRoot) =
        Real.log (2 * (L : ℝ) ^ 2 * tailPrefactorRoot) *
          (64 * Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)) by ring,
      ← Real.rpow_def_of_pos hy,
      show 2 * (L : ℝ) ^ 2 * tailPrefactorRoot = (2 * tailPrefactorRoot) * (L : ℝ) ^ 2 by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hL'.le]
    congr 2
    push_cast
    ring
  refine (Nat.floor_le (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [Real.exp_add, hexpw, mul_assoc]

end TNLean.MPS.AreaLaw
