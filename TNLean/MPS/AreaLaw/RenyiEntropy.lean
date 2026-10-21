/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.AreaLaw.Counting
import QICLean.Entropy.RegionEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Rényi entropies near order one on a gapped chain

For an interval in a finite-range gapped chain, the Rényi entropies throughout a fixed
closed interval of orders below one differ from the von Neumann entropy by at most
`16 * exp 1 * sqrt ((1 + J / Δ) * chainBudgetConst q R)`.

The entropy at order one is the regional von Neumann entropy. At the other orders the
spectral formula uses the existing surprisal moment, so zero eigenvalues are permitted.

Source: the one-dimensional note, `part1_arealaw.tex`, Remark `rem:renyi`, lines 280–286,
with the moment estimate `eq:mgf` and parameter `eq:theta`, lines 152–166.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Jensen's inequality for the exponential gives the lower log-moment bound.
Source: the one-dimensional note, `part1_arealaw.tex`, `rem:renyi`, lines 280–286. -/
private theorem mul_entropy_le_log_surprisalMoment {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (u : ℝ) :
    u * (∑ i, Real.negMulLog (p i)) ≤ Real.log (Entropy.surprisalMoment p u) := by
  have h := (convexOn_exp).map_sum_le (fun i (_ : i ∈ Finset.univ) ↦ hp i) hs
    (fun i _ ↦ Set.mem_univ (u * -Real.log (p i)))
  have h' : Real.exp (u * ∑ i, Real.negMulLog (p i)) ≤ Entropy.surprisalMoment p u := by
    simpa [smul_eq_mul, Entropy.surprisalMoment, Real.negMulLog, Finset.mul_sum,
      mul_neg, mul_assoc, mul_left_comm] using h
  exact (Real.le_log_iff_exp_le (Entropy.surprisalMoment_pos hp hs u)).mpr h'

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- The physical log-moment bound applied to the regional state.
Source: the one-dimensional note, `part1_arealaw.tex`, `eq:mgf`, lines 157–166. -/
private theorem ChainHamiltonian.log_surprisalMoment_region_le
    {L q R : ℕ} {J Δ : ℝ} (h : ChainHamiltonian L q R J)
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ)
    (X : Finset (Fin L)) {u : ℝ}
    (hu : |u| ≤ Entropy.tailRadius (J / Δ) (cutLogBudget L q R X)) :
    Real.log (Entropy.surprisalMoment
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) X Ω).eigenvalues u) ≤
    u * Entropy.regionEntropy (n := fun _ : Fin L ↦ q) X Ω +
      512 * Real.exp 1 * (J / Δ) * cutLogBudget L q R X * u ^ 2 := by
  obtain ⟨hΩ, heig, hgap⟩ := hgs
  change toEuclideanLin h.operator Ω = (E₀ : ℂ) • Ω at heig
  exact Entropy.log_surprisalMoment_cut_le (n := fun _ : Fin L ↦ q) (B := X)
    h.supported h.hermitian hJ h.norm_le hΩ hΔ heig hgap rfl
    (Entropy.regionState_isHermitian X Ω) hu

/-- Increasing the cut budget decreases the admissible moment radius.
Source: the one-dimensional note, `part1_arealaw.tex`, `eq:theta`, lines 152–155. -/
private theorem tailRadius_anti_budget {θ B B' : ℝ} (hθ : 0 ≤ θ) (hB : 1 ≤ B) (hBB' : B ≤ B') :
    Entropy.tailRadius θ B' ≤ Entropy.tailRadius θ B := by
  unfold Entropy.tailRadius
  gcongr

/-- Near-one Rényi entropies of an interval in the original gapped chain.
The entropy at order one is the existing regional von Neumann entropy.
The local function `H` is defined by the existing surprisal moment; at every
positive order other than one it is exactly the logarithm of the sum of the
eigenvalues to that order, divided by one minus the order. Zero eigenvalues
contribute zero. The final equality identifies the spectral power formula throughout
the stated interval, with the von Neumann convention at order one.
No invertibility or rank assumption is imposed.

Source: the one-dimensional note, `part1_arealaw.tex`, `rem:renyi`,
lines 280–286, with `eq:theta` and `eq:mgf`, lines 152–166.
The source explicitly restricts to the contiguous chain at lines 91–93. -/
theorem ChainHamiltonian.near_one_renyi_entropy_interval_bounds
    {L q R : ℕ} {J Δ : ℝ}
    (h : ChainHamiltonian L q R J)
    (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ)
    (l r : ℕ) :
    let X := interval L l r
    let p := (Entropy.regionState_isHermitian
      (n := fun _ : Fin L ↦ q) X Ω).eigenvalues
    let S := Entropy.regionEntropy (n := fun _ : Fin L ↦ q) X Ω
    let u₀ := Entropy.tailRadius (J / Δ) (chainBudgetConst q R)
    let H : ℝ → ℝ := fun α ↦
      if α = 1 then S
      else Real.log (Entropy.surprisalMoment p (1 - α)) / (1 - α)
    H 1 = S ∧
      ∀ α : ℝ, 1 - u₀ ≤ α → α ≤ 1 →
        S ≤ H α ∧
        H α ≤ S + 512 * Real.exp 1 * (J / Δ) *
          chainBudgetConst q R * (1 - α) ∧
        |H α - S| ≤ 16 * Real.exp 1 *
          Real.sqrt ((1 + J / Δ) * chainBudgetConst q R) ∧
        H α = if α = 1 then S else Real.log (∑ i, p i ^ α) / (1 - α) := by
  dsimp only
  refine ⟨ite_eq_left rfl, ?_⟩
  intro α hαlo hαhi
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hB := one_le_chainBudgetConst q R
  have hs : 1 ≤ Real.sqrt ((1 + J / Δ) * chainBudgetConst q R) :=
    Real.one_le_sqrt.mpr (by nlinarith [mul_nonneg hθ (zero_le_one.trans hB)])
  have hrad : Entropy.tailRadius (J / Δ) (chainBudgetConst q R) ≤ 1 / 32 := by
    simpa only [Entropy.tailRadius, mul_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 32 * 1)
        (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 32))
  rcases eq_or_lt_of_le hαhi with rfl | hαlt
  · simp only [ite_true, sub_self, mul_zero, add_zero, le_refl, abs_zero, true_and, and_true]
    positivity
  · simp only [ite_eq_right hαlt.ne]
    set p := (Entropy.regionState_isHermitian
      (n := fun _ : Fin L ↦ q) (interval L l r) Ω).eigenvalues
    set S := Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L l r) Ω
    set u := 1 - α
    have hu0 : 0 < u := sub_pos.mpr hαlt
    have hu : u ≤ Entropy.tailRadius (J / Δ) (chainBudgetConst q R) := by
      linarith only [hαlo]
    have hp : ∀ i, 0 ≤ p i :=
      (Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q)
        (interval L l r) Ω).eigenvalues_nonneg
    have hpSum : ∑ i, p i = 1 :=
      Entropy.sum_eigenvalues_partialTraceRight_eq_one
        (Ψ := Entropy.cutVector (interval L l r) Ω)
        (by rw [Entropy.norm_cutVector, hgs.1]) rfl
        (Entropy.regionState_isHermitian (interval L l r) Ω)
    have hlo : S ≤ Real.log (Entropy.surprisalMoment p u) / u :=
      (le_div_iff₀ hu0).mpr (by
        simpa only [S, Entropy.regionEntropy, vonNeumannEntropy, p, mul_comm] using
          mul_entropy_le_log_surprisalMoment hp hpSum u)
    have hcut := cutLogBudget_interval_le (L := L) (R := R) hq l r
    have hmoment := h.log_surprisalMoment_region_le hJ hΔ hgs (interval L l r)
      ((abs_of_pos hu0).le.trans (hu.trans
        (tailRadius_anti_budget hθ (one_le_cutLogBudget L q R (interval L l r)) hcut)))
    have hlog : Real.log (Entropy.surprisalMoment p u) ≤ u * S +
        512 * Real.exp 1 * (J / Δ) * chainBudgetConst q R * u ^ 2 :=
      hmoment.trans (by gcongr)
    have hupper : Real.log (Entropy.surprisalMoment p u) / u ≤ S +
        512 * Real.exp 1 * (J / Δ) * chainBudgetConst q R * u :=
      (div_le_iff₀ hu0).mpr (by nlinarith only [hlog])
    set s := Real.sqrt ((1 + J / Δ) * chainBudgetConst q R)
    have hu' : u * (32 * s) ≤ 1 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * s)).mp hu
    have hs_sq : s ^ 2 = (1 + J / Δ) * chainBudgetConst q R :=
      Real.sq_sqrt (by positivity)
    have hθB : (J / Δ) * chainBudgetConst q R ≤ s ^ 2 := by
      nlinarith only [hs_sq, hB]
    have hc1 : 512 * Real.exp 1 * (J / Δ) * chainBudgetConst q R * u * s ≤
        16 * Real.exp 1 * (J / Δ) * chainBudgetConst q R := by
      nlinarith only [mul_le_mul_of_nonneg_left hu'
        (by positivity : 0 ≤ 16 * Real.exp 1 * (J / Δ) * chainBudgetConst q R)]
    have hc : 512 * Real.exp 1 * (J / Δ) * chainBudgetConst q R * u ≤
        16 * Real.exp 1 * s :=
      (mul_le_mul_iff_right₀ (zero_lt_one.trans_le hs)).mp (by
        nlinarith only [hc1, mul_le_mul_of_nonneg_left hθB
          (by positivity : 0 ≤ 16 * Real.exp 1)])
    have hu1 : u ≠ 1 := ne_of_lt ((hu.trans hrad).trans_lt (by norm_num))
    refine ⟨hlo, hupper, ?_, ?_⟩
    · rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      linarith only [hupper, hc]
    · simpa only [u, sub_sub_cancel] using
        congrArg (fun t : ℝ ↦ Real.log t / u) (Entropy.surprisalMoment_eq_sum_rpow hp hu1)

end TNLean.MPS.AreaLaw
