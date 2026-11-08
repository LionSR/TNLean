/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GraphDegreeGrowth
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exponentially weighted tails on graphs of bounded degree

A bound on the degree implies a uniform bound for an exponential row sum
whenever the decay rate exceeds `log(D+1)`. With a local weight budget at
each anchor, the tail beyond distance `m` decays at half that excess rate.
Disconnected anchors contribute zero.

These estimates sum the omitted interactions in Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1469–1505, without a
polynomial growth hypothesis. The rate can be chosen freely before the
Lieb–Robinson estimate is applied.
-/

open scoped Topology

namespace TNLean.Lattice

/-- Exponential decay in support separation gives exponential decay in anchor distance,
including infinite distance. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `blecm`, lines 1548–1601. -/
theorem le_anchorDecay_of_separated_exp {z C A B γ : ℝ} (hγ : 0 < γ) (hC : 2 ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (R : ℕ) (δ : ℕ∞) (htriv : z ≤ 2 * A * B)
    (hsep : ∀ l : ℕ, ((2 * R + l : ℕ) : ℕ∞) < δ →
      z ≤ C * A * B * Real.exp (-(γ * l))) :
    z ≤ C * Real.exp (γ * (2 * R + 1)) * A * B *
      (if δ = ⊤ then 0 else Real.exp (-(γ * (δ.toNat : ℝ)))) := by
  split_ifs with htop
  · rw [mul_zero]
    have hlim : Filter.Tendsto (fun l : ℕ => C * A * B * Real.exp (-(γ * l)))
        Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun l : ℕ => γ * (l : ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (C * A * B)
    exact ge_of_tendsto' hlim fun l => hsep l (by rw [htop]; exact ENat.natCast_lt_top _)
  · let D := δ.toNat
    have hD : δ = (D : ℕ∞) := (ENat.natCast_toNat htop).symm
    by_cases hfar : 2 * R + 1 < D
    · have hl := hsep (D - (2 * R + 1)) (by rw [hD]; exact_mod_cast (by omega))
      refine hl.trans (le_of_eq ?_)
      have hcast : ((D - (2 * R + 1) : ℕ) : ℝ) = (D : ℝ) - (2 * R + 1) := by
        rw [Nat.cast_sub hfar.le]; push_cast; ring
      rw [hcast, show -(γ * ((D : ℝ) - (2 * R + 1))) = γ * (2 * R + 1) + -(γ * D) by ring,
        Real.exp_add]
      ring
    · push Not at hfar
      have hexp : 1 ≤ Real.exp (γ * (2 * R + 1)) * Real.exp (-(γ * D)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have : (D : ℝ) ≤ 2 * R + 1 := by exact_mod_cast hfar
        nlinarith
      have hAB : 0 ≤ A * B := mul_nonneg hA hB
      have hCAB : 0 ≤ C * A * B := by positivity
      calc z ≤ 2 * A * B := htriv
        _ ≤ C * A * B * 1 := by nlinarith [mul_le_mul_of_nonneg_right hC hAB]
        _ ≤ C * A * B * (Real.exp (γ * (2 * R + 1)) * Real.exp (-(γ * D))) :=
          mul_le_mul_of_nonneg_left hexp hCAB
        _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The sum of an exponential above the degree growth rate is uniformly bounded. -/
theorem sum_exp_neg_edist_le_degree (G : SimpleGraph ι) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ x, G.degree x ≤ D) (x : ι) {μ : ℝ}
    (hμ : Real.log (D + 1) < μ) :
    ∑ y, (if G.edist x y = ⊤ then 0 else
      Real.exp (-(μ * ((G.edist x y).toNat : ℝ)))) ≤
        1 / (1 - Real.exp (-(μ - Real.log (D + 1)))) := by
  classical
  let S := Finset.univ.filter fun y ↦ G.edist x y ≠ ⊤
  let r : ι → ℕ := fun y ↦ (G.edist x y).toNat
  let q := Real.exp (-(μ - Real.log (D + 1)))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hfib (n : ℕ) : ((S.filter fun y ↦ r y = n).card : ℝ) ≤ (D + 1 : ℝ) ^ n := by
    have hsub : (S.filter fun y ↦ r y = n) ⊆ graphClosedBall G x n := by
      intro y hy
      obtain ⟨hyS, hyn⟩ := Finset.mem_filter.mp hy
      have hyfin := (Finset.mem_filter.mp hyS).2
      rw [mem_graphClosedBall, ← hyn]
      exact (ENat.natCast_toNat hyfin).ge
    exact_mod_cast (Finset.card_le_card hsub).trans (card_graphClosedBall_le G D hD x n)
  have hgeom (n : ℕ) : (D + 1 : ℝ) ^ n * Real.exp (-(μ * n)) = q ^ n := by
    have hpow : (D + 1 : ℝ) ^ n = Real.exp (Real.log (D + 1) * n) := by
      rw [mul_comm (Real.log (D + 1)), Real.exp_nat_mul, Real.exp_log (by positivity)]
    rw [hpow, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  have heq : ∑ y, (if G.edist x y = ⊤ then 0 else Real.exp (-(μ * (r y : ℝ)))) =
      ∑ y ∈ S, Real.exp (-(μ * (r y : ℝ))) := by
    simp only [S, Finset.sum_filter]
    exact Finset.sum_congr rfl fun y _ ↦ by split_ifs <;> simp_all
  rw [heq]
  calc ∑ y ∈ S, Real.exp (-(μ * (r y : ℝ)))
      = ∑ n ∈ S.image r, ∑ y ∈ S.filter (fun y ↦ r y = n),
          Real.exp (-(μ * (r y : ℝ))) :=
        (Finset.sum_fiberwise_of_maps_to (fun y hy ↦ Finset.mem_image_of_mem r hy) _).symm
    _ = ∑ n ∈ S.image r, ((S.filter fun y ↦ r y = n).card : ℝ) *
          Real.exp (-(μ * n)) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_congr rfl (fun y hy ↦ by rw [(Finset.mem_filter.mp hy).2]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ S.image r, (D + 1 : ℝ) ^ n * Real.exp (-(μ * n)) :=
      Finset.sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_right (hfib n) (Real.exp_pos _).le
    _ = ∑ n ∈ S.image r, q ^ n := Finset.sum_congr rfl fun n _ ↦ hgeom n
    _ ≤ ∑' n : ℕ, q ^ n :=
      (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun n _ ↦ pow_nonneg hq0 n)
    _ = _ := by rw [tsum_geometric_of_lt_one hq0 hq1]; simp only [one_div, q]


/-- A degree bound and an anchor budget give an exponentially decaying weighted tail. -/
theorem sum_weight_exp_neg_edist_tail_le_degree {κ : Type*} [Fintype κ]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ x, G.degree x ≤ D)
    (a : κ → ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ y, ∑ k ∈ Finset.univ.filter (fun k ↦ a k = y), w k ≤ B)
    (x : ι) (t : Finset κ) (m : ℕ)
    (hsep : ∀ k ∈ t, (m : ℕ∞) ≤ G.edist x (a k)) {μ : ℝ}
    (hμ : Real.log (D + 1) < μ) :
    let β := (μ - Real.log (D + 1)) / 2
    ∑ k ∈ t, w k * (if G.edist x (a k) = ⊤ then 0 else
      Real.exp (-(μ * ((G.edist x (a k)).toNat : ℝ)))) ≤
        B * Real.exp (-(β * m)) / (1 - Real.exp (-β)) := by
  classical
  intro β
  have hβ : 0 < β := half_pos (sub_pos.mpr hμ)
  have hη : Real.log (D + 1) < μ - β := by dsimp [β]; linarith
  let f : ℝ → ι → ℝ := fun η y ↦ if G.edist x y = ⊤ then 0 else
    Real.exp (-(η * ((G.edist x y).toNat : ℝ)))
  have hf (η : ℝ) (y : ι) : 0 ≤ f η y := by dsimp [f]; split_ifs <;> positivity
  have hpoint (k : κ) (hk : k ∈ t) : w k * f μ (a k) ≤
      Real.exp (-(β * m)) * (w k * f (μ - β) (a k)) := by
    by_cases htop : G.edist x (a k) = ⊤
    · simp [f, htop]
    have hm : (m : ℝ) ≤ ((G.edist x (a k)).toNat : ℝ) := by
      have hmn : m ≤ (G.edist x (a k)).toNat := by
        exact_mod_cast (show (m : ℕ∞) ≤ ((G.edist x (a k)).toNat : ℕ) by
          simpa only [ENat.natCast_toNat htop] using hsep k hk)
      exact_mod_cast hmn
    have he : Real.exp (-(μ * ((G.edist x (a k)).toNat : ℝ))) ≤
        Real.exp (-(β * m)) * Real.exp (-((μ - β) * ((G.edist x (a k)).toNat : ℝ))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    simp only [f, htop, ↓reduceIte]
    calc _ ≤ w k * (Real.exp (-(β * m)) *
        Real.exp (-((μ - β) * ((G.edist x (a k)).toNat : ℝ)))) :=
          mul_le_mul_of_nonneg_left he (hw k)
      _ = _ := by ring
  have hgroup := sum_weight_mul_comp_le_budget_mul_sum a w B hBudget
    (f (μ - β)) (hf _)
  have hrow := sum_exp_neg_edist_le_degree G D hD x hη
  have hrate : μ - β - Real.log (D + 1) = β := by dsimp [β]; ring
  rw [hrate] at hrow
  calc ∑ k ∈ t, w k * f μ (a k)
      ≤ ∑ k ∈ t, Real.exp (-(β * m)) * (w k * f (μ - β) (a k)) :=
        Finset.sum_le_sum hpoint
    _ = Real.exp (-(β * m)) * ∑ k ∈ t, w k * f (μ - β) (a k) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-(β * m)) * ∑ k, w k * f (μ - β) (a k) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ ↦ mul_nonneg (hw k) (hf _ _))
    _ ≤ Real.exp (-(β * m)) * (B * ∑ y, f (μ - β) y) :=
      mul_le_mul_of_nonneg_left hgroup (Real.exp_pos _).le
    _ ≤ Real.exp (-(β * m)) * (B * (1 / (1 - Real.exp (-β)))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hrow hB
    _ = _ := by ring

end TNLean.Lattice
