/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ApproximateDiagonalization.DecayKernel
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Exponential graph kernels under spectral refinement

Hastings, arXiv:cond-mat/0508554v3, lines 1689–1708.
Disconnected components have zero mutual kernel value.
-/

open ApproximateDiagonalization

namespace TNLean.Lattice

variable {ι : Type*}

/-- Exponential graph decay, set to zero between disconnected components. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm` and lines 1689–1708. -/
noncomputable def graphDecayKernel (G : SimpleGraph ι) (γ : ℝ) (i j : ι) : ℝ :=
  if G.edist i j = ⊤ then 0 else Real.exp (-(γ * ((G.edist i j).toNat : ℝ)))

theorem graphDecayKernel_nonneg (G : SimpleGraph ι) (γ : ℝ) (i j : ι) :
    0 ≤ graphDecayKernel G γ i j := by
  unfold graphDecayKernel
  split_ifs <;> positivity

theorem graphDecayKernel_le_one (G : SimpleGraph ι) {γ : ℝ} (hγ : 0 ≤ γ) (i j : ι) :
    graphDecayKernel G γ i j ≤ 1 := by
  unfold graphDecayKernel
  split_ifs
  · norm_num
  · exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hγ (Nat.cast_nonneg _)))

theorem graphDecayKernel_symm (G : SimpleGraph ι) (γ : ℝ) (i j : ι) :
    graphDecayKernel G γ i j = graphDecayKernel G γ j i := by
  simp only [graphDecayKernel, G.edist_comm (u := i) (v := j)]

/-- The graph triangle inequality in multiplicative form, including infinite distances.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem graphDecayKernel_mul_le (G : SimpleGraph ι) {γ : ℝ} (hγ : 0 ≤ γ) (i j l : ι) :
    graphDecayKernel G γ i j * graphDecayKernel G γ j l ≤ graphDecayKernel G γ i l := by
  classical
  by_cases hij : G.edist i j = ⊤
  · simpa only [graphDecayKernel, hij, ↓reduceIte, zero_mul] using
      graphDecayKernel_nonneg G γ i l
  by_cases hjl : G.edist j l = ⊤
  · simpa only [graphDecayKernel, hjl, ↓reduceIte, mul_zero] using
      graphDecayKernel_nonneg G γ i l
  have hsum : G.edist i j + G.edist j l ≠ ⊤ := by simp [hij, hjl]
  have htri := G.edist_triangle (u := i) (v := j) (w := l)
  have hil : G.edist i l ≠ ⊤ := fun h => hsum (top_le_iff.mp (h ▸ htri))
  have hnat := ENat.toNat_le_toNat htri hsum
  rw [ENat.toNat_add hij hjl] at hnat
  have hreal : ((G.edist i l).toNat : ℝ) ≤
      ((G.edist i j).toNat : ℝ) + ((G.edist j l).toNat : ℝ) := by exact_mod_cast hnat
  simp only [graphDecayKernel, hij, hjl, hil, ↓reduceIte]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hreal hγ]

/-- Taking square roots `n` times divides the graph exponential rate by `2^n`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, with the
cross terms of each spectral refinement retained. -/
theorem sqrtKernel_graphDecayKernel (G : SimpleGraph ι) (γ : ℝ) (n : ℕ) (i j : ι) :
    sqrtKernel (graphDecayKernel G γ) n i j = graphDecayKernel G (γ / 2 ^ n) i j := by
  induction n with
  | zero => simp only [sqrtKernel_zero, pow_zero, div_one]
  | succ n ih =>
    rw [sqrtKernel_succ, ih]
    unfold graphDecayKernel
    split_ifs
    · simp
    · rw [← Real.exp_half]
      congr 1
      rw [pow_succ]
      ring


end TNLean.Lattice
