/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutatorSum
import TNLean.Lattice.GraphDegreeGrowth

/-!
# Weighted exponential sums over a graph

The polynomial sphere bound gives the weighted geometric sum used in Hastings,
arXiv:cond-mat/0508554v3, equation `oibu`, lines 1689–1694. This geometric
assumption is explicit and need not follow from bounded degree.
-/

namespace TNLean.Lattice

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A weighted exponential row sum, with a bound on the weights at each anchor.
This is the geometric summation in Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `oibu`, lines 1689–1694, valid at any positive rate. -/
theorem sum_weight_mul_exp_neg_edist_le (G : SimpleGraph ι) (a : κ → ι)
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ℝ)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i => a i = x), w i ≤ B)
    (x : ι) (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ r : ℕ,
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {β : ℝ} (hβ : 0 < β) :
    ∑ i, w i * (if G.edist x (a i) = ⊤ then 0 else
      Real.exp (-(β * ((G.edist x (a i)).toNat : ℝ)))) ≤ B * (Kg * shellSumConst β kg) := by
  classical
  let f : ι → ℝ := fun y => if G.edist x y = ⊤ then 0 else
    Real.exp (-(β * ((G.edist x y).toNat : ℝ)))
  have hf (y : ι) : 0 ≤ f y := by dsimp only [f]; split_ifs <;> positivity
  have hB : 0 ≤ B := (Finset.sum_nonneg fun i _ => hw i).trans (hBudget x)
  have hgroup := sum_weight_mul_comp_le_budget_mul_sum a w B hBudget f hf
  have hsites : ∑ y, f y ≤ Kg * shellSumConst β kg := by
    have heq : ∑ y, f y = ∑ y ∈ Finset.univ.filter (fun y => G.edist x y ≠ ⊤),
        Real.exp (-(β * ((G.edist x y).toNat : ℝ))) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      dsimp only [f]
      split_ifs <;> simp_all
    rw [heq]
    exact sum_exp_neg_edist_le G x Kg kg hGrowth hβ
  exact hgroup.trans (mul_le_mul_of_nonneg_left hsites hB)

end TNLean.Lattice
