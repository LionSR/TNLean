/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisTwoDimensional
import TNLean.Lattice.GraphDegreeGrowth

/-!
# A uniform summed bound for a two-dimensional ground space

The small spectral denominator in Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `oibu` (lines 1678–1694), is removed by choosing a compression with maximal spectral
spread after normalization by the original term norm. The bound by the spectral spread
and the bound by the commutator divided by that spread give the square root of the
commutator decay. The norm budget then sums this decay uniformly in the number of sites.

**Local fix (quantitative constant):** the uniform bound uses half the commutator decay
rate and the displayed geometric constant, in place of the printed dependence on a
compressed spectral gap. See `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`.

**Scope restriction (geometric growth):** the physical ground-space sum assumes a
polynomial sphere bound with constants independent of system size. This is not implied
by the metric and finite-range hypotheses of source lines 169–190. The unrestricted
version of eq. `oibu` is false on general metric lattices; a mathematical counterexample
is given in `docs/paper-gaps/hastings05_tree_basis_counterexample.tex`. The role of growth
is recorded in `docs/paper-gaps/hastings05_geometric_growth_scope.tex`. The abstract spectral and
weighted-budget lemmas do not acquire this restriction.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

section WeightedRow

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

end WeightedRow

noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) : InnerProductSpace ℂ (groundEigenspace H E₀) :=
  (groundEigenspace H E₀).innerProductSpace

section Graph

open GaussianFilter Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]

set_option backward.isDefEq.respectTransparency false in
/-- There is an actual orthonormal basis of a two-dimensional ground space for which the
sum of the off-diagonal parts is bounded only by the local norm budget, range, gap and
graph growth. No lower bound on a compressed spectral gap is assumed. The rate is half
the commutator decay rate. This proves the qualitative size independence of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1678–1694, with an explicit
corrected constant; see `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`. -/
theorem exists_twoDimensional_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le [NeZero d]
    (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    (hdim : Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀) = 2) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ (groundEigenspace (∑ k, h k) E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (ι → Fin d)))
        (groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm q ΔE (∑ k, h k) (h i)))‖ ≤
        Real.sqrt (commutatorConst R vR b₀ |Kg| kg *
          Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1))) *
          (|b₀| * (|Kg| * shellSumConst (commutatorRate R vR b₀ ΔE / 2) kg)) := by
  classical
  let K := groundEigenspace (∑ k, h k) E₀
  let B := fun i => groundSpaceCompression (∑ k, h k) E₀ (h i)
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
  have hC : 0 ≤ C := mul_nonneg
    (le_trans (by norm_num) (six_le_commutatorConst R vR b₀ (abs_nonneg Kg) kg))
    (Real.exp_pos _).le
  have hGrow : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r => (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  let f := fun j i => if G.edist (a j) (a i) = ⊤ then 0 else
    Real.exp (-(γ / 2 * ((G.edist (a j) (a i)).toNat : ℝ)))
  have hf (j i : κ) : 0 ≤ f j i := by dsimp only [f]; split_ifs <;> positivity
  have hnorm (i : κ) : ‖B i‖ ≤ ‖h i‖ := norm_groundSpaceCompression_le _ _ _
  have hcomm (i j : κ) : ‖B j * B i - B i * B j‖ ≤ C * ‖h j‖ * ‖h i‖ * (f j i) ^ 2 := by
    have heq : (f j i) ^ 2 = if G.edist (a j) (a i) = ⊤ then 0 else
        Real.exp (-(γ * ((G.edist (a j) (a i)).toNat : ℝ))) := by
      dsimp only [f]
      split_ifs
      · simp
      · rw [← Real.exp_nat_mul]
        congr 1
        ring
    rw [heq]
    exact (norm_groundSpaceCompression_commutator_le _ _ _ _).trans
      (norm_groundCompression_commutator_le_exp_edist G X a ha h hHerm hSupport R hDiam vR
        hCard b₀ hBudget |Kg| kg hGrow hΔE hH hgap i j)
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_norm_inner_le_sqrt_commutator_decay B
    (fun i => isSelfAdjoint_groundSpaceCompression _ _ (hHerm i)) hdim
    (fun i => ‖h i‖) (fun i => norm_nonneg _) hnorm hC f hf hcomm
  refine ⟨b, ?_⟩
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  have hv : Orthonormal ℂ (fun c => (b c : EuclideanSpace ℂ (ι → Fin d))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hbound0 : 0 ≤ Real.sqrt C * (|b₀| * (|Kg| * shellSumConst (γ / 2) kg)) := by
    have := shellSumConst_nonneg (show 0 < γ / 2 by positivity) kg
    positivity
  rcases hb with hzero | ⟨j, hb⟩
  · refine (show ∑ i, ‖offDiagonalPartFamily _ _‖ ≤ 0 from ?_).trans hbound0
    apply Finset.sum_nonpos
    intro i _
    simpa only [mul_zero] using norm_offDiagonalPartFamily_le hv
      (groundCompression (∑ k, h k) E₀ (h i)) le_rfl (fun c e hce => by
        have heq := hzero i c e hce
        change ⟪(b c : EuclideanSpace ℂ (ι → Fin d)),
          groundCompression (∑ k, h k) E₀ (h i) (b e)⟫_ℂ = 0 at heq
        simpa only [heq, norm_zero] using (le_rfl : (0 : ℝ) ≤ 0))
  · have hterm (i : κ) :
        ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (ι → Fin d)))
          (groundCompression (∑ k, h k) E₀ (h i))‖ ≤ Real.sqrt C * ‖h i‖ * f j i := by
      simpa only [Nat.reduceSub, Nat.cast_one, one_mul] using norm_offDiagonalPartFamily_le hv
        (groundCompression (∑ k, h k) E₀ (h i))
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (hf j i))
        (fun c e hce => hb i c e hce)
    calc _ ≤ ∑ i, Real.sqrt C * ‖h i‖ * f j i := Finset.sum_le_sum fun i _ => hterm i
      _ = Real.sqrt C * ∑ i, ‖h i‖ * f j i := by simp only [← mul_assoc, Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply sum_weight_mul_exp_neg_edist_le G a (fun i => ‖h i‖) (fun i => norm_nonneg _)
          |b₀| _ (a j) |Kg| kg (hGrow (a j)) (by positivity : 0 < γ / 2)
        exact fun x ↦ (sum_weight_anchor_le_of_support_budget X a ha
          (fun i ↦ ‖h i‖) (fun i ↦ norm_nonneg _) b₀ hBudget x).trans (le_abs_self b₀)

end Graph

end TNLean.Lattice
