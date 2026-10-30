/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTruncation
import TNLean.Lattice.GraphDegreeTail

/-!
# Truncation by a weighted sum of omitted interactions

The Duhamel comparison is first stated with separate commutator bounds for every
omitted term. Numerical finite-support Lieb–Robinson propagation then gives an
exponential weight for each omitted anchor. Summing these weights uses no assumption
on the cardinality of the region containing the retained interactions.

On a graph of degree at most `D`, choose `μ > log(D+1)`. The weighted omitted tail
beyond distance `m` decays at rate `(μ-log(D+1))/2`, with a constant controlled by the
anchor norm budget. The Gaussian time window remains free, for the subsequent choice
of the filter variance and the positive exponential rate in the projection radius.
The passage from a physical metric cutoff to this graph-distance tail is geometric.

Source: Hastings, arXiv:cond-mat/0508554v3, eqs. `thib`, `truncb` and `apb`,
`proj3new.tex`, lines 1469–1533. These estimates supply the weighted-tail extension
planned in `docs/paper-gaps/hastings05_geometric_growth_scope.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice

section Abstract

variable {ν κ : Type*} [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]

/-- Termwise commutator estimates give a truncation bound without a shell-size factor.
Hastings, arXiv:cond-mat/0508554v3, lines 1469–1505 and 1524–1533. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_of_commutator_bounds
    (h : κ → Matrix ν ν ℂ) (hHerm : ∀ k, (h k).IsHermitian) (s : Finset κ)
    (W : Matrix ν ν ℂ) {q ΔE T : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T)
    (C : κ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hcomm : ∀ k ∉ s, ∀ u ∈ Set.Icc (-T) T,
      ‖h k * (hermitianUnitaryPath (∑ j ∈ s, h j) u * W *
          hermitianUnitaryPath (∑ j ∈ s, h j) (-u)) -
        (hermitianUnitaryPath (∑ j ∈ s, h j) u * W *
          hermitianUnitaryPath (∑ j ∈ s, h j) (-u)) * h k‖ ≤ C k) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W -
        gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W‖ ≤
      T * (∑ k ∈ sᶜ, C k) + 2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  have hH : (∑ k, h k).IsHermitian := Matrix.isHermitian_sum _ fun k _ ↦ hHerm k
  have hHs : (∑ k ∈ s, h k).IsHermitian := Matrix.isHermitian_sum _ fun k _ ↦ hHerm k
  have hsum0 : 0 ≤ ∑ k ∈ sᶜ, C k := Finset.sum_nonneg fun k _ ↦ hC k
  have hstep (u : ℝ) (hu : u ∈ Set.Icc (-T) T) :
      ‖((∑ k, h k) - ∑ k ∈ s, h k) *
          (hermitianUnitaryPath (∑ j ∈ s, h j) u * W *
            hermitianUnitaryPath (∑ j ∈ s, h j) (-u)) -
        (hermitianUnitaryPath (∑ j ∈ s, h j) u * W *
          hermitianUnitaryPath (∑ j ∈ s, h j) (-u)) *
          ((∑ k, h k) - ∑ k ∈ s, h k)‖ ≤ ∑ k ∈ sᶜ, C k := by
    rw [← Finset.sum_compl_add_sum s h, add_sub_cancel_right,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦
      hcomm k (Finset.mem_compl.mp hk) u hu)
  have hf := norm_gaussianFilteredTerm_sub_le (ΔE := ΔE) hq hH hHs W hT
    (ε := (∑ k ∈ sᶜ, C k) * T) (mul_nonneg hsum0 hT) (fun t ht ↦ by
      have htT : |t| ≤ T := abs_le.mpr ht
      refine (norm_conj_sub_conj_le hH W fun u hu ↦ hstep u ?_).trans ?_
      · exact abs_le.mp ((by simpa using Set.abs_sub_left_of_mem_uIcc hu : |u| ≤ |t|).trans htT)
      · exact mul_le_mul_of_nonneg_left htT hsum0)
  simpa only [mul_comm T] using hf

end Abstract

section Graph

open GaussianFilter

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Finite-support propagation in the distance between two anchors, with zero kernel
between components. Hastings, arXiv:cond-mat/0508554v3, lines 1469–1505. -/
theorem norm_commutator_heisenbergEvolution_le_anchor_kernel
    (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ y ∈ X k, G.edist x y ≤ R)
    (vR : ℕ) (hvR : 1 ≤ vR) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ X j), ‖h j‖ ≤ b₀)
    (z : ι) (S : Finset ι) (hSrad : ∀ x ∈ S, G.edist z x ≤ R)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι))
    (b : ι) (Y : Finset ι) (hYrad : ∀ y ∈ Y, G.edist y b ≤ R)
    {B : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hB : B ∈ supportedOperators d (Y : Set ι))
    {μ : ℝ} (hμ : 0 < μ) (t : ℝ) :
    ‖B * heisenbergEvolution (∑ k, h k) t W -
        heisenbergEvolution (∑ k, h k) t W * B‖ ≤
      4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * ‖B‖ *
        Real.exp ((4 * vR * |b₀| * Real.exp (2 * μ * R)) * |t|) *
        (if G.edist z b = ⊤ then 0 else Real.exp (-(μ * ((G.edist z b).toNat : ℝ)))) := by
  let v : ℝ := 4 * vR * |b₀| * Real.exp (2 * μ * R)
  let C : ℝ := 4 * ((S.card : ℝ) + 1) * Real.exp (v * |t|)
  have hC : 2 ≤ C := by
    have he : 1 ≤ Real.exp (v * |t|) := Real.one_le_exp (by dsimp [v]; positivity)
    calc 2 ≤ 4 * ((S.card : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) S.card; linarith
      _ ≤ C := le_mul_of_one_le_right (by positivity) he
  have hH : (∑ k, h k).IsHermitian := Matrix.isHermitian_sum _ fun k _ ↦ hHerm k
  have hnorm : ‖heisenbergEvolution (∑ k, h k) t W‖ = ‖W‖ :=
    norm_intertwinerIntegrand hH hH W t
  have htriv : ‖B * heisenbergEvolution (∑ k, h k) t W -
      heisenbergEvolution (∑ k, h k) t W * B‖ ≤ 2 * ‖W‖ * ‖B‖ := by
    simpa only [hnorm] using norm_commutator_le B
      (heisenbergEvolution (∑ k, h k) t W)
  have hsep (l : ℕ) (hl : ((2 * R + l : ℕ) : ℕ∞) < G.edist z b) :
      ‖B * heisenbergEvolution (∑ k, h k) t W -
          heisenbergEvolution (∑ k, h k) t W * B‖ ≤
        C * ‖W‖ * ‖B‖ * Real.exp (-(μ * l)) := by
    have hd (x : ι) (hx : x ∈ S) (y : ι) (hy : y ∈ Y) :
        (l : ℕ∞) ≤ G.edist x y := by
      by_contra hn
      have hxy : G.edist x y ≤ l := (lt_of_not_ge hn).le
      have hz : G.edist z b ≤ ((2 * R + l : ℕ) : ℕ∞) := by
        calc G.edist z b ≤ G.edist z x + G.edist x y + G.edist y b :=
            (G.edist_triangle (u := z) (v := y) (w := b)).trans
              (add_le_add (G.edist_triangle (u := z) (v := x) (w := y))
                (le_refl (G.edist y b)))
          _ ≤ R + l + R := add_le_add (add_le_add (hSrad x hx) hxy) (hYrad y hy)
          _ = ((2 * R + l : ℕ) : ℕ∞) := by push_cast; ring
      exact (not_le_of_gt hl) hz
    have hLR := norm_heisenberg_commutator_le_graphDistance_finsets_numeric G X a ha
      h hHerm hSupport R hDiam vR hvR hCard b₀ hBudget S hW Y hB μ hμ.le l hd t
    calc _ = ‖heisenbergEvolution (∑ k, h k) t W * B -
          B * heisenbergEvolution (∑ k, h k) t W‖ := norm_sub_rev _ _
      _ ≤ 4 * (S.card : ℝ) * ‖W‖ * ‖B‖ *
          Real.exp (v * |t| - μ * l) := hLR
      _ = 4 * (S.card : ℝ) * Real.exp (v * |t|) * ‖W‖ * ‖B‖ *
          Real.exp (-(μ * l)) := by rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ C * ‖W‖ * ‖B‖ * Real.exp (-(μ * l)) := by dsimp [C]; gcongr; linarith
  have hbound := le_anchorDecay_of_separated_exp hμ hC (norm_nonneg W) (norm_nonneg B)
    R (G.edist z b) htriv hsep
  exact hbound.trans_eq (by dsimp [C, v]; ring)

/-- The omitted interactions are summed with their individual exponential anchor weights.
The retained family is arbitrary; no bound on its containing region is assumed.
Hastings, arXiv:cond-mat/0508554v3, lines 1469–1505 and 1524–1533. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_anchor_sum [DecidableEq κ]
    (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ y ∈ X k, G.edist x y ≤ R)
    (vR : ℕ) (hvR : 1 ≤ vR) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ X j), ‖h j‖ ≤ b₀)
    (s : Finset κ) (z : ι) (S : Finset ι) (hSrad : ∀ x ∈ S, G.edist z x ≤ R)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι))
    {q ΔE μ T : ℝ} (hq : 0 ≤ q) (hμ : 0 < μ) (hT : 0 ≤ T) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W -
        gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W‖ ≤
      4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * T *
          Real.exp ((4 * vR * |b₀| * Real.exp (2 * μ * R)) * T) *
          (∑ k ∈ sᶜ, ‖h k‖ * (if G.edist z (a k) = ⊤ then 0 else
            Real.exp (-(μ * ((G.edist z (a k)).toNat : ℝ))))) +
        2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  classical
  let v : ℝ := 4 * vR * |b₀| * Real.exp (2 * μ * R)
  let A : ℝ := 4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * Real.exp (v * T)
  let w : κ → ℝ := fun k ↦ ‖h k‖ * (if G.edist z (a k) = ⊤ then 0 else
    Real.exp (-(μ * ((G.edist z (a k)).toNat : ℝ))))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw (k : κ) : 0 ≤ w k := by dsimp [w]; split_ifs <;> positivity
  have hBudget' (x : ι) :
      ∑ j ∈ Finset.univ.filter (fun j : s ↦ x ∈ X j), ‖h j‖ ≤ b₀ := by
    rw [Finset.sum_filter, Finset.sum_coe_sort s (fun k : κ ↦ if x ∈ X k then ‖h k‖ else 0)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun j _ _ ↦ ?_)) ?_
    · split_ifs <;> simp
    · simpa only [Finset.sum_filter] using hBudget x
  have hpoint (k : κ) (_hk : k ∉ s) (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖h k * (hermitianUnitaryPath (∑ j ∈ s, h j) t * W *
          hermitianUnitaryPath (∑ j ∈ s, h j) (-t)) -
        (hermitianUnitaryPath (∑ j ∈ s, h j) t * W *
          hermitianUnitaryPath (∑ j ∈ s, h j) (-t)) * h k‖ ≤ A * w k := by
    have hb := norm_commutator_heisenbergEvolution_le_anchor_kernel G
      (fun j : s ↦ X j) (fun j : s ↦ a j) (fun j ↦ ha j)
      (fun j : s ↦ h j) (fun j ↦ hHerm j) (fun j ↦ hSupport j)
      R (fun j ↦ hDiam j) vR hvR (fun j ↦ hCard j) b₀ hBudget'
      z S hSrad hW (a k) (X k) (fun y hy ↦ hDiam k y hy (a k) (ha k)) (hSupport k) hμ t
    rw [Finset.sum_coe_sort] at hb
    have he : Real.exp (v * |t|) ≤ Real.exp (v * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by dsimp [v]; positivity))
    refine hb.trans ?_
    change _ ≤ A * w k
    change 4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * ‖h k‖ *
      Real.exp (v * |t|) * _ ≤ _
    calc _ = (4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * w k) *
          Real.exp (v * |t|) := by dsimp [w]; ring
      _ ≤ (4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * w k) *
          Real.exp (v * T) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = A * w k := by dsimp [A]; ring
  have hf := norm_gaussianFilteredTerm_sub_truncated_le_of_commutator_bounds (ΔE := ΔE)
    h hHerm s W hq hT
    (fun k ↦ A * w k) (fun k ↦ mul_nonneg hA (hw k)) hpoint
  rw [← Finset.mul_sum] at hf
  exact hf.trans_eq (by dsimp [A, w, v]; ring)

/-- A bounded-degree weighted tail controls an arbitrary truncation whose omitted
anchors are far away. There is no assumption on the size of the retained region.
Hastings, arXiv:cond-mat/0508554v3, lines 1469–1505 and 1524–1533. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_degree_tail
    (G : SimpleGraph ι) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ x, G.degree x ≤ D)
    (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ y ∈ X k, G.edist x y ≤ R)
    (vR : ℕ) (hvR : 1 ≤ vR) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ X j), ‖h j‖ ≤ b₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hAnchorBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ a j = x), ‖h j‖ ≤ B)
    (s : Finset κ) (z : ι) (S : Finset ι) (hSrad : ∀ x ∈ S, G.edist z x ≤ R)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι))
    (m : ℕ) (hsep : ∀ k ∉ s, (m : ℕ∞) ≤ G.edist z (a k))
    {q ΔE μ T : ℝ} (hq : 0 ≤ q) (hμ : Real.log (D + 1) < μ) (hT : 0 ≤ T) :
    let β := (μ - Real.log (D + 1)) / 2
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W -
        gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W‖ ≤
      4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * T *
          Real.exp ((4 * vR * |b₀| * Real.exp (2 * μ * R)) * T) *
          (B * Real.exp (-(β * m)) / (1 - Real.exp (-β))) +
        2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  classical
  intro β
  have hμ0 : 0 < μ := lt_of_le_of_lt (Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) D
    linarith : (1 : ℝ) ≤ (D : ℝ) + 1)) hμ
  have hf := norm_gaussianFilteredTerm_sub_truncated_le_anchor_sum (ΔE := ΔE) G X a ha h hHerm
    hSupport R hDiam vR hvR hCard b₀ hBudget s z S hSrad hW hq hμ0 hT
  have ht := sum_weight_exp_neg_edist_tail_le_degree G D hD a (fun k ↦ ‖h k‖)
    (fun k ↦ norm_nonneg _) B hB hAnchorBudget z sᶜ m
    (fun k hk ↦ hsep k (Finset.mem_compl.mp hk)) hμ
  refine hf.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_left ht (by positivity)

end Graph

end TNLean.Lattice
