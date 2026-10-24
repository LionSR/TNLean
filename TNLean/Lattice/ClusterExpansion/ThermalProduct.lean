/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.ClusterPart

/-!
# Products of cluster parts at every temperature

At arbitrary temperature Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1322–1341), writes `e^{-βH}` as the product of
`n` factors `e^{-βH/n}` and expands each factor in clusters. The operator `ρ_m` collects the
products in which at least `m` of the factors are replaced by cluster parts `ρ(β/n, C_j)` of
large clusters, and its bound rests on the bound of a single such product.

For a cluster `C_j` with boundary `B_j` in each factor `j < n`, consider the product
`ρ(β/n, C_0) ρ(β/n, C_1) ⋯ ρ(β/n, C_{n-1})`. A factor with `C_j = B_j = ∅` is the thermal factor
`e^{-βH/n}`. If `‖h_k‖ ≤ J` on every cluster and boundary and `n_{C_j} + n_{B_j} ≤ S n_{C_j}`, then
for every observable `O`

`|Tr (O ρ(β/n, C_0) ⋯ ρ(β/n, C_{n-1}))| ≤ ‖O‖ y^{∑_j n_{C_j}} Tr e^{-βH}`,
`y = (e^{Jβ/n} - 1) e^{SJβ/n}`.

For a single cluster part between two thermal factors this is
`norm_trace_mul_exp_mul_clusterPart_mul_exp_le_pow`, the bound stated at lines 1322–1333.

## Proof

Each cluster part is the alternating sum of `e^{-(1/n)(β W_j + β h_E)}` over `E ⊆ C_j`, with
`W_j = H - H_{B_j} - H_{C_j}`. `Matrix.norm_trace_list_prod_mul_sum_powerset_exp_le_pow`, with
weight `1/n` on every factor, bounds the trace of the product by
`‖O‖ ∏_j (e^{Jβ/n} - 1)^{n_{C_j}} (Tr e^{-β W_j})^{1/n}`. Each
`Tr e^{-β W_j} ≤ e^{(n_{C_j} + n_{B_j}) J β} Tr e^{-βH}` by `re_trace_exp_sub_sum_sub_sum_le`, and
`n_{C_j} + n_{B_j} ≤ S n_{C_j}` turns the exponential into `(e^{SJβ/n})^{n_{C_j}}`. The `n`
factors `(Tr e^{-βH})^{1/n}` multiply to `Tr e^{-βH}`.

## Main results

* `TNLean.Lattice.ClusterExpansion.clusterPart_empty_empty`: a factor without cluster or
  boundary is the thermal factor.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_list_prod_clusterPart_le_pow`: the bound
  above.

## References

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1322–1341.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice.ClusterExpansion

open Finset Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
/-- A factor without cluster and boundary is the thermal factor: `ρ(β, ∅) = e^{-βH}`. -/
theorem clusterPart_empty_empty (H : Matrix ι ι ℂ) (h : κ → Matrix ι ι ℂ) (β : ℝ) :
    clusterPart H h ∅ ∅ β = NormedSpace.exp (-(β • H)) := by
  simp [clusterPart]

/-- **Products of cluster parts.** Let `H` be Hermitian, `β ≥ 0` and `n > 0`, and for each
factor `j < n` let `C j` be a cluster with boundary `B j`, with Hermitian terms `‖h k‖ ≤ J` on
`B j ∪ C j` and `n_{C_j} + n_{B_j} ≤ S n_{C_j}`. Then for every `O`,
`|Tr (O ρ(β/n, C_0) ⋯ ρ(β/n, C_{n-1}))| ≤ ‖O‖ y^{∑_j n_{C_j}} Tr e^{-βH}` with
`y = (e^{Jβ/n} - 1) e^{SJβ/n}`. A factor with `C j = B j = ∅` is the thermal factor
`e^{-βH/n}` (`clusterPart_empty_empty`). Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1322–1341: the bound of each product of thermal factors and cluster parts in `ρ_m`. -/
theorem norm_trace_mul_list_prod_clusterPart_le_pow {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {h : κ → Matrix ι ι ℂ} {n : ℕ} (hn : 0 < n) {B C : Fin n → Finset κ}
    (hh : ∀ j, ∀ k ∈ B j ∪ C j, (h k).IsHermitian) {J : ℝ}
    (hJ : ∀ j, ∀ k ∈ B j ∪ C j, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) {S : ℝ}
    (hS : ∀ j, ((C j).card + (B j).card : ℝ) ≤ S * (C j).card) :
    ‖(O * (List.ofFn fun j ↦ clusterPart H h (B j) (C j) (β / n)).prod).trace‖ ≤
      ‖O‖ * ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))) ^ (∑ j, (C j).card) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hβn : 0 ≤ β / n := div_nonneg hβ hn'.le
  set W : Fin n → Matrix ι ι ℂ := fun j ↦ H - ∑ i ∈ B j, h i - ∑ i ∈ C j, h i with hW
  have hsumH : ∀ j, ∀ T ⊆ B j ∪ C j, (∑ i ∈ T, h i).IsHermitian := fun j T hT ↦
    (isSelfAdjoint_sum T fun i hi ↦ (hh j i (hT hi)).isSelfAdjoint).isHermitian
  have hY : ∀ j, (β • W j).IsHermitian := fun j ↦
    ((hH.sub (hsumH j _ Finset.subset_union_left)).sub
      (hsumH j _ Finset.subset_union_right)).smul (IsSelfAdjoint.all β)
  have hg : ∀ j, ∀ i ∈ C j, (β • h i).IsHermitian := fun j i hi ↦
    (hh j i (Finset.mem_union_right _ hi)).smul (IsSelfAdjoint.all β)
  have hgJ : ∀ j, ∀ i ∈ C j, ‖β • h i‖ ≤ β * J := fun j i hi ↦ by
    rw [norm_smul, Real.norm_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (hJ j i (Finset.mem_union_right _ hi)) hβ
  -- Each cluster part as the alternating sum of `e^{-(1/n) (β W_j + ∑_{i ∈ E} β h i)}`.
  have hρ : ∀ j, clusterPart H h (B j) (C j) (β / n) =
      ∑ E ∈ (C j).powerset, (-1 : ℂ) ^ ((C j).card - E.card) •
        NormedSpace.exp ((1 / n : ℝ) • -(β • W j + ∑ i ∈ E, β • h i)) := by
    intro j
    rw [clusterPart_eq_sum_powerset]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    congr 2
    rw [hW, ← Finset.smul_sum, ← Finset.smul_sum]
    module
  -- The observable as the matrix of the first factor.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let Bm : Fin (m + 1) → Matrix ι ι ℂ := Fin.cons O fun _ ↦ 1
  have hprod : O * (List.ofFn fun j ↦ clusterPart H h (B j) (C j) (β / (m + 1 : ℕ))).prod =
      (List.ofFn fun j ↦ Bm j * ∑ E ∈ (C j).powerset, (-1 : ℂ) ^ ((C j).card - E.card) •
        NormedSpace.exp ((1 / (m + 1 : ℕ) : ℝ) • -(β • W j + ∑ i ∈ E, β • h i))).prod := by
    simp only [← hρ, List.ofFn_succ, List.prod_cons, Bm, Fin.cons_zero, Fin.cons_succ,
      Matrix.one_mul, Matrix.mul_assoc]
  have hq1 : ∑ _j : Fin (m + 1), (1 / (m + 1 : ℕ) : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have key := Matrix.norm_trace_list_prod_mul_sum_powerset_exp_le_pow Bm (fun j ↦ β • W j) hY
    (fun _ ↦ 1 / (m + 1 : ℕ)) (fun _ ↦ by positivity) hq1 C (fun _ i ↦ β • h i) hg hgJ
  rw [hprod]
  refine key.trans ?_
  -- The factors of the bound.
  set Z := (NormedSpace.exp (-(β • H))).trace.re
  have hZ : 0 ≤ Z := (hH.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  set q : ℝ := 1 / (m + 1 : ℕ)
  have hq : 0 ≤ q := by positivity
  have hy : ∀ j, 0 ≤ (Real.exp (q * (β * J)) - 1) ^ (C j).card := fun j ↦ by
    rcases (C j).eq_empty_or_nonempty with hC | ⟨k, hk⟩
    · simp [hC]
    · have hJ0 : 0 ≤ J := (norm_nonneg _).trans (hJ j k (Finset.mem_union_right _ hk))
      exact pow_nonneg (sub_nonneg.mpr (Real.one_le_exp (by positivity))) _
  have hfac : ∀ j, ‖Bm j‖ * (Real.exp (q * (β * J)) - 1) ^ (C j).card *
      (NormedSpace.exp (-(β • W j))).trace.re ^ q ≤
        (if j = 0 then ‖O‖ else 1) *
          (((Real.exp (β / (m + 1 : ℕ) * J) - 1) * Real.exp (S * J * (β / (m + 1 : ℕ)))) ^
            (C j).card * Z ^ q) := by
    intro j
    have hBm : ‖Bm j‖ ≤ if j = 0 then ‖O‖ else 1 := by
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp [Bm]
      · simpa [Bm, Fin.succ_ne_zero] using (l2_opNorm_one_le : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1)
    have hYnn := (hY j).neg.re_trace_exp_nonneg
    have htr : (NormedSpace.exp (-(β • W j))).trace.re ^ q ≤
        Real.exp (S * J * (β / (m + 1 : ℕ))) ^ (C j).card * Z ^ q := by
      calc (NormedSpace.exp (-(β • W j))).trace.re ^ q
          ≤ (Real.exp (((C j).card + (B j).card) * J * β) * Z) ^ q :=
            Real.rpow_le_rpow hYnn (re_trace_exp_sub_sum_sub_sum_le hH (hh j) (hJ j) hβ) hq
        _ = Real.exp (((C j).card + (B j).card) * J * (β / (m + 1 : ℕ))) * Z ^ q := by
            rw [Real.mul_rpow (Real.exp_pos _).le hZ, ← Real.exp_mul]
            congr 2
            simp only [q]
            ring
        _ ≤ Real.exp (S * J * (β / (m + 1 : ℕ))) ^ (C j).card * Z ^ q := by
            gcongr
            exact exp_card_add_card_mul_le (hJ j) hβn (hS j)
    have hqJ : q * (β * J) = β / (m + 1 : ℕ) * J := by simp only [q]; ring
    rw [hqJ] at hy ⊢
    have hif : 0 ≤ (if j = 0 then ‖O‖ else 1) := by split_ifs <;> positivity
    calc ‖Bm j‖ * (Real.exp (β / (m + 1 : ℕ) * J) - 1) ^ (C j).card *
          (NormedSpace.exp (-(β • W j))).trace.re ^ q
        ≤ (if j = 0 then ‖O‖ else 1) * (Real.exp (β / (m + 1 : ℕ) * J) - 1) ^ (C j).card *
          (Real.exp (S * J * (β / (m + 1 : ℕ))) ^ (C j).card * Z ^ q) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hBm (hy j)) htr (Real.rpow_nonneg hYnn _)
            (mul_nonneg hif (hy j))
      _ = _ := by rw [mul_pow]; ring
  refine (Finset.prod_le_prod₀ (fun j _ ↦ ?_) fun j _ ↦ hfac j).trans_eq ?_
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (hy j))
      (Real.rpow_nonneg (hY j).neg.re_trace_exp_nonneg _)
  -- Collect the factors.
  have hqn : q * ((m + 1 : ℕ) : ℝ) = 1 := by simp only [q]; field_simp
  have hZn : (Z ^ q) ^ (m + 1) = Z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ, hqn, Real.rpow_one]
  have hif : ∏ j : Fin (m + 1), (if j = 0 then ‖O‖ else 1) = ‖O‖ := by
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_ne_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, hZn, hif]
  ring

end TNLean.Lattice.ClusterExpansion
