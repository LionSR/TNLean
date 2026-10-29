/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ListProduct
import TNLean.Lattice.ClusterExpansion.Percolation
import TNLean.Lattice.ClusterExpansion.AllTemperatures
import TNLean.Lattice.ClusterExpansion.ThermalProduct
import TNLean.Lattice.ClusterExpansion.Truncation

/-!
# The error of the truncated expansion at every temperature

At arbitrary temperature, Hastings, *Solving gapped Hamiltonians locally*
(arXiv:cond-mat/0508554v3, `References/cond-mat_0508554/proj3new.tex`, lines 1303–1347), replaces
`e^{-βH}` by the product `ρ(β, l) = ρ(β/n, l)^n` of `n` truncated factors (equation `mplt`), and
bounds the error by the operators `ρ_m` of the terms with at least `m` large clusters across the
`n` factors (lines 1334–1341), "following the same arguments as before" (line 1342).

This file proves that bound. Each factor is the inclusion–exclusion sum
`ρ(β/n, l) = ∑_U (-1)^{|U|} ρ(β/n, U)` over the admissible families `U` of large connected sets
(`truncatedExp_eq_sum`), and the empty family gives `e^{-βH/n}`. Expanding the `n`-th power gives a
sum over words `w` of `n` families, in which the word of empty families is `e^{-βH}`. Every other
word is a product of cluster parts whose trace against `O` has modulus at most
`‖O‖ (∏_j ∏_{C ∈ w_j} y^{n_C}) Tr e^{-βH}`
(`norm_trace_mul_list_prod_clusterPart_le_pow`), with `y = (e^{Jβ/n} - 1) e^{SJβ/n}`. Summing
over the words,

`|Tr (O (e^{-βH} - ρ(β/n, l)^n))| ≤ ‖O‖ ((∑_U ∏_{C ∈ U} y^{n_C})^n - 1) Tr e^{-βH}`,

and `∑_U ∏_{C ∈ U} y^{n_C} ≤ exp(∑_C y^{n_C})` over the large connected sets `C`. This is the
source's estimate of `∑_{m ≥ 1} ρ_m` by `∑_{m ≥ 1} (1/m!) (∑_C n y^{n_C})^m`.

**Local fix (number of factors):** the source prints the final bound (lines 1342–1347) with
`β/β₀` in the exponent, where its bound on `ρ_m` (lines 1334–1341) gives the number `n` of
factors. For the source's `n`, the smallest even integer with `β/n ≤ β₀`, one has
`β/β₀ ≤ n < β/β₀ + 2`, so the printed bound does not follow. The bound here has `n` and holds for
every `n > 0`. Documented in `docs/paper-gaps/hastings05_temperature_factor_count.tex`.

**Local fix (size threshold):** the percolation form takes the threshold `l` on the number of
terms of a large connected set, not on its diameter. Documented in
`docs/paper-gaps/hastings05_percolation_cluster_size.tex`.

## Main results

* `TNLean.Lattice.ClusterExpansion.sum_prod_le_exp_of_subset_powerset`: for families of subsets
  of `T` and nonnegative weights, `∑_U ∏_{i ∈ U} a_i ≤ exp(∑_{i ∈ T} a_i)`.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le`:
  `|Tr (O (e^{-βH} - ρ(β/n, l)^n))| ≤ ‖O‖ (exp(n ∑_C y^{n_C}) - 1) Tr e^{-βH}`.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation`: the
  source's form `‖O‖ (exp(n N e^{-l/ξ}) - 1) Tr e^{-βH}` from the count of large connected sets.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1303–1347.
-/

open Finset Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice.ClusterExpansion

/-- **Families of subsets.** For nonnegative weights `a` on a finite set `T` and any collection
`𝒜` of subsets of `T`, `∑_{U ∈ 𝒜} ∏_{i ∈ U} a_i ≤ exp(∑_{i ∈ T} a_i)`. The empty family
contributes `1` and the nonempty ones at most `exp(∑_{i ∈ T} a_i) - 1`
(`sum_nonempty_powerset_prod_le_exp`). -/
theorem sum_prod_le_exp_of_subset_powerset {α : Type*} {T : Finset α}
    {𝒜 : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ T.powerset) {a : α → ℝ} (ha : ∀ i ∈ T, 0 ≤ a i) :
    ∑ U ∈ 𝒜, ∏ i ∈ U, a i ≤ Real.exp (∑ i ∈ T, a i) := by
  classical
  calc ∑ U ∈ 𝒜, ∏ i ∈ U, a i ≤ ∑ U ∈ T.powerset, ∏ i ∈ U, a i :=
        sum_le_sum_of_subset_of_nonneg h𝒜 fun U hU _ ↦
          prod_nonneg fun i hi ↦ ha i (mem_powerset.1 hU hi)
    _ = 1 + ∑ U ∈ T.powerset.erase ∅, ∏ i ∈ U, a i := by
        rw [← add_sum_erase _ _ (empty_mem_powerset T), prod_empty]
    _ ≤ 1 + (Real.exp (∑ i ∈ T, a i) - 1) := by
        gcongr
        exact sum_nonempty_powerset_prod_le_exp ha
    _ = Real.exp (∑ i ∈ T, a i) := by ring

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)

/-- **The error at every temperature** (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1334–1347). Let `H = ∑_k h_k` be Hermitian with Hermitian terms of norm at most `J`, let
`β ≥ 0` and `n > 0`, and let every large connected set `C` have `n_C + n_{∂C} ≤ S n_C`. Then the
product `ρ(β, l) = ρ(β/n, l)^n` of equation `mplt`, for any `n > 0` (the source takes the
smallest even `n` with `β/n ≤ β₀`), satisfies, for every `O`,
`|Tr (O (e^{-βH} - ρ(β/n, l)^n))| ≤ ‖O‖ (exp(n ∑_C y^{n_C}) - 1) Tr e^{-βH}`, the sum over the
large connected sets, with `y = (e^{Jβ/n} - 1) e^{SJβ/n}`.

The source sums the bound `(1/m!) (∑_C n y^{n_C})^m ‖O‖` on `Z⁻¹ Tr (O ρ_m)` (lines 1334–1341)
over `m ≥ 1`; here the words of `n` admissible families are summed directly, which gives the same
exponential. Counting large connected sets gives `exp(n N exp(-l/ξ)) - 1`
(`norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation`), with the integer number `n` of
factors in place of the source's `β/β₀` (lines 1342–1347). The correction is recorded in
`docs/paper-gaps/hastings05_temperature_factor_count.tex`. -/
theorem norm_trace_mul_exp_sub_truncatedExp_pow_le {H : Matrix ι ι ℂ} (hHerm : H.IsHermitian)
    {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k) (hh : ∀ k, (h k).IsHermitian) {J : ℝ}
    (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) {S : ℝ}
    (hS : ∀ C ∈ largeConnected G large, ((#C : ℝ) + #(boundary G C)) ≤ S * #C)
    {n : ℕ} (hn : 0 < n) :
    ‖(O * (NormedSpace.exp (-(β • H)) - truncatedExp G large h (β / n) ^ n)).trace‖ ≤
      ‖O‖ * (Real.exp (n * ∑ C ∈ largeConnected G large,
          ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))) ^ #C) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  classical
  set T := largeConnected G large
  set 𝒜 : Finset (Finset (Finset κ)) := {U ∈ T.powerset | IsAdmissible G U} with h𝒜
  set y := (Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))
  set Z := (NormedSpace.exp (-(β • H))).trace.re
  set cp : Finset (Finset κ) → Matrix ι ι ℂ :=
    fun U ↦ clusterPart H h (U.biUnion (boundary G)) (U.biUnion id) (β / n)
  set f : Finset (Finset κ) → ℝ := fun U ↦ ∏ C ∈ U, y ^ #C with hf
  set term : (Fin n → Finset (Finset κ)) → Matrix ι ι ℂ :=
    fun w ↦ (List.ofFn fun j ↦ (-1 : ℂ) ^ #(w j) • cp (w j)).prod with hterm_def
  set W := Fintype.piFinset fun _ : Fin n ↦ 𝒜 with hW
  set w₀ : Fin n → Finset (Finset κ) := fun _ ↦ ∅ with hw₀_def
  have hZ : 0 ≤ Z := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  have hmem : ∀ U ∈ 𝒜, U ⊆ T ∧ IsAdmissible G U := fun U hU ↦ by
    simpa only [h𝒜, mem_filter, mem_powerset] using hU
  have hconn : ∀ U ∈ 𝒜, ∀ C ∈ U, (G.induce (C : Set κ)).Connected := fun U hU C hC ↦
    ((mem_largeConnected G).1 ((hmem U hU).1 hC)).1
  have hw₀ : w₀ ∈ W := Fintype.mem_piFinset.2 fun _ ↦ by
    change (∅ : Finset (Finset κ)) ∈ 𝒜
    exact mem_filter.2 ⟨empty_mem_powerset _, by simp [IsAdmissible]⟩
  -- The thermal factor `e^{-βH} = (e^{-βH/n})^n` is the word of empty families.
  have hexp : NormedSpace.exp (-(β • H)) = term w₀ := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsmul : -(β • H) = n • -((β / n) • H) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_neg, smul_smul, mul_div_cancel₀ _ hn']
    rw [hsmul, Matrix.exp_nsmul, ← clusterPart_empty_empty H h]
    simp [term, hw₀_def, cp, List.ofFn_const, List.prod_replicate]
  -- The `n`-th power of the truncated factor as a sum over words of admissible families.
  have hpow : truncatedExp G large h (β / n) ^ n = ∑ w ∈ W, term w := by
    rw [truncatedExp_eq_sum G large hH, sum_pow_eq_sum_words]
    refine sum_congr ?_ fun _ _ ↦ rfl
    ext w
    simp [W, h𝒜, T, Fintype.mem_piFinset]
  have hdiff : NormedSpace.exp (-(β • H)) - truncatedExp G large h (β / n) ^ n =
      -∑ w ∈ W.erase w₀, term w := by
    rw [hpow, ← add_sum_erase W _ hw₀, hexp]
    abel
  -- The weights `y^{n_C}` are nonnegative: `J ≥ 0` as soon as `C` is nonempty.
  have hy0 : ∀ C : Finset κ, 0 ≤ y ^ #C := fun C ↦ by
    rcases C.eq_empty_or_nonempty with hC | ⟨k, -⟩
    · simp [hC]
    · have hJ0 : 0 ≤ J := (norm_nonneg _).trans (hJ k)
      have hβn : 0 ≤ β / n := div_nonneg hβ n.cast_nonneg
      exact pow_nonneg (mul_nonneg (sub_nonneg.2 (Real.one_le_exp (mul_nonneg hβn hJ0)))
        (Real.exp_pos _).le) _
  -- The bound of one word.
  have hterm : ∀ w ∈ W, ‖(O * term w).trace‖ ≤ ‖O‖ * (∏ j, f (w j)) * Z := by
    intro w hw
    have hwA : ∀ j, w j ∈ 𝒜 := Fintype.mem_piFinset.1 hw
    simp only [hterm_def]
    rw [List.prod_ofFn_smul, Matrix.mul_smul, trace_smul, norm_smul, norm_prod]
    simp only [norm_pow, norm_neg, norm_one, one_pow, prod_const_one, one_mul]
    refine (norm_trace_mul_list_prod_clusterPart_le_pow hHerm hn
      (B := fun j ↦ (w j).biUnion (boundary G)) (C := fun j ↦ (w j).biUnion id)
      (fun _ k _ ↦ hh k) (fun _ k _ ↦ hJ k) O hβ fun j ↦
        card_add_card_biUnion_boundary_le G (hmem _ (hwA j)).2 (hconn _ (hwA j))
          fun C hC ↦ hS C ((hmem _ (hwA j)).1 hC)).trans_eq ?_
    rw [sum_congr rfl fun j _ ↦ card_biUnion_of_admissible G (hmem _ (hwA j)).2 (hconn _ (hwA j))]
    simp only [hf, prod_pow_eq_pow_sum]
    rfl
  -- Summing over the words.
  have hf0 : 0 ≤ ∑ U ∈ 𝒜, f U := sum_nonneg fun U _ ↦ prod_nonneg fun C _ ↦ hy0 C
  have hsum : ∑ U ∈ 𝒜, f U ≤ Real.exp (∑ C ∈ T, y ^ #C) :=
    sum_prod_le_exp_of_subset_powerset (filter_subset _ _) fun C _ ↦ hy0 C
  have hwords : ∑ w ∈ W.erase w₀, ∏ j, f (w j) = (∑ U ∈ 𝒜, f U) ^ n - 1 := by
    have h1 : (∑ U ∈ 𝒜, f U) ^ n = ∑ w ∈ W, ∏ j, f (w j) := by
      rw [hW]
      exact sum_pow' 𝒜 f n
    rw [h1, ← add_sum_erase W _ hw₀]
    simp [hw₀_def, hf]
  rw [hdiff, Matrix.mul_neg, trace_neg, norm_neg, Finset.mul_sum, trace_sum]
  calc ‖∑ w ∈ W.erase w₀, (O * term w).trace‖
      ≤ ∑ w ∈ W.erase w₀, ‖O‖ * (∏ j, f (w j)) * Z :=
        (norm_sum_le _ _).trans (sum_le_sum fun w hw ↦ hterm w (mem_of_mem_erase hw))
    _ = ‖O‖ * ((∑ U ∈ 𝒜, f U) ^ n - 1) * Z := by
        rw [← sum_mul, ← mul_sum, hwords]
    _ ≤ ‖O‖ * (Real.exp (n * ∑ C ∈ T, y ^ #C) - 1) * Z := by
        gcongr
        rw [Real.exp_nat_mul]
        exact pow_le_pow_left₀ hf0 hsum n

/-- **The error at every temperature, percolation form** (Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1342–1347). Under the hypotheses of
`norm_trace_mul_exp_sub_truncatedExp_pow_le`, let every large connected set have at least `l + 1`
terms, let there be at most `N x^k` large connected sets of `k` terms, and let
`0 < x y ≤ 1/2` with `y = (e^{Jβ/n} - 1) e^{SJβ/n}`. Then
`|Tr (O (e^{-βH} - ρ(β/n, l)^n))| ≤ ‖O‖ (exp(n N e^{-l/ξ}) - 1) Tr e^{-βH}` with
`ξ = 1 / ln(1/(xy))`. After division by `Z = Tr e^{-βH}`, this is the source's
`{exp[(β/β₀) N exp(-l/ξ_perc)] - 1} ‖O‖` with the number `n` of factors in place of `β/β₀`
(see the module docstring). -/
theorem norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation {H : Matrix ι ι ℂ}
    (hHerm : H.IsHermitian) {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k)
    (hh : ∀ k, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ}
    (hβ : 0 ≤ β) {S : ℝ}
    (hS : ∀ C ∈ largeConnected G large, ((#C : ℝ) + #(boundary G C)) ≤ S * #C)
    {n : ℕ} (hn : 0 < n) {l : ℕ} (hl : ∀ C ∈ largeConnected G large, l + 1 ≤ #C) {N x : ℝ}
    (hcount : ∀ k, (#{C ∈ largeConnected G large | #C = k} : ℝ) ≤ N * x ^ k) (hN : 0 ≤ N)
    (hx : 0 ≤ x) (hxy0 : 0 < x * ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))))
    (hxy : x * ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))) ≤ 1 / 2) :
    ‖(O * (NormedSpace.exp (-(β • H)) - truncatedExp G large h (β / n) ^ n)).trace‖ ≤
      ‖O‖ * (Real.exp (n * (N * Real.exp (-(l / (Real.log
          (x * ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))))⁻¹)⁻¹)))) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  refine (norm_trace_mul_exp_sub_truncatedExp_pow_le G large hHerm hH hh hJ O hβ hS hn).trans ?_
  set y := (Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))
  have hZ := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  have hy : 0 ≤ y := (pos_of_mul_pos_right hxy0 hx).le
  gcongr
  calc ∑ C ∈ largeConnected G large, y ^ #C ≤ N * ((x * y) ^ (l + 1) / (1 - x * y)) :=
        sum_pow_le_of_card_le hl hcount hN hx hy (by linarith)
    _ ≤ N * (x * y) ^ l := by
        gcongr
        exact pow_succ_div_one_sub_le hxy0.le hxy l
    _ = N * Real.exp (-(l / (Real.log (x * y)⁻¹)⁻¹)) := by rw [pow_eq_exp_neg_div _ hxy0]

/-- For the least sufficient even factor count, the corrected percolation error has
`β/β₀ + 2` in its exponent. The strict factor-count inequality is established by
`evenTemperatureFactors_spec`, rather than assumed.
Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312 and 1334–1347;
`docs/paper-gaps/hastings05_temperature_factor_count.tex`. -/
theorem norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation_add_two
    {H : Matrix ι ι ℂ} (hHerm : H.IsHermitian) {h : κ → Matrix ι ι ℂ}
    (hH : H = ∑ k, h k) (hh : ∀ k, (h k).IsHermitian) {J : ℝ}
    (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β β₀ : ℝ}
    (hβ : 0 < β) (hβ₀ : 0 < β₀) {S : ℝ}
    (hS : ∀ C ∈ largeConnected G large, ((#C : ℝ) + #(boundary G C)) ≤ S * #C)
    {l : ℕ} (hl : ∀ C ∈ largeConnected G large, l + 1 ≤ #C) {N x : ℝ}
    (hcount : ∀ k, (#{C ∈ largeConnected G large | #C = k} : ℝ) ≤ N * x ^ k)
    (hN : 0 ≤ N) (hx : 0 ≤ x)
    (hxy0 : 0 < x * ((Real.exp (β / evenTemperatureFactors β β₀ * J) - 1) *
      Real.exp (S * J * (β / evenTemperatureFactors β β₀))))
    (hxy : x * ((Real.exp (β / evenTemperatureFactors β β₀ * J) - 1) *
      Real.exp (S * J * (β / evenTemperatureFactors β β₀))) ≤ 1 / 2) :
    ‖(O * (NormedSpace.exp (-(β • H)) -
      truncatedExp G large h (β / (evenTemperatureFactors β β₀)) ^
        (evenTemperatureFactors β β₀))).trace‖ ≤
      ‖O‖ * (Real.exp ((β / β₀ + 2) * (N * Real.exp (-(l / (Real.log
          (x * ((Real.exp (β / (evenTemperatureFactors β β₀) * J) - 1) *
            Real.exp (S * J * (β / (evenTemperatureFactors β β₀)))))⁻¹)⁻¹)))) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  have hn : 0 < evenTemperatureFactors β β₀ := by
    have := (evenTemperatureFactors_spec hβ hβ₀).2.1
    omega
  refine (norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation G large hHerm hH hh hJ O
    hβ.le hS hn hl hcount hN hx hxy0 hxy).trans ?_
  have hZ := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (exp_evenTemperatureFactors_mul_sub_one_le hβ hβ₀
        (mul_nonneg hN (Real.exp_pos _).le)) (norm_nonneg O)) hZ

end TNLean.Lattice.ClusterExpansion
