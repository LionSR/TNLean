/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TNLean.Lattice.ConnectedSetCount

/-!
# The percolation sum of Hastings' high-temperature cluster expansion

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1196–1254), bounds the difference between the
thermal operator `ρ(β)` and its truncation `ρ(β, l_proj)` by an inclusion–exclusion sum over
families of clusters of diameter larger than `l_proj`. A family of `m` clusters `C₁, …, C_m`
contributes at most `∏ y^{n_{C_i}}`, where `n_C` is the number of sites of `C` and
`y = (e^{Jβ} − 1) e^{SJβ}`. Summing over families, the source obtains

`∑_{m ≥ 1} (1/m!) (∑_C y^{n_C})^m ≤ exp[N ∑_{n > l_proj} (xy)^n] − 1`
`≤ exp[N e^{−l_proj/ξ_perc}] − 1`

when there are at most `N xⁿ` clusters of `n` sites (lines 1227–1250).

This file proves that estimate with abstract weights. A weight `a_C` with `0 ≤ a_C ≤ y^{n_C}` stands
for the contribution of the cluster `C`. Families of clusters are finite subsets `U` of the
family `T` of large clusters, and contribute `∏_{C ∈ U} a_C`. Every cluster of `T` is assumed to
have at least `l + 1` sites, for a size threshold `l` that is a parameter of the statements.

**Local fix (size threshold):** the source starts the sum over cluster sizes at
`n = l_proj + 1` (line 1240), which holds for nearest-neighbour bonds only. With terms of range
`R`, a cluster of `n` sites spans a distance of at most `2Rn`, so diameter larger than `l_proj`
gives only `n ≥ ⌊l_proj/(2R)⌋ + 1`; the cluster `{0, 2R}` of a chain has two sites and spans
`4R`. The statements here take the size threshold `l` as a hypothesis, and the application takes
`l = ⌊l_proj/(2R)⌋`. Documented in `docs/paper-gaps/hastings05_percolation_cluster_size.tex`.

The decay is explicit in the size threshold. For `0 < xy ≤ 1/2`, the tail `∑_{n > l} (xy)^n` is
at most `(xy)^l = e^{−l/ξ}` with `ξ = 1 / ln(1/(xy))`, a decay length in units of cluster size.
With `l = ⌊l_proj/(2R)⌋` this is at most `(xy)^{−1} e^{−l_proj/ξ_perc}` with
`ξ_perc = 2R / ln(1/(xy))` in units of distance, which is the source's "`ξ_perc` of order the
interaction range" (line 1250).

## Main results

* `TNLean.Lattice.sum_powersetCard_prod_le`: the families of `m` clusters contribute at most
  `(∑_C a_C)^m / m!` (the bound on `ρ_m`, line 1210).
* `TNLean.Lattice.sum_nonempty_powerset_prod_eq`,
  `TNLean.Lattice.sum_nonempty_powerset_prod_le_exp`: all nonempty families together contribute
  `∏_C (1 + a_C) − 1 ≤ exp(∑_C a_C) − 1`.
* `TNLean.Lattice.sum_pow_le_of_card_le`: `∑_C y^{n_C} ≤ N (xy)^{l+1} / (1 − xy)` from the count
  of clusters by size.
* `TNLean.Lattice.sum_nonempty_powerset_prod_le_percolation`: the percolation bound
  `exp(N e^{−l/ξ}) − 1`, eq. `perc2` (lines 1227–1254) without the trace, in terms of the size
  threshold `l`.
* `TNLean.Lattice.sum_nonempty_powerset_prod_le_percolation_connected`: the same for families of
  connected vertex sets of a graph of maximum degree `Δ`, with `N` the number of vertices and
  `x = max(1, Δ²)`.
* `TNLean.Lattice.exists_percolation_temperature`: some `β₀ > 0` gives `xy ≤ 1/2` for every
  `0 ≤ β ≤ β₀` (line 1244).
-/

open Finset Real

namespace TNLean.Lattice

variable {ι : Type*}

section Families

/-- `s^{m+1} + (m + 1) a s^m ≤ (s + a)^{m+1}` for `s, a ≥ 0`: the first two terms of the binomial
expansion. -/
private theorem pow_succ_add_mul_le {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (m : ℕ) :
    s ^ (m + 1) + (m + 1) * a * s ^ m ≤ (s + a) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 0 ≤ s ^ m := pow_nonneg hs m
    have h2 : 0 ≤ a * a * s ^ m := by positivity
    calc s ^ (m + 1 + 1) + ((m + 1 : ℕ) + 1 : ℝ) * a * s ^ (m + 1)
        ≤ (s + a) * (s ^ (m + 1) + (m + 1) * a * s ^ m) := by
          push_cast
          rw [pow_succ s (m + 1), pow_succ s m]
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) h2]
      _ ≤ (s + a) * (s + a) ^ (m + 1) := by gcongr
      _ = (s + a) ^ (m + 1 + 1) := by ring

/-- **Families of `m` clusters.** For nonnegative weights `a` on a finite set `T`, the sum over
the `m`-element subsets `U ⊆ T` of `∏_{i ∈ U} a_i` is at most `(∑_{i ∈ T} a_i)^m / m!`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, line 1210, the bound on `ρ_m`. -/
theorem sum_powersetCard_prod_le {T : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ T, 0 ≤ a i)
    (m : ℕ) :
    ∑ U ∈ T.powersetCard m, ∏ i ∈ U, a i ≤ (∑ i ∈ T, a i) ^ m / m.factorial := by
  classical
  induction T using Finset.induction_on generalizing m with
  | empty =>
    cases m with
    | zero => simp
    | succ m => simp [powersetCard_eq_empty.2 (by simp : #(∅ : Finset ι) < m + 1)]
  | insert b T hb ih =>
    have haT : ∀ i ∈ T, 0 ≤ a i := fun i hi ↦ ha i (mem_insert_of_mem hi)
    have hab : 0 ≤ a b := ha b (mem_insert_self b T)
    have hs : 0 ≤ ∑ i ∈ T, a i := sum_nonneg haT
    rw [sum_insert hb]
    cases m with
    | zero => simp
    | succ m =>
      have hdisj : Disjoint (T.powersetCard (m + 1)) ((T.powersetCard m).image (insert b)) := by
        rw [disjoint_left]
        intro U hU hU'
        obtain ⟨V, -, rfl⟩ := mem_image.1 hU'
        exact hb ((mem_powersetCard.1 hU).1 (mem_insert_self b V))
      have hinj : ∀ U ∈ T.powersetCard m, ∀ V ∈ T.powersetCard m, insert b U = insert b V →
          U = V := fun U hU V hV h ↦ by
        have hbU : b ∉ U := fun h' ↦ hb ((mem_powersetCard.1 hU).1 h')
        have hbV : b ∉ V := fun h' ↦ hb ((mem_powersetCard.1 hV).1 h')
        simpa [erase_insert hbU, erase_insert hbV] using congrArg (·.erase b) h
      rw [powersetCard_succ_insert hb, sum_union hdisj,
        sum_image fun U hU V hV h ↦ hinj U (mem_coe.1 hU) V (mem_coe.1 hV) h]
      have hins : ∀ U ∈ T.powersetCard m, ∏ i ∈ insert b U, a i = a b * ∏ i ∈ U, a i :=
        fun U hU ↦ prod_insert fun h ↦ hb ((mem_powersetCard.1 hU).1 h)
      rw [sum_congr rfl hins, ← mul_sum]
      have h1 := ih haT (m + 1)
      have h2 := ih haT m
      have hbin := pow_succ_add_mul_le hs hab m
      rw [add_comm (∑ i ∈ T, a i)] at hbin
      calc ∑ U ∈ T.powersetCard (m + 1), ∏ i ∈ U, a i + a b * ∑ U ∈ T.powersetCard m, ∏ i ∈ U, a i
          ≤ (∑ i ∈ T, a i) ^ (m + 1) / (m + 1).factorial +
              a b * ((∑ i ∈ T, a i) ^ m / m.factorial) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 hab)
        _ = ((∑ i ∈ T, a i) ^ (m + 1) + (m + 1) * a b * (∑ i ∈ T, a i) ^ m) /
              (m + 1).factorial := by
            rw [Nat.factorial_succ]; push_cast; field_simp
        _ ≤ (a b + ∑ i ∈ T, a i) ^ (m + 1) / (m + 1).factorial := by gcongr

variable [DecidableEq ι]

/-- The sum over the nonempty subsets `U ⊆ T` of `∏_{i ∈ U} a_i` is `∏_{i ∈ T} (1 + a_i) − 1`. -/
theorem sum_nonempty_powerset_prod_eq (T : Finset ι) (a : ι → ℝ) :
    ∑ U ∈ T.powerset.erase ∅, ∏ i ∈ U, a i = ∏ i ∈ T, (1 + a i) - 1 := by
  rw [sum_erase_eq_sub (empty_mem_powerset T), ← prod_one_add, prod_empty]

/-- **All nonempty families of clusters.** For nonnegative weights `a` on a finite set `T`, the sum
over the nonempty subsets `U ⊆ T` of `∏_{i ∈ U} a_i` equals `∏_{i ∈ T} (1 + a_i) − 1`, and is at
most `exp(∑_{i ∈ T} a_i) − 1`. This is the inclusion–exclusion sum `∑_{m ≥ 1} ρ_m` of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1196–1225, estimated as at lines 1238–1241. -/
theorem sum_nonempty_powerset_prod_le_exp {T : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ T, 0 ≤ a i) :
    ∑ U ∈ T.powerset.erase ∅, ∏ i ∈ U, a i ≤ exp (∑ i ∈ T, a i) - 1 := by
  rw [sum_nonempty_powerset_prod_eq, exp_sum]
  have := prod_le_prod₀ (s := T) (f := fun i ↦ 1 + a i) (g := fun i ↦ exp (a i))
    (fun i hi ↦ by linarith [ha i hi]) fun i _ ↦ by linarith [add_one_le_exp (a i)]
  linarith

end Families

section Count

/-- A finite sum of `r^k` over exponents `k ≥ l + 1` is at most `r^{l+1} / (1 − r)` for
`0 ≤ r < 1`. -/
theorem sum_pow_le_of_forall_lt {K : Finset ℕ} {l : ℕ} (hK : ∀ k ∈ K, l + 1 ≤ k) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) : ∑ k ∈ K, r ^ k ≤ r ^ (l + 1) / (1 - r) := by
  have hsub : K ⊆ Ico (l + 1) (K.sup id + l + 2) := fun k hk ↦
    mem_Ico.2 ⟨hK k hk, by have := le_sup (f := id) hk; simp only [id] at this; omega⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ pow_nonneg hr0 _).trans ?_
  rw [geom_sum_Ico' hr1.ne (by omega)]
  gcongr
  all_goals linarith [pow_nonneg hr0 (K.sup id + l + 2)]

/-- **The sum over large clusters.** Let `T` be a finite family of clusters, where the cluster `i`
has `n i ≥ l + 1` sites and there are at most `N x^k` clusters of `k` sites. For `0 ≤ y` with
`x y < 1`, `∑_{i ∈ T} y^{n i} ≤ N (xy)^{l+1} / (1 − xy)`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1236–1241. -/
theorem sum_pow_le_of_card_le {T : Finset ι} {n : ι → ℕ} {l : ℕ} (hn : ∀ i ∈ T, l + 1 ≤ n i)
    {N x y : ℝ} (hcount : ∀ k, (#{i ∈ T | n i = k} : ℝ) ≤ N * x ^ k) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxy : x * y < 1) :
    ∑ i ∈ T, y ^ n i ≤ N * ((x * y) ^ (l + 1) / (1 - x * y)) := by
  rw [← sum_fiberwise_of_maps_to (g := n) (t := T.image n) fun i hi ↦ mem_image_of_mem n hi]
  calc ∑ k ∈ T.image n, ∑ i ∈ T with n i = k, y ^ n i
      = ∑ k ∈ T.image n, (#{i ∈ T | n i = k} : ℝ) * y ^ k := by
        refine sum_congr rfl fun k _ ↦ ?_
        rw [sum_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2], sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ T.image n, N * (x * y) ^ k := by
        refine sum_le_sum fun k _ ↦ ?_
        rw [mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hcount k) (pow_nonneg hy k)
    _ = N * ∑ k ∈ T.image n, (x * y) ^ k := by rw [mul_sum]
    _ ≤ N * ((x * y) ^ (l + 1) / (1 - x * y)) := by
        gcongr
        refine sum_pow_le_of_forall_lt (fun k hk ↦ ?_) (mul_nonneg hx hy) hxy
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hk
        exact hn i hi

end Count

section Percolation

/-- For `0 ≤ r ≤ 1/2`, the geometric tail `r^{l+1} / (1 − r)` is at most `r^l`. -/
theorem pow_succ_div_one_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (l : ℕ) :
    r ^ (l + 1) / (1 - r) ≤ r ^ l := by
  rw [div_le_iff₀ (by linarith), pow_succ]
  have := pow_nonneg hr0 l
  nlinarith

/-- For `0 < r`, `r^l = e^{−l/ξ}` with `ξ = 1 / ln(1/r)`. -/
theorem pow_eq_exp_neg_div (r : ℝ) (hr : 0 < r) (l : ℕ) :
    r ^ l = exp (-(l / (log r⁻¹)⁻¹)) := by
  rw [div_inv_eq_mul, log_inv, mul_neg, neg_neg, ← log_pow, exp_log (pow_pos hr l)]

variable [DecidableEq ι]

/-- **The percolation bound (eq. `perc2` without the trace).** Let `T` be a finite family of
clusters, where the cluster `i` has `n i ≥ l + 1` sites and there are at most `N x^k` clusters
of `k` sites, and let the weights satisfy `0 ≤ a i ≤ y^{n i}` with `0 < x y ≤ 1/2`. Then the sum
over nonempty subfamilies `U ⊆ T` of `∏_{i ∈ U} a i` is at most `exp(N e^{−l/ξ}) − 1`, with
the decay length `ξ = 1 / ln(1/(xy))` in units of cluster size. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1227–1254, with the families of clusters of
lines 1196–1225 and the size threshold of the module docstring. -/
theorem sum_nonempty_powerset_prod_le_percolation {T : Finset ι} {n : ι → ℕ} {l : ℕ}
    (hn : ∀ i ∈ T, l + 1 ≤ n i) {N x y : ℝ}
    (hcount : ∀ k, (#{i ∈ T | n i = k} : ℝ) ≤ N * x ^ k) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxy0 : 0 < x * y) (hxy : x * y ≤ 1 / 2) {a : ι → ℝ}
    (ha0 : ∀ i ∈ T, 0 ≤ a i) (ha : ∀ i ∈ T, a i ≤ y ^ n i) :
    ∑ U ∈ T.powerset.erase ∅, ∏ i ∈ U, a i ≤
      exp (N * exp (-(l / (log (x * y)⁻¹)⁻¹))) - 1 := by
  refine (sum_nonempty_powerset_prod_le_exp ha0).trans ?_
  gcongr
  calc ∑ i ∈ T, a i ≤ ∑ i ∈ T, y ^ n i := sum_le_sum ha
    _ ≤ N * ((x * y) ^ (l + 1) / (1 - x * y)) :=
        sum_pow_le_of_card_le hn hcount hN hx hy (by linarith)
    _ ≤ N * (x * y) ^ l := by
        gcongr
        exact pow_succ_div_one_sub_le hxy0.le hxy l
    _ = N * exp (-(l / (log (x * y)⁻¹)⁻¹)) := by rw [pow_eq_exp_neg_div _ hxy0]

/-- **The percolation bound for connected clusters.** Let `G` be a graph on `N` vertices with
maximum degree at most `Δ`, and put `x = max(1, Δ²)`. Let `T` be a finite family of connected
vertex sets of `G`, each with at least `l + 1` vertices, with weights `0 ≤ a C ≤ y^{#C}`, and let
`0 < x y ≤ 1/2`. Then the sum over nonempty subfamilies `U ⊆ T` of `∏_{C ∈ U} a C` is at most
`exp(N e^{−l/ξ}) − 1` with `ξ = 1 / ln(1/(xy))`. The count of clusters by size is
`card_connected_induce_le_exponential`, the lattice-animal bound cited by Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1234–1236. -/
theorem sum_nonempty_powerset_prod_le_percolation_connected {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {T : Finset (Finset V)}
    (hT : ∀ C ∈ T, (G.induce (C : Set V)).Connected) {l : ℕ} (hl : ∀ C ∈ T, l + 1 ≤ #C)
    {y : ℝ} (hy : 0 ≤ y) (hxy0 : 0 < (max 1 (Δ ^ 2) : ℕ) * y)
    (hxy : (max 1 (Δ ^ 2) : ℕ) * y ≤ 1 / 2) {a : Finset V → ℝ} (ha0 : ∀ C ∈ T, 0 ≤ a C)
    (ha : ∀ C ∈ T, a C ≤ y ^ #C) :
    ∑ U ∈ T.powerset.erase ∅, ∏ C ∈ U, a C ≤
      exp (Fintype.card V * exp (-(l / (log ((max 1 (Δ ^ 2) : ℕ) * y)⁻¹)⁻¹))) - 1 := by
  refine sum_nonempty_powerset_prod_le_percolation hl (fun k ↦ ?_) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hy hxy0 hxy ha0 ha
  have hsub : ({C ∈ T | #C = k} : Finset (Finset V)) ⊆
      ({S : Finset V | #S = k ∧ (G.induce (S : Set V)).Connected} : Finset (Finset V)) :=
      fun C hC ↦ by
    obtain ⟨hCT, hCk⟩ := mem_filter.1 hC
    exact mem_filter.2 ⟨mem_univ _, hCk, hT C hCT⟩
  exact_mod_cast (card_le_card hsub).trans (card_connected_induce_le_exponential G hΔ k)

/-- **A percolation temperature.** For real `J`, `S` and `x` there is `β₀ > 0` such that
`x (e^{Jβ} − 1) e^{SJβ} ≤ 1/2` for every `0 ≤ β ≤ β₀`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1242–1245 ("for sufficiently small `β`"). -/
theorem exists_percolation_temperature (J S x : ℝ) :
    ∃ β₀ > 0, ∀ β, 0 ≤ β → β ≤ β₀ → x * ((exp (J * β) - 1) * exp (S * J * β)) ≤ 1 / 2 := by
  have hc : Continuous fun β : ℝ ↦ x * ((exp (J * β) - 1) * exp (S * J * β)) := by fun_prop
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc.continuousAt (1 / 2) (by norm_num)
  refine ⟨δ / 2, by linarith, fun β hβ0 hβ ↦ ?_⟩
  have hd : dist β 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]; linarith
  have := h hd
  simp only [mul_zero, exp_zero, sub_self, zero_mul, mul_zero, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

end Percolation

end TNLean.Lattice
