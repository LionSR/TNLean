/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import TNLean.Lattice.ClusterExpansion.Percolation
import TNLean.Lattice.ClusterExpansion.Truncation

/-!
# Hastings' percolation bound for clusters of large diameter

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1090–1114), defines the truncation
`ρ(β, l_proj)` of `e^{-βH}` by keeping the terms of its power series in which no cluster contains
two sites at distance larger than `l_proj`, and bounds the error of the truncation by equation
`perc2` (lines 1227–1254):

`Z⁻¹ |Tr (O ρ(β)) - Tr (O ρ(β, l_proj))| ≤ {exp[N exp(-l_proj/ξ_perc)] - 1} ‖O‖`.

This file states and proves that bound in the source's terms. The terms `h_k` of
`H = ∑_k h_k` act on supports `acts k` in a pseudometric space of sites, each support of diameter
at most `2R` (a term acting on the sites within `R` of its centre), and a set `C` of terms is
large when the support of `H_C` contains two sites at distance larger than `l_proj`
(`IsLargeDiam`). The overlap graph of the supports has maximum degree `Δ`.

* A connected set of `n` terms has support of diameter at most `2Rn`, so a large connected set
  has at least `⌊l_proj/(2R)⌋ + 1` terms.
* There are at most `N x^n` connected sets of `n` terms, with `N` the number of terms and
  `x = max(1, Δ²)` (the lattice-animal count, lines 1227–1229).
* A set `C` of terms and its boundary together have at most `(Δ + 1) n_C` terms.

With `y = (e^{βJ} - 1) e^{(Δ+1)Jβ}` and `0 < xy ≤ 1/2`, the error is at most
`‖O‖ (exp(N e^{-l/ξ}) - 1) Z` with `l = ⌊l_proj/(2R)⌋` and `ξ = 1/ln(1/(xy))`, and hence at most
`‖O‖ (exp(N (xy)^{-1} e^{-l_proj/ξ_perc}) - 1) Z` with `ξ_perc = 2R/ln(1/(xy))`, of order the
interaction range as the source states (line 1247).

**Local fix (size threshold):** the source starts the sum over cluster sizes at
`n = l_proj + 1` (line 1235), which presumes that a cluster of diameter larger than `l_proj` has
more than `l_proj` sites. With terms of range `R` only `n ≥ ⌊l_proj/(2R)⌋ + 1` holds, which is the
threshold used here; in units of distance this changes the constant `N` to `N (xy)^{-1}`.
Documented in `docs/paper-gaps/hastings05_percolation_cluster_size.tex`.

**Local fix (cluster boundary):** the boundary of a cluster is the set of terms whose support
meets the support of the cluster, the neighbours in the overlap graph, and the count
`n_C + n_B ≤ S n_C` of equation `percb2` holds with `S = Δ + 1`, which counts a term and its
overlap neighbours. Documented in `docs/paper-gaps/hastings05_cluster_boundary.tex`.

## Main results

* `TNLean.Lattice.ClusterExpansion.IsLargeDiam`: a set of terms whose support has diameter larger
  than `l_proj` (lines 1104–1107).
* `TNLean.Lattice.ClusterExpansion.dist_le_of_mem_biUnion_of_connected`: a connected set of `n`
  terms has support of diameter at most `2Rn`.
* `TNLean.Lattice.ClusterExpansion.card_ge_of_isLargeDiam`: a large connected set has at least
  `⌊l_proj/(2R)⌋ + 1` terms.
* `TNLean.Lattice.ClusterExpansion.card_add_card_boundary_le`: `n_C + n_{∂C} ≤ (Δ + 1) n_C`.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam`: equation
  `perc2` with the decay length `ξ = 1/ln(1/(xy))` in units of cluster size.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam_dist`:
  equation `perc2` with the decay length `ξ_perc = 2R/ln(1/(xy))` in units of distance.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1090–1114 and 1227–1254.
-/

open Finset Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice.ClusterExpansion

variable {κ σ : Type*} [PseudoMetricSpace σ] [DecidableEq σ]

section Diameter

/-- A set `C` of terms is *large* when the support `⋃_{k ∈ C} acts k` of `H_C` contains two sites
at distance larger than `l_proj`. The truncation `ρ(β, l_proj)` keeps the terms of the power
series with no large cluster. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1104–1107. -/
def IsLargeDiam (acts : κ → Finset σ) (lproj : ℝ) (C : Finset κ) : Prop :=
  ∃ a ∈ C.biUnion acts, ∃ b ∈ C.biUnion acts, lproj < dist a b

variable {acts : κ → Finset σ} {R : ℝ}

/-- Along a walk of length `m` in the overlap graph induced on `C`, the supports of the endpoints
contain sites at distance at most `2R(m + 1)` when every support has diameter at most `2R`:
consecutive supports share a site. -/
theorem dist_le_of_walk (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R)
    {C : Finset κ} {u v : (C : Set κ)}
    (p : ((overlapGraph acts).induce (C : Set κ)).Walk u v) {a b : σ} (ha : a ∈ acts u)
    (hb : b ∈ acts v) : dist a b ≤ 2 * R * (p.length + 1) := by
  induction p generalizing a with
  | nil => simpa using hR _ a ha b hb
  | @cons u w v hadj p ih =>
    obtain ⟨-, c, hc⟩ := SimpleGraph.comap_adj.mp hadj
    rw [mem_inter] at hc
    calc dist a b ≤ dist a c + dist c b := dist_triangle _ _ _
      _ ≤ 2 * R + 2 * R * (p.length + 1) := add_le_add (hR _ a ha c hc.1) (ih hc.2 hb)
      _ = 2 * R * ((SimpleGraph.Walk.cons hadj p).length + 1) := by
          rw [SimpleGraph.Walk.length_cons]; push_cast; ring

/-- **The diameter of a connected set of terms.** If every support has diameter at most `2R` and
the terms of `C` are connected in the overlap graph, the support of `H_C` has diameter at most
`2R n_C`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1097–1100 (active bonds have
length at most `2R`). -/
theorem dist_le_of_mem_biUnion_of_connected (hR0 : 0 ≤ R)
    (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R) {C : Finset κ}
    (hC : ((overlapGraph acts).induce (C : Set κ)).Connected) {a b : σ}
    (ha : a ∈ C.biUnion acts) (hb : b ∈ C.biUnion acts) : dist a b ≤ 2 * R * #C := by
  classical
  obtain ⟨i, hi, hai⟩ := mem_biUnion.1 ha
  obtain ⟨j, hj, hbj⟩ := mem_biUnion.1 hb
  obtain ⟨p⟩ := hC.preconnected ⟨i, hi⟩ ⟨j, hj⟩
  have hlen : (p.toPath : _).1.length < #C := by
    simpa using (p.toPath : _).2.length_lt
  refine (dist_le_of_walk hR (p.toPath : _).1 hai hbj).trans ?_
  have : ((p.toPath : _).1.length : ℝ) + 1 ≤ #C := by exact_mod_cast hlen
  gcongr

variable [Fintype κ] [DecidableEq κ]

/-- **The size threshold.** If every support has diameter at most `2R` with `R > 0`, a large
connected set of terms has at least `⌊l_proj/(2R)⌋ + 1` terms. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, line 1235, starts the sum at `l_proj + 1` instead; see
the module docstring. -/
theorem card_ge_of_isLargeDiam (hR0 : 0 < R)
    (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R) {lproj : ℝ} {C : Finset κ}
    (hC : C ∈ largeConnected (overlapGraph acts) (IsLargeDiam acts lproj)) :
    ⌊lproj / (2 * R)⌋₊ + 1 ≤ #C := by
  obtain ⟨hconn, a, ha, b, hb, hab⟩ := (mem_largeConnected _).1 hC
  have hd := dist_le_of_mem_biUnion_of_connected hR0.le hR hconn ha hb
  obtain ⟨i, hi, -⟩ := mem_biUnion.1 ha
  have hne : #C ≠ 0 := (card_pos.2 ⟨i, hi⟩).ne'
  rw [Nat.add_one_le_iff, Nat.floor_lt' hne, div_lt_iff₀ (by positivity)]
  linarith [mul_comm (2 * R) (#C : ℝ)]

end Diameter

section Boundary

variable [Fintype κ] [DecidableEq κ]

/-- **The boundary count.** In a graph of maximum degree `Δ`, a set `C` and its boundary have
together at most `(Δ + 1) n_C` elements. For the overlap graph this is the count
`n_C + n_B ≤ S n_C` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, line 1186, with
`S = Δ + 1`. -/
theorem card_add_card_boundary_le (G : SimpleGraph κ) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : ∀ k, G.degree k ≤ Δ) (C : Finset κ) : #C + #(boundary G C) ≤ (Δ + 1) * #C :=
  card_add_card_clusterBoundary_le _ C (fun i ↦ insert i (G.neighborFinset i))
    (fun i _ ↦ mem_insert_self i _)
    (fun j i _ hij ↦ mem_insert_of_mem ((G.mem_neighborFinset i j).2
      ((G.mem_neighborFinset j i).1 hij).symm))
    fun i _ ↦ (card_insert_le _ _).trans (by
      have := hΔ i; rw [G.card_neighborFinset_eq_degree]; omega)

end Boundary

section Percolation

variable [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {acts : κ → Finset σ} {R : ℝ}

open Classical in
/-- **Equation `perc2`, in units of cluster size.** Let the terms `h_k` of the Hermitian
`H = ∑_k h_k` be Hermitian with `‖h_k‖ ≤ J`, act on supports of diameter at most `2R` with
`R > 0`, and overlap at most `Δ` other terms each. Let `β ≥ 0`, `x = max(1, Δ²)`,
`y = (e^{βJ} - 1) e^{(Δ+1)Jβ}` and `0 < xy ≤ 1/2`. Then the truncation `ρ(β, l_proj)`, which
keeps the terms of the power series with no cluster of diameter larger than `l_proj`, satisfies
`|Tr (O (e^{-βH} - ρ(β, l_proj)))| ≤ ‖O‖ (exp(N e^{-l/ξ}) - 1) Tr e^{-βH}`, with `N` the number
of terms, `l = ⌊l_proj/(2R)⌋` and `ξ = 1/ln(1/(xy))`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1227–1254, with the size threshold of the module docstring. The hypothesis
`0 < xy` only excludes `β J = 0`, where the truncation is exact and `ξ` is undefined. -/
theorem norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam (hR0 : 0 < R)
    (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R) {Δ : ℕ}
    (hΔ : ∀ k, (overlapGraph acts).degree k ≤ Δ) (lproj : ℝ) {H : Matrix ι ι ℂ}
    (hHerm : H.IsHermitian) {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k)
    (hh : ∀ k, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ}
    (hβ : 0 ≤ β)
    (hxy0 : 0 < ((max 1 (Δ ^ 2) : ℕ) : ℝ) *
      ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))
    (hxy : ((max 1 (Δ ^ 2) : ℕ) : ℝ) *
      ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)) ≤ 1 / 2) :
    ‖(O * (NormedSpace.exp (-(β • H)) -
        truncatedExp (overlapGraph acts) (IsLargeDiam acts lproj) h β)).trace‖ ≤
      ‖O‖ * (Real.exp (Fintype.card κ * Real.exp (-(⌊lproj / (2 * R)⌋₊ /
          (Real.log (((max 1 (Δ ^ 2) : ℕ) : ℝ) *
            ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))⁻¹)⁻¹))) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  set G := overlapGraph acts
  set T := largeConnected G (IsLargeDiam acts lproj)
  set y := (Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)
  have hS : ∀ C ∈ T, ((#C : ℝ) + #(boundary G C)) ≤ ((Δ : ℝ) + 1) * #C := fun C _ ↦ by
    exact_mod_cast card_add_card_boundary_le G hΔ C
  refine (norm_trace_mul_exp_sub_truncatedExp_le G _ hHerm hH hh hJ O hβ hS).trans ?_
  have hZ := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  have hy : 0 ≤ y := (pos_of_mul_pos_right hxy0 (Nat.cast_nonneg _)).le
  rw [← sum_mul, ← mul_sum]
  gcongr
  calc ∑ U ∈ T.powerset with IsAdmissible G U ∧ U.Nonempty, ∏ C ∈ U, y ^ #C
      ≤ ∑ U ∈ T.powerset.erase ∅, ∏ C ∈ U, y ^ #C :=
        sum_le_sum_of_subset_of_nonneg (fun U hU ↦ by
          obtain ⟨hUT, -, hne⟩ := mem_filter.1 hU
          exact mem_erase.2 ⟨hne.ne_empty, hUT⟩)
          fun _ _ _ ↦ prod_nonneg fun _ _ ↦ pow_nonneg hy _
    _ ≤ _ := sum_nonempty_powerset_prod_le_percolation_connected G hΔ
        (fun C hC ↦ ((mem_largeConnected G).1 hC).1)
        (fun C hC ↦ card_ge_of_isLargeDiam hR0 hR hC) hy hxy0 hxy
        (fun _ _ ↦ pow_nonneg hy _) fun _ _ ↦ le_rfl

/-- `e^{-l/ξ} ≤ r^{-1} e^{-l_proj/ξ_perc}` for `l = ⌊l_proj/(2R)⌋`, `ξ = 1/ln(1/r)` and
`ξ_perc = 2R/ln(1/r)`, when `0 < r < 1` and `R > 0`: the passage from cluster size to distance,
using `l ≥ l_proj/(2R) - 1`. -/
theorem exp_neg_floor_div_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hR0 : 0 < R) (lproj : ℝ) :
    Real.exp (-(⌊lproj / (2 * R)⌋₊ / (Real.log r⁻¹)⁻¹)) ≤
      r⁻¹ * Real.exp (-(lproj / (2 * R / Real.log r⁻¹))) := by
  have hE : r⁻¹ = Real.exp (Real.log r⁻¹) := (Real.exp_log (inv_pos.2 hr0)).symm
  set L := Real.log r⁻¹ with hL
  have hL0 : 0 < L := Real.log_pos ((one_lt_inv₀ hr0).2 hr1)
  have hfl := Nat.sub_one_lt_floor (lproj / (2 * R))
  calc Real.exp (-(⌊lproj / (2 * R)⌋₊ / L⁻¹)) ≤ Real.exp (L + -(lproj / (2 * R / L))) := by
        refine Real.exp_le_exp.2 ?_
        rw [div_inv_eq_mul, show lproj / (2 * R / L) = L * (lproj / (2 * R)) by
          field_simp]
        nlinarith [mul_le_mul_of_nonneg_left hfl.le hL0.le]
    _ = r⁻¹ * Real.exp (-(lproj / (2 * R / L))) := by rw [Real.exp_add, ← hE]

open Classical in
/-- **Equation `perc2`, in units of distance.** Under the hypotheses of
`norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam`,
`|Tr (O (e^{-βH} - ρ(β, l_proj)))| ≤ ‖O‖ (exp(N (xy)^{-1} e^{-l_proj/ξ_perc}) - 1) Tr e^{-βH}`
with `ξ_perc = 2R/ln(1/(xy))`, of order the interaction range. After division by
`Z = Tr e^{-βH}` this is the source's `{exp[N exp(-l_proj/ξ_perc)] - 1} ‖O‖` with the constant
`N (xy)^{-1}` in place of `N` (see the module docstring). Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1246–1254. -/
theorem norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam_dist (hR0 : 0 < R)
    (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R) {Δ : ℕ}
    (hΔ : ∀ k, (overlapGraph acts).degree k ≤ Δ) (lproj : ℝ) {H : Matrix ι ι ℂ}
    (hHerm : H.IsHermitian) {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k)
    (hh : ∀ k, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ}
    (hβ : 0 ≤ β)
    (hxy0 : 0 < ((max 1 (Δ ^ 2) : ℕ) : ℝ) *
      ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))
    (hxy : ((max 1 (Δ ^ 2) : ℕ) : ℝ) *
      ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)) ≤ 1 / 2) :
    ‖(O * (NormedSpace.exp (-(β • H)) -
        truncatedExp (overlapGraph acts) (IsLargeDiam acts lproj) h β)).trace‖ ≤
      ‖O‖ * (Real.exp (Fintype.card κ *
          ((((max 1 (Δ ^ 2) : ℕ) : ℝ) *
            ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))⁻¹ *
          Real.exp (-(lproj / (2 * R / Real.log (((max 1 (Δ ^ 2) : ℕ) : ℝ) *
            ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))⁻¹))))) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  refine (norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam hR0 hR hΔ lproj hHerm hH hh hJ O
    hβ hxy0 hxy).trans ?_
  have hZ := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  have key := exp_neg_floor_div_le hxy0 (by linarith) hR0 lproj
  gcongr

end Percolation

end TNLean.Lattice.ClusterExpansion
