/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceExpAlternatingSum

/-!
# The cluster part of the high-temperature expansion

Let `H` be a Hermitian Hamiltonian containing the Hermitian terms `h k`, let `C` be a cluster of
terms and `B` its boundary. Hastings' operator `ρ(β, C)` is the sum of the
terms of the power series of `e^{-βH}` that contain every `h i` with `i ∈ C` and no `h j` with
`j ∈ B`. By inclusion and exclusion it is the alternating sum

`ρ(β, C) = ∑_{D ⊆ C} (-1)^{|D|} e^{-β (H - H_B - H_D)}`,

with `H_D = ∑_{k ∈ D} h k`, which is the definition used here. If `‖h k‖ ≤ J` on `B ∪ C` and
`β ≥ 0`, then for every observable `O`,

`|Tr (O ρ(β, C))| ≤ ‖O‖ (e^{βJ} - 1)^{n_C} e^{(n_C + n_B) J β} Tr e^{-βH}`.

## Main results

* `TNLean.Lattice.ClusterExpansion.clusterPart`: the operator `ρ(β, C)`.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_clusterPart_le`: the bound above.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_clusterPart_le_pow`: equation `percb2`, the
  bound `‖O‖ y^{n_C} Tr e^{-βH}` when `n_C + n_B ≤ S n_C`.
* `TNLean.Lattice.ClusterExpansion.norm_trace_mul_clusterPart_biUnion_le`: the same bound for
  several disjoint clusters, `‖O‖ ∏_i y^{n_{C_i}} Tr e^{-βH}`.
* `TNLean.Lattice.ClusterExpansion.card_add_card_clusterBoundary_le`: the count
  `n_C + n_{B(C)} ≤ S n_C` when the terms acting on each site lie in a set of at most `S`.

## References

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1174–1195.

**Local fix (right side of the single-cluster bound):** the source states the bound before
equation `percb2` with `Tr(O e^{-βH})` on the right, which fails as printed; the form proved here,
with `‖O‖ Tr e^{-βH}` and `‖H_C + H_B‖ ≤ (n_C + n_B) J`, is the one equation `percb2` uses.
Documented in `docs/paper-gaps/hastings05_cluster_part_trace_pairing.tex`.

The final step of `percb2`, `n_C + n_B ≤ S n_C`, is a property of clusters on a lattice, proved
by `card_add_card_clusterBoundary_le`.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice.ClusterExpansion

open Finset Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- Hastings' operator `ρ(β, C)`: the terms of the power series of `e^{-βH}` containing every
term of the cluster `C` and no term of its boundary `B`, written by inclusion and exclusion as
`∑_{D ⊆ C} (-1)^{|D|} e^{-β (H - H_B - H_D)}`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1174–1177. -/
noncomputable def clusterPart (H : Matrix ι ι ℂ) (h : κ → Matrix ι ι ℂ) (B C : Finset κ)
    (β : ℝ) : Matrix ι ι ℂ :=
  ∑ D ∈ C.powerset, (-1 : ℂ) ^ D.card •
    NormedSpace.exp (-(β • (H - ∑ k ∈ B, h k - ∑ k ∈ D, h k)))

omit [DecidableEq κ] in
/-- The cluster part as the alternating sum over the retained terms `E = C \ D`, in the form of
`Matrix.norm_trace_mul_sum_powerset_exp_le`. -/
theorem clusterPart_eq_sum_powerset (H : Matrix ι ι ℂ) (h : κ → Matrix ι ι ℂ)
    (B C : Finset κ) (β : ℝ) :
    clusterPart H h B C β =
      ∑ E ∈ C.powerset, (-1 : ℂ) ^ (C.card - E.card) •
        NormedSpace.exp (-(β • (H - ∑ k ∈ B, h k - ∑ k ∈ C, h k) + ∑ k ∈ E, β • h k)) := by
  classical
  refine Finset.sum_nbij' (fun D ↦ C \ D) (fun E ↦ C \ E) ?_ ?_ ?_ ?_ ?_
  · intro D _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro E _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro D hD
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hD)
  · intro E hE
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hE)
  · intro D hD
    have hDC := Finset.mem_powerset.mp hD
    have hcard : C.card - (C \ D).card = D.card := by
      rw [Finset.card_sdiff_of_subset hDC]
      exact Nat.sub_sub_self (Finset.card_le_card hDC)
    have hexp : β • (H - ∑ k ∈ B, h k - ∑ k ∈ C, h k) + ∑ k ∈ C \ D, β • h k =
        β • (H - ∑ k ∈ B, h k - ∑ k ∈ D, h k) := by
      rw [← Finset.smul_sum, ← smul_add, ← Finset.sum_sdiff hDC]
      congr 1
      abel
    rw [hcard, hexp]

/-- **The single-cluster bound of the high-temperature expansion.** For a Hermitian `H`,
Hermitian terms `h k` with `‖h k‖ ≤ J` on a cluster `C` and its boundary `B`, `β ≥ 0` and every
`O`, `|Tr (O ρ(β, C))| ≤ ‖O‖ (e^{βJ} - 1)^{n_C} e^{(n_C + n_B) J β} Tr e^{-βH}`.

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1174–1195: the bound before
equation `percb2` with `‖O‖ Tr e^{-βH}` in place of the printed `Tr(O e^{-βH})`, and with
`‖H_C + H_{B(C)}‖ ≤ (n_C + n_{B(C)}) J`. The source's boundary is disjoint from the cluster; the
bound does not need this. -/
theorem norm_trace_mul_clusterPart_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {h : κ → Matrix ι ι ℂ} {B C : Finset κ}
    (hh : ∀ k ∈ B ∪ C, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k ∈ B ∪ C, ‖h k‖ ≤ J)
    (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) :
    ‖(O * clusterPart H h B C β).trace‖ ≤
      ‖O‖ * (Real.exp (β * J) - 1) ^ C.card * Real.exp ((C.card + B.card) * J * β) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  have hBsub : B ⊆ B ∪ C := Finset.subset_union_left
  have hCsub : C ⊆ B ∪ C := Finset.subset_union_right
  have hsumH : ∀ T ⊆ B ∪ C, (∑ k ∈ T, h k).IsHermitian := fun T hT ↦
    (isSelfAdjoint_sum T fun k hk ↦ (hh k (hT hk)).isSelfAdjoint).isHermitian
  have hsum : ∀ T ⊆ B ∪ C, ‖∑ k ∈ T, h k‖ ≤ T.card * J := fun T hT ↦
    (norm_sum_le _ _).trans <| by
      simpa using Finset.sum_le_sum fun k hk ↦ hJ k (hT hk)
  have hY : (β • (H - ∑ k ∈ B, h k - ∑ k ∈ C, h k)).IsHermitian :=
    ((hH.sub (hsumH B hBsub)).sub (hsumH C hCsub)).smul (IsSelfAdjoint.all β)
  have hg : ∀ k ∈ C, (β • h k).IsHermitian := fun k hk ↦
    (hh k (hCsub hk)).smul (IsSelfAdjoint.all β)
  have hgJ : ∀ k ∈ C, ‖β • h k‖ ≤ β * J := fun k hk ↦ by
    rw [norm_smul, Real.norm_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (hJ k (hCsub hk)) hβ
  -- The alternating-sum bound, with `Y = β (H - H_B - H_C)` and the terms `β h k`.
  have h1 : ‖(O * clusterPart H h B C β).trace‖ ≤ ‖O‖ * (Real.exp (β * J) - 1) ^ C.card *
      (NormedSpace.exp (-(β • (H - ∑ k ∈ B, h k - ∑ k ∈ C, h k)))).trace.re := by
    rw [clusterPart_eq_sum_powerset]
    exact Matrix.norm_trace_mul_sum_powerset_exp_le_pow C hY (fun k ↦ β • h k) hg hgJ O
  -- The trace of `e^{-Y}` against the partition function.
  have hV : (β • (∑ k ∈ B, h k + ∑ k ∈ C, h k)).IsHermitian :=
    ((hsumH B hBsub).add (hsumH C hCsub)).smul (IsSelfAdjoint.all β)
  have hX : (-(β • H)).IsHermitian := (hH.smul (IsSelfAdjoint.all β)).neg
  have hYV : -(β • (H - ∑ k ∈ B, h k - ∑ k ∈ C, h k)) =
      -(β • H) + β • (∑ k ∈ B, h k + ∑ k ∈ C, h k) := by
    rw [smul_sub, smul_sub, smul_add]
    abel
  have hnormV : ‖β • (∑ k ∈ B, h k + ∑ k ∈ C, h k)‖ ≤ (C.card + B.card) * J * β := by
    rw [norm_smul, Real.norm_of_nonneg hβ]
    calc β * ‖∑ k ∈ B, h k + ∑ k ∈ C, h k‖
        ≤ β * (B.card * J + C.card * J) :=
          mul_le_mul_of_nonneg_left
            ((norm_add_le _ _).trans (add_le_add (hsum B hBsub) (hsum C hCsub))) hβ
      _ = (C.card + B.card) * J * β := by ring
  have hZ : 0 ≤ (NormedSpace.exp (-(β • H))).trace.re := by
    rw [hX.re_trace_exp_eq_sum]
    exact Finset.sum_nonneg fun i _ ↦ (Real.exp_pos _).le
  have h2 : (NormedSpace.exp (-(β • (H - ∑ k ∈ B, h k - ∑ k ∈ C, h k)))).trace.re ≤
      Real.exp ((C.card + B.card) * J * β) * (NormedSpace.exp (-(β • H))).trace.re := by
    rw [hYV]
    exact (hX.re_trace_exp_add_le hV).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hnormV) hZ)
  -- The cluster factor is nonnegative: `J ≥ 0` as soon as the cluster is nonempty.
  have hP : 0 ≤ ‖O‖ * (Real.exp (β * J) - 1) ^ C.card := by
    refine mul_nonneg (norm_nonneg _) ?_
    rcases C.eq_empty_or_nonempty with hC | ⟨k, hk⟩
    · simp [hC]
    · have hJ0 : 0 ≤ J := (norm_nonneg _).trans (hJ k (hCsub hk))
      exact pow_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hβ hJ0))) _
  calc ‖(O * clusterPart H h B C β).trace‖
      ≤ ‖O‖ * (Real.exp (β * J) - 1) ^ C.card *
          (NormedSpace.exp (-(β • (H - ∑ k ∈ B, h k - ∑ k ∈ C, h k)))).trace.re := h1
    _ ≤ ‖O‖ * (Real.exp (β * J) - 1) ^ C.card *
        (Real.exp ((C.card + B.card) * J * β) * (NormedSpace.exp (-(β • H))).trace.re) :=
      mul_le_mul_of_nonneg_left h2 hP
    _ = _ := by ring

/-- **Equation `percb2`.** If the cluster and its boundary satisfy `n_C + n_B ≤ S n_C`, then
`|Tr (O ρ(β, C))| ≤ ‖O‖ y^{n_C} Tr e^{-βH}` with `y = (e^{βJ} - 1) e^{SJβ}`.

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1186–1195, multiplied by
`Z = Tr e^{-βH}`; the source states it as `Z⁻¹ Tr (O ρ(β, C)) ≤ ‖O‖ y^{n_C}`. The source
derives `n_C + n_B ≤ S n_C` from the lattice; here it is the hypothesis `hS`, which
`card_add_card_clusterBoundary_le` supplies. -/
theorem norm_trace_mul_clusterPart_le_pow {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {h : κ → Matrix ι ι ℂ} {B C : Finset κ}
    (hh : ∀ k ∈ B ∪ C, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k ∈ B ∪ C, ‖h k‖ ≤ J)
    (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) {S : ℝ}
    (hS : (C.card + B.card : ℝ) ≤ S * C.card) :
    ‖(O * clusterPart H h B C β).trace‖ ≤
      ‖O‖ * ((Real.exp (β * J) - 1) * Real.exp (S * J * β)) ^ C.card *
        (NormedSpace.exp (-(β • H))).trace.re := by
  have hZ : 0 ≤ (NormedSpace.exp (-(β • H))).trace.re := by
    rw [(hH.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_eq_sum]
    exact Finset.sum_nonneg fun i _ ↦ (Real.exp_pos _).le
  -- `(n_C + n_B) J β ≤ S n_C J β`, using `J ≥ 0` when `B ∪ C` is nonempty.
  have hexp : Real.exp ((C.card + B.card) * J * β) ≤ Real.exp (S * J * β) ^ C.card := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    rcases (B ∪ C).eq_empty_or_nonempty with hBC | ⟨k, hk⟩
    · obtain ⟨hB, hC⟩ := Finset.union_eq_empty.mp hBC
      simp [hB, hC]
    · have hJβ : 0 ≤ J * β := mul_nonneg ((norm_nonneg _).trans (hJ k hk)) hβ
      calc (C.card + B.card : ℝ) * J * β = (C.card + B.card) * (J * β) := by ring
        _ ≤ S * C.card * (J * β) := mul_le_mul_of_nonneg_right hS hJβ
        _ = C.card * (S * J * β) := by ring
  have hP : 0 ≤ ‖O‖ * (Real.exp (β * J) - 1) ^ C.card := by
    refine mul_nonneg (norm_nonneg _) ?_
    rcases C.eq_empty_or_nonempty with hC | ⟨k, hk⟩
    · simp [hC]
    · have hJ0 : 0 ≤ J := (norm_nonneg _).trans (hJ k (Finset.mem_union_right _ hk))
      exact pow_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hβ hJ0))) _
  calc ‖(O * clusterPart H h B C β).trace‖
      ≤ ‖O‖ * (Real.exp (β * J) - 1) ^ C.card * Real.exp ((C.card + B.card) * J * β) *
          (NormedSpace.exp (-(β • H))).trace.re :=
        norm_trace_mul_clusterPart_le hH hh hJ O hβ
    _ ≤ ‖O‖ * (Real.exp (β * J) - 1) ^ C.card * Real.exp (S * J * β) ^ C.card *
          (NormedSpace.exp (-(β • H))).trace.re :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hP) hZ
    _ = _ := by rw [mul_pow, ← mul_assoc]

/-- **Several clusters.** For pairwise disjoint clusters `C i`, `i ∈ T`, with boundaries `B i`
satisfying `n_{C_i} + n_{B_i} ≤ S n_{C_i}`, the operator `ρ(β, C_1, …, C_m)` of the terms containing
every cluster and no boundary term satisfies
`|Tr (O ρ(β, C_1, …, C_m))| ≤ ‖O‖ (∏_i y^{n_{C_i}}) Tr e^{-βH}` with `y = (e^{βJ} - 1) e^{SJβ}`.

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1218–1224 (the remark added after the
bound on `ρ_m`): the bound on `ρ(β, C_1, C_2, …)` derived in the same way as equation `percb2`.
For clusters of one term of the power series, no cluster meets the boundary of another, so the
cluster part of the union with the union of the boundaries is that operator. -/
theorem norm_trace_mul_clusterPart_biUnion_le {ν : Type*} {T : Finset ν}
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {h : κ → Matrix ι ι ℂ} {B C : ν → Finset κ}
    (hdisj : (T : Set ν).PairwiseDisjoint C)
    (hh : ∀ k ∈ T.biUnion B ∪ T.biUnion C, (h k).IsHermitian) {J : ℝ}
    (hJ : ∀ k ∈ T.biUnion B ∪ T.biUnion C, ‖h k‖ ≤ J)
    (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) {S : ℝ}
    (hS : ∀ i ∈ T, ((C i).card + (B i).card : ℝ) ≤ S * (C i).card) :
    ‖(O * clusterPart H h (T.biUnion B) (T.biUnion C) β).trace‖ ≤
      ‖O‖ * (∏ i ∈ T, ((Real.exp (β * J) - 1) * Real.exp (S * J * β)) ^ (C i).card) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  have hCcard : (T.biUnion C).card = ∑ i ∈ T, (C i).card := Finset.card_biUnion hdisj
  have hS' : ((T.biUnion C).card + (T.biUnion B).card : ℝ) ≤ S * (T.biUnion C).card := by
    have hB : ((T.biUnion B).card : ℝ) ≤ ∑ i ∈ T, ((B i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    rw [hCcard]
    push_cast
    calc (∑ i ∈ T, ((C i).card : ℝ)) + ((T.biUnion B).card : ℝ)
        ≤ ∑ i ∈ T, (((C i).card : ℝ) + (B i).card) := by
          rw [Finset.sum_add_distrib]; linarith
      _ ≤ ∑ i ∈ T, S * (C i).card := Finset.sum_le_sum hS
      _ = S * ∑ i ∈ T, ((C i).card : ℝ) := (Finset.mul_sum _ _ _).symm
  rw [Finset.prod_pow_eq_pow_sum, ← hCcard]
  exact norm_trace_mul_clusterPart_le_pow hH hh hJ O hβ hS'

section Boundary

variable [Fintype κ]

/-- The boundary `B(C)` of a cluster `C` of term centres: the terms `j ∉ C` acting on some site of
`C`, where `acts j` is the set of sites on which `H_j` acts. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1131–1134. -/
def clusterBoundary (acts : κ → Finset κ) (C : Finset κ) : Finset κ :=
  {j | j ∉ C ∧ ∃ i ∈ C, i ∈ acts j}

/-- **The boundary count.** Let `nbhd i` contain `i` and every term acting on the site `i`, with
at most `S` elements for each site of `C`. Then `n_C + n_{B(C)} ≤ S n_C`, the hypothesis of
`norm_trace_mul_clusterPart_le_pow`. In Hastings' setting `nbhd i` is the set of sites within the
interaction range `R` of `i`, of which there are at most `S`, and `H_j` acts only within distance
`R` of `j`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 181–183 and 1186. -/
theorem card_add_card_clusterBoundary_le (acts : κ → Finset κ) (C : Finset κ)
    (nbhd : κ → Finset κ) (hself : ∀ i ∈ C, i ∈ nbhd i)
    (hacts : ∀ j, ∀ i ∈ C, i ∈ acts j → j ∈ nbhd i) {S : ℕ} (hS : ∀ i ∈ C, #(nbhd i) ≤ S) :
    #C + #(clusterBoundary acts C) ≤ S * #C := by
  have hdisj : Disjoint C (clusterBoundary acts C) :=
    Finset.disjoint_left.mpr fun i hi hiB ↦ (Finset.mem_filter.mp hiB).2.1 hi
  have hsub : C ∪ clusterBoundary acts C ⊆ C.biUnion nbhd := by
    intro j hj
    rw [Finset.mem_biUnion]
    rcases Finset.mem_union.mp hj with hjC | hjB
    · exact ⟨j, hjC, hself j hjC⟩
    · obtain ⟨-, -, i, hi, hij⟩ := Finset.mem_filter.mp hjB
      exact ⟨i, hi, hacts j i hi hij⟩
  rw [← Finset.card_union_of_disjoint hdisj]
  calc #(C ∪ clusterBoundary acts C) ≤ #(C.biUnion nbhd) := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ C, #(nbhd i) := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ C, S := Finset.sum_le_sum hS
    _ = S * #C := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end Boundary

end TNLean.Lattice.ClusterExpansion
