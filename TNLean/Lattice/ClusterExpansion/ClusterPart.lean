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

## References

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1174–1195. The source states the bound before equation `percb2` with `Tr(O e^{-βH})` on
the right; the form proved here, with `‖O‖ Tr e^{-βH}` and `‖H_C + H_B‖ ≤ (n_C + n_B) J`, is the
one equation `percb2` uses. The final step of `percb2`, `n_C + n_B ≤ S n_C`, is a property of
clusters on a lattice and is not made here.
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

/-- The cluster part as the alternating sum over the retained terms `E = C \ D`, in the form of
`Matrix.norm_trace_mul_sum_powerset_exp_le`. -/
theorem clusterPart_eq_sum_powerset (H : Matrix ι ι ℂ) (h : κ → Matrix ι ι ℂ)
    (B C : Finset κ) (β : ℝ) :
    clusterPart H h B C β =
      ∑ E ∈ C.powerset, (-1 : ℂ) ^ (C.card - E.card) •
        NormedSpace.exp (-(β • (H - ∑ k ∈ B, h k - ∑ k ∈ C, h k) + ∑ k ∈ E, β • h k)) := by
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

end TNLean.Lattice.ClusterExpansion
