/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BNTBlockIntersection
import TNLean.MPS.CanonicalForm.PGVWC07CanonicalForm
import TNLean.MPS.MPDO.BiCFDerivation.Selectors
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan

/-!
# Cut rank of a translation-invariant canonical form

**Source.** Pérez-García, Verstraete, Wolf, Cirac 2007 (arXiv:quant-ph/0608197),
`Papers/quant-ph_0608197/MPSarchive.tex` lines 1320–1326 (the state of a canonical form is
the sum of the weighted block states), lines 1346–1349 (the direct-sum lemma), and the proof
of the W-state corollary, lines 2187–2225: cutting a periodic canonical form with condition
C1 in each block into two pieces, each of length at least \(3(b-1)(L_0+1)\), the reduced
state of one piece has rank at least \(\sum_j D_j^2\).

**Formalized here.** The simultaneous product span of the blocks of a canonical form at
every length at least \(\max(L_0, 3(b-1)(L_0+1))\), from condition C1 in each block and the
direct-sum lemma; and the rank inequality of the claim at lines 2193–2204, in the form: if
the functions of the first piece obtained by fixing the second piece lie in a subspace
\(V\), then \(\sum_j D_j^2\le\dim V\).

## Main results

* `Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose` — block injectivity of the adjoint
  family gives block injectivity at the same length.
* `MPSTensor.wordTupleSpanTop_of_le_one` — a family of at most one block spans simultaneously
  wherever its block is injective.
* `MPSTensor.PGVWC07CanonicalFormData.wordTupleSpanTop_of_ge` — the simultaneous product span
  of the blocks beyond the direct-sum length.
* `MPSTensor.sum_sq_dim_le_finrank_of_forall_mem` — the cut-rank lower bound
  \(\sum_j D_j^2\le\dim V\).

The block expansion of the amplitudes and the irreducibility of the blocks are proved with the
canonical form itself, in `TNLean.MPS.CanonicalForm.PGVWC07CanonicalForm`. This file sits next
to the direct-sum lemma for canonical-form blocks, `BNTBlockIntersection`, which it applies.

## References

- [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) -- Pérez-García,
  Verstraete, Wolf, Cirac, *Matrix Product State Representations*
-/

open scoped Matrix BigOperators ComplexOrder

namespace Kraus

variable {d D : ℕ}

/-- Bridge: block injectivity passes from the adjoint family `K_i^†` to `K`, since conjugate
transposition maps the words of `K^†` of length `L` onto the reversed words of `K`. -/
theorem isNBlkInjective_of_isNBlkInjective_conjTranspose
    {K : Fin d → Matrix (Fin D) (Fin D) ℂ} {L : ℕ}
    (hK : IsNBlkInjective (fun i => (K i)ᴴ) L) : IsNBlkInjective K L := by
  unfold IsNBlkInjective wordSpan at hK ⊢
  refine eq_top_iff.mpr fun X _ => ?_
  have key : ∀ Y ∈ Submodule.span ℂ
      (Set.range fun σ : Fin L → Fin d => evalWord (fun i => (K i)ᴴ) (List.ofFn σ)),
      Yᴴ ∈ Submodule.span ℂ
        (Set.range fun σ : Fin L → Fin d => evalWord K (List.ofFn σ)) := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ, rfl⟩ := hx
      refine Submodule.subset_span ⟨σ ∘ Fin.rev, ?_⟩
      simp only [evalWord_conjTranspose, Matrix.conjTranspose_conjTranspose, List.ofFn_reverse]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.conjTranspose_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Matrix.conjTranspose_smul]; exact Submodule.smul_mem _ _ hx
  simpa using key Xᴴ (by rw [hK]; exact Submodule.mem_top)

end Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- Bridge: a family of at most one block spans the product algebra at a length where its
block is injective. -/
theorem wordTupleSpanTop_of_le_one {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) (hr : r ≤ 1) {L : ℕ}
    (hA : ∀ k, Kraus.IsNBlkInjective (A k) L) : WordTupleSpanTop A L := by
  classical
  unfold WordTupleSpanTop
  refine eq_top_iff.mpr fun M _ => ?_
  interval_cases r
  · rw [Subsingleton.elim M 0]; exact Submodule.zero_mem _
  · have hM : M 0 ∈ Submodule.span ℂ
        (Set.range fun σ : Fin L → Fin d => Kraus.evalWord (A 0) (List.ofFn σ)) := by
      rw [(hA 0).span_eq_top]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hM
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, funext fun k => ?_⟩
    rw [Fin.fin_one_eq_zero k, ← hc, Finset.sum_apply]
    rfl

namespace PGVWC07CanonicalFormData

variable {A : MPSTensor d D} (h : PGVWC07CanonicalFormData A)

/-- Source: arXiv:quant-ph/0608197, direct-sum lemma (lines 1346–1349) together with
condition C1 in each block (lines 1314–1323), as used in the proof of the W-state corollary
(lines 2193–2222). For a canonical form with condition C1 at length `L₀` in each block and
pairwise distinct blocks, the tuples of block words of any length `n ≥ max(L₀, 3(b-1)(L₀+1))`
span the product of the block matrix algebras.

**Stricter hypothesis.** The source assumes, without loss of generality, only that the block
states `|φ_{A^j}⟩` are pairwise different (lines 1329–1330). The hypothesis
`BlocksNotGaugePhaseEquiv` used here, the one the direct-sum lemma is formalized with, is
stronger: two equal blocks with different weights, or two blocks related by a gauge and a
phase `ω` with `ω^N ≠ 1`, give different states but violate it. The source's reduction to
pairwise different states does not supply it, and removing it is not formalized; see
`docs/paper-gaps/rmp_w_state_ti_bound.tex`. The length `L₀` in the threshold covers a single
block, where the direct-sum lemma is vacuous and the source length `3(b-1)(L₀+1)` is zero. -/
theorem wordTupleSpanTop_of_ge {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hC1 : ∀ k, Kraus.IsNBlkInjective (h.blocks k) L₀)
    (hDistinct : BlocksNotGaugePhaseEquiv (d := d) h.blocks)
    {n : ℕ} (hn : max L₀ (3 * (h.r - 1) * (L₀ + 1)) ≤ n) :
    WordTupleSpanTop h.blocks n := by
  have : ∀ k, NeZero (h.dim k) := fun k => ⟨(h.dim_pos k).ne'⟩
  rcases le_or_gt h.r 1 with hr | hr
  · exact wordTupleSpanTop_of_ge_of_unital _
      (wordTupleSpanTop_of_le_one _ hr hC1) h.unital (le_of_max_le_left hn)
  · choose Λ hΛ _ hΛfix using h.dual_fixedPoint
    refine wordTupleSpanTop_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint
      h.blocks hr (HasIrreducibleBlocks.ofForall h.isIrreducibleFamily_blocks)
      hDistinct Λ hΛ (fun j => ?_) hC1 hL₀ h.unital ?_
    · rw [Kraus.transferMap_apply]
      simpa only [Matrix.conjTranspose_conjTranspose] using hΛfix j
    · calc (h.r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))
          = 3 * (h.r - 1) * (L₀ + 1) := by ring
        _ ≤ n := le_of_max_le_right hn

end PGVWC07CanonicalFormData

/-- The linear map sending a tuple of block matrices `Δ` to the function
`σ ↦ ∑_k tr(Δ_k A^k_σ)` on words of length `R`. -/
noncomputable def blockTracePairing {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) (R : ℕ) :
    ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₗ[ℂ]
      ((Fin R → Fin d) → ℂ) where
  toFun Δ σ := ∑ k, Matrix.trace (Δ k * Kraus.evalWord (A k) (List.ofFn σ))
  map_add' Δ Δ' := by
    funext σ
    simp [Matrix.add_mul, Matrix.trace_add, Finset.sum_add_distrib]
  map_smul' c Δ := by
    funext σ
    simp [Matrix.trace_smul, Finset.mul_sum]

/-- Source: arXiv:quant-ph/0608197, proof of the W-state corollary, lines 2193–2222 (the
claim that the vectors `|Φ_{α,β}⟩` and `|Ψ_{α,β}⟩`, `(α, β) ∈ S`, are linearly independent,
so that the reduced state of the first `R` sites has rank at least `∑_j D_j^2`).

Let the block words of lengths `R` and `R'` span the product of the block matrix algebras,
and let `c_k ≠ 0`. If, for every word `τ` of length `R'`, the function
`σ ↦ ∑_k c_k tr(A^k_σ A^k_τ)` of words of length `R` lies in a subspace `V`, then
`∑_k D_k^2 ≤ dim V`. The span hypotheses are the source's direct-sum lemma and condition C1
by blocks, supplied by `PGVWC07CanonicalFormData.wordTupleSpanTop_of_ge`. -/
theorem sum_sq_dim_le_finrank_of_forall_mem {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) (c : Fin r → ℂ) (hc : ∀ k, c k ≠ 0)
    {R R' : ℕ} (hR : WordTupleSpanTop A R) (hR' : WordTupleSpanTop A R')
    (V : Submodule ℂ ((Fin R → Fin d) → ℂ))
    (hV : ∀ τ : Fin R' → Fin d,
      (fun σ : Fin R → Fin d => ∑ k, c k *
        Matrix.trace (Kraus.evalWord (A k) (List.ofFn σ) *
          Kraus.evalWord (A k) (List.ofFn τ))) ∈ V) :
    ∑ k, dim k ^ 2 ≤ Module.finrank ℂ V := by
  classical
  set Ψ := blockTracePairing A R
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro Δ hΔ
    funext k
    exact block_matrices_eq_zero_of_wordTupleSpanTop_trace A hR Δ
      (fun σ => congrFun (LinearMap.mem_ker.mp hΔ) σ) k
  -- The scaled word tuples of length `R'` still span.
  set T : (Fin R' → Fin d) → ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
    fun τ k => c k • Kraus.evalWord (A k) (List.ofFn τ)
  have hT : Submodule.span ℂ (Set.range T) = ⊤ := by
    refine eq_top_iff.mpr fun M _ => ?_
    have hM : (fun k => (c k)⁻¹ • M k) ∈
        Submodule.span ℂ (Set.range (wordTuple A R')) := by
      rw [hR']; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hM
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨a, funext fun k => ?_⟩
    have hk := congrFun ha k
    simp only [Finset.sum_apply, Pi.smul_apply, wordTuple] at hk
    simp only [Finset.sum_apply, Pi.smul_apply, T]
    simp_rw [smul_comm (a _) (c k)]
    rw [← Finset.smul_sum, hk, smul_smul, mul_inv_cancel₀ (hc k), one_smul]
  have hrange : LinearMap.range Ψ ≤ V := by
    rw [LinearMap.range_eq_map, ← hT, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
    refine SetLike.mem_coe.mpr ?_
    convert hV τ using 1
    funext σ
    simp only [Ψ, blockTracePairing, LinearMap.coe_mk, AddHom.coe_mk, T, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_comm]
  calc ∑ k, dim k ^ 2
      = Module.finrank ℂ ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
        rw [Module.finrank_pi_fintype]
        simp [Module.finrank_matrix, sq]
    _ = Module.finrank ℂ (LinearMap.range Ψ) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank ℂ V := Submodule.finrank_mono hrange

end MPSTensor
