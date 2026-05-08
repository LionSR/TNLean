/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.EqualProportional
import TNLean.MPS.FundamentalTheorem.OverlapConvergenceAux
import TNLean.MPS.Overlap.SelfOverlapAux

/-!
# Auxiliary lemmas for heterogeneous equal-case block matching

This module collects small auxiliary lemmas used by the two core lemmas
`exists_nondecaying_overlap_of_sameMPV₂_CFBNT`
(`TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap`) and
`blocks_match_of_sameMPV₂_CFBNT` (`TNLean.MPS.FundamentalTheorem.Full.BlocksMatch`)
that together prove the self-contained equal-case fundamental theorem
`fundamentalTheorem_equalMPV_CFBNT_hetero` in `TNLean.MPS.FundamentalTheorem.Full`.
That declaration is a restricted CFBNT comparison lemma rather than the full
source-paper Fundamental Theorem.

## Main statements

* `tendsto_inner_zero_swap`: swapping a decaying overlap conjugates the inner product.
* `eq_one_of_pow_tendsto_nhds_one`: powers converging to `1` force the base to be `1`.

The companion `tendsto_norm_selfOverlap_one`, also used in this file's downstream
consumers, lives upstream in `TNLean.MPS.Overlap.SelfOverlapAux`.

This file collects public auxiliary lemmas used by heterogeneous equal-case
block matching.

## References

* Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
* Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled
  pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.

## Tags

matrix product states, block matching, gauge-phase equivalence, overlap, helpers
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-! ## Helpers for the heterogeneous equal-case fundamental theorem -/

/-- Swapping a decaying overlap conjugates the corresponding inner product. -/
lemma tendsto_inner_zero_swap
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds 0)) :
    Tendsto (fun N => mpvInner (d := d) B A N) atTop (nhds 0) := by
  have hAB := tendsto_inner_zero A B h
  have hSwap :
      (fun N => mpvInner (d := d) B A N) =
        fun N => star (mpvInner (d := d) A B N) := by
    ext N
    simp [mpvInner, inner_conj_symm]
  rw [hSwap]
  simpa using hAB.star

/-- If the powers of a complex number converge to `1`, then the number itself is `1`. -/
lemma eq_one_of_pow_tendsto_nhds_one {c : ℂ}
    (hc : Tendsto (fun N : ℕ => c ^ N) atTop (nhds 1)) :
    c = 1 := by
  have h_shift : Tendsto (fun N : ℕ => c ^ (N + 1)) atTop (nhds 1) :=
    hc.comp (tendsto_add_atTop_nat 1)
  have h_mul : Tendsto (fun N : ℕ => c * c ^ N) atTop (nhds (c * 1)) :=
    tendsto_const_nhds.mul hc
  have h_eq_fun : (fun N : ℕ => c ^ (N + 1)) = fun N : ℕ => c * c ^ N := by
    ext N
    rw [pow_succ, mul_comm]
  have hlim := tendsto_nhds_unique (h_eq_fun ▸ h_shift) h_mul
  simpa using hlim.symm

end MPSTensor
