/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.EqualProportional
import TNLean.MPS.FundamentalTheorem.OverlapConvergenceAux

/-!
# Helpers for the heterogeneous equal-case fundamental theorem

This module collects small helper lemmas used by the two core private lemmas
`exists_nondecaying_overlap_of_sameMPV₂_CFBNT`
(`TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap`) and
`blocks_match_of_sameMPV₂_CFBNT` (`TNLean.MPS.FundamentalTheorem.Full.BlocksMatch`)
that together prove the self-contained equal-case fundamental theorem
`fundamentalTheorem_equalMPV_CFBNT_hetero` in `TNLean.MPS.FundamentalTheorem.Full`.

## Main statements

* `tendsto_norm_selfOverlap_one`: normed form of a self-overlap tending to `1`.
* `tendsto_inner_zero_swap`: swapping a decaying overlap conjugates the inner product.
* `mpvOverlap_eq_selfOverlap_of_forall_mpv_eq`: pointwise equal MPVs imply cross-overlap
  equals self-overlap of the first tensor.
* `gaugePhaseEquiv_of_block_sameMPV₂`: per-block `SameMPV₂` combined with block properties
  yields dimension equality and `GaugePhaseEquiv` (Layer 2 of the proof architecture).

## References

* Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
* Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled
  pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.

## Tags

matrix product states, fundamental theorem, gauge-phase equivalence, overlap, helpers
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-! ## Helpers for the heterogeneous equal-case fundamental theorem -/

/-- Overlap of two blocks with pointwise-equal MPVs equals the self-overlap of the first. -/
private lemma mpvOverlap_eq_selfOverlap_of_forall_mpv_eq
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ) :
    ∀ N, mpvOverlap (d := d) A B N = mpvOverlap (d := d) A A N := by
  intro N
  simp only [mpvOverlap, h]

/-- Norm-convergence version of normalized self-overlap convergence. -/
lemma tendsto_norm_selfOverlap_one
    {D : ℕ} (A : MPSTensor d D)
    (hA : Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ))) :
    Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1) := by
  simpa [norm_one] using hA.norm

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

/-- **Layer 2: Per-block `SameMPV₂` + block properties → dim equality + GaugePhaseEquiv.**

Given two individual blocks with pointwise-equal MPVs, both injective and left-canonical,
and with the first block's self-overlap tending to 1:
1. The cross-overlap equals the self-overlap (→ 1), hence does not decay to 0.
2. Dimension mismatch would force overlap → 0 (`mpvOverlap_tendsto_zero_of_dim_ne`).
   Contradiction ⟹ dimensions match.
3. Non-gauge-phase-equivalence would force overlap → 0
   (`mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left`).
   Contradiction ⟹ gauge-phase equivalent. -/
private lemma gaugePhaseEquiv_of_block_sameMPV₂
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hA_norm : (∑ i : Fin d, (A i)ᴴ * (A i)) = 1)
    (hB_norm : (∑ i : Fin d, (B i)ᴴ * (B i)) = 1)
    (hA_self : Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)))
    (hSameMPV : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ) :
    ∃ hdim : D₁ = D₂,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- Cross-overlap = self-overlap → 1.
  have hOvEq := mpvOverlap_eq_selfOverlap_of_forall_mpv_eq A B hSameMPV
  have hOvOne : Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds (1 : ℂ)) :=
    hA_self.congr (fun N => (hOvEq N).symm)
  have hOvNot0 : ¬ Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds 0) :=
    fun h0 => one_ne_zero (tendsto_nhds_unique hOvOne h0)
  -- Dim equality by contradiction.
  have hdim : D₁ = D₂ := by
    by_contra hne
    exact hOvNot0
      (mpvOverlap_tendsto_zero_of_dim_ne A B hA_inj hB_inj hA_norm hB_norm hne)
  refine ⟨hdim, ?_⟩
  -- GaugePhaseEquiv by contradiction.
  by_contra hNotGPE
  exact hOvNot0
    (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      hdim A B hA_inj hB_inj hA_norm hB_norm hNotGPE)

end MPSTensor
