/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.CanonicalFormSepAux

/-!
# Separated canonical-form hypotheses and block separation

This file proves the core block-separation result from the separated canonical-form hypotheses
defined in `CanonicalFormSepAux`, and then rebuilds legacy canonical-form formulations on top.

## Main results

- `block_separation_core` — extracts per-block `SameMPV` from a weighted sum identity,
  using the injective-block variant.
- `block_separation_all_words` / `block_separation_all_words_of_irreducible_TP` — public
  formulations of the core induction.
- `per_block_sameMPV_of_canonical_form` / `per_block_sameMPV_of_normal_canonical_form` —
  block-separation from bundled canonical-form predicates.
- `fundamentalTheorem_canonicalForm` / `fundamentalTheorem_canonicalForm_explicit` —
  canonical-form formulations of the MPS fundamental theorem.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.show false

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

section BlockSeparationCoreInduction

private lemma sameMPV_of_mpvOverlap_tendsto_one_of_injective
    {D : ℕ} [NeZero D] (A B : MPSTensor d D)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_lc : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (hSelf :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A A N)
        Filter.atTop (nhds (1 : ℂ)))
    (hCross :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N)
        Filter.atTop (nhds (1 : ℂ))) :
    SameMPV A B := by
  exact
    sameMPV_of_gaugePhaseEquiv_of_mpvOverlap_tendsto_one
      (A := A) (B := B) (hSelf := hSelf) (hCross := hCross)
      (gaugePhaseEquiv_of_mpvOverlap_tendsto_one
        (A := A) (B := B) hA_inj hB_inj hA_lc hB_lc hCross)

private lemma sameMPV_of_mpvOverlap_tendsto_one_of_irreducible_TP
    {D : ℕ} [NeZero D] (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_lc : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (hSelf :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A A N)
        Filter.atTop (nhds (1 : ℂ)))
    (hCross :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N)
        Filter.atTop (nhds (1 : ℂ))) :
    SameMPV A B := by
  exact
    sameMPV_of_gaugePhaseEquiv_of_mpvOverlap_tendsto_one
      (A := A) (B := B) (hSelf := hSelf) (hCross := hCross)
      (gaugePhaseEquiv_of_mpvOverlap_tendsto_one_of_irreducible_TP
        (A := A) (B := B) hA_irr hB_irr hA_lc hB_lc hCross)

private theorem leading_block_sameMPV_of_crossOverlap_tendsto_one
    {r : ℕ} {dim : Fin (Nat.succ (Nat.succ r)) → ℕ}
    [∀ k, NeZero (dim k)]
    (μ : Fin (Nat.succ (Nat.succ r)) → ℂ)
    (A B : (k : Fin (Nat.succ (Nat.succ r))) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin (Nat.succ (Nat.succ r)) => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_lc : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hA_overlap :
      ∀ k,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
          Filter.atTop (nhds (1 : ℂ)))
    (hSame_of_cross :
      Filter.Tendsto (fun N => mpvOverlap (d := d) (A 0) (B 0) N)
        Filter.atTop (nhds (1 : ℂ)) →
      SameMPV (A 0) (B 0))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin (Nat.succ (Nat.succ r)), (μ k) ^ N *
        (mpv (A k) σ - mpv (B k) σ) = 0) :
    SameMPV (A 0) (B 0) := by
  have h_sum_overlap :
      ∀ N : ℕ,
        ∑ k : Fin (Nat.succ (Nat.succ r)),
            (star (μ k)) ^ N *
              (mpvOverlap (d := d) (A 0) (A k) N -
                mpvOverlap (d := d) (A 0) (B k) N) = 0 := by
    intro N
    classical
    have hs_star :
        ∀ σ : Fin N → Fin d,
          ∑ k : Fin (Nat.succ (Nat.succ r)),
              (star (μ k)) ^ N *
                (star (mpv (A k) σ) - star (mpv (B k) σ)) = 0 := by
      intro σ
      have hs := h_summed N σ
      have hs' : star (∑ k : Fin (Nat.succ (Nat.succ r)),
          (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ)) = (0 : ℂ) := by
        simpa using congrArg star hs
      simpa [star_sum, star_mul, star_pow, star_sub,
        mul_comm, mul_left_comm, mul_assoc] using hs'
    calc
      ∑ k : Fin (Nat.succ (Nat.succ r)),
          (star (μ k)) ^ N *
            (mpvOverlap (d := d) (A 0) (A k) N -
              mpvOverlap (d := d) (A 0) (B k) N)
          =
          ∑ k : Fin (Nat.succ (Nat.succ r)),
            (star (μ k)) ^ N *
              (∑ σ : Fin N → Fin d,
                mpv (A 0) σ * (star (mpv (A k) σ) - star (mpv (B k) σ))) := by
            simp [mpvOverlap, Finset.sum_sub_distrib, mul_sub]
      _ =
          ∑ k : Fin (Nat.succ (Nat.succ r)),
            ∑ σ : Fin N → Fin d,
              (star (μ k)) ^ N *
                (mpv (A 0) σ * (star (mpv (A k) σ) - star (mpv (B k) σ))) := by
            simp [Finset.mul_sum, mul_assoc]
      _ =
          ∑ σ : Fin N → Fin d,
            ∑ k : Fin (Nat.succ (Nat.succ r)),
              (star (μ k)) ^ N *
                (mpv (A 0) σ * (star (mpv (A k) σ) - star (mpv (B k) σ))) := by
            simpa using
              (Finset.sum_comm (s := (Finset.univ : Finset (Fin (Nat.succ (Nat.succ r)))))
                (t := (Finset.univ : Finset (Fin N → Fin d)))
                (f := fun k σ =>
                  (star (μ k)) ^ N *
                    (mpv (A 0) σ * (star (mpv (A k) σ) - star (mpv (B k) σ)))))
      _ =
          ∑ σ : Fin N → Fin d,
            mpv (A 0) σ *
              ∑ k : Fin (Nat.succ (Nat.succ r)),
                (star (μ k)) ^ N *
                  (star (mpv (A k) σ) - star (mpv (B k) σ)) := by
            refine Finset.sum_congr rfl ?_
            intro σ _
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro σ _
            exact mul_eq_zero_of_right (mpv (A 0) σ) (hs_star σ)
  let δ : Fin (Nat.succ (Nat.succ r)) → ℕ → ℂ :=
    fun k N => mpvOverlap (d := d) (A 0) (A k) N - mpvOverlap (d := d) (A 0) (B k) N
  let Dsum : ℝ := ∑ k : Fin (Nat.succ (Nat.succ r)), (dim k : ℝ)
  let Bbound : ℝ := 2 * (dim 0 : ℝ) * Dsum
  have hBbound_nn : 0 ≤ Bbound := by
    have h2dim0 : 0 ≤ (2 : ℝ) * (dim 0 : ℝ) := by positivity
    have hDsum : 0 ≤ Dsum := by
      refine Finset.sum_nonneg ?_
      intro k _
      positivity
    simpa [Bbound, mul_assoc] using mul_nonneg h2dim0 hDsum
  have hδ_bound : ∀ k N, ‖δ k N‖ ≤ Bbound := by
    intro k N
    have h1 :
        ‖mpvOverlap (d := d) (A 0) (A k) N‖ ≤ (dim 0 : ℝ) * (dim k : ℝ) :=
      leftCanonical_mpvOverlap_bound (d := d) (A := A 0) (B := A k)
        (hA_lc 0) (hA_lc k) N
    have h2 :
        ‖mpvOverlap (d := d) (A 0) (B k) N‖ ≤ (dim 0 : ℝ) * (dim k : ℝ) :=
      leftCanonical_mpvOverlap_bound (d := d) (A := A 0) (B := B k)
        (hA_lc 0) (hB_lc k) N
    have hdim_le : (dim k : ℝ) ≤ Dsum := by
      have hnonneg : ∀ j : Fin (Nat.succ (Nat.succ r)), 0 ≤ (dim j : ℝ) := fun _ => by
        positivity
      simpa [Dsum] using
        (Finset.single_le_sum (s := (Finset.univ : Finset (Fin (Nat.succ (Nat.succ r)))))
          (f := fun j : Fin (Nat.succ (Nat.succ r)) => (dim j : ℝ))
          (hf := fun j _ => hnonneg j) (a := k) (h := Finset.mem_univ k))
    calc
      ‖δ k N‖
          = ‖mpvOverlap (d := d) (A 0) (A k) N -
              mpvOverlap (d := d) (A 0) (B k) N‖ := rfl
      _ ≤ ‖mpvOverlap (d := d) (A 0) (A k) N‖ +
            ‖mpvOverlap (d := d) (A 0) (B k) N‖ := norm_sub_le _ _
      _ ≤ (dim 0 : ℝ) * (dim k : ℝ) + (dim 0 : ℝ) * (dim k : ℝ) := by
            gcongr
      _ = 2 * (dim 0 : ℝ) * (dim k : ℝ) := by ring
      _ ≤ 2 * (dim 0 : ℝ) * Dsum := by
            have h2dim0 : 0 ≤ (2 : ℝ) * (dim 0 : ℝ) := by positivity
            have := mul_le_mul_of_nonneg_left hdim_le h2dim0
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
      _ = Bbound := by
            simp [Bbound, mul_assoc, mul_left_comm, mul_comm]
  -- After dividing by the leading weight `μ 0`, the tail terms decay because
  -- strict weight ordering gives a geometric factor `ρ < 1`. The overlap
  -- estimates above are used only to bound the coefficients `δ k N`; they are
  -- not the source of the decay themselves.
  let ρ : ℝ :=
    ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ / ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖
  have hρ_pos : 0 < ρ := by
    have hμ0 : 0 < ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ :=
      norm_pos_iff.mpr (hμ_ne_zero 0)
    have hμ1 : 0 < ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ :=
      norm_pos_iff.mpr (hμ_ne_zero 1)
    exact div_pos hμ1 hμ0
  have hρ_lt : ρ < 1 := by
    have hμ0 : 0 < ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ :=
      norm_pos_iff.mpr (hμ_ne_zero 0)
    have h01 : (0 : Fin (Nat.succ (Nat.succ r))) < 1 :=
      (Fin.zero_lt_one : (0 : Fin (Nat.succ (Nat.succ r))) < 1)
    have hstrict :
        ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ <
          ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ :=
      hμ_strict h01
    exact (div_lt_one hμ0).2 hstrict
  have hρ_bound :
      ∀ k : Fin (Nat.succ (Nat.succ r)),
        k ≠ (0 : Fin (Nat.succ (Nat.succ r))) →
          ‖star (μ k)‖ ≤ ‖star (μ (0 : Fin (Nat.succ (Nat.succ r))))‖ * ρ := by
    intro k hk
    have hanti : Antitone (fun j : Fin (Nat.succ (Nat.succ r)) => ‖μ j‖) :=
      hμ_strict.antitone
    have hkval : (k : ℕ) ≠ 0 := by
      simpa using (Fin.val_ne_of_ne hk)
    have hk1 : (1 : Fin (Nat.succ (Nat.succ r))) ≤ k := by
      apply (Fin.le_iff_val_le_val).2
      have : (1 : ℕ) ≤ (k : ℕ) :=
        (Nat.one_le_iff_ne_zero).2 hkval
      simpa using this
    have hk_le : ‖μ k‖ ≤ ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ := hanti hk1
    have hμ0ne : ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ ≠ 0 := by
      exact ne_of_gt (norm_pos_iff.mpr (hμ_ne_zero 0))
    have hmul : ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ * ρ =
        ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ := by
      dsimp [ρ]
      calc
        ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ *
            (‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ /
              ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖)
            = (‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ *
                ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖) /
                ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ := by
                  simpa [mul_assoc] using
                    (mul_div_assoc
                      ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖
                      ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖
                      ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖).symm
        _ = ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖ := by
              simpa [mul_assoc] using
                (mul_div_cancel_left₀
                  (M₀ := ℝ)
                  (b := ‖μ (1 : Fin (Nat.succ (Nat.succ r)))‖)
                  (a := ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖)
                  hμ0ne)
    have : ‖μ k‖ ≤ ‖μ (0 : Fin (Nat.succ (Nat.succ r)))‖ * ρ := by
      simpa [hmul] using hk_le
    simpa [norm_star] using this
  have hpeel :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ N : ℕ, ‖δ (0 : Fin (Nat.succ (Nat.succ r))) N‖ ≤ C * ρ ^ N :=
    peeling_exponential_bound (r := Nat.succ (Nat.succ r))
      (hr := Nat.succ_pos _)
      (α := fun k : Fin (Nat.succ (Nat.succ r)) => star (μ k))
      (hα₀ := (star_ne_zero).2 (hμ_ne_zero 0))
      (δ := δ)
      (B := Bbound) (hB_nn := hBbound_nn)
      (hδ_bound := hδ_bound)
      (h_sum := fun N => by simpa [δ] using h_sum_overlap N)
      (ρ := ρ) (hρ_pos := hρ_pos) (hρ_lt := hρ_lt)
      (hρ_bound := by
        intro k hk
        simpa using (hρ_bound k hk))
  rcases hpeel with ⟨C, hC_nn, hδ0_le⟩
  have hδ0_tendsto :
      Filter.Tendsto (fun N => δ (0 : Fin (Nat.succ (Nat.succ r))) N)
        Filter.atTop (nhds 0) := by
    have habs : |ρ| < 1 := by
      have hpos : 0 < ρ := hρ_pos
      have hlt : ρ < 1 := hρ_lt
      simpa [abs_of_pos hpos] using hlt
    have hpow :
        Filter.Tendsto (fun N => ρ ^ N) Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs)
    have hmul :
        Filter.Tendsto (fun N => C * ρ ^ N) Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (Filter.Tendsto.const_mul C hpow)
    have hnorm :
        Filter.Tendsto (fun N => ‖δ (0 : Fin (Nat.succ (Nat.succ r))) N‖)
          Filter.atTop (nhds (0 : ℝ)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (f := fun N => ‖δ (0 : Fin (Nat.succ (Nat.succ r))) N‖)
        (g := fun _ => (0 : ℝ)) (h := fun N => C * ρ ^ N)
        (hg := tendsto_const_nhds)
        (hh := hmul)
        (hgf := fun N => norm_nonneg (δ (0 : Fin (Nat.succ (Nat.succ r))) N))
        (hfh := fun N => hδ0_le N)
    exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm
  have hCross_tendsto :
      Filter.Tendsto (fun N => mpvOverlap (d := d) (A 0) (B 0) N)
        Filter.atTop (nhds (1 : ℂ)) := by
    have hSelf := hA_overlap (0 : Fin (Nat.succ (Nat.succ r)))
    have h :
        Filter.Tendsto
          (fun N =>
            mpvOverlap (d := d) (A 0) (A 0) N -
              δ (0 : Fin (Nat.succ (Nat.succ r))) N)
          Filter.atTop (nhds (1 : ℂ)) := by
      simpa using (hSelf.sub hδ0_tendsto)
    refine Filter.Tendsto.congr (fun N => ?_) h
    simp [δ, sub_sub]
  exact hSame_of_cross hCross_tendsto

private theorem block_separation_core_of_crossOverlap_tendsto_one
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_lc : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hA_overlap :
      ∀ k,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
          Filter.atTop (nhds (1 : ℂ)))
    (hSame_of_cross :
      ∀ k,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (B k) N)
          Filter.atTop (nhds (1 : ℂ)) →
        SameMPV (A k) (B k))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) := by
  classical
  revert μ A B hμ_strict hμ_ne_zero hA_lc hB_lc hA_overlap hSame_of_cross h_summed
  induction r with
  | zero =>
      intro μ A B hμ_strict hμ_ne_zero hA_lc hB_lc hA_overlap hSame_of_cross h_summed k
      exact k.elim0
  | succ r ih =>
      intro μ A B hμ_strict hμ_ne_zero hA_lc hB_lc hA_overlap hSame_of_cross h_summed
      cases r with
      | zero =>
          intro k
          have hk : k = 0 := Fin.ext (by omega)
          subst hk
          intro N σ
          have h_eq : (μ 0) ^ N * (mpv (A 0) σ - mpv (B 0) σ) = 0 := by
            simpa [Fin.sum_univ_one] using h_summed N σ
          have hμ_pow : (μ 0) ^ N ≠ 0 := pow_ne_zero N (hμ_ne_zero 0)
          have hsub := (mul_eq_zero.mp h_eq).resolve_left hμ_pow
          exact sub_eq_zero.mp hsub
      | succ r =>
          have hHead : SameMPV (A 0) (B 0) :=
            leading_block_sameMPV_of_crossOverlap_tendsto_one
              μ A B hμ_strict hμ_ne_zero hA_lc hB_lc hA_overlap (hSame_of_cross 0)
              h_summed
          have h_summed_tail :
              ∀ (N : ℕ) (σ : Fin N → Fin d),
                ∑ k : Fin (Nat.succ r),
                  (μ k.succ) ^ N * (mpv (A k.succ) σ - mpv (B k.succ) σ) = 0 := by
            intro N σ
            have hsum :
                (μ 0) ^ N * (mpv (A 0) σ - mpv (B 0) σ) +
                  ∑ k : Fin (Nat.succ r),
                    (μ k.succ) ^ N * (mpv (A k.succ) σ - mpv (B k.succ) σ) = 0 := by
              simpa [Fin.sum_univ_succ] using h_summed N σ
            have hhead : (μ 0) ^ N * (mpv (A 0) σ - mpv (B 0) σ) = 0 := by
              rw [hHead N σ, sub_self, mul_zero]
            rw [hhead, zero_add] at hsum
            exact hsum
          have hTail :
              ∀ k : Fin (Nat.succ r), SameMPV (A k.succ) (B k.succ) := by
            have hμ_strict_tail :
                StrictAnti (fun k : Fin (Nat.succ r) => ‖μ k.succ‖) := by
              intro a b hab
              have hab' : a.succ < b.succ := (Fin.succ_lt_succ_iff).2 hab
              exact hμ_strict hab'
            exact ih
              (dim := fun k : Fin (Nat.succ r) => dim k.succ)
              (μ := fun k : Fin (Nat.succ r) => μ k.succ)
              (A := fun k : Fin (Nat.succ r) => A k.succ)
              (B := fun k : Fin (Nat.succ r) => B k.succ)
              (hμ_strict := hμ_strict_tail)
              (hμ_ne_zero := fun k => hμ_ne_zero k.succ)
              (hA_lc := fun k => hA_lc k.succ)
              (hB_lc := fun k => hB_lc k.succ)
              (hA_overlap := fun k => hA_overlap k.succ)
              (hSame_of_cross := fun k hCross => hSame_of_cross k.succ hCross)
              (h_summed := h_summed_tail)
          intro k
          refine Fin.cases
            (motive := fun k : Fin (Nat.succ (Nat.succ r)) => SameMPV (A k) (B k))
            hHead (fun k => hTail k) k

end BlockSeparationCoreInduction

/-! ### Block separation core lemma (mixed-transfer / overlap argument)

This is the literature-aligned block-separation step in canonical form.
Compared to the naive statement in `PiAlgebra/BlockSeparation.lean`, we assume:

* `hB_inj` : every block of `B` is injective (needed for the overlap decay lemma
  `mpvOverlap_tendsto_zero`), and
* `hA_overlap` : aperiodicity / primitive normalization, expressed as
  `mpvOverlap (A k) (A k) N → 1` as `N → ∞`. This rules out the "overlap → 0" branch
  in the equal-or-orthogonal dichotomy.

The proof follows Pérez-García et al. (2007, Appendix E) / Cirac et al. (2021, Theorem IV.3):
we take overlaps with the leading block, divide by the leading weight, and use the
strict modulus ordering of the weights together with uniform overlap bounds to invoke
`peeling_exponential_bound`. Thus the geometric decay comes from the weight ratio,
while the overlap theorems are used only for boundedness and contradiction steps.
Once the leading mixed overlap is shown to tend to `1`, a nonzero limit first rules
out a bond-dimension mismatch via the rectangular decay lemma; in the equal-dimension
case, the usual overlap-decay contradiction forces gauge-phase equivalence of the
leading block. Finally one iterates by induction on the number of blocks.
-/
lemma block_separation_core
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_inj : ∀ k, IsInjective (A k))
    (hB_inj : ∀ k, IsInjective (B k))
    (hA_lc : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hA_overlap :
      ∀ k,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
          Filter.atTop (nhds (1 : ℂ)))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) :=
  block_separation_core_of_crossOverlap_tendsto_one
    μ A B hμ_strict hμ_ne_zero hA_lc hB_lc hA_overlap
    (fun k hCross =>
      sameMPV_of_mpvOverlap_tendsto_one_of_injective
        (A := A k) (B := B k) (hA_inj := hA_inj k) (hB_inj := hB_inj k)
        (hA_lc := hA_lc k) (hB_lc := hB_lc k)
        (hSelf := hA_overlap k) (hCross := hCross))
    h_summed

/-! ### Block separation -/

section BlockSeparation

/-- The summed identity for a fixed word w and all powers L.
From SameMPV₂ of block-diagonal tensors, for any word w of length M:
  ∑_k (μ_k^M)^L · [tr(T_k^L) - tr(U_k^L)] = 0
where T_k = evalWord(A_k, w), U_k = evalWord(B_k, w). -/
theorem summed_identity_for_word
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0)
    (w : List (Fin d)) (L : ℕ) :
    ∑ k : Fin r, ((μ k) ^ w.length) ^ L *
      (Matrix.trace ((evalWord (A k) w) ^ L) -
       Matrix.trace ((evalWord (B k) w) ^ L)) = 0 := by
  set M := w.length
  have hlen : ((List.replicate L w).flatten).length = M * L := by
    rw [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul, mul_comm]
  set σ : Fin (M * L) → Fin d := fun i =>
    ((List.replicate L w).flatten).get (Fin.cast hlen.symm i)
  have hofFn : List.ofFn σ = (List.replicate L w).flatten := by
    simpa [σ, hlen] using (List.ofFn_getElem (xs := (List.replicate L w).flatten))
  have hsummed := h_summed (M * L) σ
  simp only [mpv, coeff, hofFn, evalWord_flatten_replicate, mul_sub] at hsummed
  simpa [M, pow_mul, mul_sub] using hsummed

theorem sameMPV_of_charpoly_eq_all_words
    {D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (h : ∀ w : List (Fin d), (evalWord A w).charpoly = (evalWord B w).charpoly) :
    SameMPV A B := by
  intro N σ
  simp only [mpv, coeff]
  exact Matrix.trace_eq_of_charpoly_eq _ _ (h (List.ofFn σ))

/-- Block separation for all blocks: a direct consequence of the core lemma.
Under canonical form hypotheses, the summed identity implies per-block SameMPV.
Requires injectivity of all blocks (used in the core lemma for the spectral gap
argument). -/
lemma block_separation_all_words
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_inj : ∀ k, IsInjective (A k))
    (hB_inj : ∀ k, IsInjective (B k))
    (hA_lc : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hA_overlap :
      ∀ k,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
          Filter.atTop (nhds (1 : ℂ)))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N *
        (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) :=
  block_separation_core μ A B hμ_strict hμ_ne_zero hA_inj hB_inj hA_lc hB_lc hA_overlap h_summed

/-- NT / normal-canonical formulation of `block_separation_all_words`.

Besides irreducibility and left-canonical normalization on both block families,
this lemma also assumes the self-overlap convergence hypothesis on the
`A`-blocks: `mpvOverlap (A k) (A k) N → 1`.

The proof is the same peeling / induction argument as `block_separation_core`.
The geometric decay again comes from the strict weight ordering after dividing by
the leading weight, while the NT overlap lemmas provide the boundedness and
contradiction hypotheses. At the identification step,
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP` first excludes a
bond-dimension mismatch, and
`gaugePhaseEquiv_of_mpvOverlap_tendsto_one_of_irreducible_TP` replaces the
injective equal-dimension overlap-decay contradiction via the irreducible
modulus-one-eigenvalue-rigidity argument. -/
lemma block_separation_all_words_of_irreducible_TP
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_strict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hA_irr : ∀ k, IsIrreducibleTensor (A k))
    (hB_irr : ∀ k, IsIrreducibleTensor (B k))
    (hA_lc : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hA_overlap :
      ∀ k,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N)
          Filter.atTop (nhds (1 : ℂ)))
    (h_summed : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N *
        (mpv (A k) σ - mpv (B k) σ) = 0) :
    ∀ k, SameMPV (A k) (B k) :=
  block_separation_core_of_crossOverlap_tendsto_one
    μ A B hμ_strict hμ_ne_zero hA_lc hB_lc hA_overlap
    (fun k hCross =>
      sameMPV_of_mpvOverlap_tendsto_one_of_irreducible_TP
        (A := A k) (B := B k) (hA_irr := hA_irr k) (hB_irr := hB_irr k)
        (hA_lc := hA_lc k) (hB_lc := hB_lc k)
        (hSelf := hA_overlap k) (hCross := hCross))
    h_summed

end BlockSeparation

/-! ### Block separation under canonical form -/

section CanonicalFormSeparation

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

private lemma summed_block_difference_eq_zero_of_sameMPV₂
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ k : Fin r, (μ k) ^ N * (mpv (A k) σ - mpv (B k) σ) = 0 := by
  intro N σ
  have hEq := sameMPV₂_summed_blocks μ A B hSame₂ N σ
  have hSub :
      ∑ k : Fin r, (μ k) ^ N * mpv (A k) σ -
          ∑ k : Fin r, (μ k) ^ N * mpv (B k) σ = 0 := by
    exact sub_eq_zero.mpr (by simpa [smul_eq_mul] using hEq)
  simpa [Finset.sum_sub_distrib, mul_sub] using hSub

private lemma per_block_sameMPV_of_sameMPV₂_of_card_le_one
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hμ_ne_zero : ∀ k, μ k ≠ 0)
    (hr : r ≤ 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) := by
  intro k N σ
  have hEq := sameMPV₂_summed_blocks μ A B hSame₂ N σ
  interval_cases r
  · exact k.elim0
  · have hk : k = 0 := Fin.ext (by omega)
    subst hk
    simp only [Fin.sum_univ_one, smul_eq_mul] at hEq
    exact mul_left_cancel₀ (pow_ne_zero N (hμ_ne_zero 0)) hEq

/-- Additive split form of `per_block_sameMPV_of_canonical_form`.

This lemma isolates exactly the pieces of the canonical-form bundle used in the
block-separation argument: injectivity, left-canonical normalization, strict nonzero weights,
and self-overlap normalization. The canonical-form formulation below is recovered by
projection from `IsCanonicalForm`.
-/
lemma per_block_sameMPV_of_separated_canonical_data
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hWeights : HasStrictOrderedNonzeroWeights μ)
    (hA_inj : HasInjectiveBlocks (d := d) A)
    (hA_left : IsLeftCanonicalBlockFamily (d := d) A)
    (hA_overlap : HasNormalizedSelfOverlap (d := d) A)
    (hB_inj : HasInjectiveBlocks (d := d) B)
    (hB_left : IsLeftCanonicalBlockFamily (d := d) B)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) := by
  by_cases hr : r ≤ 1
  · exact per_block_sameMPV_of_sameMPV₂_of_card_le_one μ A B hWeights.mu_ne_zero hr hSame₂
  · push Not at hr
    exact block_separation_all_words μ A B hWeights.mu_strict_anti hWeights.mu_ne_zero
      hA_inj.block_injective hB_inj.block_injective hA_left.leftCanonical hB_left.leftCanonical
      hA_overlap.overlap_tendsto_one
      (summed_block_difference_eq_zero_of_sameMPV₂ μ A B hSame₂)

/-- Reformulation extracting per-block `SameMPV` from canonical-form data with a strict
ordering witness. The strict ordering is available at the BNT level (`IsCanonicalFormBNT.mu_strict_anti`)
but not from the base `IsCanonicalForm` which only guarantees non-increasing moduli. -/
lemma per_block_sameMPV_of_canonical_form
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hStrict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hB_inj : ∀ k, IsInjective (B k))
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) :=
  per_block_sameMPV_of_separated_canonical_data μ A B
    ⟨hStrict, hA.mu_ne_zero⟩
    hA.toHasInjectiveBlocks
    hA.toIsLeftCanonicalBlockFamily
    hA.toHasNormalizedSelfOverlap
    (HasInjectiveBlocks.ofForall hB_inj)
    (IsLeftCanonicalBlockFamily.ofForall hB_lc)
    hSame₂

/-- Block separation for normal canonical form (NT blocks).

This is the analogue of `per_block_sameMPV_of_canonical_form`, replacing
injective canonical-form blocks by irreducible + primitive + left-canonical
blocks. The underlying proof uses the same peeling argument as the injective
canonical-form lemma, but the leading-block identification step uses the
irreducible modulus-one-eigenvalue-rigidity theorem (after separately ruling out
a bond-dimension mismatch) instead of the injective overlap-decay
contradiction. Since both block families use the same dimension function, the
conclusion is the homogeneous predicate `SameMPV`. -/
lemma per_block_sameMPV_of_normal_canonical_form
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hA : IsNormalCanonicalForm μ A)
    (hStrict : StrictAnti (fun k : Fin r => ‖μ k‖))
    {B : (k : Fin r) → MPSTensor d (dim k)}
    (hB_irr : ∀ k, IsIrreducibleTensor (B k))
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks (d := d) (μ := μ) A)
                        (toTensorFromBlocks (d := d) (μ := μ) B)) :
    ∀ k, SameMPV (A k) (B k) := by
  by_cases hr : r ≤ 1
  · exact per_block_sameMPV_of_sameMPV₂_of_card_le_one μ A B hA.mu_ne_zero hr hSame₂
  · push Not at hr
    intro k
    exact block_separation_all_words_of_irreducible_TP μ A B
      hStrict hA.mu_ne_zero hA.block_irreducible hB_irr hA.leftCanonical hB_lc
      (fun j => hA.overlap_tendsto_one j)
      (summed_block_difference_eq_zero_of_sameMPV₂ μ A B hSame₂) k

/-- Separated-data variant of `fundamentalTheorem_canonicalForm`.

This is the preferred formulation: it only asks for the pieces of canonical-form
structure actually used by the proof. The canonical-form formulation below remains available
around this one. -/
lemma fundamentalTheorem_of_separated_canonical_data
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hWeights : HasStrictOrderedNonzeroWeights μ)
    (hA_inj : HasInjectiveBlocks (d := d) A)
    (hA_left : IsLeftCanonicalBlockFamily (d := d) A)
    (hA_overlap : HasNormalizedSelfOverlap (d := d) A)
    (hB_inj : HasInjectiveBlocks (d := d) B)
    (hB_left : IsLeftCanonicalBlockFamily (d := d) B)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) := by
  have hSep := per_block_sameMPV_of_separated_canonical_data μ A B
    hWeights hA_inj hA_left hA_overlap hB_inj hB_left hSame₂
  exact fundamentalTheorem_multiBlock_full μ A B hA_inj.block_injective hSep

/-- Explicit gauge-matrix form of `fundamentalTheorem_of_separated_canonical_data`. -/
lemma fundamentalTheorem_of_separated_canonical_data_explicit
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hWeights : HasStrictOrderedNonzeroWeights μ)
    (hA_inj : HasInjectiveBlocks (d := d) A)
    (hA_left : IsLeftCanonicalBlockFamily (d := d) A)
    (hA_overlap : HasNormalizedSelfOverlap (d := d) A)
    (hB_inj : HasInjectiveBlocks (d := d) B)
    (hB_left : IsLeftCanonicalBlockFamily (d := d) B)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  have hSep := per_block_sameMPV_of_separated_canonical_data μ A B
    hWeights hA_inj hA_left hA_overlap hB_inj hB_left hSame₂
  exact fundamentalTheorem_multiBlock_explicit A B hA_inj.block_injective hSep

/-- Reformulation of `fundamentalTheorem_of_separated_canonical_data` for canonical-form data
with an explicit strict-ordering witness. This is the strict same-structure
specialization, not the full source-paper canonical-form theorem. -/
lemma fundamentalTheorem_canonicalForm
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hStrict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hB_inj : ∀ k, IsInjective (B k))
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  fundamentalTheorem_of_separated_canonical_data μ A B
    ⟨hStrict, hA.mu_ne_zero⟩
    hA.toHasInjectiveBlocks
    hA.toIsLeftCanonicalBlockFamily
    hA.toHasNormalizedSelfOverlap
    (HasInjectiveBlocks.ofForall hB_inj)
    (IsLeftCanonicalBlockFamily.ofForall hB_lc)
    hSame₂

/-- Explicit gauge-matrix reformulation of
`fundamentalTheorem_of_separated_canonical_data_explicit` with strict-ordering witness. -/
lemma fundamentalTheorem_canonicalForm_explicit
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalForm μ A)
    (hStrict : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hB_inj : ∀ k, IsInjective (B k))
    (hB_lc : ∀ k, ∑ i : Fin d, (B k i)ᴴ * (B k i) = 1)
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) :=
  fundamentalTheorem_of_separated_canonical_data_explicit μ A B
    ⟨hStrict, hA.mu_ne_zero⟩
    hA.toHasInjectiveBlocks
    hA.toIsLeftCanonicalBlockFamily
    hA.toHasNormalizedSelfOverlap
    (HasInjectiveBlocks.ofForall hB_inj)
    (IsLeftCanonicalBlockFamily.ofForall hB_lc)
    hSame₂

end CanonicalFormSeparation

end MPSTensor
