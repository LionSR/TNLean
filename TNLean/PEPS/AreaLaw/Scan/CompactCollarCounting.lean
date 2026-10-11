/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth

/-!
# Counting compact scan endpoints

The initial target contributes its own cardinality; each positive ambient
layer contributes at most the source row bound. Thus the compact collar has
at most `|T| + nL` sites, independently of the surrounding physical domain.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 21–29 and 323–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- Summing actual ambient layers bounds the dilation without any ambient-domain
volume factor. No cardinality bound for the whole dilation is assumed. -/
theorem card_ambientDilation_le_of_layers (T : Finset (ℤ × ℤ)) (n L : ℕ)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) :
    (ambientDilation T L).card ≤ T.card + n * L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hp := ih (fun d hd hL ↦ hrows d hd (Nat.le_succ_of_le hL))
    have hr := hrows (L + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hr
    have hc := Finset.card_le_card_sdiff_add_card
      (s := ambientDilation T (L + 1)) (t := ambientDilation T L)
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- Actual chosen-color sites of ambient depth at most `L` inject into the
ambient dilation, even when the physical domain has holes or extra components. -/
theorem card_compact_collar_le {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset (Site Λ)) (n L : ℕ)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) :
    (A.filter fun x ↦ ambientDepth T hT x.val ≤ L).card ≤ T.card + n * L := by
  apply le_trans _ (card_ambientDilation_le_of_layers T n L hrows)
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro x hx
    exact (ambientDepth_le_iff_mem_dilation T hT x.val L).mp (Finset.mem_filter.mp hx).2
  · exact Subtype.val_injective.injOn

end TNLean.PEPS.AreaLaw.Scan
