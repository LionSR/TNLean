/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.SetTheory.Cardinal.Finite
import TNLean.PEPS.AreaLaw.Geometry.FanRuns

/-!
# Counting connected runs in a cell fan

Each connected run contains a fan triangle. Thus the number of runs is at
most the number of triangles, which is at most eight. This applies to every
splitting mask and every binary labeling, including a constant labeling.
It applies both to the initial belt fans and to the fully split replacement
fan. The estimate concerns the existing connected-run identifiers only.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, fan runs, lines 299–318, replacement sectors,
lines 398–417, and `geometry:total-repairs`, lines 682–691.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Any cell fan has at most eight connected runs of equal-colored triangles.
The same bound applies to the fully split replacement fan, independently of
the old identifiers assigned to its wedges.
Source: area-law Section 11, lines 299–318 and 398–417. -/
theorem card_cellFanRun_le_eight (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2) :
    Nat.card (CellFanRun o ℓ z split family) ≤ 8 := by
  have hcard : Nat.card (CellFanRun o ℓ z split family) ≤
      Nat.card (CellFanSlot split) :=
    Nat.card_le_card_of_surjective
      (cellFanRunGraph o ℓ z split family).connectedComponentMk Quot.mk_surjective
  exact hcard.trans (by simpa only [Nat.card_eq_fintype_card] using
    (card_cellFanSlot_bounds split).2)

end TNLean.PEPS.AreaLaw.Geometry
