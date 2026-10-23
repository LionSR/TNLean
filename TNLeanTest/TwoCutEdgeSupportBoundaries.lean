/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoCutEdgeSupports

/-! Actual chains with adjacent cuts and with edges in all three regions. -/

open TNLean.MPS.AreaLaw

-- Both genuine boundary edges of the least possible chain; the middle site is shared.
private abbrev adjacentCuts :=
  interval_edge_classification_of_lt (L := 3) (u := 0) (v := 1) (by decide) (by decide)

-- Edges 0, 2 and 4 lie in the left, middle and right regions respectively.
private abbrev separatedCuts :=
  interval_edge_classification_of_lt (L := 6) (u := 1) (v := 3) (by decide) (by decide)

example : interval 6 0 2 ⊆ interval 6 0 2 ∨
    interval 6 0 2 ⊆ interval 6 2 4 ∨
    interval 6 0 2 ⊆ (interval 6 0 2 ∪ interval 6 2 4)ᶜ :=
  separatedCuts.2.2.2.2 0 (by decide) (by decide) (by decide)

example : interval 6 2 4 ⊆ interval 6 0 2 ∨
    interval 6 2 4 ⊆ interval 6 2 4 ∨
    interval 6 2 4 ⊆ (interval 6 0 2 ∪ interval 6 2 4)ᶜ :=
  separatedCuts.2.2.2.2 2 (by decide) (by decide) (by decide)

example : interval 6 4 6 ⊆ interval 6 0 2 ∨
    interval 6 4 6 ⊆ interval 6 2 4 ∨
    interval 6 4 6 ⊆ (interval 6 0 2 ∪ interval 6 2 4)ᶜ :=
  separatedCuts.2.2.2.2 4 (by decide) (by decide) (by decide)
