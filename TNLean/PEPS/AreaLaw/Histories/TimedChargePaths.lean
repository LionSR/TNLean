/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting chronologically labelled charge paths

Choosing `j` distinct charge times contributes a binomial coefficient, not the
larger power of the window length. Spatial label paths are then paired with
those times in chronological order. Labels in the spatial family are stored
backwards, starting at the tested endpoint.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 309–321, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {Time I : Type*} [LinearOrder Time] [DecidableEq I]

/-- All chronological pairings of a `j`-element time subset with a reversed
spatial label path. -/
def timedChargePaths (window : Finset Time) (labels : Finset (List I)) (j : ℕ) :
    Finset (List (Time × I)) :=
  ((window.powersetCard j) ×ˢ labels).image
    (fun p ↦ (p.1.sort (· ≤ ·)).zip p.2.reverse)

/-- Selecting charge times costs the exact binomial factor. The image can only
reduce cardinality, so no independence or injectivity premise is required. -/
theorem card_timedChargePaths_le (window : Finset Time) (labels : Finset (List I)) (j : ℕ) :
    (timedChargePaths window labels j).card ≤ window.card.choose j * labels.card := by
  calc
    _ ≤ ((window.powersetCard j) ×ˢ labels).card := Finset.card_image_le
    _ = _ := by
      simpa only [Finset.card_powersetCard] using
        Finset.card_product (window.powersetCard j) labels

/-- An ordered event list belongs to its time-window and spatial-path cover. -/
theorem mem_timedChargePaths (window : Finset Time) (labels : Finset (List I))
    (events : List (Time × I))
    (horder : events.Pairwise (fun a b ↦ a.1 < b.1))
    (hwindow : ∀ e ∈ events, e.1 ∈ window)
    (hlabels : (events.map Prod.snd).reverse ∈ labels) :
    events ∈ timedChargePaths window labels events.length := by
  have htimes : (events.map Prod.fst).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using horder
  have hnodup : (events.map Prod.fst).Nodup :=
    htimes.imp fun h ↦ ne_of_lt h
  have hsort : ((events.map Prod.fst).toFinset.sort (· ≤ ·)) = events.map Prod.fst :=
    (List.toFinset_sort (· ≤ ·) hnodup).mpr (htimes.imp fun h ↦ le_of_lt h)
  apply Finset.mem_image.mpr
  refine ⟨((events.map Prod.fst).toFinset, (events.map Prod.snd).reverse), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, hlabels⟩
    · intro t ht
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      exact hwindow e he
    · rw [List.toFinset_card_of_nodup hnodup, List.length_map]
  · simp only [hsort, List.reverse_reverse]
    simpa only [List.unzip_fst, List.unzip_snd] using List.zip_unzip events

/-- Every path in the cover has exactly `j` events when each spatial path does. -/
theorem length_of_mem_timedChargePaths {window : Finset Time} {labels : Finset (List I)}
    {j : ℕ} {events : List (Time × I)}
    (hlabels : ∀ l ∈ labels, l.length = j)
    (he : events ∈ timedChargePaths window labels j) : events.length = j := by
  obtain ⟨⟨times, ls⟩, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨ht, hl⟩ := Finset.mem_product.mp hp
  have hcard := (Finset.mem_powersetCard.mp ht).2
  simp only [List.length_zip, Finset.length_sort, List.length_reverse, hcard, hlabels ls hl,
    min_self]

/-- Every event time in the cover is in the chosen finite window. -/
theorem time_mem_of_mem_timedChargePaths {window : Finset Time} {labels : Finset (List I)}
    {j : ℕ} {events : List (Time × I)}
    (he : events ∈ timedChargePaths window labels j) :
    ∀ e ∈ events, e.1 ∈ window := by
  obtain ⟨⟨times, ls⟩, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨ht, _⟩ := Finset.mem_product.mp hp
  intro e he
  exact (Finset.mem_powersetCard.mp ht).1
    ((Finset.mem_sort (· ≤ ·)).mp (List.of_mem_zip he).1)

/-- Sorting a subset gives distinct chronological times, even when labels repeat. -/
theorem ordered_of_mem_timedChargePaths {window : Finset Time} {labels : Finset (List I)}
    {j : ℕ} {events : List (Time × I)}
    (hlabels : ∀ l ∈ labels, l.length = j)
    (he : events ∈ timedChargePaths window labels j) :
    events.Pairwise (fun a b ↦ a.1 < b.1) := by
  obtain ⟨⟨times, ls⟩, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨ht, hl⟩ := Finset.mem_product.mp hp
  have hlength : (times.sort (· ≤ ·)).length ≤ ls.reverse.length := by
    simp only [Finset.length_sort, List.length_reverse, hlabels ls hl,
      (Finset.mem_powersetCard.mp ht).2, le_refl]
  rw [← List.pairwise_map, List.map_fst_zip hlength]
  exact ((times.pairwise_sort (· ≤ ·)).sortedLE.sortedLT_of_nodup
    (times.sort_nodup _)).pairwise

/-- Pair indices in an inclusive backward window: `k-(t+1) ≤ W` permits
`W+1` indices, rather than `W`. -/
def recentChargeTimes (k W : ℕ) : Finset ℕ := Finset.Ico (k - (W + 1)) k

/-- The inclusive terminal interval contains at most `W+1` charge times. -/
theorem card_recentChargeTimes_le (k W : ℕ) : (recentChargeTimes k W).card ≤ W + 1 := by
  simp only [recentChargeTimes, Nat.card_Ico]
  omega

/-- Integer pair-clock inequalities place an ancestry event in the finite window. -/
theorem mem_recentChargeTimes {k W t : ℕ} (ht : t < k)
    (hwindow : (k : ℤ) - (t + 1) ≤ W) : t ∈ recentChargeTimes k W := by
  simp only [recentChargeTimes, Finset.mem_Ico]
  omega

/-- For a nonempty positive-radius ancestry, a convenient source-scale window
has at most `9nr₀j` slots; this absorbs all endpoint and floor corrections. -/
theorem card_ancestry_time_window_le {n r j : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hj : 0 < j) (k : ℕ) :
    (recentChargeTimes k (4 * n * (r * j + 1))).card ≤ 9 * n * r * j := by
  have h := card_recentChargeTimes_le k (4 * n * (r * j + 1))
  have hrj : 1 ≤ r * j := Nat.mul_pos hr hj
  have hnprod : n ≤ n * (r * j) := by nlinarith
  nlinarith

end TNLean.PEPS.AreaLaw.Scan
