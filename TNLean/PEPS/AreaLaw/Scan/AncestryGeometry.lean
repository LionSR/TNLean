/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ChargeAncestry
import Mathlib.Data.List.Chain

/-!
# Spatial geometry of actual charge ancestries

The endpoint belongs to its last charge ball, and consecutive charge anchors
are at graph distance at most `2r₀`. These follow from the actual extracted
ancestry: the shared predecessor belongs to both balls. They permit counting
label paths without treating repeated anchors as distinct physical sites.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 291–316, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- A nonempty ancestry ends in a ball containing its actual endpoint. -/
theorem ChargeAncestry.endpoint_mem_last_ball {g r k : ℕ}
    {choices : ℕ → Bool × Fin S.M} {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) :
    ∀ e, events.getLast? = some e → x ∈ S.ball e.2 := by
  induction h with
  | initial => simp
  | retain h ih => exact ih
  | fill => simp
  | charge i hp hs hsel hy hx ih => simpa using hx
  | chargeFill k x y i hf hslot hs hsel hy hx => simpa using hx

/-- Consecutive actual charge labels have intersecting radius balls and hence
anchors at graph distance at most twice the charge radius. -/
theorem ChargeAncestry.anchor_chain {g r k : ℕ}
    {choices : ℕ → Bool × Fin S.M} {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) :
    events.IsChain (fun a b ↦ S.graph.edist (S.anchor a.2) (S.anchor b.2) ≤
      ((2 * S.r₀ : ℕ) : ℕ∞)) := by
  induction h with
  | initial => simp
  | retain h ih => exact ih
  | fill => simp
  | @charge k x y events i hp hs hsel hy hx ih =>
    apply List.isChain_append.mpr
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = (k, i) := by
      simpa only [List.head?_cons, Option.mem_def, Option.some.injEq] using hb.symm
    subst b
    have hya := hp.endpoint_mem_last_ball S a ha
    have hva : S.graph.edist (S.anchor a.2) y ≤ (S.r₀ : ℕ∞) :=
      (Finset.mem_filter.mp hya).2
    have hvb : S.graph.edist (S.anchor i) y ≤ (S.r₀ : ℕ∞) :=
      (Finset.mem_filter.mp hy).2
    calc
      S.graph.edist (S.anchor a.2) (S.anchor i) ≤
          S.graph.edist (S.anchor a.2) y + S.graph.edist y (S.anchor i) :=
        SimpleGraph.edist_triangle
      _ ≤ (S.r₀ : ℕ∞) + S.r₀ :=
        add_le_add hva (by simpa only [SimpleGraph.edist_comm] using hvb)
      _ = ((2 * S.r₀ : ℕ) : ℕ∞) := by simp [two_mul]
  | chargeFill => simp

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
