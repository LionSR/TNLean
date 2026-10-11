/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ChargeAncestry

/-!
# Lead and deterministic time windows of charge ancestries

Each charge contributes at most twice its radius to oriented depth. The root
front is the front at the first charge, rather than the final front. Keeping
this difference gives the short terminal time interval in the bad-history
count. Time here counts fill/charge pairs, not individual rounds.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 294–306, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- Front at the earliest charge, or the current front for an empty ancestry. -/
def ancestryFront (g r k : ℕ) (side : Bool) (events : List (ℕ × I)) : ℤ :=
  match events with
  | [] => S.front g r k side
  | e :: _ => S.front g r (e.1 + 1) side

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- The deterministic front is monotone in completed pair time. -/
theorem front_mono (g r : ℕ) (side : Bool) : Monotone (fun k ↦ S.front g r k side) :=
  monotone_nat_of_le_succ fun k ↦ S.front_mono_succ g r k side

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- In pair time the front advances at least one row per `2n` pairs, up to two
rounding errors. The multiplied form avoids division and floor ambiguity. -/
theorem front_speed (g r a b : ℕ) (side : Bool) (hn : 0 < S.n) (hab : a ≤ b) :
    (b : ℤ) - a ≤ 2 * S.n * (S.front g r b side - S.front g r a side + 2) := by
  have ha := Nat.mod_lt (fillCount a side) hn
  have hb := Nat.mod_lt (fillCount b side) hn
  have hea := Nat.mod_add_div (fillCount a side) S.n
  have heb := Nat.mod_add_div (fillCount b side) S.n
  have hcounts : b - a ≤ 2 * (fillCount b side - fillCount a side) + 1 := by
    cases side <;> simp only [fillCount, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hmono : fillCount a side ≤ fillCount b side := by
    cases side <;> simp only [fillCount, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hcountZ : (b : ℤ) - a ≤ 2 * ((fillCount b side : ℤ) - fillCount a side) + 1 := by
    exact_mod_cast hcounts
  have heaZ : ((fillCount a side % S.n : ℕ) : ℤ) +
      S.n * ((fillCount a side / S.n : ℕ) : ℤ) = fillCount a side := by exact_mod_cast hea
  have hebZ : ((fillCount b side % S.n : ℕ) : ℤ) +
      S.n * ((fillCount b side / S.n : ℕ) : ℤ) = fillCount b side := by exact_mod_cast heb
  have hbZ : ((fillCount b side % S.n : ℕ) : ℤ) < S.n := by exact_mod_cast hb
  have haZ : (0 : ℤ) ≤ (fillCount a side % S.n : ℕ) := by positivity
  have hnZ : (0 : ℤ) < S.n := by exact_mod_cast hn
  simp only [front, nominalFront]
  nlinarith

omit [DecidableEq V] [Fintype I] [LinearOrder I] in
private theorem ball_depth_step (side : Bool) (i : I) (x y : V)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hx : x ∈ S.ball i) (hy : y ∈ S.ball i) :
    orientedDepth S.depth side x ≤ orientedDepth S.depth side y + 2 * S.r₀ := by
  have hxv := abs_le.mp (hdepth i x hx)
  have hyv := abs_le.mp (hdepth i y hy)
  cases side <;> simp only [orientedDepth, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The depth gain of an actual ancestry is at most `2r₀` per charge, measured
from its first charge's front. Empty ancestries cannot lead the current front. -/
theorem ChargeAncestry.depth_le {g r k : ℕ} {choices : ℕ → Bool × Fin S.M}
    {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀) :
    orientedDepth S.depth side x ≤ S.ancestryFront g r k side events +
      2 * S.r₀ * events.length := by
  induction h with
  | initial x hxA hx =>
    simp only [ancestryFront, List.length_nil, Nat.cast_zero, mul_zero, add_zero]
    simp only [initialPartition, hxA] at hx
    cases side <;> simp only [orientedDepth, front, nominalFront, initialFront,
      fillCount, Bool.false_eq_true, ↓reduceIte] <;> split_ifs at hx <;> simp_all <;> omega
  | @retain k x events hp ih =>
    cases events with
    | nil =>
      simp only [ancestryFront, List.length_nil, Nat.cast_zero, mul_zero, add_zero] at *
      exact ih.trans (S.front_mono_succ g r k side)
    | cons e es => exact ih
  | fill k x hs hslot =>
    have hd := fillSlot_depth hslot
    rw [hs] at hd
    change orientedDepth S.depth side x = S.front g r k side at hd
    simpa only [ancestryFront, List.length_nil, Nat.cast_zero, mul_zero, add_zero, hd]
      using S.front_mono_succ g r k side
  | @charge k x y events i hp hs hsel hy hx ih =>
    have hv := S.ball_depth_step side i x y hdepth hx hy
    cases events with
    | nil =>
      have hf := S.front_mono_succ g r k side
      simp only [ancestryFront, List.nil_append, List.length_singleton, Nat.cast_one,
        List.length_nil, Nat.cast_zero, mul_zero, add_zero, mul_one] at *
      omega
    | cons e es =>
      simp only [ancestryFront, List.cons_append, List.length_cons, List.length_append,
        Nat.cast_add, Nat.cast_one] at *
      nlinarith
  | chargeFill k x y i hf hslot hs hsel hy hx =>
    have hd := fillSlot_depth hslot
    rw [hf] at hd
    change orientedDepth S.depth side y = S.front g r k side at hd
    have hv := S.ball_depth_step side i x y hdepth hx hy
    have hm := S.front_mono_succ g r k side
    simp only [ancestryFront, List.length_singleton, Nat.cast_one, mul_one]
    omega

/-- A bad endpoint forces a nonempty, long ancestry and locates every charge
inside an explicit short terminal interval. The bounds are finite, with no
asymptotic probability assumption. -/
theorem ChargeAncestry.bad_length_and_time {g r k : ℕ}
    {choices : ℕ → Bool × Fin S.M} {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) (hn : 0 < S.n)
    (hdepth : ∀ i x, x ∈ S.ball i → |S.depth x - S.depth (S.anchor i)| ≤ S.r₀)
    (hbad : 2 * S.front g r k side + S.D < 2 * orientedDepth S.depth side x) :
    events ≠ [] ∧ (S.D : ℤ) < 4 * S.r₀ * events.length ∧
      ∀ e ∈ events, (k : ℤ) - (e.1 + 1) ≤
        4 * S.n * ((S.r₀ : ℤ) * events.length + 1) := by
  have hd := h.depth_le S hdepth
  have hne : events ≠ [] := by
    intro he
    subst events
    simp only [ancestryFront, List.length_nil, Nat.cast_zero, mul_zero, add_zero] at hd
    have hD : (0 : ℤ) ≤ S.D := by positivity
    omega
  obtain ⟨e₀, es, he⟩ := List.exists_cons_of_ne_nil hne
  subst events
  have ht₀ := h.time_lt S e₀ (by simp)
  have hm := S.front_mono g r side (Nat.succ_le_of_lt ht₀)
  simp only [ancestryFront] at hd
  refine ⟨by simp, by nlinarith, ?_⟩
  intro e he
  have ht := h.time_lt S e he
  have horder : e₀.1 ≤ e.1 := by
    rcases List.mem_cons.mp he with he | he
    · subst e; exact le_rfl
    · exact (List.pairwise_cons.mp (h.ordered S)).1 e he |>.le
  have hs := S.front_speed g r (e₀.1 + 1) k side hn (Nat.succ_le_of_lt ht₀)
  have hD : (0 : ℤ) ≤ S.D := by positivity
  have hnZ : (0 : ℤ) < S.n := by exact_mod_cast hn
  have hoZ : (e₀.1 : ℤ) ≤ e.1 := by exact_mod_cast horder
  have hdelta : S.front g r k side - S.front g r (e₀.1 + 1) side ≤
      2 * S.r₀ * (e₀ :: es).length := by omega
  have hmul := mul_le_mul_of_nonneg_left hdelta (show (0 : ℤ) ≤ 2 * S.n by positivity)
  push_cast at hs
  nlinarith

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
