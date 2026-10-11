/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualHistory
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Probability of prescribed labelled charge hits

Fix all initial offsets and a finite set of distinct charge times. At each
prescribed time, require one band to choose a specified side and label. The
actual nominal front and its sorted candidate list are deterministic functions
of these fixed data. Consequently each required hit occupies at most one
side-and-slot coordinate. Factoring the finite product of independent choices
gives a factor of at most `1 / (2M)` per prescribed time.

The event may impose additional conditions, including successful physical
moves. Those conditions need not be independent: only the underlying sampled
choice coordinates are used in this upper bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 286–321, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators


private theorem sum_ite_le_sum_of_cover {α Ω : Type*} [Fintype Ω]
    (s : Finset α) (w : ℝ) (hw : 0 ≤ w)
    (E : Ω → Prop) [DecidablePred E] (P : α → Ω → Prop) [∀ a, DecidablePred (P a)]
    (bound : α → ℝ) (hbound : ∀ a ∈ s, (∑ c, if P a c then w else 0) ≤ bound a)
    (hcover : ∀ c, E c → ∃ a ∈ s, P a c) :
    (∑ c, if E c then w else 0) ≤ ∑ a ∈ s, bound a := by
  have hnonneg (a : α) (c : Ω) : 0 ≤ if P a c then w else 0 := by
    split_ifs
    · exact hw
    · exact le_rfl
  calc
    _ ≤ ∑ c : Ω, ∑ a ∈ s, if P a c then w else 0 := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : E c
      · obtain ⟨a, ha, hp⟩ := hcover c hc
        simpa only [hc, ite_true, hp] using
          (Finset.single_le_sum (fun b _ ↦ hnonneg b c) ha)
      · simp only [hc, ite_false]
        exact Finset.sum_nonneg fun a _ ↦ hnonneg a c
    _ = ∑ a ∈ s, ∑ c : Ω, if P a c then w else 0 := Finset.sum_comm
    _ ≤ ∑ a ∈ s, bound a := Finset.sum_le_sum hbound

namespace CollarScan

variable {V I : Type*} [Fintype I] [LinearOrder I]
  (S : CollarScan V I)

private theorem slot_eq_of_selected_eq_some (g r k : ℕ) (side : Bool)
    {a b : Fin S.M} {i : I}
    (ha : S.selected g r k (side, a) = some i)
    (hb : S.selected g r k (side, b) = some i) : a = b := by
  obtain ⟨ha', hai⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hb', hbi⟩ := List.getElem?_eq_some_iff.mp hb
  apply Fin.ext
  exact (Finset.sort_nodup _ _).getElem_inj_iff.mp (hai.trans hbi.symm)

/-- A prescribed side and label have probability at most one side-and-slot atom.
No candidate-capacity assumption is needed: an absent or truncated label has
probability zero. `08-scanner.tex`, lines 127–135 and 317–319. -/
theorem sum_chargeWeight_selected_le (hM : 0 < S.M) (g : Fin S.K)
    (r k : ℕ) (side : Bool) (i : I) :
    (∑ c : ChargeChoices S.K S.M,
      if (c g).1 = side ∧ S.selected g r k (c g) = some i
      then chargeWeight c else 0) ≤ 1 / (2 * (S.M : ℝ)) := by
  classical
  by_cases hex : ∃ a : Fin S.M, S.selected g r k (side, a) = some i
  · obtain ⟨a, ha⟩ := hex
    have heq (c : ChargeChoices S.K S.M) :
        ((c g).1 = side ∧ S.selected g r k (c g) = some i) ↔ c g = (side, a) := by
      constructor
      · rintro ⟨hs, hi⟩
        have hpair : c g = (side, (c g).2) := Prod.ext hs rfl
        rw [hpair] at hi
        exact hpair.trans (congrArg (Prod.mk side) (S.slot_eq_of_selected_eq_some g r k side hi ha))
      · intro hc
        simpa [hc] using ha
    simp_rw [heq]
    exact (sum_chargeWeight_band hM g (side, a)).le
  · have hfalse (c : ChargeChoices S.K S.M) :
        ¬ ((c g).1 = side ∧ S.selected g r k (c g) = some i) := by
      rintro ⟨hs, hi⟩
      apply hex
      refine ⟨(c g).2, ?_⟩
      simpa only [← hs, Prod.mk.eta] using hi
    simp only [ite_eq_right (hfalse _), Finset.sum_const_zero]
    positivity

/-- Conditional on the fixed initial offsets, any event requiring the specified
labelled hits at distinct times has classical weight at most `(1 / (2M))^j`,
where `j` is the number of prescribed times. The zero-based time `t` reads the
actual post-fill front `t + 1`. This counts selections rather than assuming
independence of successful moves. `08-scanner.tex`, lines 286–321. -/
theorem sum_chargePathWeight_le_of_selected
    (hM : 0 < S.M) {k : ℕ} (offsets : Fin S.K → Fin S.m)
    (times : Finset (Fin k)) (band : Fin k → Fin S.K)
    (side : Fin k → Bool) (label : Fin k → I)
    (E : (Fin k → ChargeChoices S.K S.M) → Prop) [DecidablePred E]
    (hhit : ∀ c, E c → ∀ t ∈ times,
      (c t (band t)).1 = side t ∧
        S.selected (band t) (offsets (band t)) (t.val + 1) (c t (band t)) =
          some (label t)) :
    (∑ c : Fin k → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0) ≤
        (1 / (2 * (S.M : ℝ))) ^ times.card := by
  classical
  let P (t : Fin k) (c : ChargeChoices S.K S.M) : Prop :=
    t ∈ times → (c (band t)).1 = side t ∧
      S.selected (band t) (offsets (band t)) (t.val + 1) (c (band t)) = some (label t)
  let f (t : Fin k) (c : ChargeChoices S.K S.M) : ℝ :=
    if P t c then chargeWeight c else 0
  have hnonneg (t : Fin k) (c : ChargeChoices S.K S.M) : 0 ≤ f t c := by
    dsimp [f]
    split_ifs
    · exact chargeWeight_nonneg c
    · exact le_rfl
  have hround (t : Fin k) :
      (∑ c : ChargeChoices S.K S.M, f t c) ≤
        if t ∈ times then 1 / (2 * (S.M : ℝ)) else 1 := by
    by_cases ht : t ∈ times
    · simpa only [f, P, ht, true_implies, ite_true] using
        S.sum_chargeWeight_selected_le hM (band t) (offsets (band t)) (t.val + 1)
          (side t) (label t)
    · simp only [f, P, ht, false_implies, ite_true, ite_false]
      exact (sum_chargeWeight S.K hM).le
  calc
    _ ≤ ∑ c : Fin k → ChargeChoices S.K S.M, ∏ t, f t (c t) := by
      apply Finset.sum_le_sum
      intro c _
      rw [show (∏ t, f t (c t)) =
          if ∀ t, P t (c t) then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0 by
        simp only [f]
        rw [Finset.prod_ite_zero]
        simp [chargeWeight]]
      by_cases hc : E c
      · have hp : ∀ t, P t (c t) := fun t ht ↦ hhit c hc t ht
        simp [hc, hp]
      · simp only [hc, ite_false]
        split_ifs <;> positivity
    _ = ∏ t : Fin k, ∑ c : ChargeChoices S.K S.M, f t c := (Fintype.prod_sum f).symm
    _ ≤ ∏ t : Fin k, if t ∈ times then 1 / (2 * (S.M : ℝ)) else 1 := by
      apply Finset.prod_le_prod₀
      · intro t _
        exact Finset.sum_nonneg fun c _ ↦ hnonneg t c
      · intro t _
        exact hround t
    _ = (1 / (2 * (S.M : ℝ))) ^ times.card := by
      rw [Fintype.prod_ite_mem]
      simp



/-- Natural-number event times match the actual ancestry lists. Distinct times
force one independent coordinate per event, including repeated labels. Empty
lists require no inhabitedness assumption on the label type.
`08-scanner.tex`, lines 291–321. -/
theorem sum_chargePathWeight_le_of_selected_list
    (hM : 0 < S.M) {k : ℕ} (offsets : Fin S.K → Fin S.m)
    (g : Fin S.K) (side : Bool) (events : List (ℕ × I))
    (htimes : ∀ e ∈ events, e.1 < k) (hdistinct : (events.map Prod.fst).Nodup)
    (E : (Fin k → ChargeChoices S.K S.M) → Prop) [DecidablePred E]
    (hhit : ∀ c, E c → ∀ e (he : e ∈ events),
      (c ⟨e.1, htimes e he⟩ g).1 = side ∧
        S.selected g (offsets g) (e.1 + 1) (c ⟨e.1, htimes e he⟩ g) = some e.2) :
    (∑ c : Fin k → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0) ≤
        (1 / (2 * (S.M : ℝ))) ^ events.length := by
  classical
  by_cases hempty : events = []
  · subst events
    simp only [List.length_nil, pow_zero]
    calc
      _ ≤ ∑ _c : Fin k → ChargeChoices S.K S.M,
          ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k := by
        apply Finset.sum_le_sum
        intro c _
        split_ifs
        · exact le_rfl
        · positivity
      _ = 1 := by
        have h := congrArg (fun z : ℝ ↦ z ^ k) (sum_chargeWeight S.K hM)
        rw [Fintype.sum_pow] at h
        simpa [chargeWeight] using h
  · let times : Finset (Fin k) := Finset.univ.filter fun t ↦ t.val ∈ events.map Prod.fst
    have himage : times.image Fin.val = (events.map Prod.fst).toFinset := by
      ext n
      simp only [times, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, List.mem_toFinset]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hn
        obtain ⟨e, he, hen⟩ := List.mem_map.mp hn
        refine ⟨⟨n, ?_⟩, hn, rfl⟩
        simpa only [← hen] using htimes e he
    have hcard : times.card = events.length := by
      calc
        times.card = (times.image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
        _ = (events.map Prod.fst).toFinset.card := congrArg Finset.card himage
        _ = events.length := by rw [List.toFinset_card_of_nodup hdistinct, List.length_map]
    let label (t : Fin k) : I :=
      if h : ∃ e ∈ events, e.1 = t.val then (Classical.choose h).2
      else (events.head hempty).2
    have h := S.sum_chargePathWeight_le_of_selected hM offsets times
      (fun _ ↦ g) (fun _ ↦ side) label E ?_
    · simpa only [hcard] using h
    · intro c hc t ht
      obtain ⟨e, he, het⟩ := List.mem_map.mp (Finset.mem_filter.mp ht).2
      have hex : ∃ e ∈ events, e.1 = t.val := ⟨e, he, het⟩
      have hevent := Classical.choose_spec hex
      have hfin : (⟨(Classical.choose hex).1, htimes _ hevent.1⟩ : Fin k) = t :=
        Fin.ext hevent.2
      simpa only [label, dite_eq_left hex, hfin, hevent.2] using
        hhit c hc (Classical.choose hex) hevent.1

/-- A finite family of prescribed labelled chains bounds any event it covers.
Each chain contributes its actual independent-choice bound; no probability bound
is assumed for the chains or for successful moves. `08-scanner.tex`, lines 310–325. -/
theorem sum_chargePathWeight_le_sum_of_selected_cover
    (hM : 0 < S.M) {k : ℕ} (offsets : Fin S.K → Fin S.m)
    {α : Type*} (chains : Finset α) (times : α → Finset (Fin k))
    (band : α → Fin k → Fin S.K) (side : α → Fin k → Bool)
    (label : α → Fin k → I)
    (E : (Fin k → ChargeChoices S.K S.M) → Prop) [DecidablePred E]
    (hcover : ∀ c, E c → ∃ a ∈ chains, ∀ t ∈ times a,
      (c t (band a t)).1 = side a t ∧
        S.selected (band a t) (offsets (band a t)) (t.val + 1) (c t (band a t)) =
          some (label a t)) :
    (∑ c : Fin k → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0) ≤
        ∑ a ∈ chains, (1 / (2 * (S.M : ℝ))) ^ (times a).card := by
  classical
  let P (a : α) (c : Fin k → ChargeChoices S.K S.M) : Prop :=
    ∀ t ∈ times a, (c t (band a t)).1 = side a t ∧
      S.selected (band a t) (offsets (band a t)) (t.val + 1) (c t (band a t)) =
        some (label a t)
  apply sum_ite_le_sum_of_cover chains _ (by positivity) E P
    (fun a ↦ (1 / (2 * (S.M : ℝ))) ^ (times a).card)
  · intro a _
    exact S.sum_chargePathWeight_le_of_selected hM offsets (times a)
      (band a) (side a) (label a) (P a) (fun c hc ↦ hc)
  · exact hcover

/-- An explicit finite family of natural-time labelled event lists gives the
sum of its independent-coordinate bounds. The lists may overlap as events.
This is the union bound used after counting actual charge ancestries.
`08-scanner.tex`, lines 310–325. -/
theorem sum_chargePathWeight_le_sum_of_selected_list_cover
    (hM : 0 < S.M) {k : ℕ} (offsets : Fin S.K → Fin S.m)
    (g : Fin S.K) (side : Bool) (chains : Finset (List (ℕ × I)))
    (htimes : ∀ events ∈ chains, ∀ e ∈ events, e.1 < k)
    (hdistinct : ∀ events ∈ chains, (events.map Prod.fst).Nodup)
    (E : (Fin k → ChargeChoices S.K S.M) → Prop) [DecidablePred E]
    (hcover : ∀ c, E c → ∃ events, ∃ hevents : events ∈ chains, ∀ e (he : e ∈ events),
      (c ⟨e.1, htimes events hevents e he⟩ g).1 = side ∧
        S.selected g (offsets g) (e.1 + 1)
          (c ⟨e.1, htimes events hevents e he⟩ g) = some e.2) :
    (∑ c : Fin k → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0) ≤
        ∑ events ∈ chains, (1 / (2 * (S.M : ℝ))) ^ events.length := by
  classical
  let P (events : List (ℕ × I)) (c : Fin k → ChargeChoices S.K S.M) : Prop :=
    ∃ hevents : events ∈ chains, ∀ e (he : e ∈ events),
      (c ⟨e.1, htimes events hevents e he⟩ g).1 = side ∧
        S.selected g (offsets g) (e.1 + 1)
          (c ⟨e.1, htimes events hevents e he⟩ g) = some e.2
  apply sum_ite_le_sum_of_cover chains _ (by positivity) E P
    (fun events ↦ (1 / (2 * (S.M : ℝ))) ^ events.length)
  · intro events hevents
    apply S.sum_chargePathWeight_le_of_selected_list hM offsets g side events
      (htimes events hevents) (hdistinct events hevents) (P events)
    rintro c ⟨_, hhit⟩ e he
    exact hhit e he
  · intro c hc
    obtain ⟨events, hevents, hhit⟩ := hcover c hc
    exact ⟨events, hevents, hevents, hhit⟩

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
