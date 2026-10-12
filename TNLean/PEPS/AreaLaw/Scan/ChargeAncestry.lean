/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AssignedLead

/-!
# Charge ancestry of the actual finite scanner

An assigned site is traced to an initial site or a deterministic fill. Each
subsequent edge records a selected charge label and two points in its graph
ball. Times are pair indices: the charge at index `t` sees the front after
`t + 1` fills. Every physical assignment has such an ancestry, proved from the evaluator.
The relation is an overapproximation for upper bounds: its constructors do not
assert that each scheduled fill or selected charge actually made a new move.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 286–311, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- A chronological charge path rooted at an initial site or a scheduled fill slot.
Retaining a path does not append a charge. A charge immediately following a
root fill is recorded at that same pair index. The relation deliberately also
allows selected charges that made no move; only the forward implication from
an actual assignment is used in probability upper bounds. -/
inductive ChargeAncestry (g r : ℕ) (choices : ℕ → Bool × Fin S.M) (side : Bool) :
    ℕ → V → List (ℕ × I) → Prop
  | initial (x : V) (hxA : x ∈ S.A)
      (hx : initialPartition S.A S.depth (S.lower g r) (S.upper g r) x = some side) :
      ChargeAncestry g r choices side 0 x []
  | retain {k x events} (h : ChargeAncestry g r choices side k x events) :
      ChargeAncestry g r choices side (k + 1) x events
  | fill (k : ℕ) (x : V) (hside : fillSide k = side)
      (hslot : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
        (fillSide k) (fillCount k (fillSide k)) = some x) :
      ChargeAncestry g r choices side (k + 1) x []
  | charge {k x y events} (i : I)
      (hprev : ChargeAncestry g r choices side k y events)
      (hside : (choices k).1 = side)
      (hselect : S.selected g r (k + 1) (choices k) = some i)
      (hy : y ∈ S.ball i) (hx : x ∈ S.ball i) :
      ChargeAncestry g r choices side (k + 1) x (events ++ [(k, i)])
  | chargeFill (k : ℕ) (x y : V) (i : I)
      (hfillSide : fillSide k = side)
      (hslot : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
        (fillSide k) (fillCount k (fillSide k)) = some y)
      (hside : (choices k).1 = side)
      (hselect : S.selected g r (k + 1) (choices k) = some i)
      (hy : y ∈ S.ball i) (hx : x ∈ S.ball i) :
      ChargeAncestry g r choices side (k + 1) x [(k, i)]

omit [Fintype I] [LinearOrder I] in
private theorem fill_some_origin (g r k : ℕ) (σ : PhysicalPartition V)
    (x : V) (side : Bool)
    (hx : fill S.A S.depth S.n (S.lower g r) (S.upper g r) k σ x = some side) :
    σ x = some side ∨ (fillSide k = side ∧
      fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
        (fillSide k) (fillCount k (fillSide k)) = some x) := by
  cases he : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) with
  | none => exact Or.inl (by simpa only [fill, he] using hx)
  | some y =>
    simp only [fill, he, assign] at hx
    split_ifs at hx with h
    · have hxy : x = y := Finset.mem_singleton.mp h.1
      exact Or.inr ⟨Option.some.inj hx, by simp only [hxy]⟩
    · exact Or.inl hx

/-- Every actual assigned site in the chosen color has a charge ancestry.
The only spatial input says that a selected ball meeting the actual middle
lies in the chosen color; physical cut clearance proves this input. -/
theorem bandState_has_chargeAncestry (g r : ℕ) (choices : ℕ → Bool × Fin S.M)
    (hcontained : ∀ t i,
      S.selected g r (t + 1) (choices t) = some i →
      (S.ball i ∩ middle (fill S.A S.depth S.n (S.lower g r) (S.upper g r) t
        (S.bandState g r t (fun j ↦ choices j)))).Nonempty → S.ball i ⊆ S.A)
    (k : ℕ) (side : Bool) (x : V) (hxA : x ∈ S.A)
    (hx : S.bandState g r k (fun j ↦ choices j) x = some side) :
    ∃ events, S.ChargeAncestry g r choices side k x events := by
  induction k generalizing side x with
  | zero => exact ⟨[], .initial x hxA hx⟩
  | succ k ih =>
    let σ := fill S.A S.depth S.n (S.lower g r) (S.upper g r) k
      (S.bandState g r k (fun j ↦ choices j))
    have hstep : S.chargeStep g r (k + 1) (choices k) σ x = some side := hx
    have hfill (y : V) (hyA : y ∈ S.A) (hy : σ y = some side) :
        (∃ events, S.ChargeAncestry g r choices side k y events) ∨
        (fillSide k = side ∧ fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
          (fillSide k) (fillCount k (fillSide k)) = some y) := by
      rcases S.fill_some_origin g r k _ y side hy with hold | hf
      · exact Or.inl (ih side y hyA hold)
      · exact Or.inr hf
    have hkeep (hy : σ x = some side) :
        ∃ events, S.ChargeAncestry g r choices side (k + 1) x events := by
      rcases hfill x hxA hy with ⟨events, hp⟩ | ⟨hs, hf⟩
      · exact ⟨events, .retain hp⟩
      · exact ⟨[], .fill k x hs hf⟩
    cases he : S.selected g r (k + 1) (choices k) with
    | none => exact hkeep (by simpa only [chargeStep, he] using hstep)
    | some i =>
      by_cases hs : (S.ball i ∩ receiving σ (choices k).1).Nonempty ∧
          (S.ball i ∩ middle σ).Nonempty
      · simp only [chargeStep, he, charge, ite_eq_left hs, assign] at hstep
        split_ifs at hstep with hmove
        · have hside : (choices k).1 = side := Option.some.inj hstep
          obtain ⟨y, hy⟩ := hs.1
          obtain ⟨hyball, hyrecv⟩ := Finset.mem_inter.mp hy
          have hyassigned : σ y = some side := by
            simpa only [hside] using (Finset.mem_filter.mp hyrecv).2
          have hyA := hcontained k i he hs.2 hyball
          rcases hfill y hyA hyassigned with ⟨events, hp⟩ | ⟨hfside, hfslot⟩
          · exact ⟨events ++ [(k, i)], .charge i hp hside he hyball hmove.1⟩
          · exact ⟨[(k, i)], .chargeFill k x y i hfside hfslot hside he hyball hmove.1⟩
        · exact hkeep hstep
      · exact hkeep (by simpa only [chargeStep, he, charge, ite_eq_right hs] using hstep)

/-- A scheduled fill cannot create a bad lead: its row is at the old front,
and consuming the fill only advances fronts. Thus every bad old-charge site
was already bad in the preceding completed-pair state. -/
theorem oldChargeState_bad_implies_state_bad {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (x : V)
    (hx : S.oldChargeState h g x = some side)
    (hbad : 2 * S.front g (h.1 g) (k + 1) side + S.D <
      2 * orientedDepth S.depth side x) :
    S.state h g x = some side ∧
      2 * S.front g (h.1 g) k side + S.D < 2 * orientedDepth S.depth side x := by
  have hm := S.front_mono_succ g (h.1 g) k side
  rcases S.fill_some_origin g (h.1 g) k (S.state h g) x side hx with hold | ⟨hs, hf⟩
  · exact ⟨hold, by omega⟩
  · have hd := fillSlot_depth hf
    rw [hs] at hd
    change orientedDepth S.depth side x = S.front g (h.1 g) k side at hd
    have hD : (0 : ℤ) ≤ S.D := by positivity
    omega

/-- Once initially assigned, a site keeps its side under every actual fill and
charge, including sites outside the chosen color. -/
theorem bandState_of_initial_assigned (g r k : ℕ)
    (choices : Fin k → Bool × Fin S.M) (x : V) (side : Bool)
    (hx : initialPartition S.A S.depth (S.lower g r) (S.upper g r) x = some side) :
    S.bandState g r k choices x = some side := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    have hold := ih (fun j ↦ choices j.castSucc)
    let σ := S.bandState g r k (fun j ↦ choices j.castSucc)
    have hf : fill S.A S.depth S.n (S.lower g r) (S.upper g r) k σ x = some side := by
      cases he : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
          (fillSide k) (fillCount k (fillSide k)) with
      | none => simpa only [fill, he] using hold
      | some y =>
        simpa only [fill, he] using assign_of_assigned σ (fillSide k) side {y} hold
    change S.chargeStep g r (k + 1) (choices (Fin.last k)) _ x = some side
    cases he : S.selected g r (k + 1) (choices (Fin.last k)) with
    | none => simpa only [chargeStep, he] using hf
    | some i =>
      simp only [chargeStep, he]
      unfold charge
      split_ifs
      · exact assign_of_assigned _ _ _ _ hf
      · exact hf

/-- A bad completed-pair endpoint was initially in the middle. Thus bad endpoints
come from the compact collar, never from the arbitrary exterior far-side volume. -/
theorem bad_bandState_initial_none (g r k : ℕ)
    (choices : Fin k → Bool × Fin S.M) (side : Bool) (x : V) (hxA : x ∈ S.A)
    (hx : S.bandState g r k choices x = some side)
    (hbad : 2 * S.front g r k side + S.D < 2 * orientedDepth S.depth side x) :
    initialPartition S.A S.depth (S.lower g r) (S.upper g r) x = none := by
  cases he : initialPartition S.A S.depth (S.lower g r) (S.upper g r) x with
  | none => rfl
  | some old =>
    have hp := S.bandState_of_initial_assigned g r k choices x old he
    have hs : old = side := Option.some.inj (hp.symm.trans hx)
    subst old
    have hd : orientedDepth S.depth side x ≤ S.front g r 0 side := by
      simp only [initialPartition, hxA] at he
      cases side <;> simp only [orientedDepth, front, nominalFront, initialFront,
        fillCount, Bool.false_eq_true, ↓reduceIte] <;> split_ifs at he <;> simp_all <;> omega
    have hm := (monotone_nat_of_le_succ fun t ↦ S.front_mono_succ g r t side) (Nat.zero_le k)
    have hD : (0 : ℤ) ≤ S.D := by positivity
    dsimp only at hm
    omega

/-- Every recorded charge is at a strictly earlier pair index. -/
theorem ChargeAncestry.time_lt {g r k : ℕ} {choices : ℕ → Bool × Fin S.M}
    {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) :
    ∀ e ∈ events, e.1 < k := by
  induction h with
  | initial => simp
  | retain h ih => intro e he; exact Nat.lt_succ_of_lt (ih e he)
  | fill => simp
  | charge i hp hs hsel hy hx ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact Nat.lt_succ_of_lt (ih e he)
    · simpa only [List.mem_singleton.mp he] using Nat.lt_succ_self _
  | chargeFill => simp

/-- Charge times in an ancestry are strictly increasing, so their random
coordinates are distinct. Repeated interaction anchors still retain their labels. -/
theorem ChargeAncestry.ordered {g r k : ℕ} {choices : ℕ → Bool × Fin S.M}
    {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) :
    events.Pairwise (fun a b ↦ a.1 < b.1) := by
  induction h with
  | initial => simp
  | retain h ih => exact ih
  | fill => simp
  | charge i hp hs hsel hy hx ih =>
    rw [List.pairwise_append]
    exact ⟨ih, by simp, by simpa only [List.mem_singleton, forall_eq] using hp.time_lt S⟩
  | chargeFill => simp

/-- Every ancestry edge is a prescribed side-and-labelled-slot hit of the actual
fixed-offset choice path. No independence of successful physical moves is claimed. -/
theorem ChargeAncestry.selected {g r k : ℕ} {choices : ℕ → Bool × Fin S.M}
    {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) :
    ∀ e ∈ events, (choices e.1).1 = side ∧
      S.selected g r (e.1 + 1) (choices e.1) = some e.2 := by
  induction h with
  | initial => simp
  | retain h ih => exact ih
  | fill => simp
  | charge i hp hs hsel hy hx ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ih e he
    · simpa only [List.mem_singleton.mp he] using And.intro hs hsel
  | chargeFill k x y i hf hslot hs hsel hy hx => simpa using And.intro hs hsel

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
