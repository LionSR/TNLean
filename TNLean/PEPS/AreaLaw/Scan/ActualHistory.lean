/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FillCoverage
import TNLean.PEPS.AreaLaw.Scan.ChargeSlots
import TNLean.PEPS.AreaLaw.Scan.HistoryWeights
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Actual finite fill and charge histories

Every history evaluates to a physical partition in each band. Initial offsets
set the two depth cutoffs, fills consume the fixed padded row schedules, and
charges read the actual labelled candidate list at the current nominal front.
A blank charge slot makes no move. A nonblank slot moves its graph ball's
unassigned part exactly when that ball meets the receiving side and the middle.

The finite product histories and their classical weights are independent of
replica number and of any quantum state. No entropy, energy, good-history tail,
or transported-measure statement is part of this construction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–154, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- Physical and combinatorial input to the scanner. All states and histories are
constructed from these data. The depth is specialized to the actual ambient
target distance separately; interaction balls always use `graph.edist`. -/
structure CollarScan (V I : Type*) where
  graph : SimpleGraph V
  A : Finset V
  depth : V → ℤ
  anchor : I → V
  n : ℕ
  m : ℕ
  K : ℕ
  D : ℕ
  r₀ : ℕ
  C₁ : ℝ

namespace CollarScan

variable (S : CollarScan V I)

/-- The fixed padded charge capacity. -/
noncomputable def M : ℕ := chargeSlotCount S.C₁ S.n S.D

/-- The band's initial near-side cutoff. -/
def lower (g r : ℕ) : ℤ := (8 * g * S.m + S.m + r : ℕ)

/-- The band's initial far-side cutoff. -/
def upper (g r : ℕ) : ℤ := (8 * g * S.m + 5 * S.m + r : ℕ)

/-- The designated graph-radius ball of a label. -/
noncomputable def ball (i : I) : Finset V :=
  Finset.univ.filter fun x ↦ S.graph.edist (S.anchor i) x ≤ S.r₀

/-- One band's nominal front after `k` consumed fills. -/
def front (g r k : ℕ) (side : Bool) : ℤ :=
  nominalFront S.n (S.lower g r) (S.upper g r) k side

/-- The charge candidates at the actual nominal front, with multiplicities retained. -/
noncomputable def candidates (g r k : ℕ) (side : Bool) : List I :=
  orderedChargeCandidates (orientedDepth S.depth side) S.anchor
    (S.front g r k side - S.r₀) (S.front g r k side + S.D)

/-- Read the actual padded charge slot at this front. -/
noncomputable def selected (g r k : ℕ) (c : Bool × Fin S.M) : Option I :=
  paddedChargeSlot (S.candidates g r k c.1) S.M c.2

/-- A charge changes the physical state but consumes no fill slot. -/
noncomputable def chargeStep (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V) : PhysicalPartition V :=
  match S.selected g r k c with
  | none => σ
  | some i => charge σ c.1 (S.ball i)

/-- A fill followed by its independent random charge. The charge sees the front after
that fill, including when the fill was blank or its site had already been assigned. -/
noncomputable def pairStep (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V) : PhysicalPartition V :=
  S.chargeStep g r (k + 1) c (fill S.A S.depth S.n (S.lower g r) (S.upper g r) k σ)

/-- Recursively evaluate one band's finite choices into its actual physical partition. -/
noncomputable def bandState (g r : ℕ) : (k : ℕ) → (Fin k → Bool × Fin S.M) →
    PhysicalPartition V
  | 0, _ => initialPartition S.A S.depth (S.lower g r) (S.upper g r)
  | k + 1, choices => S.pairStep g r k (choices (Fin.last k))
      (bandState g r k (fun i ↦ choices i.castSucc))

/-- The physical partition of each band after all recorded fill/charge pairs. -/
noncomputable def state {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) :
    PhysicalPartition V :=
  S.bandState g (h.1 g) k (fun t ↦ h.2 t g)

/-- The old partition at the next charge, after its preceding deterministic fill. -/
noncomputable def oldChargeState {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K) :
    PhysicalPartition V :=
  fill S.A S.depth S.n (S.lower g (h.1 g)) (S.upper g (h.1 g)) k (S.state h g)

/-- Extending the finite history performs exactly its scheduled fill and recorded charge. -/
theorem state_extendHistory {k : ℕ} (h : History S.K S.m S.M k)
    (c : ChargeChoices S.K S.M) (g : Fin S.K) :
    S.state (extendHistory h c) g =
      S.chargeStep g (h.1 g) (k + 1) (c g) (S.oldChargeState h g) := by
  simp [state, extendHistory, bandState, pairStep, oldChargeState]

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- Attaching a charge's choices preserves the offsets and the fronts after the
preceding fill. The next fill is determined by the number of completed pairs. -/
theorem front_extendHistory {k : ℕ} (h : History S.K S.m S.M k) (g : Fin S.K)
    (c : ChargeChoices S.K S.M) (side : Bool) :
    S.front g ((extendHistory h c).1 g) (k + 1) side =
      S.front g (h.1 g) (k + 1) side := rfl

/-- The graph-ball move of a selected split label is exactly its old unassigned part. -/
theorem chargeStep_moves_middle_part (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V) (i : I) (hselect : S.selected g r k c = some i)
    (hsplit : (S.ball i ∩ receiving σ c.1).Nonempty ∧ (S.ball i ∩ middle σ).Nonempty) :
    middle σ \ middle (S.chargeStep g r k c σ) = S.ball i ∩ middle σ := by
  simp only [chargeStep, hselect]
  exact charge_moves_middle_part σ c.1 (S.ball i) hsplit

omit [Fintype I] [LinearOrder I] in
private theorem fill_none (g r k : ℕ) (σ : PhysicalPartition V) (x : V)
    (hx : fill S.A S.depth S.n (S.lower g r) (S.upper g r) k σ x = none) :
    σ x = none ∧
      fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
        (fillSide k) (fillCount k (fillSide k)) ≠ some x := by
  cases he : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) with
  | none => simpa [fill, he] using hx
  | some y =>
    simp only [fill, he, assign_eq_none, Finset.mem_singleton] at hx
    exact ⟨hx.1, by simpa [he, eq_comm] using hx.2⟩

private theorem chargeStep_none (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V) (x : V) (hx : S.chargeStep g r k c σ x = none) :
    σ x = none := by
  cases he : S.selected g r k c with
  | none => simpa only [chargeStep, he] using hx
  | some i =>
    simp only [chargeStep, he] at hx
    by_cases hs : (S.ball i ∩ receiving σ c.1).Nonempty ∧ (S.ball i ∩ middle σ).Nonempty
    · have hh : assign σ c.1 (S.ball i) x = none := by simpa [charge, hs] using hx
      exact ((assign_eq_none _ _ _ _).mp hh).1
    · simpa [charge, hs] using hx

/-- Every site remaining unassigned was initially unassigned and has survived every
consumed fill slot. This is an invariant of the actual recursive evaluator. -/
theorem bandState_unassigned (g r : ℕ) (k : ℕ) (choices : Fin k → Bool × Fin S.M)
    (x : V) (hx : S.bandState g r k choices x = none) :
    initialPartition S.A S.depth (S.lower g r) (S.upper g r) x = none ∧
      ∀ f < k, fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
        (fillSide f) (fillCount f (fillSide f)) ≠ some x := by
  induction k with
  | zero => exact ⟨hx, by omega⟩
  | succ k ih =>
    have hfill := S.chargeStep_none g r (k + 1) (choices (Fin.last k))
      (fill S.A S.depth S.n (S.lower g r) (S.upper g r) k
        (S.bandState g r k (fun i ↦ choices i.castSucc))) x hx
    obtain ⟨hold, hslot⟩ := S.fill_none g r k _ x hfill
    obtain ⟨hinit, hprev⟩ := ih (fun i ↦ choices i.castSucc) hold
    refine ⟨hinit, fun f hf ↦ ?_⟩
    by_cases hfk : f < k
    · exact hprev f hfk
    · have heq : f = k := by omega
      simpa only [heq] using hslot

/-- Sites still in the old middle were in the initial middle of that band. -/
theorem oldChargeState_initial_none {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (x : V) (hx : S.oldChargeState h g x = none) :
    initialPartition S.A S.depth (S.lower g (h.1 g)) (S.upper g (h.1 g)) x = none := by
  have hold := (S.fill_none g (h.1 g) k (S.state h g) x hx).1
  exact (S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) x hold).1

/-- No unassigned physical site can lie in a row already completed by the fill
schedule. The bound is proved for the old state of every actual charge history. -/
theorem oldChargeState_front_le {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (side : Bool) (x : V) (hn : 0 < S.n)
    (hrow : (orientedRow S.depth side (orientedDepth S.depth side x)).length ≤ S.n)
    (hx : S.oldChargeState h g x = none) :
    S.front g (h.1 g) (k + 1) side ≤ orientedDepth S.depth side x := by
  obtain ⟨hold, hslot⟩ := S.fill_none g (h.1 g) k (S.state h g) x hx
  obtain ⟨hinit, hprev⟩ :=
    S.bandState_unassigned g (h.1 g) k (fun t ↦ h.2 t g) x hold
  apply nominalFront_le_of_unconsumed S.A S.depth hn (S.lower g (h.1 g))
    (S.upper g (h.1 g)) (k + 1) side x hinit hrow
  intro f hf
  by_cases hfk : f < k
  · exact hprev f hfk
  · have heq : f = k := by omega
    simpa only [heq] using hslot

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
