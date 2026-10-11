/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-!
# Physical partitions and the deterministic collar schedule

The state assigns every physical site to the near side, the middle, or the far
side. Moving a set changes precisely its currently unassigned sites. Positive
depth rows are fixed finite lists, padded by absent entries. Fill indices count
consumed slots, including blanks and previously assigned sites; charge choices
never occur in that counter. In the lattice specialization, choose a row order
with physical sites first. Missing ambient sites occupy trailing blank slots;
the ambient row bound ensures that this is an allowed padded row order. Sites
outside the chosen color remain in the physical row order but read as blanks.

The depth function is an integer-valued physical depth. For the collar scan it
is the ambient sup-norm distance to the target, not the graph distance used for
interaction balls. All statements here are finite combinatorial statements on
those actual rows and partitions, with no probabilities or transported states.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–137, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `false` is the near side, `true` the far side; `none` is the unassigned middle. -/
abbrev PhysicalPartition (V : Type*) := V → Option Bool

/-- The actual unassigned sites of a physical partition. -/
def middle (σ : PhysicalPartition V) : Finset V :=
  Finset.univ.filter fun x ↦ σ x = none

/-- The actual physical sites of one receiving side. -/
def receiving (σ : PhysicalPartition V) (side : Bool) : Finset V :=
  Finset.univ.filter fun x ↦ σ x = some side

/-- Transfer only the unassigned part of the selected set. -/
def assign (σ : PhysicalPartition V) (side : Bool) (move : Finset V) :
    PhysicalPartition V :=
  fun x ↦ if x ∈ move ∧ σ x = none then some side else σ x

omit [Fintype V] in
@[simp] theorem assign_eq_none (σ : PhysicalPartition V) (side : Bool)
    (move : Finset V) (x : V) :
    assign σ side move x = none ↔ σ x = none ∧ x ∉ move := by
  simp only [assign]
  split_ifs <;> simp_all
  tauto

/-- A transition can only remove sites from the middle. -/
theorem middle_assign_subset (σ : PhysicalPartition V) (side : Bool) (move : Finset V) :
    middle (assign σ side move) ⊆ middle σ := by
  simp only [middle, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    assign_eq_none]
  exact fun _ h ↦ h.1

/-- The moved physical set is exactly the old middle intersected with the selected set. -/
theorem middle_sdiff_middle_assign (σ : PhysicalPartition V) (side : Bool)
    (move : Finset V) :
    middle σ \ middle (assign σ side move) = move ∩ middle σ := by
  ext x
  simp only [middle, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    assign_eq_none, Finset.mem_inter]
  tauto

omit [Fintype V] in
/-- Assignments to either physical side are never overwritten. -/
theorem assign_of_assigned (σ : PhysicalPartition V) (side old : Bool)
    (move : Finset V) {x : V} (hx : σ x = some old) :
    assign σ side move x = some old := by
  simp [assign, hx]

/-- The manuscript's initial physical partition, with near cutoff `lo` and far cutoff `hi`.
Every site outside the chosen color belongs to the far side. -/
def initialPartition (A : Finset V) (depth : V → ℤ) (lo hi : ℤ) : PhysicalPartition V :=
  fun x ↦ if x ∉ A then some true else if depth x ≤ lo then some false
    else if hi < depth x then some true else none

/-- Oriented depth increases into the middle from either receiving side. -/
def orientedDepth (depth : V → ℤ) (side : Bool) (x : V) : ℤ :=
  if side then -depth x else depth x

/-- Initial oriented depth of the next incomplete row. -/
def initialFront (lo hi : ℤ) (side : Bool) : ℤ := if side then -hi else lo + 1

/-- The number of slots already consumed on a side after `k` fills. -/
def fillCount (k : ℕ) (side : Bool) : ℕ := if side then k / 2 else (k + 1) / 2

/-- Fill side alternates, starting on the near side. It is not the random charge side. -/
def fillSide (k : ℕ) : Bool := decide (k % 2 = 1)

/-- The nominal front is determined by consumed fill slots alone. -/
def nominalFront (n : ℕ) (lo hi : ℤ) (k : ℕ) (side : Bool) : ℤ :=
  initialFront lo hi side + (fillCount k side / n : ℕ)

/-- A fill consumes exactly one slot on its receiving side. -/
theorem fillCount_succ (k : ℕ) (side : Bool) :
    fillCount (k + 1) side = fillCount k side + if side = fillSide k then 1 else 0 := by
  cases side <;> simp only [fillCount, Bool.false_eq_true, ↓reduceIte, fillSide]
  all_goals split_ifs <;> simp_all <;> omega

/-- Fixed row order; it is chosen once and is independent of all histories. -/
noncomputable def depthRow (depth : V → ℤ) (d : ℤ) : List V :=
  (Finset.univ.filter fun x ↦ depth x = d).toList

omit [DecidableEq V] in
@[simp] theorem mem_depthRow (depth : V → ℤ) (d : ℤ) (x : V) :
    x ∈ depthRow depth d ↔ depth x = d := by
  simp [depthRow]

/-- Both sides use the fixed within-row order; the far side visits depths in reverse. -/
noncomputable def orientedRow (depth : V → ℤ) (side : Bool) (d : ℤ) : List V :=
  if side then depthRow depth (-d) else depthRow depth d

omit [DecidableEq V] in
@[simp] theorem mem_orientedRow (depth : V → ℤ) (side : Bool) (d : ℤ) (x : V) :
    x ∈ orientedRow depth side d ↔ orientedDepth depth side x = d := by
  cases side <;> simp [orientedRow, orientedDepth]
  omega

/-- Absent row entries pad each fixed order to `n` slots. -/
noncomputable def fillSlot (A : Finset V) (depth : V → ℤ) (n : ℕ)
    (lo hi : ℤ) (side : Bool) (t : ℕ) : Option V :=
  let d := initialFront lo hi side + (t / n : ℕ)
  (orientedRow depth side d)[t % n]? |>.filter fun x ↦ x ∈ A

/-- A fill consumes its prescribed slot even if it is blank or already assigned. -/
noncomputable def fill (A : Finset V) (depth : V → ℤ) (n : ℕ)
    (lo hi : ℤ) (k : ℕ) (σ : PhysicalPartition V) : PhysicalPartition V :=
  let side := fillSide k
  match fillSlot A depth n lo hi side (fillCount k side) with
  | none => σ
  | some x => assign σ side {x}

/-- A blank slot leaves the physical partition unchanged, while its fill index is consumed. -/
theorem fill_blank (A : Finset V) (depth : V → ℤ) (n : ℕ) (lo hi : ℤ)
    (k : ℕ) (σ : PhysicalPartition V)
    (h : fillSlot A depth n lo hi (fillSide k) (fillCount k (fillSide k)) = none) :
    fill A depth n lo hi k σ = σ ∧
      fillCount (k + 1) (fillSide k) = fillCount k (fillSide k) + 1 := by
  constructor
  · simp [fill, h]
  · simp [fillCount_succ]

/-- A previously assigned slot also consumes a fill without moving any physical site. -/
theorem fill_assigned (A : Finset V) (depth : V → ℤ) (n : ℕ) (lo hi : ℤ)
    (k : ℕ) (σ : PhysicalPartition V) (x : V) (old : Bool)
    (h : fillSlot A depth n lo hi (fillSide k) (fillCount k (fillSide k)) = some x)
    (hx : σ x = some old) :
    fill A depth n lo hi k σ = σ ∧
      fillCount (k + 1) (fillSide k) = fillCount k (fillSide k) + 1 := by
  constructor
  · simp only [fill, h]
    funext y
    by_cases hy : y = x
    · subst y; simpa only [hx] using assign_of_assigned σ (fillSide k) old {x} hx
    · simp [assign, hy]
  · simp [fillCount_succ]

/-- Charge eligibility is a physical intersection test, not a supplied sampling event. -/
def charge (σ : PhysicalPartition V) (side : Bool) (support : Finset V) :
    PhysicalPartition V :=
  if (support ∩ receiving σ side).Nonempty ∧ (support ∩ middle σ).Nonempty
  then assign σ side support else σ

/-- On a split support the actual charged set is precisely its unassigned part. -/
theorem charge_moves_middle_part (σ : PhysicalPartition V) (side : Bool)
    (support : Finset V)
    (hs : (support ∩ receiving σ side).Nonempty ∧ (support ∩ middle σ).Nonempty) :
    middle σ \ middle (charge σ side support) = support ∩ middle σ := by
  simp [charge, hs, middle_sdiff_middle_assign]

end TNLean.PEPS.AreaLaw.Scan
