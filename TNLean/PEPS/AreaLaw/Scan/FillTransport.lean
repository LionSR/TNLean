/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.HistoryMeanTree
import TNLean.PEPS.AreaLaw.Scan.PhysicalBandCommutation

/-!
# Actual deterministic fill transport

The scheduled physical fill determines a quantum move: a blank slot does
nothing, and an occupied slot transfers its singleton's old middle part to
the scheduled side. The conditional tree is a singleton, while the existing
recursive history tree is retained without reassociation.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–154, and `06-transport.tex`, lines 257–286,
at `openai/math@adc7f124`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower TensorPower.ReplicaTransport

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- The actual scheduled fill transfers only its singleton's unassigned part.
An absent slot is the identity move, even though the fill index is consumed. -/
def quantumFillMove (g r k : ℕ) (σ : PhysicalPartition V) : Move (V ⊕ Bool) :=
  match fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) with
  | none => .stay
  | some x => augmentedMove σ (fillSide k) {x}

/-- Quantum-region bookkeeping agrees with the actual deterministic fill. -/
theorem quantumFillMove_apply (g r k : ℕ) (σ : PhysicalPartition V) :
    (S.quantumFillMove g r k σ).apply (augmentedPartition σ) =
      augmentedPartition (fill S.A S.depth S.n (S.lower g r) (S.upper g r) k σ) := by
  cases he : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) with
  | none => simp [quantumFillMove, fill, he, Move.apply]
  | some x =>
    simp only [quantumFillMove, fill, he]
    exact augmentedMove_apply σ (fillSide k) {x}

/-- Every actual fill transfers a subsystem of the old middle. -/
theorem quantumFillMove_isValid (g r k : ℕ) (σ : PhysicalPartition V) :
    (S.quantumFillMove g r k σ).IsValid (augmentedPartition σ) := by
  cases he : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) with
  | none => simp [quantumFillMove, he, Move.IsValid, Move.subsystem]
  | some x =>
    simp only [quantumFillMove, he]
    exact augmentedMove_isValid σ (fillSide k) {x}

/-- An occupied slot that was already assigned moves the empty subsystem. -/
theorem quantumFillMove_subsystem_of_assigned (g r k : ℕ) (σ : PhysicalPartition V)
    (x : V) (old : Bool)
    (hslot : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) = some x)
    (hx : σ x = some old) : (S.quantumFillMove g r k σ).subsystem = ∅ := by
  have hempty : {x} ∩ middle σ = ∅ := by simp [middle, hx]
  cases hs : fillSide k <;>
    simp [quantumFillMove, hslot, augmentedMove, hs, hempty, Move.subsystem]

/-- One deterministic fill on a supplied history tree. Its new state is the
pre-charge state of the same history, with no extra random choice. -/
def fillTransportData {k : ℕ} (histTree : Matrix.MeanTree (History S.K S.m S.M k)) :
    TransportData (V ⊕ Bool) S.K (History S.K S.m S.M k) (fun _ => Unit) where
  histTree := histTree
  choiceTree _ := fillChoiceTree
  old h g := augmentedPartition (S.state h g)
  move h _ g := S.quantumFillMove g (h.1 g) k (S.state h g)

/-- The new leaf of the fill is exactly the following charge's old partition. -/
theorem fillTransportData_new {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (h : History S.K S.m S.M k) (c : Unit) (g : Fin S.K) :
    (S.fillTransportData histTree).new h c g =
      augmentedPartition (S.oldChargeState h g) :=
  S.quantumFillMove_apply g (h.1 g) k (S.state h g)

/-- The terminal fill statuses are the completed and pre-charge statuses of
the same history. This preserves the original terminal labels. -/
theorem fillTransportData_leafPart {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (h : History S.K S.m S.M k) (c : Option Unit) (g : Fin S.K) :
    (S.fillTransportData histTree).leafPart ⟨h, c⟩ g =
      S.quantumHistoryPartition h g c.isSome := by
  cases c with
  | none => rfl
  | some c => exact S.fillTransportData_new histTree h c g

/-- All bands commute across independent fill histories and old/new statuses,
as operators on the symmetric replica subspace. -/
theorem fillTransportData_crossBandCommute {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.fillTransportData histTree).CrossBandCommute n t replicas := by
  apply ((S.fillTransportData histTree).crossBandCommute_iff t replicas).mpr
  rintro ⟨h, c⟩ ⟨h', c'⟩ g g' hgg
  rw [fillTransportData_leafPart, fillTransportData_leafPart]
  rcases lt_or_gt_of_ne hgg with hlt | hgt
  · exact S.commute_quantumHistoryPartition h h' g g' hlt c.isSome c'.isSome n ht replicas
  · exact (S.commute_quantumHistoryPartition h' h g' g hgt
      c'.isSome c.isSome n ht replicas).symm

/-- Actual fill data use the already constructed recursive physical history
tree, with the singleton conditional tree at every leaf. -/
def actualFillData (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ) :
    TransportData (V ⊕ Bool) S.K (History S.K S.m S.M k) (fun _ => Unit) :=
  S.fillTransportData (historyMeanTree S.K S.m S.M hm hM k)

/-- Positive actual history weights, probability-one fill choices, genuine
partitions and valid moves give the standing transport hypotheses. -/
theorem actualFillData_isAdmissible (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ) :
    (S.actualFillData hm hM k).IsAdmissible := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    change 0 < (historyMeanTree S.K S.m S.M hm hM k).weight h
    rw [historyMeanTree_weight, historyWeight]
    positivity
  · intro h c
    cases c
    change 0 < fillChoiceTree.weight ()
    rw [fillChoiceTree_weight]
    exact zero_lt_one
  · intro h g
    exact augmentedPartition_isPartition (S.state h g)
  · intro h c g
    exact S.quantumFillMove_isValid g (h.1 g) k (S.state h g)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
