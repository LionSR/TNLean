/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AugmentedPartition
import TNLean.PEPS.AreaLaw.Scan.NestedBandMetric
import TNLean.PEPS.AreaLaw.Scan.BandNesting

/-!
# Actual cross-band quantum commutation

The actual scanner satisfies the cross-band commutation condition of
Proposition 7.4 for every pair of terminal histories, including mixed old/new
statuses. All assertions concern the symmetric replica space. History and
choice trees are supplied without changing their shape or regrouping means.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower TensorPower.ReplicaTransport

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- Select an actual completed status or the following pre-charge status. -/
def quantumHistoryPartition {k : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (preCharge : Bool) : PYF (V ⊕ Bool) :=
  augmentedPartition (if preCharge then S.oldChargeState h g else S.state h g)

/-- Both actual fill-round endpoints and charge-round endpoints have commuting
extended band metrics, across independent histories, times and statuses. -/
theorem commute_quantumHistoryPartition {k k' : ℕ}
    (h : History S.K S.m S.M k) (h' : History S.K S.m S.M k')
    (g g' : Fin S.K) (hg : g < g') (preCharge preCharge' : Bool)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    Commute (symBandMetric n t replicas (S.quantumHistoryPartition h g preCharge))
      (symBandMetric n t replicas (S.quantumHistoryPartition h' g' preCharge')) := by
  apply commute_symBandMetric_of_nested ht replicas
    (augmentedPartition_isPartition _) (augmentedPartition_isPartition _)
  apply augmentedPartition_nested
  cases preCharge <;> cases preCharge' <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · exact S.state_near_middle_subset_later_near h h' g g' hg
  · exact S.state_near_middle_subset_later_old_near h h' g g' hg
  · exact S.old_near_middle_subset_later_state_near h h' g g' hg
  · exact S.oldChargeState_near_middle_subset_later_near h h' g g' hg

/-- The actual enabled charge transfers the graph ball's old middle part.
An absent slot or a non-split ball does nothing. -/
def quantumChargeMove (g r k : ℕ) (c : Bool × Fin S.M) (σ : PhysicalPartition V) :
    Move (V ⊕ Bool) :=
  match S.selected g r k c with
  | none => .stay
  | some i =>
    if (S.ball i ∩ receiving σ c.1).Nonempty ∧ (S.ball i ∩ middle σ).Nonempty
    then augmentedMove σ c.1 (S.ball i) else .stay

/-- Quantum-region bookkeeping agrees exactly with the actual physical charge. -/
theorem quantumChargeMove_apply (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V) :
    (S.quantumChargeMove g r k c σ).apply (augmentedPartition σ) =
      augmentedPartition (S.chargeStep g r k c σ) := by
  cases he : S.selected g r k c with
  | none => simp [quantumChargeMove, chargeStep, he, Move.apply]
  | some i =>
    simp only [quantumChargeMove, chargeStep, he, charge]
    split_ifs
    · exact augmentedMove_apply σ c.1 (S.ball i)
    · rfl

/-- Every actual charge is a valid middle-to-side quantum-region move. -/
theorem quantumChargeMove_isValid (g r k : ℕ) (c : Bool × Fin S.M)
    (σ : PhysicalPartition V) :
    (S.quantumChargeMove g r k c σ).IsValid (augmentedPartition σ) := by
  cases he : S.selected g r k c with
  | none => simp [quantumChargeMove, he, Move.IsValid, Move.subsystem]
  | some i =>
    simp only [quantumChargeMove, he]
    split_ifs
    · exact augmentedMove_isValid σ c.1 (S.ball i)
    · simp [Move.IsValid, Move.subsystem]

/-- One charge round on the supplied finite trees. This definition does not choose
or reassociate any matrix mean: it supplies only actual partitions and moves. -/
def chargeTransportData {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M)) :
    TransportData (V ⊕ Bool) S.K (History S.K S.m S.M k)
      (fun _ => ChargeChoices S.K S.M) where
  histTree := histTree
  choiceTree := choiceTree
  old h g := augmentedPartition (S.oldChargeState h g)
  move h c g := S.quantumChargeMove g (h.1 g) (k + 1) (c g) (S.oldChargeState h g)

/-- New leaves evaluate to the actual extended history. -/
theorem chargeTransportData_new {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (h : History S.K S.m S.M k) (c : ChargeChoices S.K S.M) (g : Fin S.K) :
    (S.chargeTransportData histTree choiceTree).new h c g =
      augmentedPartition (S.state (extendHistory h c) g) := by
  rw [state_extendHistory]
  exact S.quantumChargeMove_apply g (h.1 g) (k + 1) (c g) (S.oldChargeState h g)

private theorem chargeTransportData_leaf_nested {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (j j' : Σ _h : History S.K S.m S.M k, Option (ChargeChoices S.K S.M))
    (g g' : Fin S.K) (hg : g < g') :
    ((S.chargeTransportData histTree choiceTree).leafPart j g).P ∪
        ((S.chargeTransportData histTree choiceTree).leafPart j g).Y ⊆
      ((S.chargeTransportData histTree choiceTree).leafPart j' g').P := by
  obtain ⟨h, c⟩ := j
  obtain ⟨h', c'⟩ := j'
  cases c with
  | none =>
    cases c' with
    | none =>
      exact augmentedPartition_nested
        (S.oldChargeState_near_middle_subset_later_near h h' g g' hg)
    | some c' =>
      simp only [TransportData.leafPart, chargeTransportData_new]
      exact augmentedPartition_nested
        (S.old_near_middle_subset_later_state_near h (extendHistory h' c') g g' hg)
  | some c =>
    cases c' with
    | none =>
      simp only [TransportData.leafPart, chargeTransportData_new]
      exact augmentedPartition_nested
        (S.state_near_middle_subset_later_old_near (extendHistory h c) h' g g' hg)
    | some c' =>
      simp only [TransportData.leafPart, chargeTransportData_new]
      exact augmentedPartition_nested
        (S.state_near_middle_subset_later_near
          (extendHistory h c) (extendHistory h' c') g g' hg)

private theorem chargeTransportData_leaf_isPartition {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (j : Σ _h : History S.K S.m S.M k, Option (ChargeChoices S.K S.M)) (g : Fin S.K) :
    ((S.chargeTransportData histTree choiceTree).leafPart j g).IsPartition := by
  obtain ⟨h, c⟩ := j
  cases c with
  | none => exact augmentedPartition_isPartition _
  | some c =>
    simp only [TransportData.leafPart, chargeTransportData_new]
    exact augmentedPartition_isPartition _

/-- Actual augmented charge histories satisfy cross-band commutation on the symmetric
replica subspace, across arbitrary histories and every old/new status pair. -/
theorem chargeTransportData_crossBandCommute {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.chargeTransportData histTree choiceTree).CrossBandCommute n t replicas := by
  intro j j' g g' hgg
  rcases lt_or_gt_of_ne hgg with hlt | hgt
  · exact bandMetric_commute_on_symmetric_of_nested ht replicas
      (S.chargeTransportData_leaf_isPartition histTree choiceTree j g)
      (S.chargeTransportData_leaf_isPartition histTree choiceTree j' g')
      (S.chargeTransportData_leaf_nested histTree choiceTree j j' g g' hlt)
  · intro w hw
    exact (bandMetric_commute_on_symmetric_of_nested ht replicas
      (S.chargeTransportData_leaf_isPartition histTree choiceTree j' g')
      (S.chargeTransportData_leaf_isPartition histTree choiceTree j g)
      (S.chargeTransportData_leaf_nested histTree choiceTree j' j g' g hgt) w hw).symm

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
