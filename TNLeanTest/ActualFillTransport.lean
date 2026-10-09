/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FillSupportCompatibility
import TNLean.PEPS.AreaLaw.Scan.FillTransportEndpoints
import TNLeanTest.ActualBandGeometryData

/-!
# Actual deterministic fill regressions

Blank and occupied slots, both scheduled sides, an already assigned singleton,
positive actual tree weights, exact adjacent-round roots, and the shared
two-band physical support fixture with repeated anchor labels.
-/

set_option autoImplicit false

open TensorPower TensorPower.ReplicaTransport
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

namespace TNLeanTest.ActualFillTransport

noncomputable section

/-- A single physical site with a two-slot row, leaving one genuine padding slot. -/
private def singletonScan (z : ℤ) : CollarScan Unit Unit where
  graph := ⊥
  A := Finset.univ
  depth _ := z
  anchor _ := ()
  n := 2
  m := 1
  K := 1
  D := 1
  r₀ := 0
  C₁ := 1

private theorem near_slot :
    fillSlot (singletonScan 2).A (singletonScan 2).depth (singletonScan 2).n
      ((singletonScan 2).lower 0 0) ((singletonScan 2).upper 0 0) false 0 = some () := by
  norm_num [singletonScan, CollarScan.lower, CollarScan.upper, fillSlot,
    initialFront, orientedRow, depthRow, Finset.univ_unique]

private theorem far_slot :
    fillSlot (singletonScan 5).A (singletonScan 5).depth (singletonScan 5).n
      ((singletonScan 5).lower 0 0) ((singletonScan 5).upper 0 0) true 0 = some () := by
  norm_num [singletonScan, CollarScan.lower, CollarScan.upper, fillSlot,
    initialFront, orientedRow, depthRow, Finset.univ_unique]

private theorem padded_slot :
    fillSlot (singletonScan 2).A (singletonScan 2).depth (singletonScan 2).n
      ((singletonScan 2).lower 0 0) ((singletonScan 2).upper 0 0) false 1 = none := by
  norm_num [singletonScan, CollarScan.lower, CollarScan.upper, fillSlot,
    initialFront, orientedRow, depthRow, Finset.univ_unique]

-- These slot outcomes are computed from the schedule, with no slot premise.
example : (singletonScan 2).quantumFillMove 0 0 0 (fun _ => none) =
    .toP {Sum.inl ()} := by
  simp only [CollarScan.quantumFillMove, show fillSide 0 = false from rfl,
    show fillCount 0 false = 0 from rfl, near_slot]
  simp [augmentedMove, middle, Finset.univ_unique]

example : (singletonScan 5).quantumFillMove 0 0 1 (fun _ => none) =
    .toF {Sum.inl ()} := by
  simp only [CollarScan.quantumFillMove, show fillSide 1 = true from rfl,
    show fillCount 1 true = 0 from rfl, far_slot]
  simp [augmentedMove, middle, Finset.univ_unique]

example : (singletonScan 2).quantumFillMove 0 0 2 (fun _ => none) = .stay := by
  simp only [CollarScan.quantumFillMove, show fillSide 2 = false from rfl,
    show fillCount 2 false = 1 from rfl, padded_slot]

example : ((singletonScan 2).quantumFillMove 0 0 0 (fun _ => some true)).subsystem = ∅ :=
  (singletonScan 2).quantumFillMove_subsystem_of_assigned 0 0 0 _ () true near_slot rfl

example : ((singletonScan 2).quantumFillMove 0 0 0 (fun _ => some true)).apply
    (augmentedPartition fun _ => some true) = augmentedPartition (fun _ => some true) := by
  simp only [CollarScan.quantumFillMove, show fillSide 0 = false from rfl,
    show fillCount 0 false = 0 from rfl, near_slot]
  simp [augmentedMove, middle, Move.apply]

example : ((singletonScan 2).quantumFillMove 0 0 2 (fun _ => none)).apply
    (augmentedPartition fun _ => none) = augmentedPartition (fun _ => none) := by
  simp only [CollarScan.quantumFillMove, show fillSide 2 = false from rfl,
    show fillCount 2 false = 1 from rfl, padded_slot, Move.apply]

example : fillCount 3 false = fillCount 2 false + 1 := rfl

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable (S : CollarScan V I)

example (g r k : ℕ) (σ : PhysicalPartition V)
    (hslot : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) = none) :
    S.quantumFillMove g r k σ = .stay := by
  simp [CollarScan.quantumFillMove, hslot]

example (g r : ℕ) (σ : PhysicalPartition V) (x : V)
    (hslot : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r) false 0 = some x) :
    S.quantumFillMove g r 0 σ = augmentedMove σ false {x} := by
  simpa [CollarScan.quantumFillMove, fillSide, fillCount] using
    congrArg (fun slot => match slot with
      | none => Move.stay
      | some y => augmentedMove σ false {y}) hslot

example (g r : ℕ) (σ : PhysicalPartition V) (x : V)
    (hslot : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r) true 0 = some x) :
    S.quantumFillMove g r 1 σ = augmentedMove σ true {x} := by
  simpa [CollarScan.quantumFillMove, fillSide, fillCount] using
    congrArg (fun slot => match slot with
      | none => Move.stay
      | some y => augmentedMove σ true {y}) hslot

example (g r k : ℕ) (σ : PhysicalPartition V) (x : V) (old : Bool)
    (hslot : fillSlot S.A S.depth S.n (S.lower g r) (S.upper g r)
      (fillSide k) (fillCount k (fillSide k)) = some x)
    (hx : σ x = some old) : (S.quantumFillMove g r k σ).subsystem = ∅ :=
  S.quantumFillMove_subsystem_of_assigned g r k σ x old hslot hx

-- No positive-band-count assumption is required by admission.
example (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ) :
    (S.actualFillData hm hM k).IsAdmissible :=
  S.actualFillData_isAdmissible hm hM k

example (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ) :
    (({ S with K := 0 } : CollarScan V I).actualFillData hm hM k).IsAdmissible :=
  ({ S with K := 0 } : CollarScan V I).actualFillData_isAdmissible hm hM k

example (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.actualFillData hm hM k).CrossBandCommute n t replicas :=
  S.fillTransportData_crossBandCommute _ n ht replicas

example (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.actualFillData hm hM k).rootPath n t replicas 0 =
      (historyMeanTree S.K S.m S.M hm hM k).eval
        (fun h => S.quantumHistoryMetric n t replicas h false) :=
  S.actualFillData_rootPath_zero hm hM k n ht replicas

example (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.actualFillData hm hM k).rootPath n t replicas 1 =
      (historyMeanTree S.K S.m S.M hm hM k).eval
        (fun h => S.quantumHistoryMetric n t replicas h true) :=
  S.actualFillData_rootPath_one hm hM k n ht replicas

example (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.actualFillData hm hM k).rootPath n t replicas 1 =
      (S.chargeTransportData (historyMeanTree S.K S.m S.M hm hM k)
        (fun _ => chargeChoiceTree S.K S.M hM)).rootPath n t replicas 0 :=
  S.actualFillData_rootPath_one_eq_charge_zero hm hM k n ht replicas

example (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.chargeTransportData (historyMeanTree S.K S.m S.M hm hM k)
      (fun _ => chargeChoiceTree S.K S.M hM)).rootPath n t replicas 1 =
      (S.actualFillData hm hM (k + 1)).rootPath n t replicas 0 :=
  S.charge_rootPath_one_eq_actualFillData_zero hm hM k n ht replicas

open TNLeanTest.ActualBandGeometryData

-- Physical supports keep three distinct labels, including the repeated anchor.
example (histTree : Matrix.MeanTree (History scan.K scan.m scan.M 0))
    (n : Site domain ⊕ Bool → ℕ) (E : EnergyTerms (Site domain ⊕ Bool) n (Fin 3))
    (hsupport : ∀ i, E.support i =
      (designatedSupport scan.graph (scan.truncationSet 192) scan.r₀ (scan.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩) :
    (scan.fillTransportData histTree).SupportCompatible E :=
  CollarScan.fillTransportData_supportCompatible_domainGraph target_nonempty scan rfl rfl
    histTree (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ambient_rows clearance n E hsupport

end
end TNLeanTest.ActualFillTransport
