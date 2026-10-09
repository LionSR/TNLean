/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FillTransport

/-!
# Exact endpoints of actual fill and charge roots

The physical terminal metrics are positive definite by the actual ordered-band
geometry. A fill changes only the inputs of the existing history tree; its new
root is exactly the following charge's old root. A charge substitutes its fixed
conditional trees at those leaves, giving exactly the next fill's old root.
No equality of probability distributions or reassociation of matrix means is used.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 257–286, and `08-scanner.tex`, lines 83–154,
at `openai/math@adc7f124`.
-/

open scoped Matrix unitInterval

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower TensorPower.ReplicaTransport

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- The ordered product of actual band metrics at a completed or pre-charge
status, extended by the identity outside the symmetric replica subspace. -/
def quantumHistoryMetric (n : V ⊕ Bool → ℕ) (t : ℝ) (replicas : ℕ)
    {k : ℕ} (h : History S.K S.m S.M k) (preCharge : Bool) :
    Matrix (Config replicas fun v => Fin (n v)) (Config replicas fun v => Fin (n v)) ℂ :=
  (List.ofFn fun g => symBandMetric n t replicas
    (S.quantumHistoryPartition h g preCharge)).prod

/-- Actual history metrics are positive definite; no positivity assumption
on a terminal matrix is added to the scanner data. -/
theorem posDef_quantumHistoryMetric (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) {k : ℕ}
    (h : History S.K S.m S.M k) (preCharge : Bool) :
    (S.quantumHistoryMetric n t replicas h preCharge).PosDef := by
  apply Matrix.MeanTree.posDef_listProd_ofFn
  · intro g
    exact posDef_symBandMetric (augmentedPartition_isPartition _) ht replicas
  · intro g g' hgg
    rcases lt_or_gt_of_ne hgg with hlt | hgt
    · exact S.commute_quantumHistoryPartition h h g g' hlt
        preCharge preCharge n ht replicas
    · exact (S.commute_quantumHistoryPartition h h g' g hgt
        preCharge preCharge n ht replicas).symm

/-- The old metric of a fill is its actual completed-history metric. -/
theorem fillTransportData_oldMetric {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (n : V ⊕ Bool → ℕ) (t : ℝ) (replicas : ℕ) (h : History S.K S.m S.M k) :
    (S.fillTransportData histTree).oldMetric n t replicas h =
      S.quantumHistoryMetric n t replicas h false := rfl

/-- The new metric of a fill is its actual pre-charge metric. -/
theorem fillTransportData_newMetric {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (n : V ⊕ Bool → ℕ) (t : ℝ) (replicas : ℕ)
    (h : History S.K S.m S.M k) (c : Unit) :
    (S.fillTransportData histTree).newMetric n t replicas h c =
      S.quantumHistoryMetric n t replicas h true := by
  simp only [TransportData.newMetric, fillTransportData_new]
  rfl

/-- A charge starts at the same pre-charge metric that ends its fill. -/
theorem chargeTransportData_oldMetric {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (n : V ⊕ Bool → ℕ) (t : ℝ) (replicas : ℕ) (h : History S.K S.m S.M k) :
    (S.chargeTransportData histTree choiceTree).oldMetric n t replicas h =
      S.quantumHistoryMetric n t replicas h true := rfl

/-- A charge ends at the completed metric of the actual extended history. -/
theorem chargeTransportData_newMetric {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (n : V ⊕ Bool → ℕ) (t : ℝ) (replicas : ℕ)
    (h : History S.K S.m S.M k) (c : ChargeChoices S.K S.M) :
    (S.chargeTransportData histTree choiceTree).newMetric n t replicas h c =
      S.quantumHistoryMetric n t replicas (extendHistory h c) false := by
  simp only [TransportData.newMetric, chargeTransportData_new]
  rfl

private theorem actualFillData_rootPath_eq (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) (t : ℝ) (replicas : ℕ) (p : ℝ) :
    (S.actualFillData hm hM k).rootPath n t replicas p =
      Matrix.Transport.interpRoot (historyMeanTree S.K S.m S.M hm hM k)
        (fun _ => fillChoiceTree) (fun h => S.quantumHistoryMetric n t replicas h false)
        (fun h _ => S.quantumHistoryMetric n t replicas h true)
        (Set.projIcc (0 : ℝ) 1 zero_le_one p) := by
  have hnew : (S.actualFillData hm hM k).newMetric n t replicas =
      fun h (_ : Unit) => S.quantumHistoryMetric n t replicas h true := by
    funext h c
    exact S.fillTransportData_newMetric _ n t replicas h c
  change Matrix.Transport.interpRoot (historyMeanTree S.K S.m S.M hm hM k)
    (fun _ => fillChoiceTree) ((S.actualFillData hm hM k).oldMetric n t replicas)
    ((S.actualFillData hm hM k).newMetric n t replicas) _ = _
  rw [hnew]

private theorem chargeTransportData_rootPath_eq {k : ℕ}
    (histTree : Matrix.MeanTree (History S.K S.m S.M k))
    (choiceTree : History S.K S.m S.M k → Matrix.MeanTree (ChargeChoices S.K S.M))
    (n : V ⊕ Bool → ℕ) (t : ℝ) (replicas : ℕ) (p : ℝ) :
    (S.chargeTransportData histTree choiceTree).rootPath n t replicas p =
      Matrix.Transport.interpRoot histTree choiceTree
        (fun h => S.quantumHistoryMetric n t replicas h true)
        (fun h c => S.quantumHistoryMetric n t replicas (extendHistory h c) false)
        (Set.projIcc (0 : ℝ) 1 zero_le_one p) := by
  have hnew : (S.chargeTransportData histTree choiceTree).newMetric n t replicas =
      fun h c => S.quantumHistoryMetric n t replicas (extendHistory h c) false := by
    funext h c
    exact S.chargeTransportData_newMetric histTree choiceTree n t replicas h c
  change Matrix.Transport.interpRoot histTree choiceTree
    ((S.chargeTransportData histTree choiceTree).oldMetric n t replicas)
    ((S.chargeTransportData histTree choiceTree).newMetric n t replicas) _ = _
  rw [hnew]

/-- The old endpoint of the actual fill is the existing history root evaluated
at its completed physical metrics. -/
theorem actualFillData_rootPath_zero (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.actualFillData hm hM k).rootPath n t replicas 0 =
      (historyMeanTree S.K S.m S.M hm hM k).eval
        (fun h => S.quantumHistoryMetric n t replicas h false) := by
  rw [actualFillData_rootPath_eq, Set.projIcc_left]
  exact fill_interpRoot_zero S.K S.m S.M hm hM k _ _
    (fun h => S.posDef_quantumHistoryMetric n ht replicas h false)
    (fun h => S.posDef_quantumHistoryMetric n ht replicas h true)

/-- The new endpoint of the actual fill changes only the existing history
tree's inputs to its pre-charge physical metrics. -/
theorem actualFillData_rootPath_one (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.actualFillData hm hM k).rootPath n t replicas 1 =
      (historyMeanTree S.K S.m S.M hm hM k).eval
        (fun h => S.quantumHistoryMetric n t replicas h true) := by
  rw [actualFillData_rootPath_eq, Set.projIcc_right]
  exact fill_interpRoot_one S.K S.m S.M hm hM k _ _
    (fun h => S.posDef_quantumHistoryMetric n ht replicas h false)
    (fun h => S.posDef_quantumHistoryMetric n ht replicas h true)

/-- Exact hand-off from a fill to its following charge on the same history
tree. Matrix positivity follows from the actual geometry. -/
theorem actualFillData_rootPath_one_eq_charge_zero
    (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.actualFillData hm hM k).rootPath n t replicas 1 =
      (S.chargeTransportData (historyMeanTree S.K S.m S.M hm hM k)
        (fun _ => chargeChoiceTree S.K S.M hM)).rootPath n t replicas 0 := by
  rw [S.actualFillData_rootPath_one hm hM k n ht replicas,
    chargeTransportData_rootPath_eq, Set.projIcc_left]
  exact (charge_interpRoot_zero S.K S.m S.M hm hM k _ _
    (fun h => S.posDef_quantumHistoryMetric n ht replicas h true)
    (fun h => S.posDef_quantumHistoryMetric n ht replicas h false)).symm

/-- Exact hand-off from an actual charge to the next deterministic fill.
The next history tree is the recursively substituted tree, not a reassociation. -/
theorem charge_rootPath_one_eq_actualFillData_zero
    (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (replicas : ℕ) :
    (S.chargeTransportData (historyMeanTree S.K S.m S.M hm hM k)
      (fun _ => chargeChoiceTree S.K S.M hM)).rootPath n t replicas 1 =
      (S.actualFillData hm hM (k + 1)).rootPath n t replicas 0 := by
  rw [S.actualFillData_rootPath_zero hm hM (k + 1) n ht replicas,
    chargeTransportData_rootPath_eq, Set.projIcc_right]
  exact charge_interpRoot_one S.K S.m S.M hm hM k _ _
    (fun h => S.posDef_quantumHistoryMetric n ht replicas h true)
    (fun h => S.posDef_quantumHistoryMetric n ht replicas h false)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
