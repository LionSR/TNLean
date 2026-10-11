/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.HistoryMeanTree
import TNLean.PEPS.AreaLaw.Scan.PhysicalBandCommutation

/-!
# Admissible transport data for the actual charge trees

The actual augmented charge partitions are placed on the recursively
constructed physical history tree and its fixed uniform conditional charge
trees. Exact classical weights give positive terminal masses. No tree is
reassociated and no quantum state or sampling estimate is supplied as data.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 257–286, and `08-scanner.tex`, lines 83–154,
at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower.ReplicaTransport

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- Actual charge data on the fixed recursive history tree, using its actual
uniform conditional choices rather than newly chosen equivalent distributions. -/
noncomputable def actualChargeData (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ) :
    TransportData (V ⊕ Bool) S.K (History S.K S.m S.M k)
      (fun _ => ChargeChoices S.K S.M) :=
  S.chargeTransportData (historyMeanTree S.K S.m S.M hm hM k)
    (fun _ => chargeChoiceTree S.K S.M hM)

/-- The actual charge trees have positive path weights, genuine partitions,
and valid old-middle moves. These are derived from the actual construction. -/
theorem actualChargeData_isAdmissible (hm : 0 < S.m) (hM : 0 < S.M) (k : ℕ) :
    (S.actualChargeData hm hM k).IsAdmissible := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    change 0 < (historyMeanTree S.K S.m S.M hm hM k).weight h
    rw [historyMeanTree_weight, historyWeight]
    positivity
  · intro h c
    change 0 < (chargeChoiceTree S.K S.M hM).weight c
    rw [chargeChoiceTree_weight, chargeWeight]
    positivity
  · intro h g
    exact augmentedPartition_isPartition (S.oldChargeState h g)
  · intro h c g
    exact S.quantumChargeMove_isValid g (h.1 g) (k + 1) (c g) (S.oldChargeState h g)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
