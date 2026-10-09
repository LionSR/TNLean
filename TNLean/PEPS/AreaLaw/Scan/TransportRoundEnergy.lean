/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TransportRound

/-!
# The literal scan energy sum

Splitting the terminal sigma type into old and new leaves identifies the two
probability factors in the scanner energy sum with the existing transport error.
The parameter is restricted to `[0,1]`: the transport tree clamps real parameters,
whereas the scanner's displayed old and new weights use `1-p` and `p` directly.

This is an uncompiled, acceptance-dependent consumer of the pending upstream
measure API. It neither chooses an eigenvector nor asserts a zero-copy eigenvalue.
Source: *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, displays `transport:terminal-weights` and `transport:energy`.
-/

open scoped BigOperators Matrix unitInterval
open Matrix MeasureTheory Set
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

variable {V H ι : Type} [Fintype V] [DecidableEq V] {K : ℕ}
  [Fintype H] [DecidableEq H] {C : H → Type}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] [Fintype ι]
  (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]
  (E : EnergyTerms V n ι) (good : H → Prop) (t : ℝ)
  (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

private theorem sum_splitLeaves (i : ι) (F : (Σ h, Option (C h)) → ℝ) :
    (∑ j ∈ D.splitLeaves E i, F j) =
      (∑ h, if ⟨h, none⟩ ∈ D.splitLeaves E i then F ⟨h, none⟩ else 0) +
        ∑ h, ∑ c, if ⟨h, some c⟩ ∈ D.splitLeaves E i then F ⟨h, some c⟩ else 0 := by
  classical
  calc
    _ = ∑ j, if j ∈ D.splitLeaves E i then F j else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Fintype.sum_option, Finset.sum_add_distrib]

/-- On the closed interpolation interval the scanner's split weight is exactly
the total weight of the corresponding transport leaves. -/
theorem transportScanRound_splitWeight {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (i : ι) :
    (transportScanRound D n E good t pre).splitWeight p i = D.splitWeight E i p := by
  classical
  have hp' : ((projIcc (0 : ℝ) 1 zero_le_one p : I) : ℝ) = p :=
    congrArg Subtype.val (projIcc_of_mem _ hp)
  rw [TransportData.splitWeight, sum_splitLeaves]
  simp only [TransportData.tree, MeanTree.weight_interpTree_old,
    MeanTree.weight_interpTree_new, hp']
  rfl

/-- The inner energy sum retains each terminal probability and its own old or new
state, with the literal `η^(1/8)` symbol. -/
theorem transportScanRound_termEnergy (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (i : ι) :
    (transportScanRound D n E good t pre).termEnergy k p i =
      ∑ j ∈ D.splitLeaves E i,
        (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).weight j *
          ∫ u, Transport.fourierWeight u *
            realCoherentIntegral k (base n) (D.state n t k (pre k) p j u)
              (fun θ => D.splitEta E i j ((EuclideanSpace.equiv _ ℂ).symm θ) ^
                (1 / 8 : ℝ)) := by
  classical
  have hp' : ((projIcc (0 : ℝ) 1 zero_le_one p : I) : ℝ) = p :=
    congrArg Subtype.val (projIcc_of_mem _ hp)
  rw [sum_splitLeaves]
  simp only [TransportData.tree, MeanTree.weight_interpTree_old,
    MeanTree.weight_interpTree_new, hp']
  unfold ScanRound.termEnergy
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro h _
    change (if _ then _ else _) = (if _ then _ else _)
    split_ifs with hi
    · exact congrArg (fun x : ℝ => (1 - p) * D.histTree.weight h * x)
        (integral_transportScanRound_old D n E good t pre hD ht k hcomm p h
          (D.continuous_splitEta_rpow E i ⟨h, none⟩))
    · rfl
  · apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro c _
    change (if _ then _ else _) = (if _ then _ else _)
    split_ifs with hi
    · exact congrArg (fun x : ℝ => p * D.histTree.weight h * (D.choiceTree h).weight c * x)
        (integral_transportScanRound_new D n E good t pre hD ht k hcomm p h c
          (D.continuous_splitEta_rpow E i ⟨h, some c⟩))
    · rfl

/-- The scanner energy sum equals the existing transport energy error, retaining
both split-probability factors. The closed-interval guard is essential. -/
theorem transportScanRound_energySum (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (k : ℕ) (hcomm : D.CrossBandCommute n t k)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    (transportScanRound D n E good t pre).energySum k p =
      D.energyError E t k (pre k) p := by
  unfold ScanRound.energySum TransportData.energyError
  apply Finset.sum_congr rfl
  intro i _
  rw [transportScanRound_splitWeight D n E good t pre hp i,
    transportScanRound_termEnergy D n E good t pre hD ht k hcomm hp i]

end TNLean.PEPS.AreaLaw.Scan
