/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteMiddleOutput
import TNLean.MPS.MPU.TwoSiteSurjectivity
import TNLean.QCA.BlockingIntervalCoordinates
import TNLean.QCA.BlockingQCA
import TNLean.QCA.SupportIntersection

/-!
# Exact local action after the supplied physical blocking

The actual supplied-data automorphism sends one complete central two-block
interval to the four adjacent output blocks with its literal two-link
matrix. Actual physical blocking then identifies this with the nearest
neighbour pair action used for the QCA support algebras.

Source: arXiv:1703.09188, StandardForm and Appendix,
lines 603–622 and 2300–2334.
-/

open scoped Matrix

namespace SpinChain

/-- Removing identity spectator sites from consecutive interval matrix
coordinates does not change the quasi-local observable. Source context:
arXiv:1703.09188, Appendix identity inclusions, lines 2292–2295. -/
theorem quasiLocalIntervalObservable_chainWindowOperator
    (d n p s : ℕ) [NeZero d] (hn : 0 < n) (a : ℤ)
    (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    quasiLocalIntervalObservable d (a - p) (p + (n + s))
      (MPSTensor.chainWindowOperator (p + (n + s)) p A) =
        quasiLocalIntervalObservable d a n A := by
  let B := (intervalCoordinates d a n).symm A
  let hIncl : finiteChainRegion a n ⊆ finiteChainRegion (a - p) (p + (n + s)) := by
    simpa only [Nat.add_assoc] using finiteChainRegion_subset_expanded a n p s
  have h := intervalCoordinates_localInclusion_eq_bufferedWindowMatrix d n p s a B
  rw [StarAlgEquiv.apply_symm_apply,
    MPOTensor.bufferedWindowMatrix_eq_chainWindowOperator d n p s hn] at h
  have hB : (intervalCoordinates d (a - p) (p + (n + s))).symm
      (MPSTensor.chainWindowOperator (p + (n + s)) p A) = localInclusion hIncl B :=
    (StarAlgEquiv.symm_apply_eq _).mpr h.symm
  rw [quasiLocalIntervalObservable_apply, hB, quasiLocalObservable_localInclusion]
  rfl

variable {d D ℓ r : ℕ} [NeZero d] {U : MPOTensor d D}
  (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
  {u : Matrix (Fin ℓ × Fin r)
    (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
  {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
    (Fin r × Fin ℓ) ℂ}
  (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)

/-- The completed actual action on a central two-block interval is its
literal six-block output window. The chain is constructed with enough
buffers for every site of the entire input interval.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
theorem bufferedMPUQuasiLocalAut_central_interval
    (a : ℤ)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    bufferedMPUQuasiLocalAut hU k hk S
      (quasiLocalIntervalObservable d (a + (2 * k : ℕ)) (2 * k)
        (Matrix.reindex (MPOTensor.originalSiteHeisenbergCentreEquiv d k)
          (MPOTensor.originalSiteHeisenbergCentreEquiv d k) A)) =
      quasiLocalIntervalObservable d a (3 * (2 * k))
        (MPOTensor.originalSiteHeisenbergOutputWindow k u v A) := by
  classical
  let J := finiteChainRegion (a + (2 * k : ℕ)) (2 * k)
  let B : LocalAlgebra d J := (intervalCoordinates d (a + (2 * k : ℕ)) (2 * k)).symm
    (Matrix.reindex (MPOTensor.originalSiteHeisenbergCentreEquiv d k)
      (MPOTensor.originalSiteHeisenbergCentreEquiv d k) A)
  let hcentral : J ⊆ finiteChainRegion a (3 * (2 * k)) := by
    intro x hx
    simp only [J, finiteChainRegion, Finset.mem_Ico] at *
    omega
  have hinput : (intervalCoordinates d a (3 * (2 * k))).symm
      (MPOTensor.originalSiteHeisenbergInputWindow d k A) = localInclusion hcentral B := by
    apply (intervalCoordinates d a (3 * (2 * k))).injective
    rw [StarAlgEquiv.apply_symm_apply]
    exact (intervalCoordinates_centralInclusion_originalSiteHeisenbergInputWindow d k a A).symm
  have hN : 1 < 0 + (3 * (2 * k) + 2 * k) := by omega
  have hSource := finiteChainLocalObservable_originalSiteHeisenbergWindow
    hU k 0 (2 * k) hN a S A
  rw [hinput, finiteChainLocalObservable_localInclusion] at hSource
  have hSourceQ := congrArg (algebraicToQuasiLocal d) hSource
  simp only [sub_zero, zero_add] at hSourceQ
  let hJ : J ⊆ finiteChainRegion a (3 * (2 * k) + 2 * k) := by
    intro x hx
    simp only [J, finiteChainRegion, Finset.mem_Ico] at *
    omega
  have hb : ∀ x ∈ J, a ≤ x - (2 * k : ℕ) ∧
      x + (4 * k : ℕ) ≤ a + (3 * (2 * k) + 2 * k) := by
    intro x hx
    simp only [J, finiteChainRegion, Finset.mem_Ico] at hx
    omega
  have hF := bufferedMPUQuasiLocalAction_finiteChainConjugation hU k hk S
    J a (3 * (2 * k) + 2 * k) hN hJ hb B
  rw [bufferedMPUQuasiLocalAut_apply]
  change bufferedMPUQuasiLocalAction hU k hk S (quasiLocalObservable d J B) = _
  rw [hF]
  exact hSourceQ

/-- The actual central-interval output lies on exactly the four adjacent
half blocks with the existing two-link output matrix. No support or
finite-image equation is supplied as a premise.
Source: arXiv:1703.09188, Appendix, lines 2300–2334. -/
theorem bufferedMPUQuasiLocalAut_central_interval_four_output
    (a : ℤ)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    bufferedMPUQuasiLocalAut hU k hk S
      (quasiLocalIntervalObservable d (a + (2 * k : ℕ)) (2 * k)
        (Matrix.reindex (MPOTensor.originalSiteHeisenbergCentreEquiv d k)
          (MPOTensor.originalSiteHeisenbergCentreEquiv d k) A)) =
      quasiLocalIntervalObservable d (a + (k : ℕ)) (4 * k)
        (Matrix.reindex (MPOTensor.originalSiteHeisenbergOutputCentreEquiv d k)
          (MPOTensor.originalSiteHeisenbergOutputCentreEquiv d k)
            (MPOTensor.twoLinkOutputObservable u v A)) := by
  rw [bufferedMPUQuasiLocalAut_central_interval hU k hk S a A,
    MPOTensor.originalSiteHeisenbergOutputWindow_eq_chainWindowOperator k hk u v A]
  have h := quasiLocalIntervalObservable_chainWindowOperator d (4 * k) k k (by omega)
    (a + (k : ℕ))
    (Matrix.reindex (MPOTensor.originalSiteHeisenbergOutputCentreEquiv d k)
      (MPOTensor.originalSiteHeisenbergOutputCentreEquiv d k)
        (MPOTensor.twoLinkOutputObservable u v A))
  have ha : a + (k : ℕ) - (k : ℕ) = a := by omega
  simpa only [ha, show k + (4 * k + k) = 3 * (2 * k) by omega] using h

end SpinChain
