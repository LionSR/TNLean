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
import TNLean.MPS.ParentHamiltonian.QuasiLocalWindowCoordinates

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
  exact quasiLocalIntervalObservable_chainWindowOperator a (3 * (2 * k)) k
    (Matrix.reindex (MPOTensor.originalSiteHeisenbergOutputCentreEquiv d k)
      (MPOTensor.originalSiteHeisenbergOutputCentreEquiv d k)
        (MPOTensor.twoLinkOutputObservable u v A)) (by omega) (by omega)

/-- After the actual supplied physical blocking, an arbitrary pair
observable has precisely the four-site two-link output matrix. The
finite identity and blocking coordinate equations derive the action.
Source: arXiv:1703.09188, Appendix, lines 2313–2334. -/
theorem blocked_bufferedMPUQuasiLocalAut_pair_interval [NeZero k]
    (a : ℤ)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    blockedAutomorphism d k (bufferedMPUQuasiLocalAut hU k hk S)
      (quasiLocalIntervalObservable (MPSTensor.blockPhysDim d k) a 2
        (Matrix.reindex (finTwoArrowEquiv (Fin (MPSTensor.blockPhysDim d k))).symm
          (finTwoArrowEquiv (Fin (MPSTensor.blockPhysDim d k))).symm A)) =
      quasiLocalIntervalObservable (MPSTensor.blockPhysDim d k) (a - 1) 4
        (Matrix.reindex (MPOTensor.originalSiteHeisenbergOutputBlockEquiv
          (MPSTensor.blockPhysDim d k))
          (MPOTensor.originalSiteHeisenbergOutputBlockEquiv (MPSTensor.blockPhysDim d k))
          (MPOTensor.twoLinkOutputObservable u v A)) := by
  have hE₂ : (finTwoArrowEquiv (Fin (MPSTensor.blockPhysDim d k))).symm.trans
      (MPSTensor.blockedConfigEquiv d 2 k) = MPOTensor.originalSiteHeisenbergCentreEquiv d k := by
    apply Equiv.ext
    intro c
    exact (MPOTensor.originalSiteHeisenbergCentreEquiv_eq_blockedConfigEquiv d k c).symm
  have hInput : Matrix.reindex (MPSTensor.blockedConfigEquiv d 2 k)
      (MPSTensor.blockedConfigEquiv d 2 k)
      (Matrix.reindex (finTwoArrowEquiv (Fin (MPSTensor.blockPhysDim d k))).symm
        (finTwoArrowEquiv (Fin (MPSTensor.blockPhysDim d k))).symm A) =
      Matrix.reindex (MPOTensor.originalSiteHeisenbergCentreEquiv d k)
        (MPOTensor.originalSiteHeisenbergCentreEquiv d k) A := by
    rw [← hE₂]
    rfl
  have hOutput : Matrix.reindex (MPSTensor.blockedConfigEquiv d 4 k)
      (MPSTensor.blockedConfigEquiv d 4 k)
      (Matrix.reindex (MPOTensor.originalSiteHeisenbergOutputBlockEquiv
        (MPSTensor.blockPhysDim d k))
        (MPOTensor.originalSiteHeisenbergOutputBlockEquiv (MPSTensor.blockPhysDim d k))
        (MPOTensor.twoLinkOutputObservable u v A)) =
      Matrix.reindex (MPOTensor.originalSiteHeisenbergOutputCentreEquiv d k)
        (MPOTensor.originalSiteHeisenbergOutputCentreEquiv d k)
        (MPOTensor.twoLinkOutputObservable u v A) := rfl
  have hF := bufferedMPUQuasiLocalAut_central_interval_four_output hU k hk S
    ((a - 2) * (k : ℤ)) A
  have hStart : (a - 2) * (k : ℤ) + (2 * k : ℕ) = a * k := by push_cast; ring
  have hEnd : (a - 2) * (k : ℤ) + (k : ℕ) = (a - 1) * k := by ring
  rw [hStart, hEnd] at hF
  apply (quasiLocalBlocking d k).injective
  rw [blockedAutomorphism_apply, StarAlgEquiv.apply_symm_apply,
    quasiLocalBlocking_quasiLocalIntervalObservable,
    quasiLocalBlocking_quasiLocalIntervalObservable, hInput, hOutput]
  exact hF

/-- The actual blocked pair image is supported on its four adjacent
sites, for every observable in the complete input-pair algebra.
Source: arXiv:1703.09188, Appendix, lines 2313–2318. -/
theorem blocked_bufferedMPUQuasiLocalAut_pair_supportedIn [NeZero k]
    (a : ℤ) {X : QuasiLocalAlgebra (MPSTensor.blockPhysDim d k)}
    (hX : QuasiLocalSupportedIn X (finiteChainRegion a 2)) :
    QuasiLocalSupportedIn
      (blockedAutomorphism d k (bufferedMPUQuasiLocalAut hU k hk S) X)
      (finiteChainRegion (a - 1) 4) := by
  classical
  obtain ⟨B, rfl⟩ := hX
  let E := (finTwoArrowEquiv (Fin (MPSTensor.blockPhysDim d k))).symm
  let A := Matrix.reindex E.symm E.symm
    (intervalCoordinates (MPSTensor.blockPhysDim d k) a 2 B)
  have hA : Matrix.reindex E E A =
      intervalCoordinates (MPSTensor.blockPhysDim d k) a 2 B := by
    ext row col
    simp only [A, Matrix.reindex_apply, Equiv.symm_apply_apply]
  have hinput : quasiLocalIntervalObservable (MPSTensor.blockPhysDim d k) a 2
      (Matrix.reindex E E A) = quasiLocalObservable _ (finiteChainRegion a 2) B := by
    rw [hA, quasiLocalIntervalObservable_apply, StarAlgEquiv.symm_apply_apply]
  have h := blocked_bufferedMPUQuasiLocalAut_pair_interval hU k hk S a A
  change blockedAutomorphism d k (bufferedMPUQuasiLocalAut hU k hk S)
    (quasiLocalIntervalObservable _ a 2 (Matrix.reindex E E A)) = _ at h
  rw [hinput] at h
  exact ⟨_, h.symm⟩

/-- Intersecting the two actual overlapping pair-image bounds derives
nearest-neighbour support for every blocked singleton.
Source: arXiv:1703.09188, Appendix, lines 2313–2318. -/
theorem blocked_bufferedMPUQuasiLocalAut_singleton_supportedIn [NeZero k]
    (x : ℤ) {X : QuasiLocalAlgebra (MPSTensor.blockPhysDim d k)}
    (hX : QuasiLocalSupportedIn X {x}) :
    QuasiLocalSupportedIn
      (blockedAutomorphism d k (bufferedMPUQuasiLocalAut hU k hk S) X)
      (finiteChainRegion (x - 1) 3) := by
  have hleft : ({x} : Finset ℤ) ⊆ finiteChainRegion (x - 1) 2 := by
    simp only [Finset.singleton_subset_iff, finiteChainRegion, Finset.mem_Ico]
    omega
  have hright : ({x} : Finset ℤ) ⊆ finiteChainRegion x 2 := by
    simp only [Finset.singleton_subset_iff, finiteChainRegion, Finset.mem_Ico]
    omega
  have h₁ := blocked_bufferedMPUQuasiLocalAut_pair_supportedIn hU k hk S (x - 1)
    (hX.mono hleft)
  have h₂ := blocked_bufferedMPUQuasiLocalAut_pair_supportedIn hU k hk S x
    (hX.mono hright)
  have hInter : finiteChainRegion (x - 1 - 1) 4 ∩ finiteChainRegion (x - 1) 4 =
      finiteChainRegion (x - 1) 3 := by
    ext y
    simp only [finiteChainRegion, Finset.mem_inter, Finset.mem_Ico]
    omega
  simpa only [hInter] using h₁.inter h₂

/-- The actual supplied-block automorphism has the nearest-neighbour
propagation needed by the GNVW support-factor construction. It is derived
from the literal pair action, not supplied as a locality hypothesis.
Source: arXiv:1703.09188, Appendix, lines 2313–2318. -/
theorem blocked_bufferedMPUQuasiLocalAut_propagatesWithin [NeZero k] :
    PropagatesWithin (blockedAutomorphism d k (bufferedMPUQuasiLocalAut hU k hk S))
      (Finset.Icc (-1) 1) := by
  classical
  intro Λ X hX
  obtain ⟨A, rfl⟩ := hX
  let b := MPSTensor.blockPhysDim d k
  let ω := blockedAutomorphism d k (bufferedMPUQuasiLocalAut hU k hk S)
  let K := regionSumset Λ (Finset.Icc (-1) 1)
  let T := (quasiLocalObservable b K).range.comap
    (ω.toStarAlgHom.comp (algebraicToQuasiLocal b))
  have hsites : ∀ x ∈ Λ, (localObservable b {x}).range ≤ T := by
    intro x hx z hz
    obtain ⟨B, rfl⟩ := hz
    have h := blocked_bufferedMPUQuasiLocalAut_singleton_supportedIn hU k hk S x
      (show QuasiLocalSupportedIn (quasiLocalObservable b {x} B) {x} from ⟨B, rfl⟩)
    have hsub : finiteChainRegion (x - 1) 3 ⊆ K := by
      intro y hy
      have hy' := Finset.mem_Ico.mp hy
      apply (mem_regionSumset y Λ _).mpr
      refine ⟨x, hx, y - x, ?_, by omega⟩
      simp only [Finset.mem_Icc]
      omega
    exact h.mono hsub
  exact range_localObservable_le_of_singletons Λ T hsites ⟨A, rfl⟩

end SpinChain
