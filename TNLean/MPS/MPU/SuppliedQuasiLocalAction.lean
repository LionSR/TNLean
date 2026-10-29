/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SuppliedWindowCoordinates
import TNLean.MPS.MPU.QuasiLocalAction
import TNLean.QCA.QuasiLocalInterval

/-!
# Actual completed action on one directly supplied tensor cell

The named bare-MPU automorphism is evaluated on a buffered finite chain.
The directly supplied finite-window identity gives its actual output on
the three neighbouring cells. Any equivalent physical alphabet is allowed;
its sitewise reindexing is done only in finite matrix coordinates.

**Scope restriction (supplied standard form):** The standard-form datum
and its gates are supplied; constructing these data is separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.

Source: CPSV17, StandardForm and eq:appendix-1, lines 603–622 and
2300–2306, with physical reindexing as in IndexTh(ii), lines 824–847.
-/

open scoped Matrix

namespace SpinChain

private theorem finiteChainLocalObservable_suppliedWindow
    {d b D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (e : Fin b ≃ Fin (d * d)) (S : MPOTensor.TwoSiteStandardFormData W u v)
    (p s : ℕ) (hN : 1 < p + (3 + s)) (a : ℤ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    finiteChainLocalObservable ((S.isMPU W u v).reindexPhysical e) hN (a - p)
      (show finiteChainRegion a 3 ⊆ finiteChainRegion (a - p) (p + (3 + s)) by
        simpa only [Nat.add_assoc] using finiteChainRegion_subset_expanded a 3 p s)
      ((intervalCoordinates b a 3).symm (MPOTensor.twoSiteSuppliedInputWindow e A)) =
      localObservable b (finiteChainRegion a 3)
        ((intervalCoordinates b a 3).symm (MPOTensor.twoSiteSuppliedOutputWindow e u v A)) := by
  let hW := (S.isMPU W u v).reindexPhysical e
  let hΛ : finiteChainRegion a 3 ⊆ finiteChainRegion (a - p) (p + (3 + s)) := by
    simpa only [Nat.add_assoc] using finiteChainRegion_subset_expanded a 3 p s
  have hconj : finiteChainConjugation hW hN (a - p)
      (localInclusion hΛ ((intervalCoordinates b a 3).symm
        (MPOTensor.twoSiteSuppliedInputWindow e A))) =
      localInclusion hΛ ((intervalCoordinates b a 3).symm
        (MPOTensor.twoSiteSuppliedOutputWindow e u v A)) := by
    apply (intervalCoordinates b (a - p) (p + (3 + s))).injective
    simp only [finiteChainConjugation_apply, map_mul, map_star,
      intervalCoordinates_finiteChainMPOMatrix,
      intervalCoordinates_localInclusion_eq_bufferedWindowMatrix,
      StarAlgEquiv.apply_symm_apply, Matrix.star_eq_conjTranspose]
    exact MPOTensor.mpo_reindexPhysical_suppliedBufferedWindow_conjugation e S p s A
  change localObservable b _ (finiteChainConjugation hW hN (a - p)
    (localInclusion hΛ _)) = _
  rw [hconj, localObservable_localInclusion]

private theorem suppliedWindow_centralInclusion {d b : ℕ}
    (e : Fin b ≃ Fin (d * d))
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (intervalCoordinates b (-1) 3).symm (MPOTensor.twoSiteSuppliedInputWindow e A) =
      localInclusion (show finiteChainRegion 0 1 ⊆ finiteChainRegion (-1) 3 by
        intro x hx
        simp only [finiteChainRegion, Finset.mem_Ico] at hx ⊢
        omega)
        ((intervalCoordinates b 0 1).symm
          (Matrix.reindex (MPOTensor.twoSiteSuppliedCellEquiv e)
            (MPOTensor.twoSiteSuppliedCellEquiv e) A)) := by
  apply (intervalCoordinates b (-1) 3).injective
  rw [StarAlgEquiv.apply_symm_apply,
    MPOTensor.twoSiteSuppliedInputWindow_eq_bufferedCell]
  have h := intervalCoordinates_localInclusion_eq_bufferedWindowMatrix b 1 1 1 0
    ((intervalCoordinates b 0 1).symm
      (Matrix.reindex (MPOTensor.twoSiteSuppliedCellEquiv e)
        (MPOTensor.twoSiteSuppliedCellEquiv e) A))
  simpa only [StarAlgEquiv.apply_symm_apply] using h.symm

/-- The named actual bare-MPU automorphism, for a directly supplied
tensor in any equivalent physical alphabet, sends its singleton input
to the actual standard-form four-half-site output on cells -1,0,1.
No compatible family, extra blocking scale, or inverse action is a premise.
Source: CPSV17 StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem mpuQuasiLocalEquiv_supplied_singleton
    {d b D ℓ r : ℕ} [NeZero b] {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (e : Fin b ≃ Fin (d * d)) (S : MPOTensor.TwoSiteStandardFormData W u v)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    mpuQuasiLocalEquiv ((S.isMPU W u v).reindexPhysical e)
        (quasiLocalIntervalObservable b 0 1
          (Matrix.reindex (MPOTensor.twoSiteSuppliedCellEquiv e)
            (MPOTensor.twoSiteSuppliedCellEquiv e) A)) =
      quasiLocalIntervalObservable b (-1) 3
        (MPOTensor.twoSiteSuppliedOutputWindow e u v A) := by
  classical
  let hW := (S.isMPU W u v).reindexPhysical e
  let R : ℕ := 4 * D ^ 4
  let p := R + 1
  let s := R + 1
  let N := p + (3 + s)
  let a : ℤ := -1 - p
  have hN : 1 < N := by dsimp [N, p, s]; omega
  have hWindow : finiteChainRegion (-1) 3 ⊆ finiteChainRegion a N := by
    simpa only [a, N, Nat.add_assoc] using finiteChainRegion_subset_expanded (-1) 3 p s
  have hSingle : finiteChainRegion 0 1 ⊆ finiteChainRegion (-1) 3 := by
    intro x hx
    simp only [finiteChainRegion, Finset.mem_Ico] at hx ⊢
    omega
  have hΛ := hSingle.trans hWindow
  have hR : (R : ℤ) = 4 * (D : ℤ) ^ 4 := by
    simp only [R, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  have hbuffer : regionSumset (finiteChainRegion 0 1)
      (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) ⊆ finiteChainRegion a N := by
    simp only [← hR]
    intro z hz
    obtain ⟨j, hj, n, hn, rfl⟩ := (mem_regionSumset z _ _).mp hz
    simp only [finiteChainRegion, Finset.mem_Ico] at hj ⊢
    simp only [Finset.mem_Icc] at hn
    dsimp only [a, N, p, s]
    push_cast
    omega
  have hFinite := finiteChainLocalObservable_suppliedWindow e S p s hN (-1) A
  rw [suppliedWindow_centralInclusion, finiteChainLocalObservable_localInclusion] at hFinite
  calc
    mpuQuasiLocalEquiv hW
        (quasiLocalIntervalObservable b 0 1
          (Matrix.reindex (MPOTensor.twoSiteSuppliedCellEquiv e)
            (MPOTensor.twoSiteSuppliedCellEquiv e) A)) =
        algebraicToQuasiLocal b
          (finiteChainLocalObservable hW hN a hΛ
            ((intervalCoordinates b 0 1).symm
              (Matrix.reindex (MPOTensor.twoSiteSuppliedCellEquiv e)
                (MPOTensor.twoSiteSuppliedCellEquiv e) A))) :=
      mpuQuasiLocalEquiv_finiteChainConjugation hW _ a N hN hΛ hbuffer _
    _ = quasiLocalIntervalObservable b (-1) 3
        (MPOTensor.twoSiteSuppliedOutputWindow e u v A) :=
      congrArg (algebraicToQuasiLocal b) hFinite

end SpinChain
