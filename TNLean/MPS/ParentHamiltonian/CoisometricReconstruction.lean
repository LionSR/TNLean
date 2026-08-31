/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTRefinement
import TNLean.MPS.CanonicalForm.CPSVBlocking
import TNLean.MPS.ParentHamiltonian.BlockSumGroundSpace

/-!
# Local ground spaces under coisometric reconstruction

A positive-length local MPS space is unchanged when a tensor is reconstructed
inside a larger bond space through a rectangular coisometry.  The two boundary
maps are \(X \mapsto UXU^*\) and \(Y \mapsto U^*YU\).

## Main result

* `MPSTensor.groundSpace_eq_of_coisometry_reconstruction`: exact equality of
  positive-length local ground spaces.

## Reference context

Equation `II_CF1` of Cirac--Perez-Garcia--Schuch--Verstraete,
arXiv:1606.00608, lines 237--244, states the literal direct-sum canonical form
\(A^i=\bigoplus_k\mu_kA_k^i\). It does not state the general rectangular
coisometry-invariance theorem below. That theorem is a derived trace-cyclicity
result for any exact coisometric reconstruction.
-/

open scoped Matrix

namespace MPSTensor

variable {s d n : ℕ}

/-- A positive-length local MPS space is invariant under an exact rectangular
coisometric reconstruction.

If \(A_i=U^*C_iU\) and \(UU^*=1\), cyclicity of trace identifies the boundary
parametrizations through \(X \mapsto UXU^*\) and \(Y \mapsto U^*YU\).

This is a derived transport lemma, not a theorem stated in
arXiv:1606.00608. Its hypotheses abstract the exact reconstruction used by
the canonical-form data. -/
theorem groundSpace_eq_of_coisometry_reconstruction
    {A : MPSTensor s d} {C : MPSTensor s n}
    (U : Matrix (Fin n) (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ i, A i = Uᴴ * C i * U)
    {L : ℕ} (hL : 0 < L) :
    groundSpace A L = groundSpace C L := by
  have hMap (X : Matrix (Fin d) (Fin d) ℂ) :
      groundSpaceMap A L X = groundSpaceMap C L (U * X * Uᴴ) := by
    ext σ
    rw [groundSpaceMap_apply, groundSpaceMap_apply]
    have hword : List.ofFn σ ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      simp [hL.ne'] at this
    rw [evalWord_eq_coisometry_reconstruction_of_ne_nil
      U hU hReconstruct (List.ofFn σ) hword]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm Uᴴ (Kraus.evalWord C (List.ofFn σ) * U * X)
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    exact ⟨U * X * Uᴴ, (hMap X).symm⟩
  · rintro _ ⟨Y, rfl⟩
    refine ⟨Uᴴ * Y * U, ?_⟩
    rw [hMap]
    congr 1
    simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]

private theorem groundSpace_smul_eq (A : MPSTensor s d) (ζ : ℂ) (hζ : ζ ≠ 0)
    (L : ℕ) :
    groundSpace (ζ • A) L = groundSpace A L := by
  have hMap (X : Matrix (Fin d) (Fin d) ℂ) :
      groundSpaceMap (ζ • A) L X = groundSpaceMap A L ((ζ ^ L) • X) := by
    ext σ
    rw [groundSpaceMap_apply, groundSpaceMap_apply]
    change Matrix.trace
        (Kraus.evalWord (fun i ↦ ζ • A i) (List.ofFn σ) * X) = _
    rw [Kraus.evalWord_smul]
    simp [Matrix.trace_smul]
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    exact ⟨(ζ ^ L) • X, (hMap X).symm⟩
  · rintro _ ⟨Y, rfl⟩
    refine ⟨(ζ ^ L)⁻¹ • Y, ?_⟩
    rw [hMap]
    congr 1
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero L hζ), one_smul]

private theorem groundSpace_blockTensor_cast_dim
    {D₁ D₂ : ℕ} (h : D₁ = D₂) (A : MPSTensor s D₁) (p L : ℕ) :
    groundSpace
        (MPSTensor.blockTensor (cast (congr_arg (MPSTensor s) h) A) p) L =
      groundSpace (MPSTensor.blockTensor A p) L := by
  subst D₂
  rfl

/-- The positive-length local space of a blocked literal CPSV canonical form is
the sum of the local spaces of its blocked distinct BNT representatives.
Repeated gauge-phase copies and the rectangular ambient coisometry do not
change this sum.

This is derived from the literal direct-sum canonical form at
arXiv:1606.00608, equation `II_CF1`, lines 237--244, and the phase-gauge BNT
regrouping in equations `eq:II_ABasicTensors` and `decBSV`, lines 265--301. -/
theorem CPSVCanonicalFormData.groundSpace_blockTensor_eq_iSup_representatives
    {A : MPSTensor s d} (data : CPSVCanonicalFormData A)
    (ref : data.BNTRefinement) {p L : ℕ} (hp : 0 < p) (hL : 0 < L) :
    groundSpace (MPSTensor.blockTensor A p) L =
      ⨆ j : Fin data.phaseClasses.g,
        groundSpace (MPSTensor.blockTensor (data.blocks (data.representativeIndex j)) p) L := by
  classical
  have hCopy (k : Fin data.r) :
      groundSpace (MPSTensor.blockTensor (data.blocks k) p) L =
        groundSpace
          (MPSTensor.blockTensor
            (data.blocks (data.representativeIndex (data.classCopy k).1)) p) L := by
    have hGauge : GaugeEquiv (ref.regroupedBlocks k) (data.blocks k) :=
      ⟨ref.listedGauge k, ref.blocksEqListedGaugeConj k⟩
    have hPhaseNe : ref.copyPhase k ≠ 0 := by
      intro hk
      simpa [hk] using ref.copyPhaseNorm k
    have hBlockedEq :
        MPSTensor.blockTensor (ref.regroupedBlocks k) p =
          (ref.copyPhase k ^ p) •
            MPSTensor.blockTensor
              (cast (congr_arg (MPSTensor s) (ref.copyDimEq k))
                (data.blocks (data.representativeIndex (data.classCopy k).1))) p := by
      funext i
      simp [Kraus.blockTensor, ref.regroupedBlocksEq, Kraus.evalWord_smul,
        Kraus.length_wordOfBlock]
    calc
      groundSpace (MPSTensor.blockTensor (data.blocks k) p) L =
          groundSpace (MPSTensor.blockTensor (ref.regroupedBlocks k) p) L :=
        (hGauge.blockTensor p).groundSpace_eq L |>.symm
      _ = groundSpace
          ((ref.copyPhase k ^ p) •
            MPSTensor.blockTensor
              (cast (congr_arg (MPSTensor s) (ref.copyDimEq k))
                (data.blocks (data.representativeIndex (data.classCopy k).1))) p) L := by
        rw [hBlockedEq]
      _ = groundSpace
          (MPSTensor.blockTensor
            (cast (congr_arg (MPSTensor s) (ref.copyDimEq k))
              (data.blocks (data.representativeIndex (data.classCopy k).1))) p) L :=
        groundSpace_smul_eq _ _ (pow_ne_zero p hPhaseNe) L
      _ = groundSpace
          (MPSTensor.blockTensor
            (data.blocks (data.representativeIndex (data.classCopy k).1)) p) L :=
        groundSpace_blockTensor_cast_dim (ref.copyDimEq k) _ p L
  have hCopies :
      (⨆ k : Fin data.r, groundSpace (MPSTensor.blockTensor (data.blocks k) p) L) =
        ⨆ j : Fin data.phaseClasses.g,
          groundSpace (MPSTensor.blockTensor (data.blocks (data.representativeIndex j)) p) L := by
    apply le_antisymm
    · refine iSup_le fun k ↦ ?_
      rw [hCopy k]
      exact le_iSup (fun j : Fin data.phaseClasses.g ↦
        groundSpace (MPSTensor.blockTensor (data.blocks (data.representativeIndex j)) p) L)
        (data.classCopy k).1
    · refine iSup_le fun j ↦ ?_
      let q : Fin (data.phaseClasses.copies j) :=
        ⟨0, data.phaseClasses.copies_pos j⟩
      let k : Fin data.r := data.classCopyEquiv ⟨j, q⟩
      have hkClass : (data.classCopy k).1 = j := by
        simpa [k] using congrArg Sigma.fst (data.classCopy_classCopyEquiv j q)
      have hkRep : k = data.representativeIndex j := by
        rfl
      rw [← hkRep, hCopy k, hkClass]
      exact le_iSup (fun k : Fin data.r ↦
        groundSpace (MPSTensor.blockTensor (data.blocks k) p) L) k
  let blocked := data.blockTensor p hp
  calc
    groundSpace (MPSTensor.blockTensor A p) L =
        groundSpace
          (toTensorFromBlocks (d := blockPhysDim s p) blocked.weights blocked.blocks) L :=
      groundSpace_eq_of_coisometry_reconstruction blocked.ambient_coisometry
        blocked.coisometric blocked.reconstruct hL
    _ = ⨆ k : Fin data.r, groundSpace (MPSTensor.blockTensor (data.blocks k) p) L := by
      simpa [blocked, CPSVCanonicalFormData.blockTensor] using
        groundSpace_toTensorFromBlocks_eq_iSup
          blocked.weights blocked.blocks blocked.weights_ne_zero L
    _ = _ := hCopies

end MPSTensor
