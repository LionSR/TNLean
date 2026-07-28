/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KoashiImoto.RecoveredConditionalDilation.Basic

/-!
# Recovered conditional sector action

This file derives the dependent block and output-slice data for the HJPW
recovery operation.  It bridges the generic fixed-environment dilation
machinery to the supported sectors supplied by the recovered conditional
block form.

Source: Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 6, equation (15), lines 547--560;
Appendix A, Theorem 10, Property 2, lines 791--800; the equivalence
2 iff 2', lines 808--823; and the operation-level proof of 2',
lines 853--882.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace Matrix

open RecoveredConditionalDilationInternal

variable {dA dB dC : ℕ}

/-- Source-specific square slices and local rectangular Kraus blocks for the
HJPW recovery operation. -/
theorem RecoveredConditionalDilationInternal.exists_recoveredSliceSectorBlocks
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian)
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm) :
    ∃ (r : ℕ)
      (R : Fin r → Matrix (Fin dB × Fin dC) (Fin dB) ℂ)
      (S : Fin (dC * r) → Matrix (Fin dB) (Fin dB) ℂ)
      (C : Fin (dC * r) → ∀ j : Fin F.jointSupport.K,
        Matrix (Fin (F.jointSupport.m j)) (Fin (F.jointSupport.m j)) ℂ)
      (L : Fin r → ∀ j : Fin F.jointSupport.K,
        Matrix (Fin (F.jointSupport.m j) × Fin dC)
          (Fin (F.jointSupport.m j)) ℂ),
      (∀ X, partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
          (traceLeftA_posSemidef hρ_dm.1) X =
        rectangularKrausMap R X) ∧
      (∑ i, (R i)ᴴ * R i = (1 : Matrix (Fin dB) (Fin dB) ℂ)) ∧
      (∀ k, S k = rightOutputSlice
        (R (finProdFinEquiv.symm k).2) (finProdFinEquiv.symm k).1) ∧
      (∀ X, Kraus.map S X = recoveredMiddleChannel ρ_ABC hρ_dm.1 X) ∧
      (∀ k, S k * F.jointSupport.V =
        F.jointSupport.V *
          (Kraus.supportCompressedKraus F.jointSupport.V S) k) ∧
      (∀ k,
        Matrix.reindex F.jointSupport.e.symm F.jointSupport.e.symm
            (star F.jointSupport.U *
              (Kraus.supportCompressedKraus F.jointSupport.V S) k *
                F.jointSupport.U) =
          Matrix.blockDiagonal' fun j ↦
            C k j ⊗ₖ
              (1 : Matrix (Fin (F.jointSupport.d j))
                (Fin (F.jointSupport.d j)) ℂ)) ∧
      (∀ k, S k * (F.jointSupport.V * F.jointSupport.U) =
        (F.jointSupport.V * F.jointSupport.U) *
          Matrix.reindex F.jointSupport.e F.jointSupport.e
            (Matrix.blockDiagonal' fun j ↦
              C k j ⊗ₖ
                (1 : Matrix (Fin (F.jointSupport.d j))
                  (Fin (F.jointSupport.d j)) ℂ))) ∧
      (∀ j, Kraus.IsTP (fun k ↦ C k j)) ∧
      (∀ i j u c u', L i j (u, c) u' =
        C (finProdFinEquiv (c, i)) j u u') ∧
      (∀ j, ∑ i, (L i j)ᴴ * L i j =
        (1 : Matrix (Fin (F.jointSupport.m j))
          (Fin (F.jointSupport.m j)) ℂ)) ∧
      ∀ j,
        partialTraceRight
            (rectangularKrausMap (fun i ↦ L i j) (F.jointSupport.σ j)) =
          F.jointSupport.σ j := by
  classical
  obtain ⟨r, R, hRmap, hRtp⟩ :=
    partialTraceRightPetzChannel_traceA_ABC_isKrausCPTP ρ_ABC hρ_dm
  let S : Fin (dC * r) → Matrix (Fin dB) (Fin dB) ℂ :=
    fun k ↦ rightOutputSlice
      (R (finProdFinEquiv.symm k).2) (finProdFinEquiv.symm k).1
  have hSmap :
      ∀ X, Kraus.map S X = recoveredMiddleChannel ρ_ABC hρ_dm.1 X := by
    intro X
    rw [recoveredMiddleChannel, LinearMap.comp_apply]
    calc
      rectangularKrausMap S X =
          rectangularKrausMap
            (fun p : Fin dC × Fin r ↦ rightOutputSlice (R p.2) p.1) X :=
        DFunLike.congr_fun
          (rectangularKrausMap_equiv finProdFinEquiv
            (fun p : Fin dC × Fin r ↦ rightOutputSlice (R p.2) p.1)) X
      _ = partialTraceRight (rectangularKrausMap R X) :=
        (partialTraceRight_rectangularKrausMap_eq_slices R X).symm
      _ = partialTraceRight
          (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
            (traceLeftA_posSemidef hρ_dm.1) X) :=
        congrArg partialTraceRight (hRmap X).symm
  have hStp : Kraus.IsTP S := by
    apply kraus_sum_conjTranspose_mul_of_tp S
      (recoveredMiddleChannel ρ_ABC hρ_dm.1)
    · exact fun X ↦ (hSmap X).symm
    · exact
        (recoveredMiddleChannel_isKrausCPTP ρ_ABC hρ_dm).trace_map
  let G : Kraus.PreservingKrausFamily
      (recoveredConditionalState (traceC_ABC ρ_ABC)) :=
    { numKraus := dC * r
      Kfam := S
      isPreserving := ⟨hStp, fun x ↦ by
        rw [hSmap]
        exact recoveredMiddleChannel_recoveredConditionalState
          ρ_ABC hρ_dm hSSA x⟩ }
  have hSsupport : ∀ k, S k * F.jointSupport.V =
      F.jointSupport.V *
        (Kraus.supportCompressedKraus F.jointSupport.V S) k := by
    let μ := recoveredConditionalState (traceC_ABC ρ_ABC)
    let hμbar := Kraus.commonAverage_posSemidef μ
      (recoveredConditionalState_posSemidef
        (SSAPosDef.traceC_ABC_posSemidef hρ_dm.1))
    have hInv : ∀ k,
        (1 - hμbar.supportProj) * S k * hμbar.supportProj = 0 := by
      simpa only [Kraus.stationaryProj] using
        (Kraus.lowerZero_of_posSemidef_fixedPoint S
          (Kraus.commonAverage μ) hμbar G.map_commonAverage).2
    have hQV : hμbar.supportProj * F.jointSupport.V =
        F.jointSupport.V := by
      rw [← F.jointSupport.V_range]
      simp [Matrix.mul_assoc, F.jointSupport.V_isometry]
    intro k
    have hQKV : hμbar.supportProj * S k * F.jointSupport.V =
        S k * F.jointSupport.V := by
      have h := hInv k
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
      calc
        hμbar.supportProj * S k * F.jointSupport.V =
            hμbar.supportProj * S k *
              (hμbar.supportProj * F.jointSupport.V) := by rw [hQV]
        _ = (hμbar.supportProj * S k * hμbar.supportProj) *
              F.jointSupport.V := by simp only [Matrix.mul_assoc]
        _ = (S k * hμbar.supportProj) * F.jointSupport.V := by rw [← h]
        _ = S k * F.jointSupport.V := by rw [Matrix.mul_assoc, hQV]
    rw [← hQKV, ← F.jointSupport.V_range]
    simp only [Kraus.supportCompressedKraus, Matrix.mul_assoc]
  obtain ⟨hGsupport, _⟩ :=
    F.jointSupport.preserving_support_action G
  let Gsupport : Kraus.PreservingKrausFamily
      (Kraus.supportCompressedFamily F.jointSupport.V
        (recoveredConditionalState (traceC_ABC ρ_ABC))) :=
    { numKraus := dC * r
      Kfam := Kraus.supportCompressedKraus F.jointSupport.V S
      isPreserving := hGsupport }
  obtain ⟨C, hCblock, hCtp, hCfix, _⟩ :=
    F.jointSupport.preserving_block_action Gsupport
  have hSblock : ∀ k, S k * (F.jointSupport.V * F.jointSupport.U) =
      (F.jointSupport.V * F.jointSupport.U) *
        Matrix.reindex F.jointSupport.e F.jointSupport.e
          (Matrix.blockDiagonal' fun j ↦
            C k j ⊗ₖ
              (1 : Matrix (Fin (F.jointSupport.d j))
                (Fin (F.jointSupport.d j)) ℂ)) := by
    intro k
    let Bk := Matrix.reindex F.jointSupport.e F.jointSupport.e
      (Matrix.blockDiagonal' fun j ↦
        C k j ⊗ₖ
          (1 : Matrix (Fin (F.jointSupport.d j))
            (Fin (F.jointSupport.d j)) ℂ))
    have hcoord :
        star F.jointSupport.U *
            (Kraus.supportCompressedKraus F.jointSupport.V S) k *
              F.jointSupport.U = Bk := by
      have h := congrArg
        (Matrix.reindex F.jointSupport.e F.jointSupport.e) (hCblock k)
      simpa [Bk] using h
    have hUright : F.jointSupport.U * star F.jointSupport.U = 1 :=
      Matrix.mem_unitaryGroup_iff.mp F.jointSupport.U_unitary
    calc
      S k * (F.jointSupport.V * F.jointSupport.U) =
          (S k * F.jointSupport.V) * F.jointSupport.U := by
            simp only [Matrix.mul_assoc]
      _ = (F.jointSupport.V *
            (Kraus.supportCompressedKraus F.jointSupport.V S) k) *
            F.jointSupport.U := by rw [hSsupport k]
      _ = F.jointSupport.V *
          (F.jointSupport.U * Bk) := by
            rw [← hcoord]
            simp only [Matrix.mul_assoc]
            apply congrArg (fun X ↦ F.jointSupport.V * X)
            calc
              (Kraus.supportCompressedKraus F.jointSupport.V S) k *
                    F.jointSupport.U =
                  (F.jointSupport.U * star F.jointSupport.U) *
                    ((Kraus.supportCompressedKraus
                      F.jointSupport.V S) k * F.jointSupport.U) := by
                        rw [hUright, Matrix.one_mul]
              _ = F.jointSupport.U *
                  (star F.jointSupport.U *
                    ((Kraus.supportCompressedKraus
                      F.jointSupport.V S) k * F.jointSupport.U)) := by
                        simp only [Matrix.mul_assoc]
      _ = (F.jointSupport.V * F.jointSupport.U) * Bk := by
        simp only [Matrix.mul_assoc]
  let L : Fin r → ∀ j : Fin F.jointSupport.K,
      Matrix (Fin (F.jointSupport.m j) × Fin dC)
        (Fin (F.jointSupport.m j)) ℂ :=
    fun i j uc u' ↦ C (finProdFinEquiv (uc.2, i)) j uc.1 u'
  have hLtp : ∀ j, ∑ i, (L i j)ᴴ * L i j =
      (1 : Matrix (Fin (F.jointSupport.m j))
        (Fin (F.jointSupport.m j)) ℂ) := by
    intro j
    have hCtpj := hCtp j
    unfold Kraus.IsTP at hCtpj
    ext u u'
    have hentry := congrFun (congrFun hCtpj u) u'
    simp only [Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply] at hentry ⊢
    rw [← hentry]
    rw [← finProdFinEquiv.sum_comp]
    simp only [Fintype.sum_prod_type, L]
    calc
      (∑ i : Fin r, ∑ v : Fin (F.jointSupport.m j), ∑ c : Fin dC,
          star (C (finProdFinEquiv (c, i)) j v u) *
            C (finProdFinEquiv (c, i)) j v u') =
          ∑ i : Fin r, ∑ c : Fin dC, ∑ v : Fin (F.jointSupport.m j),
            star (C (finProdFinEquiv (c, i)) j v u) *
              C (finProdFinEquiv (c, i)) j v u' := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ c : Fin dC, ∑ i : Fin r, ∑ v : Fin (F.jointSupport.m j),
            star (C (finProdFinEquiv (c, i)) j v u) *
              C (finProdFinEquiv (c, i)) j v u' :=
        Finset.sum_comm
  have hLfix : ∀ j,
      partialTraceRight
          (rectangularKrausMap (fun i ↦ L i j) (F.jointSupport.σ j)) =
        F.jointSupport.σ j := by
    intro j
    let A : Fin dC × Fin r →
        Matrix (Fin (F.jointSupport.m j))
          (Fin (F.jointSupport.m j)) ℂ :=
      fun p ↦ C (finProdFinEquiv p) j
    have hrel :
        (fun k ↦ A (finProdFinEquiv.symm k)) = (fun k ↦ C k j) := by
      funext k
      simp only [A, Equiv.apply_symm_apply]
    have hslices :
        (fun p : Fin dC × Fin r ↦ rightOutputSlice (L p.2 j) p.1) = A := by
      funext p
      ext u u'
      rfl
    calc
      partialTraceRight
          (rectangularKrausMap (fun i ↦ L i j) (F.jointSupport.σ j)) =
          rectangularKrausMap
              (fun p : Fin dC × Fin r ↦
                rightOutputSlice (L p.2 j) p.1)
              (F.jointSupport.σ j) :=
        partialTraceRight_rectangularKrausMap_eq_slices
          (fun i ↦ L i j) (F.jointSupport.σ j)
      _ = rectangularKrausMap A (F.jointSupport.σ j) := by
        rw [hslices]
      _ = rectangularKrausMap
          (fun k ↦ A (finProdFinEquiv.symm k))
          (F.jointSupport.σ j) := by
        exact DFunLike.congr_fun
          (rectangularKrausMap_equiv finProdFinEquiv A).symm
          (F.jointSupport.σ j)
      _ = Kraus.map (fun k ↦ C k j) (F.jointSupport.σ j) := by
        rw [hrel]
        rfl
      _ = F.jointSupport.σ j := hCfix j
  refine ⟨r, R, S, C, L, hRmap, hRtp, ?_, hSmap, hSsupport,
    ?_, hSblock, hCtp, ?_, hLtp, hLfix⟩
  · intro k
    rfl
  · intro k
    exact hCblock k
  · intro i j u c u'
    rfl

end Matrix
