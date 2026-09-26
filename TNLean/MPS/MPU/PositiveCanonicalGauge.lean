/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.SingleBlock
import TNLean.MPS.MPU.CanonicalForm
import TNLean.MPS.MPDO.BondSimilarity
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.CanonicalForm.Existence

/-!
# Positive gauges and canonical representatives of normal MPUs

A positive definite left fixed point determines a trace-preserving bond gauge.
Unitary diagonalization of a right fixed point then gives canonical form II
without changing the bond dimension or the periodic operators.

Source: arXiv:1703.09188, canonical form II, lines 269–281, and the
canonical-gauge step in Proposition IV.5, lines 798–802.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The positive square-root bond gauge preserves every periodic operator.
Source: CPSV17, Proposition IV.5, lines 798–802. -/
private theorem positive_gauge_mpo_eq {d D : ℕ}
    (U : MPOTensor d D) (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (N : ℕ) :
    MPOTensor.mpo (fun i j ↦ CFC.sqrt L * U i j * (CFC.sqrt L)⁻¹) N =
      MPOTensor.mpo U N := by
  exact (MPOTensor.mpo_eq_of_conj
    (Matrix.mul_nonsing_inv _ hL.isUnit_det_cfc_sqrt)
    (Matrix.nonsing_inv_mul _ hL.isUnit_det_cfc_sqrt) (fun _ _ ↦ rfl) N).symm

private theorem normalizedFlattening_positive_gauge {d D : ℕ}
    (U : MPOTensor d D) (L : Matrix (Fin D) (Fin D) ℂ) :
    MPOTensor.normalizedFlattening
        (fun i j ↦ CFC.sqrt L * U i j * (CFC.sqrt L)⁻¹ : MPOTensor d D) =
      Kraus.tpGauge U.normalizedFlattening L := by
  funext ij
  simp only [MPOTensor.normalizedFlattening, MPOTensor.toMPSTensor, Kraus.tpGauge,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Normalized flattening commutes with unitary bond conjugation. -/
private theorem normalizedFlattening_unitary_conj {d D : ℕ}
    (U : MPOTensor d D) (V : Matrix.unitaryGroup (Fin D) ℂ) :
    MPOTensor.normalizedFlattening
        (fun i j ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j *
          (V : Matrix (Fin D) (Fin D) ℂ) : MPOTensor d D) =
      fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * U.normalizedFlattening ij *
        (V : Matrix (Fin D) (Fin D) ℂ) := by
  exact funext fun ij ↦ by
    simp only [MPOTensor.normalizedFlattening, MPOTensor.toMPSTensor,
      Matrix.mul_smul, Matrix.smul_mul]

/-- Unitary bond conjugation preserves every periodic operator. -/
private theorem unitary_conj_mpo_eq {d D : ℕ}
    (U : MPOTensor d D) (V : Matrix.unitaryGroup (Fin D) ℂ) (N : ℕ) :
    MPOTensor.mpo
        (fun i j ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j *
          (V : Matrix (Fin D) (Fin D) ℂ)) N = MPOTensor.mpo U N := by
  exact (MPOTensor.mpo_eq_of_conj
    (by simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self V)
    (by simpa only [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem V.prop)
    (fun _ _ ↦ rfl) N).symm

/-- A normal left-canonical MPU with a normalized diagonal positive fixed point
has full-support canonical-form-II data in its given coordinates.
Source: CPSV17, canonical form II, lines 269–281. -/
private noncomputable def canonicalFormII_of_normal_leftCanonical
    (U : MPOTensor d D) (hU : U.IsMPU)
    (hNormal : MPSTensor.IsNormalTensor U.normalizedFlattening)
    (hLeft : MPSTensor.IsLeftCanonical U.normalizedFlattening)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag)
    (hρtrace : Matrix.trace ρ = 1)
    (hρfix : Kraus.transferMap U.normalizedFlattening ρ = ρ) :
    MPOTensor.IsMPUCanonicalFormII U := by
  let : NeZero D := ⟨hNormal.bondDim_ne_zero⟩
  refine {
    isMPU := hU
    cfii := MPSTensor.CPSVCanonicalFormIIData.ofNormalLeftCanonical
      hNormal hLeft ρ hρpd hρdiag hρfix
    fullSupport_eq := ?_
    ρ := ρ
    ρ_posDef := hρpd
    ρ_isDiag := hρdiag
    ρ_trace := hρtrace
    ρ_fixed := hρfix }
  change (∑ _ : Fin 1, D) = D
  simp

/-- Spectral normality is preserved by unitary bond conjugation. -/
private theorem unitary_conj_normal {r D : ℕ} (A : MPSTensor r D)
    (hA : MPSTensor.IsNormalTensor A) (V : Matrix.unitaryGroup (Fin D) ℂ) :
    MPSTensor.IsNormalTensor
      (fun i ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i *
        (V : Matrix (Fin D) (Fin D) ℂ)) := by
  apply hA.of_gaugeEquiv
  exact (show MPSTensor.GaugeEquiv A
    (fun i ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i *
      (V : Matrix (Fin D) (Fin D) ℂ)) from
    ⟨(MPSTensor.unitaryGL V)⁻¹, fun i ↦ by simp [MPSTensor.unitaryGL]⟩).symm

/-- Unitary diagonalization after the positive square-root gauge.

Source: arXiv:1703.09188, canonical form II, lines 269–281, and the
canonical-gauge step of Proposition IV.5, lines 798–802. -/
private theorem positive_gauge_exists_diagonal_fixedPoint
    (U : MPOTensor d D) (hNormal : MPSTensor.IsNormalTensor U.normalizedFlattening)
    (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (hfix : Kraus.mapLM (fun i ↦ (U.normalizedFlattening i)ᴴ) L = L) :
    let A := Kraus.tpGauge U.normalizedFlattening L
    ∃ (V : Matrix.unitaryGroup (Fin D) ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      let B : MPSTensor (d * d) D := fun i ↦
        (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (V : Matrix (Fin D) (Fin D) ℂ)
      MPSTensor.SameMPV₂ A B ∧ ρ.PosDef ∧ ρ.IsDiag ∧ Matrix.trace ρ = 1 ∧
        MPSTensor.IsLeftCanonical B ∧ Kraus.transferMap B ρ = ρ := by
  have hNormalTP : MPSTensor.IsNormalTensor (Kraus.tpGauge U.normalizedFlattening L) :=
    hNormal.of_gaugeEquiv (MPSTensor.gaugeEquiv_tpGauge U.normalizedFlattening L hL).symm
  obtain ⟨V, Λ, hSame, hΛ, hdiag, hTP, hΛfix⟩ :=
    MPSTensor.exists_CFII_data_of_TP_of_isIrreducibleTensor _
      (Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint _ L hL hfix)
      hNormalTP.no_invariant_proj (Nat.pos_of_ne_zero hNormal.bondDim_ne_zero)
  let : NeZero D := ⟨hNormal.bondDim_ne_zero⟩
  have htrace : 0 < Matrix.trace Λ := hΛ.trace_pos
  refine ⟨V, (Matrix.trace Λ)⁻¹ • Λ, hSame,
    hΛ.smul (RCLike.inv_pos_of_pos htrace), hdiag.smul _, ?_, hTP, ?_⟩
  · simp only [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt htrace)]
  · simp only [map_smul, hΛfix]

/-- The positive square-root gauge followed by unitary diagonalization gives
a full-support MPU canonical-form-II representative.
This construction assumes normality and a positive definite adjoint fixed point.
It is the canonical-gauge step of arXiv:1703.09188, Proposition IV.5,
lines 798–802, with canonical form II as in lines 269–281. -/
theorem exists_canonicalFormII_positiveGauge
    (U : MPOTensor d D) (hU : U.IsMPU)
    (hNormal : MPSTensor.IsNormalTensor U.normalizedFlattening)
    (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (hfix : Kraus.mapLM (fun i ↦ (U.normalizedFlattening i)ᴴ) L = L) :
    ∃ V : Matrix.unitaryGroup (Fin D) ℂ,
      let B : MPOTensor d D := fun i j ↦
        (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          (CFC.sqrt L * U i j * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ)
      Nonempty (MPOTensor.IsMPUCanonicalFormII B) ∧
        ∀ N, MPOTensor.mpo B N = MPOTensor.mpo U N := by
  obtain ⟨V, ρ, hSame, hρ, hdiag, hρtr, hLeft, hfix⟩ :=
    positive_gauge_exists_diagonal_fixedPoint U hNormal L hL hfix
  have hnorm : MPOTensor.normalizedFlattening
      (fun i j ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (CFC.sqrt L * U i j * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ) :
          MPOTensor d D) =
      fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        Kraus.tpGauge U.normalizedFlattening L ij * (V : Matrix (Fin D) (Fin D) ℂ) :=
    (normalizedFlattening_unitary_conj _ V).trans
      (congrArg (fun A : MPSTensor (d * d) D ↦ fun ij ↦
        (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A ij * (V : Matrix (Fin D) (Fin D) ℂ))
        (normalizedFlattening_positive_gauge U L))
  have hEq (N : ℕ) : MPOTensor.mpo
      (fun i j ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (CFC.sqrt L * U i j * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ)) N =
      MPOTensor.mpo U N :=
    (unitary_conj_mpo_eq _ V N).trans (positive_gauge_mpo_eq U L hL N)
  exact ⟨V, ⟨canonicalFormII_of_normal_leftCanonical _
    (fun N hN ↦ (hEq N).symm ▸ hU N hN)
    (hnorm.symm ▸ unitary_conj_normal _
      (hNormal.of_gaugeEquiv (MPSTensor.gaugeEquiv_tpGauge U.normalizedFlattening L hL).symm)
      V)
    (hnorm.symm ▸ hLeft) ρ hρ hdiag hρtr (hnorm.symm ▸ hfix)⟩, hEq⟩

end MPOTensor
