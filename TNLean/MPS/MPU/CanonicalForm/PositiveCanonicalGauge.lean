/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.CanonicalForm.SimpleMPU.FullSupport
import TNLean.MPS.MPU.CanonicalForm.VirtualSandwich
import TNLean.MPS.Operator.Periodic.BondSimilarity
import TNLean.MPS.Tensor.Gauge.TPGauge
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.CanonicalForm.NormalBlocks.IrreducibleDecomposition
import TNLean.MPS.MPU.CanonicalForm.MPUCanonicalForm

/-!
# Positive gauges and canonical representatives of normal MPUs

A positive definite left fixed point determines a trace-preserving bond gauge.
Unitary diagonalization of a right fixed point then gives canonical form II
without changing the bond dimension or the periodic operators.

Source: arXiv:1703.09188, canonical form II, lines 269–281, and the
canonical-gauge step in Proposition IV.5, lines 798–804.

## Canonical form up to similarity

An MPU tensor in canonical form is similar, by one invertible bond matrix, to an MPU tensor in
canonical form II. The source passes to canonical form II "without loss of generality" by a gauge
transformation (arXiv:1703.09188, `Papers/1703.09188/paper_v2.tex`, lines 294 and 356); this file
states that gauge as a lemma (the chapter's Lemma "Canonical form up to similarity").

The normalized tensor `d^{-1/2} U` is normal (Proposition `prop:normal-tensor`). A positive
definite fixed point `σ` of the dual transfer map gives the left-canonical gauge
`σ^{1/2} A σ^{-1/2}`, and a unitary `V` diagonalizing the fixed point of the gauged transfer map
then gives canonical form II with one block filling the bond space. The similarity is
`X = V^† σ^{1/2}`.

### Main results

* `MPOTensor.IsMPU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm` — an MPU tensor in
  canonical form is `X⁻¹ U' X` for an invertible `X` and an MPU tensor `U'` in canonical
  form II.
-/

section

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The positive square-root bond gauge preserves every periodic operator.
Source: CPSV17, Proposition IV.5, lines 798–804. -/
private theorem positive_gauge_mpo_eq {d D : ℕ}
    (U : MPOTensor d D) (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (N : ℕ) :
    MPOTensor.mpo (fun ij ↦ CFC.sqrt L * U ij * (CFC.sqrt L)⁻¹) N =
      MPOTensor.mpo U N := by
  exact (MPOTensor.mpo_eq_of_conj
    (Matrix.mul_nonsing_inv _ hL.isUnit_det_cfc_sqrt)
    (Matrix.nonsing_inv_mul _ hL.isUnit_det_cfc_sqrt) (fun _ _ ↦ rfl) N).symm

/-- Normalized flattening commutes with conjugation of every letter by fixed
bond matrices. -/
private theorem normalizedFlattening_conj {d D : ℕ}
    (U : MPOTensor d D) (X Y : Matrix (Fin D) (Fin D) ℂ) :
    MPOTensor.normalizedFlattening (fun ij ↦ X * U ij * Y : MPOTensor d D) =
      fun ij ↦ X * U.normalizedFlattening ij * Y := by
  funext ij
  simp only [MPOTensor.normalizedFlattening, MPOTensor.toMPSTensor,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Unitary bond conjugation preserves every periodic operator. -/
private theorem unitary_conj_mpo_eq {d D : ℕ}
    (U : MPOTensor d D) (V : Matrix.unitaryGroup (Fin D) ℂ) (N : ℕ) :
    MPOTensor.mpo
        (fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * U ij *
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
canonical-gauge step of Proposition IV.5, lines 798–804. -/
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
    MPSTensor.exists_CFII_data_of_TP_of_isIrreducibleFamily _
      (Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint _ L hL hfix)
      hNormalTP.no_invariant_proj (Nat.pos_of_ne_zero hNormal.bondDim_ne_zero)
  let : NeZero D := ⟨hNormal.bondDim_ne_zero⟩
  have htrace : 0 < Matrix.trace Λ := hΛ.trace_pos
  refine ⟨V, (Matrix.trace Λ)⁻¹ • Λ, hSame,
    hΛ.smul (RCLike.inv_pos_of_pos htrace), hdiag.smul _, ?_, hTP, ?_⟩
  · simp only [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt htrace)]
  · simp only [map_smul, hΛfix]

/-- The positive square-root gauge and unitary diagonalization preserve
both source ranks. Source: CPSV17, Proposition IV.5, lines 797–804. -/
private theorem source_ranks_canonical_gauge {d D : ℕ}
    (W : MPOTensor d D) (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (V : Matrix.unitaryGroup (Fin D) ℂ) :
    let B : MPOTensor d D := fun ij ↦
      (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (CFC.sqrt L * W ij * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ)
    MPOTensor.rightRank B = MPOTensor.rightRank W ∧
      MPOTensor.leftRank B = MPOTensor.leftRank W := by
  have hS : IsUnit (CFC.sqrt L) := (Matrix.isUnit_iff_isUnit_det _).2 hL.isUnit_det_cfc_sqrt
  have hSi : IsUnit ((CFC.sqrt L)⁻¹) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hL.isUnit_det_inv_sqrt
  have hV : IsUnit (V : Matrix (Fin D) (Fin D) ℂ) := Unitary.isUnit_coe
  have hVs : IsUnit ((V : Matrix (Fin D) (Fin D) ℂ)ᴴ) := hV.star
  exact ⟨(MPOTensor.rightRank_virtualSandwich _
    (MPOTensor.virtualSandwich (CFC.sqrt L) W (CFC.sqrt L)⁻¹) _ hVs hV).trans
      (MPOTensor.rightRank_virtualSandwich _ W _ hS hSi),
    (MPOTensor.leftRank_virtualSandwich _
      (MPOTensor.virtualSandwich (CFC.sqrt L) W (CFC.sqrt L)⁻¹) _ hVs hV).trans
      (MPOTensor.leftRank_virtualSandwich _ W _ hS hSi)⟩

/-- The positive square-root gauge followed by unitary diagonalization gives
a full-support MPU canonical-form-II representative with the same periodic
operators and both source ranks unchanged.
This construction assumes normality and a positive definite adjoint fixed point.
It is the canonical-gauge step of arXiv:1703.09188, Proposition IV.5,
lines 798–804, with canonical form II as in lines 269–281. -/
theorem exists_canonicalFormII_positiveGauge
    (U : MPOTensor d D) (hU : U.IsMPU)
    (hNormal : MPSTensor.IsNormalTensor U.normalizedFlattening)
    (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (hfix : Kraus.mapLM (fun i ↦ (U.normalizedFlattening i)ᴴ) L = L) :
    ∃ V : Matrix.unitaryGroup (Fin D) ℂ,
      let B : MPOTensor d D := fun ij ↦
        (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          (CFC.sqrt L * U ij * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ)
      Nonempty (MPOTensor.IsMPUCanonicalFormII B) ∧
        (∀ N, MPOTensor.mpo B N = MPOTensor.mpo U N) ∧
        MPOTensor.rightRank B = MPOTensor.rightRank U ∧
        MPOTensor.leftRank B = MPOTensor.leftRank U := by
  obtain ⟨V, ρ, hSame, hρ, hdiag, hρtr, hLeft, hfix⟩ :=
    positive_gauge_exists_diagonal_fixedPoint U hNormal L hL hfix
  have hnorm : MPOTensor.normalizedFlattening
      (fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (CFC.sqrt L * U ij * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ) :
          MPOTensor d D) =
      fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        Kraus.tpGauge U.normalizedFlattening L ij * (V : Matrix (Fin D) (Fin D) ℂ) :=
    (normalizedFlattening_conj _ _ _).trans
      (congrArg (fun A : MPSTensor (d * d) D ↦ fun ij ↦
        (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A ij * (V : Matrix (Fin D) (Fin D) ℂ))
        (normalizedFlattening_conj U (CFC.sqrt L) (CFC.sqrt L)⁻¹))
  have hEq (N : ℕ) : MPOTensor.mpo
      (fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (CFC.sqrt L * U ij * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ)) N =
      MPOTensor.mpo U N :=
    (unitary_conj_mpo_eq _ V N).trans (positive_gauge_mpo_eq U L hL N)
  exact ⟨V, ⟨canonicalFormII_of_normal_leftCanonical _
    (fun N hN ↦ (hEq N).symm ▸ hU N hN)
    (hnorm.symm ▸ unitary_conj_normal _
      (hNormal.of_gaugeEquiv (MPSTensor.gaugeEquiv_tpGauge U.normalizedFlattening L hL).symm)
      V)
    (hnorm.symm ▸ hLeft) ρ hρ hdiag hρtr (hnorm.symm ▸ hfix)⟩,
    hEq, source_ranks_canonical_gauge U L hL V⟩

end MPOTensor

end

section

open scoped Matrix ComplexOrder MatrixOrder

namespace MPOTensor

variable {d D : ℕ}

/-- **Canonical form up to similarity.** An MPU tensor `U` in canonical form is similar to an MPU
tensor in canonical form II: there is an invertible bond matrix `X` such that `X U X⁻¹` is in
canonical form II. The similar tensor generates the same periodic operators as `U`.

Source: arXiv:1703.09188, `Papers/1703.09188/paper_v2.tex`, lines 294 and 356 (the gauge to
canonical form II taken without loss of generality); the chapter's Lemma "Canonical form up to
similarity". The proof follows the left-canonical gauge `σ^{1/2} A σ^{-1/2}` of the normal tensor
`A = d^{-1/2} U` by a unitary diagonalization of its fixed point. -/
theorem IsMPU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor) :
    ∃ X : GL (Fin D) ℂ, Nonempty (IsMPUCanonicalFormII (virtualSandwich
      (X : Matrix (Fin D) (Fin D) ℂ) U ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) := by
  have hNormal := hU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm hcf
  obtain ⟨σ, hσ, hσfix, -⟩ := hNormal.exists_tpGauge
  obtain ⟨V, hV, -⟩ := exists_canonicalFormII_positiveGauge U hU hNormal σ hσ hσfix
  let S : GL (Fin D) ℂ := Matrix.nonsingInvUnit (CFC.sqrt σ) hσ.isUnit_det_cfc_sqrt
  have hX : (((MPSTensor.unitaryGL V)⁻¹ * S : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * CFC.sqrt σ := rfl
  have hXinv : ((((MPSTensor.unitaryGL V)⁻¹ * S)⁻¹ : GL (Fin D) ℂ) :
      Matrix (Fin D) (Fin D) ℂ) = (CFC.sqrt σ)⁻¹ * (V : Matrix (Fin D) (Fin D) ℂ) := rfl
  refine ⟨(MPSTensor.unitaryGL V)⁻¹ * S, ?_⟩
  rw [hX, hXinv]
  convert hV using 3
  funext ij
  simp only [virtualSandwich, Matrix.mul_assoc]

end MPOTensor

end
