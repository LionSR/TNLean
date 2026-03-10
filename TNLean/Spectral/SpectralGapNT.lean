/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGapRect
import TNLean.Channel.PerronFrobeniusExistence
import TNLean.MPS.IrreducibleFormII
import TNLean.MPS.BlockingPeriodicityCFII2

/-!
# Spectral gap for normal tensor (irreducible + TP) blocks

This file proves the overlap dichotomy for irreducible trace-preserving / left-canonical
blocks without assuming injectivity, following the Cauchy--Schwarz argument from
Cirac et al., arXiv:1606.00608, Appendix A, Lemma A.1.

The key new rigidity statement is
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`: if two irreducible
left-canonical tensors have mixed-transfer spectral radius at least `1`, then they are
already gauge-phase equivalent.

The same-dimension rigidity step is now fully formalized. The downstream strict-gap and
overlap-decay consequences for equal bond dimension are routed through the existing
spectral-radius infrastructure, and the rectangular different-dimension analogue is
formalized below as well.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal ENNReal Matrix.Norms.Elementwise

namespace MPSTensor

variable {d D D₁ D₂ : ℕ}

private lemma sum_sandwich (L R : Matrix (Fin D) (Fin D) ℂ)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ i : Fin d, L * M i * R = L * (∑ i : Fin d, M i) * R := by
  rw [Finset.mul_sum, Finset.sum_mul]

section SameDimension

set_option maxHeartbeats 1600000 in
-- This proof is large: it chains gauge transformations, fixed-point uniqueness,
-- and a Schur decomposition argument simultaneously for two tensor trains.
private theorem eigenvector_gives_gauge_of_irreducible_TP [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    GaugePhaseEquiv A B := by
  classical
  have hA_irrMap : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor A hA_irr
  have hB_irrMap : IsIrreducibleMap (transferMap (d := d) (D := D) B) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor B hB_irr
  obtain ⟨ρA, hρA_psd, hρA_ne, hρA_fix⟩ :=
    exists_posSemidef_fixedPoint A hA_left (NeZero.pos D)
  obtain ⟨ρB, hρB_psd, hρB_ne, hρB_fix⟩ :=
    exists_posSemidef_fixedPoint B hB_left (NeZero.pos D)
  have hρA_pd : ρA.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible A hA_irrMap ρA hρA_psd hρA_ne hρA_fix
  have hρB_pd : ρB.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible B hB_irrMap ρB hρB_psd hρB_ne hρB_fix
  rcases CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hρA_pd.isStrictlyPositive with
    ⟨S0A, hS0A_unit, hρA_eq⟩
  let SA : Matrix (Fin D) (Fin D) ℂ := S0Aᴴ
  have hSA_unit : IsUnit SA := by
    simpa [SA, Matrix.star_eq_conjTranspose] using (IsUnit.star hS0A_unit)
  have hSA_det : SA.det ≠ 0 := by
    have hdet_unit : IsUnit SA.det := (Matrix.isUnit_iff_isUnit_det (A := SA)).1 hSA_unit
    exact hdet_unit.ne_zero
  have hSA_isUnitdet : IsUnit SA.det := Ne.isUnit hSA_det
  have hSA_mul : SA * SAᴴ = ρA := by
    calc
      SA * SAᴴ = S0Aᴴ * (S0Aᴴ)ᴴ := by rfl
      _ = S0Aᴴ * S0A := by simp
      _ = ρA := by simpa [Matrix.star_eq_conjTranspose] using hρA_eq.symm
  rcases CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hρB_pd.isStrictlyPositive with
    ⟨S0B, hS0B_unit, hρB_eq⟩
  let SB : Matrix (Fin D) (Fin D) ℂ := S0Bᴴ
  have hSB_unit : IsUnit SB := by
    simpa [SB, Matrix.star_eq_conjTranspose] using (IsUnit.star hS0B_unit)
  have hSB_det : SB.det ≠ 0 := by
    have hdet_unit : IsUnit SB.det := (Matrix.isUnit_iff_isUnit_det (A := SB)).1 hSB_unit
    exact hdet_unit.ne_zero
  have hSB_isUnitdet : IsUnit SB.det := Ne.isUnit hSB_det
  have hSB_mul : SB * SBᴴ = ρB := by
    calc
      SB * SBᴴ = S0Bᴴ * (S0Bᴴ)ᴴ := by rfl
      _ = S0Bᴴ * S0B := by simp
      _ = ρB := by simpa [Matrix.star_eq_conjTranspose] using hρB_eq.symm
  have hSBh_det : (SBᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSB_det
  have hSBh_isUnitdet : IsUnit (SBᴴ).det := Ne.isUnit hSBh_det
  have hSA_inv_mul : SA⁻¹ * SA = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.nonsing_inv_mul SA hSA_isUnitdet
  have hSA_mul_inv : SA * SA⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.mul_nonsing_inv SA hSA_isUnitdet
  have hSB_inv_mul : SB⁻¹ * SB = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.nonsing_inv_mul SB hSB_isUnitdet
  have hSB_mul_inv : SB * SB⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.mul_nonsing_inv SB hSB_isUnitdet
  have hSBh_inv_mul : (SBᴴ)⁻¹ * SBᴴ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.nonsing_inv_mul SBᴴ hSBh_isUnitdet
  have hSBh_mul_inv : SBᴴ * (SBᴴ)⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.mul_nonsing_inv SBᴴ hSBh_isUnitdet
  have hSAh_det : (SAᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSA_det
  have hSAh_isUnitdet : IsUnit (SAᴴ).det := Ne.isUnit hSAh_det
  have hSAh_inv_mul : (SAᴴ)⁻¹ * SAᴴ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.nonsing_inv_mul SAᴴ hSAh_isUnitdet
  have hSAh_mul_inv : SAᴴ * (SAᴴ)⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.mul_nonsing_inv SAᴴ hSAh_isUnitdet
  let A' : MPSTensor d D := fun i => SA⁻¹ * A i * SA
  let B' : MPSTensor d D := fun i => SB⁻¹ * B i * SB
  have hA'unital : ∑ i : Fin d, (A' i) * (A' i)ᴴ = 1 := by
    simpa [A'] using
      (gauged_unital (A := A) (S := SA) (ρ := ρA)
        (hS_inv := hSA_det) (hSS := hSA_mul) (hfix := hρA_fix))
  have hB'unital : ∑ i : Fin d, (B' i) * (B' i)ᴴ = 1 := by
    simpa [B'] using
      (gauged_unital (A := B) (S := SB) (ρ := ρB)
        (hS_inv := hSB_det) (hSS := hSB_mul) (hfix := hρB_fix))
  let X' : Matrix (Fin D) (Fin D) ℂ := SA⁻¹ * X * (SBᴴ)⁻¹
  have hX'ne : X' ≠ 0 := by
    intro h0
    have hXeq : X = SA * X' * SBᴴ := by
      have hXinv_mul : (SBᴴ)⁻¹ * SBᴴ = (1 : Matrix (Fin D) (Fin D) ℂ) := hSBh_inv_mul
      have hXmul_inv : SA * SA⁻¹ = (1 : Matrix (Fin D) (Fin D) ℂ) := hSA_mul_inv
      have : SA * X' * SBᴴ = X := by
        calc
          SA * X' * SBᴴ = SA * (SA⁻¹ * X * (SBᴴ)⁻¹) * SBᴴ := by rfl
          _ = (SA * SA⁻¹) * X * ((SBᴴ)⁻¹ * SBᴴ) := by
            have hleft : SA * (SA⁻¹ * X * (SBᴴ)⁻¹) = (SA * SA⁻¹) * X * (SBᴴ)⁻¹ := by
              calc
                SA * (SA⁻¹ * X * (SBᴴ)⁻¹) = (SA * SA⁻¹) * (X * (SBᴴ)⁻¹) := by
                  simp [mul_assoc]
                _ = ((SA * SA⁻¹) * X) * (SBᴴ)⁻¹ := by
                  simp [mul_assoc]
                _ = (SA * SA⁻¹) * X * (SBᴴ)⁻¹ := by
                  simp [mul_assoc]
            calc
              SA * (SA⁻¹ * X * (SBᴴ)⁻¹) * SBᴴ
                  = ((SA * SA⁻¹) * X * (SBᴴ)⁻¹) * SBᴴ := by
                      simp [mul_assoc]
              _ = (SA * SA⁻¹) * X * ((SBᴴ)⁻¹ * SBᴴ) := by
                  simp [mul_assoc]
          _ = (1 : Matrix (Fin D) (Fin D) ℂ) * X * (1 : Matrix (Fin D) (Fin D) ℂ) := by
            simp [hXmul_inv, hXinv_mul]
          _ = X := by simp
      simpa using this.symm
    have : X = 0 := by simpa [h0] using hXeq
    exact hX this
  have hFXsum : ∑ i : Fin d, A i * X * (B i)ᴴ = μ • X := by
    simpa [mixedTransferMap_apply] using hFX
  have hFX' : mixedTransferMap A' B' X' = μ • X' := by
    have hterm :
        ∀ i : Fin d,
          (A' i) * X' * (B' i)ᴴ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
      intro i
      have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
        simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, mul_assoc]
      calc
        (A' i) * X' * (B' i)ᴴ
            = (SA⁻¹ * A i * SA) * (SA⁻¹ * X * (SBᴴ)⁻¹) * (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) := by
                simp [A', X', hBstar, mul_assoc]
        _ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
                have hSA_cancel' (Z : Matrix (Fin D) (Fin D) ℂ) : SA * (SA⁻¹ * Z) = Z := by
                  calc
                    SA * (SA⁻¹ * Z) = (SA * SA⁻¹) * Z := by
                      simp [mul_assoc]
                    _ = (1 : Matrix (Fin D) (Fin D) ℂ) * Z := by simp [hSA_mul_inv]
                    _ = Z := by simp
                have hSBh_cancel' (Z : Matrix (Fin D) (Fin D) ℂ) : (SBᴴ)⁻¹ * (SBᴴ * Z) = Z := by
                  calc
                    (SBᴴ)⁻¹ * (SBᴴ * Z) = ((SBᴴ)⁻¹ * SBᴴ) * Z := by
                      simp [mul_assoc]
                    _ = (1 : Matrix (Fin D) (Fin D) ℂ) * Z := by simp [hSBh_inv_mul]
                    _ = Z := by simp
                have hSBstep :
                    X * ((SBᴴ)⁻¹ * (SBᴴ * ((B i)ᴴ * (SBᴴ)⁻¹))) =
                      X * ((B i)ᴴ * (SBᴴ)⁻¹) := by
                  simpa [mul_assoc] using
                    congrArg (fun T => X * T) (hSBh_cancel' (((B i)ᴴ) * (SBᴴ)⁻¹))
                have hSAstep :
                    A i * (SA * (SA⁻¹ * (X * ((B i)ᴴ * (SBᴴ)⁻¹)))) =
                      A i * (X * ((B i)ᴴ * (SBᴴ)⁻¹)) := by
                  simpa [mul_assoc] using
                    congrArg (fun T => A i * T) (hSA_cancel' (X * ((B i)ᴴ * (SBᴴ)⁻¹)))
                simpa [mul_assoc, hSBstep] using congrArg (fun T => SA⁻¹ * T) hSAstep
    calc
      mixedTransferMap A' B' X' = ∑ i : Fin d, (A' i) * X' * (B' i)ᴴ := by
        simp [mixedTransferMap_apply]
      _ = ∑ i : Fin d, SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
        simp [hterm]
      _ = SA⁻¹ * (∑ i : Fin d, A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
        simpa using
          (sum_sandwich (L := SA⁻¹) (R := (SBᴴ)⁻¹)
            (M := fun i : Fin d => A i * X * (B i)ᴴ))
      _ = SA⁻¹ * (μ • X) * (SBᴴ)⁻¹ := by rw [hFXsum]
      _ = μ • (SA⁻¹ * X * (SBᴴ)⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = μ • X' := rfl
  let K : Fin d → Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
    fun i => Matrix.fromBlocks (A' i) 0 0 (B' i)
  let M : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
    Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) X' 0 0
  have hK_unital : Kraus.IsUnital K := by
    unfold Kraus.IsUnital
    have hsum :
        (∑ i : Fin d, K i * (K i)ᴴ) =
          Matrix.fromBlocks (∑ i : Fin d, (A' i) * (A' i)ᴴ)
            (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
            (∑ i : Fin d, (B' i) * (B' i)ᴴ) := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b)
      · simp [Matrix.sum_apply, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      · simp [Matrix.sum_apply, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      · simp [Matrix.sum_apply, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
      · simp [Matrix.sum_apply, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    calc
      (∑ i : Fin d, K i * (K i)ᴴ)
          = Matrix.fromBlocks (∑ i : Fin d, (A' i) * (A' i)ᴴ)
              (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
              (∑ i : Fin d, (B' i) * (B' i)ᴴ) := hsum
      _ = Matrix.fromBlocks (1 : Matrix (Fin D) (Fin D) ℂ) 0 0 (1 : Matrix (Fin D) (Fin D) ℂ) := by
        simp [hA'unital, hB'unital]
      _ = (1 : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ) := by
        simp
  have hEigM : Kraus.map K M = μ • M := by
    have hmap :
        Kraus.map K M =
          Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ)
            (mixedTransferMap A' B' X') 0 0 := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b)
      · simp [Kraus.map, K, M, Matrix.sum_apply, mixedTransferMap_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, mul_assoc]
      · simp [Kraus.map, K, M, Matrix.sum_apply, mixedTransferMap_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, mul_assoc]
      · simp [Kraus.map, K, M, Matrix.sum_apply, mixedTransferMap_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, mul_assoc]
      · simp [Kraus.map, K, M, Matrix.sum_apply, mixedTransferMap_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, mul_assoc]
    simp [hmap, M, hFX', Matrix.fromBlocks_smul]
  let rhoT : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
    Matrix.fromBlocks (SAᴴ * SA) 0 0 (SBᴴ * SB)
  have hrhoT_pd : rhoT.PosDef := by
    let Sblock : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
      Matrix.fromBlocks SA 0 0 SB
    let SblockInv : Matrix (Fin D ⊕ Fin D) (Fin D ⊕ Fin D) ℂ :=
      Matrix.fromBlocks SA⁻¹ 0 0 SB⁻¹
    have hSblock_unit : IsUnit Sblock := by
      refine (isUnit_iff_exists_inv).2 ?_
      refine ⟨SblockInv, ?_⟩
      simp [Sblock, SblockInv, Matrix.fromBlocks_multiply, hSA_mul_inv, hSB_mul_inv]
    have hrhoT_strict : IsStrictlyPositive rhoT := by
      refine (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).2 ?_
      refine ⟨Sblock, hSblock_unit, ?_⟩
      simp [rhoT, Sblock, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
    exact (Matrix.IsStrictlyPositive.posDef hrhoT_strict)
  have hrhoT_fix : Kraus.adjointMap K rhoT = rhoT := by
    have hAblock : ∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * SA := by
      have htermA : ∀ i : Fin d,
          (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * ((A i)ᴴ * A i) * SA := by
        intro i
        have hSAh_cancel' (Z : Matrix (Fin D) (Fin D) ℂ) : (SAᴴ)⁻¹ * (SAᴴ * Z) = Z := by
          calc
            (SAᴴ)⁻¹ * (SAᴴ * Z) = ((SAᴴ)⁻¹ * SAᴴ) * Z := by
              simp [mul_assoc]
            _ = (1 : Matrix (Fin D) (Fin D) ℂ) * Z := by simp [hSAh_inv_mul]
            _ = Z := by simp
        have hSA_cancel' (Z : Matrix (Fin D) (Fin D) ℂ) : SA * (SA⁻¹ * Z) = Z := by
          calc
            SA * (SA⁻¹ * Z) = (SA * SA⁻¹) * Z := by
              simp [mul_assoc]
            _ = (1 : Matrix (Fin D) (Fin D) ℂ) * Z := by simp [hSA_mul_inv]
            _ = Z := by simp
        have hAstar : (A' i)ᴴ = SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹ := by
          simp [A', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, mul_assoc]
        calc
          (A' i)ᴴ * (SAᴴ * SA) * (A' i)
              = (SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹) * (SAᴴ * SA) * (SA⁻¹ * A i * SA) := by
                  simp [A', Matrix.conjTranspose_nonsing_inv, mul_assoc]
          _ = SAᴴ * ((A i)ᴴ * A i) * SA := by
                  have hmid : (SAᴴ)⁻¹ * (SAᴴ * SA) = SA := hSAh_cancel' SA
                  have hright : SA * (SA⁻¹ * (A i * SA)) = A i * SA := by
                    simp [hSA_cancel']
                  simp [mul_assoc, hmid, hright]
      calc
        ∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i)
            = ∑ i : Fin d, SAᴴ * ((A i)ᴴ * A i) * SA := by
                simp [htermA]
        _ = SAᴴ * (∑ i : Fin d, (A i)ᴴ * A i) * SA := by
                simp [sum_sandwich (L := SAᴴ) (R := SA)
                    (M := fun i : Fin d => (A i)ᴴ * A i)]
        _ = SAᴴ * 1 * SA := by rw [hA_left]
        _ = SAᴴ * SA := by simp
    have hBblock : ∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * SB := by
      have htermB : ∀ i : Fin d,
          (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * ((B i)ᴴ * B i) * SB := by
        intro i
        have hSBh_cancel' (Z : Matrix (Fin D) (Fin D) ℂ) : (SBᴴ)⁻¹ * (SBᴴ * Z) = Z := by
          calc
            (SBᴴ)⁻¹ * (SBᴴ * Z) = ((SBᴴ)⁻¹ * SBᴴ) * Z := by
              simp [mul_assoc]
            _ = (1 : Matrix (Fin D) (Fin D) ℂ) * Z := by simp [hSBh_inv_mul]
            _ = Z := by simp
        have hSB_cancel' (Z : Matrix (Fin D) (Fin D) ℂ) : SB * (SB⁻¹ * Z) = Z := by
          calc
            SB * (SB⁻¹ * Z) = (SB * SB⁻¹) * Z := by
              simp [mul_assoc]
            _ = (1 : Matrix (Fin D) (Fin D) ℂ) * Z := by simp [hSB_mul_inv]
            _ = Z := by simp
        have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
          simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, mul_assoc]
        calc
          (B' i)ᴴ * (SBᴴ * SB) * (B' i)
              = (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) * (SBᴴ * SB) * (SB⁻¹ * B i * SB) := by
                  simp [B', Matrix.conjTranspose_nonsing_inv, mul_assoc]
          _ = SBᴴ * ((B i)ᴴ * B i) * SB := by
                  have hmid : (SBᴴ)⁻¹ * (SBᴴ * SB) = SB := hSBh_cancel' SB
                  have hright : SB * (SB⁻¹ * (B i * SB)) = B i * SB := by
                    simp [hSB_cancel']
                  simp [mul_assoc, hmid, hright]
      calc
        ∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i)
            = ∑ i : Fin d, SBᴴ * ((B i)ᴴ * B i) * SB := by
                simp [htermB]
        _ = SBᴴ * (∑ i : Fin d, (B i)ᴴ * B i) * SB := by
                simp [sum_sandwich (L := SBᴴ) (R := SB)
                    (M := fun i : Fin d => (B i)ᴴ * B i)]
        _ = SBᴴ * 1 * SB := by rw [hB_left]
        _ = SBᴴ * SB := by simp
    have hAdj :
        Kraus.adjointMap K rhoT =
          Matrix.fromBlocks (∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i))
            (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
            (∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i)) := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b)
      · simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose, mul_assoc]
      · simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose, mul_assoc]
      · simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose, mul_assoc]
      · simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose, mul_assoc]
    simp [hAdj, rhoT, hAblock, hBblock]
  have hμ_conj : ‖(starRingEnd ℂ) μ‖ = 1 := by
    simpa [Complex.norm_conj] using hμ
  have hEigMstar : Kraus.map K Mᴴ = (starRingEnd ℂ μ) • Mᴴ := by
    have h1 : Kraus.map K Mᴴ = (Kraus.map K M)ᴴ := by
      simp [Kraus.map_conjTranspose (K := K) M]
    calc
      Kraus.map K Mᴴ = (Kraus.map K M)ᴴ := h1
      _ = (μ • M)ᴴ := by simp [hEigM]
      _ = (starRingEnd ℂ μ) • Mᴴ := by simp [Matrix.conjTranspose_smul]
  have hKS_Mstar :
      Kraus.map K (Mᴴᴴ * Mᴴ) = (Kraus.map K Mᴴ)ᴴ * Kraus.map K Mᴴ :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      (K := K) hK_unital (ρ := rhoT) hrhoT_pd hrhoT_fix Mᴴ (starRingEnd ℂ μ) hEigMstar hμ_conj
  have hComm_Mstar : ∀ i : Fin d, Mᴴ * (K i)ᴴ = (K i)ᴴ * Kraus.map K Mᴴ :=
    Kraus.kraus_commute_of_ks_equality (K := K) hK_unital Mᴴ hKS_Mstar
  have hInter2 : ∀ i : Fin d, A' i * X' = μ • X' * B' i := by
    intro i
    have h' : Mᴴ * (K i)ᴴ = (K i)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) := by
      simp [hEigMstar, hComm_Mstar i]
    have hL : Mᴴ * (K i)ᴴ =
        Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
          (X'ᴴ * (A' i)ᴴ) (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K i)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) =
        Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
          ((starRingEnd ℂ μ) • ((B' i)ᴴ * X'ᴴ)) (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_smul]
    have hfb :
        Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
            (X'ᴴ * (A' i)ᴴ) (0 : Matrix (Fin D) (Fin D) ℂ) =
          Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) (0 : Matrix (Fin D) (Fin D) ℂ)
            ((starRingEnd ℂ μ) • ((B' i)ᴴ * X'ᴴ)) (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa [hL, hR] using h'
    have h21 : X'ᴴ * (A' i)ᴴ = (starRingEnd ℂ μ) • ((B' i)ᴴ * X'ᴴ) :=
      (Matrix.fromBlocks_inj.1 hfb).2.2.1
    have h22 := congrArg Matrix.conjTranspose h21
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, starRingEnd_apply, star_star] at h22
    rw [← smul_mul_assoc] at h22
    exact h22
  let XXh : Matrix (Fin D) (Fin D) ℂ := X' * X'ᴴ
  have hXXh_ne : XXh ≠ 0 := by
    intro h0
    apply hX'ne
    exact Matrix.self_mul_conjTranspose_eq_zero.mp (by simpa [XXh] using h0)
  have hμ_star_mul : star μ * μ = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hμ]
  have hμ_mul_star : μ * star μ = 1 := by
    simpa [mul_comm] using hμ_star_mul
  have hμ_starRing_mul : ((starRingEnd ℂ) μ) * μ = 1 := by
    simpa [Complex.star_def] using hμ_star_mul
  have hsmul_self_mul_conjTranspose :
      ∀ N : Matrix (Fin D) (Fin D) ℂ, (μ • N) * (μ • N)ᴴ = N * Nᴴ := by
    intro N
    calc
      (μ • N) * (μ • N)ᴴ = (((starRingEnd ℂ) μ) * μ) • (N * Nᴴ) := by
        simp [Matrix.conjTranspose_smul, smul_smul, mul_comm]
      _ = N * Nᴴ := by simp [hμ_starRing_mul]
  have hXXh_fix' : transferMap A' XXh = XXh := by
    have hterm :
        ∀ i : Fin d,
          A' i * XXh * (A' i)ᴴ = X' * (B' i * (B' i)ᴴ) * X'ᴴ := by
      intro i
      have hAX : A' i * X' = μ • (X' * B' i) := by
        simpa [smul_mul_assoc] using hInter2 i
      calc
        A' i * XXh * (A' i)ᴴ = (A' i * X') * (A' i * X')ᴴ := by
          simp [XXh, Matrix.mul_assoc, Matrix.conjTranspose_mul]
        _ = (μ • (X' * B' i)) * (μ • (X' * B' i))ᴴ := by
          simp [hAX]
        _ = (X' * B' i) * (X' * B' i)ᴴ := hsmul_self_mul_conjTranspose (X' * B' i)
        _ = X' * (B' i * (B' i)ᴴ) * X'ᴴ := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    calc
      transferMap A' XXh = ∑ i : Fin d, A' i * XXh * (A' i)ᴴ := by
        simp [transferMap_apply]
      _ = ∑ i : Fin d, X' * (B' i * (B' i)ᴴ) * X'ᴴ := by
        simp [hterm]
      _ = X' * (∑ i : Fin d, B' i * (B' i)ᴴ) * X'ᴴ := by
        simpa using
          (sum_sandwich (L := X') (R := X'ᴴ)
            (M := fun i : Fin d => B' i * (B' i)ᴴ))
      _ = XXh := by
        simp [XXh, hB'unital]
  let Q : Matrix (Fin D) (Fin D) ℂ := SA * XXh * SAᴴ
  have hQ_psd : Q.PosSemidef := by
    simpa [Q, XXh, Matrix.mul_assoc, Matrix.conjTranspose_mul] using
      Matrix.posSemidef_self_mul_conjTranspose (SA * X')
  have hQ_fix : transferMap A Q = Q := by
    have hAiSA : ∀ i : Fin d, A i * SA = SA * A' i := by
      intro i
      simpa [A', Matrix.mul_assoc] using
        (Matrix.mul_nonsing_inv_cancel_left (A := SA) (B := A i * SA) hSA_isUnitdet).symm
    have hSAhAiH : ∀ i : Fin d, SAᴴ * (A i)ᴴ = (A' i)ᴴ * SAᴴ := by
      intro i
      simp [A', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
        Matrix.mul_assoc, hSAh_inv_mul]
    have hterm :
        ∀ i : Fin d,
          A i * Q * (A i)ᴴ = SA * (A' i * XXh * (A' i)ᴴ) * SAᴴ := by
      intro i
      calc
        A i * Q * (A i)ᴴ = (A i * SA) * XXh * (SAᴴ * (A i)ᴴ) := by
          simp [Q, Matrix.mul_assoc]
        _ = (SA * A' i) * XXh * ((A' i)ᴴ * SAᴴ) := by
          rw [hAiSA i, hSAhAiH i]
        _ = SA * (A' i * XXh * (A' i)ᴴ) * SAᴴ := by
          simp [Matrix.mul_assoc]
    calc
      transferMap A Q = ∑ i : Fin d, A i * Q * (A i)ᴴ := by
        simp [transferMap_apply]
      _ = ∑ i : Fin d, SA * (A' i * XXh * (A' i)ᴴ) * SAᴴ := by
        simp [hterm]
      _ = SA * (∑ i : Fin d, A' i * XXh * (A' i)ᴴ) * SAᴴ := by
        simpa using
          (sum_sandwich (L := SA) (R := SAᴴ)
            (M := fun i : Fin d => A' i * XXh * (A' i)ᴴ))
      _ = SA * transferMap A' XXh * SAᴴ := by
        simp [transferMap_apply]
      _ = SA * XXh * SAᴴ := by rw [hXXh_fix']
      _ = Q := rfl
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := A) hA_irrMap ρA Q hρA_psd hρA_ne
      hQ_psd hρA_fix hQ_fix with ⟨c, hQ_scalar⟩
  have hXXh_scalar : XXh = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have hQ_scalar' : SA * XXh * SAᴴ = c • (SA * SAᴴ) := by
      simpa [Q, hSA_mul] using hQ_scalar
    have hcancel := congrArg (fun T => SA⁻¹ * T * (SAᴴ)⁻¹) hQ_scalar'
    calc
      XXh = (SA⁻¹ * SA) * XXh := by simp [hSA_inv_mul]
      _ = SA⁻¹ * (SA * XXh) := by simp [Matrix.mul_assoc]
      _ = SA⁻¹ * (SA * XXh * SAᴴ) * (SAᴴ)⁻¹ := by
        simp [Matrix.mul_assoc, hSAh_mul_inv]
      _ = SA⁻¹ * (c • (SA * SAᴴ)) * (SAᴴ)⁻¹ := hcancel
      _ = c • (SA⁻¹ * (SA * SAᴴ) * (SAᴴ)⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
        simp [Matrix.mul_assoc, hSA_inv_mul, hSAh_mul_inv]
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    apply hXXh_ne
    simp [hXXh_scalar, hc0]
  have hXXh_scalar' : X' * X'ᴴ = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [XXh] using hXXh_scalar
  have hX'_right_inv : X' * (c⁻¹ • X'ᴴ) = 1 := by
    calc
      X' * (c⁻¹ • X'ᴴ) = c⁻¹ • (X' * X'ᴴ) := by
        simp
      _ = c⁻¹ • (c • (1 : Matrix (Fin D) (Fin D) ℂ)) := by
        rw [hXXh_scalar']
      _ = 1 := by
        simp [hc_ne0]
  have hX'isUnitdet : IsUnit X'.det := Matrix.isUnit_det_of_right_inverse hX'_right_inv
  have hμ_ne0 : μ ≠ 0 := by
    intro h0
    have : (‖μ‖ : ℝ) = 0 := by simp [h0]
    linarith [hμ, this]
  have hper : ∀ i : Fin d, B' i = μ⁻¹ • (X'⁻¹ * A' i * X') := by
    intro i
    have hAX : A' i * X' = μ • X' * B' i := hInter2 i
    have : X'⁻¹ * (A' i * X') = X'⁻¹ * (μ • X' * B' i) := by simp [hAX]
    have : X'⁻¹ * A' i * X' = μ • B' i := by
      rw [← Matrix.mul_assoc] at this
      rw [this, smul_mul_assoc, mul_smul_comm, Matrix.nonsing_inv_mul_cancel_left _ _ hX'isUnitdet]
    have hμinv : μ⁻¹ * μ = (1 : ℂ) := by simp [hμ_ne0]
    calc
      B' i = μ⁻¹ • (μ • B' i) := by
        simp [smul_smul, hμinv]
      _ = μ⁻¹ • (X'⁻¹ * A' i * X') := by
        simp [this]
  let Ymat : Matrix (Fin D) (Fin D) ℂ := SB * X'⁻¹ * SA⁻¹
  let Yinv : Matrix (Fin D) (Fin D) ℂ := SA * X' * SB⁻¹
  have hYmul : Ymat * Yinv = 1 := by
    have h1 : SA⁻¹ * (SA * X' * SB⁻¹) = X' * SB⁻¹ := by
      rw [Matrix.mul_assoc SA X' SB⁻¹, Matrix.nonsing_inv_mul_cancel_left _ _ hSA_isUnitdet]
    have h2 : X'⁻¹ * (X' * SB⁻¹) = SB⁻¹ := by
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hX'isUnitdet]
    have h3 : SB * SB⁻¹ = 1 := by
      exact Matrix.mul_nonsing_inv _ hSB_isUnitdet
    calc Ymat * Yinv = SB * X'⁻¹ * SA⁻¹ * (SA * X' * SB⁻¹) := rfl
      _ = SB * X'⁻¹ * (SA⁻¹ * (SA * X' * SB⁻¹)) := by rw [Matrix.mul_assoc]
      _ = SB * X'⁻¹ * (X' * SB⁻¹) := by rw [h1]
      _ = SB * (X'⁻¹ * (X' * SB⁻¹)) := by rw [Matrix.mul_assoc]
      _ = SB * SB⁻¹ := by rw [h2]
      _ = 1 := h3
  have hYinv_mul : Yinv * Ymat = 1 := by
    have h1 : SB⁻¹ * (SB * X'⁻¹ * SA⁻¹) = X'⁻¹ * SA⁻¹ := by
      rw [Matrix.mul_assoc SB X'⁻¹ SA⁻¹, Matrix.nonsing_inv_mul_cancel_left _ _ hSB_isUnitdet]
    have h2 : X' * (X'⁻¹ * SA⁻¹) = SA⁻¹ := by
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hX'isUnitdet]
    have h3 : SA * SA⁻¹ = 1 := by
      exact Matrix.mul_nonsing_inv _ hSA_isUnitdet
    calc Yinv * Ymat = SA * X' * SB⁻¹ * (SB * X'⁻¹ * SA⁻¹) := rfl
      _ = SA * X' * (SB⁻¹ * (SB * X'⁻¹ * SA⁻¹)) := by rw [Matrix.mul_assoc]
      _ = SA * X' * (X'⁻¹ * SA⁻¹) := by rw [h1]
      _ = SA * (X' * (X'⁻¹ * SA⁻¹)) := by rw [Matrix.mul_assoc]
      _ = SA * SA⁻¹ := by rw [h2]
      _ = 1 := h3
  let Ygl : GL (Fin D) ℂ := ⟨Ymat, Yinv, hYmul, hYinv_mul⟩
  refine ⟨Ygl, μ⁻¹, inv_ne_zero (norm_ne_zero_iff.mp (by rw [hμ]; norm_num)), ?_⟩
  intro i
  have : B i = μ⁻¹ • (Ymat * A i * Yinv) := by
    have hBi : B i = SB * (B' i) * SB⁻¹ := by
      have : SB * (SB⁻¹ * B i * SB) * SB⁻¹ = B i := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.mul_nonsing_inv _ hSB_isUnitdet, mul_one,
          Matrix.mul_nonsing_inv_cancel_left _ _ hSB_isUnitdet]
      exact this.symm
    rw [hBi, hper i]
    simp only [smul_mul_assoc, mul_smul_comm]
    congr 1
    simp only [A', Ymat, Yinv, Matrix.mul_assoc]
  simpa [Ygl] using this

theorem modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B := by
  rcases eq_or_ne D 0 with rfl | hD
  · exact ⟨1, 1, one_ne_zero, fun i => by ext a; exact a.elim0⟩
  haveI : NeZero D := ⟨hD⟩
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  haveI : Nontrivial V := by
    haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
    exact Matrix.nonempty
  haveI : Nontrivial (V →L[ℂ] V) := ContinuousLinearMap.instNontrivialId
  obtain ⟨μ, hμ_spec, hμ_norm⟩ := spectrum.exists_nnnorm_eq_spectralRadius F'
  have h_spec_eq := AlgEquiv.spectrum_eq Φ (mixedTransferMap A B)
  have hμ_spec_end : μ ∈ spectrum ℂ (mixedTransferMap A B) := h_spec_eq ▸ hμ_spec
  have hμ_ev : Module.End.HasEigenvalue (mixedTransferMap A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec_end
  obtain ⟨X, hX_mem, hX_ne⟩ := hμ_ev.exists_hasEigenvector
  have hFX : mixedTransferMap A B X = μ • X := Module.End.mem_eigenspace_iff.mp hX_mem
  have hμ_le : ‖μ‖ ≤ 1 := eigenvalue_norm_le_one A B hA_left hB_left μ hμ_ev
  have hμ_ge : (1 : ℝ≥0∞) ≤ ‖μ‖₊ := by
    rw [hμ_norm]
    exact hsr
  have hμ_eq : ‖μ‖ = 1 := le_antisymm hμ_le (by
    rw [ENNReal.one_le_coe_iff] at hμ_ge
    exact_mod_cast hμ_ge)
  exact eigenvector_gives_gauge_of_irreducible_TP
    A B X μ hA_irr hB_irr hA_left hB_left hFX hμ_eq hX_ne

/--
**Strict mixed-transfer spectral gap** for distinct irreducible left-canonical blocks of the
same bond dimension.
-/
theorem spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 := by
  refine lt_of_le_of_ne (spectralRadius_mixedTransfer_le_one A B hA_left hB_left) ?_
  intro hEq
  exact hAB <| modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    A B hA_irr hB_irr hA_left hB_left hEq.ge

/--
**Power decay** for the mixed transfer operator of distinct irreducible left-canonical
blocks of the same bond dimension.
-/
theorem mixedTransfer_pow_tendsto_zero_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  have h_clm : Filter.Tendsto (fun n => F' ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one F' <| by
      simpa [F', Φ, mixedTransferSpectralRadius] using
        spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
          A B hA_irr hB_irr hA_left hB_left hAB
  have h_eval := (ContinuousLinearMap.apply ℂ V X).continuous.tendsto (0 : V →L[ℂ] V)
  rw [map_zero] at h_eval
  suffices hpow : ∀ n, ((mixedTransferMap A B) ^ n) X = (F' ^ n) X by
    simp_rw [hpow]
    exact h_eval.comp h_clm
  intro n
  have h_pow : F' ^ n = Φ ((mixedTransferMap A B) ^ n) := (map_pow Φ _ n).symm
  simp only [h_pow]
  rfl

end SameDimension

section SameDimensionOverlap

variable [NeZero D]

/--
**Overlap decay** for distinct irreducible left-canonical blocks of the same bond dimension.
-/
theorem mpvOverlap_tendsto_zero_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  exact mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B) <| by
    simpa [mixedTransferSpectralRadius] using
      spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
        A B hA_irr hB_irr hA_left hB_left hAB

end SameDimensionOverlap

section DifferentDimensions

private lemma injective_vecMul_of_det_unit {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) (hM : IsUnit M.det) :
    Function.Injective M.vecMul := by
  exact (Matrix.vecMul_injective_iff_isUnit).2
    ((Matrix.isUnit_iff_isUnit_det (A := M)).2 hM)

private lemma mul_mul_conjTranspose_ne_zero_of_ne_zero {D : ℕ}
    (S : Matrix (Fin D) (Fin D) ℂ) (hS : IsUnit S.det)
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M ≠ 0) :
    S * M * Sᴴ ≠ 0 := by
  have hS_unit : IsUnit S := (Matrix.isUnit_iff_isUnit_det (A := S)).2 hS
  have hSstar_unit : IsUnit Sᴴ := by
    simpa [Matrix.star_eq_conjTranspose] using IsUnit.star hS_unit
  intro h0
  apply hM
  have h1 : M * Sᴴ = 0 := by
    apply IsUnit.mul_left_cancel hS_unit
    simpa [Matrix.mul_assoc] using h0
  have h2 : M = 0 := by
    apply IsUnit.mul_right_cancel hSstar_unit
    simpa using h1
  exact h2

private lemma injective_of_posDef_conjTranspose_mul_self
    (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (hpd : (Xᴴ * X).PosDef) :
    ∀ v : Fin D₂ → ℂ, X *ᵥ v = 0 → v = 0 := by
  intro v hv
  by_contra hv0
  have hpos : 0 < star v ⬝ᵥ ((Xᴴ * X) *ᵥ v) := hpd.dotProduct_mulVec_pos hv0
  have hzero : (Xᴴ * X) *ᵥ v = 0 := by
    have hXh : Xᴴ *ᵥ (X *ᵥ v) = 0 := by simp [hv]
    simpa [Matrix.mulVec_mulVec] using hXh
  simp [hzero] at hpos

private lemma dim_le_of_injective_matrix [NeZero D₂]
    (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (h_inj : ∀ v : Fin D₂ → ℂ, X *ᵥ v = 0 → v = 0) :
    D₂ ≤ D₁ := by
  let f : (Fin D₂ → ℂ) →ₗ[ℂ] (Fin D₁ → ℂ) := Matrix.toLin' X
  have hf_inj : Function.Injective f := by
    intro u v huv
    have h1 : f u - f v = 0 := sub_eq_zero.mpr huv
    have h2 : f (u - v) = 0 := by simp [h1]
    have h3 : X *ᵥ (u - v) = 0 := h2
    have h4 : u - v = 0 := h_inj _ h3
    exact eq_of_sub_eq_zero h4
  have h1 : Module.finrank ℂ (Fin D₂ → ℂ) ≤ Module.finrank ℂ (Fin D₁ → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hf_inj
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using h1

set_option maxHeartbeats 1600000 in
-- The rectangular gauge + block-Kraus + fixed-point-uniqueness chain is large.
private theorem dim_eq_of_modulus_one_eigenvector_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) (μ : ℂ)
    (hFX : mixedTransferMap₂ A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    D₁ = D₂ := by
  classical
  have hD₁pos : 0 < D₁ := Nat.pos_of_ne_zero (NeZero.ne D₁)
  have hD₂pos : 0 < D₂ := Nat.pos_of_ne_zero (NeZero.ne D₂)
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D₁) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor A hA_irr
  have hIrrB : IsIrreducibleMap (transferMap (d := d) (D := D₂) B) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor B hB_irr
  obtain ⟨ρA, hρA_psd, hρA_ne, hρA_fix⟩ :=
    exists_posSemidef_fixedPoint A hA_left hD₁pos
  obtain ⟨ρB, hρB_psd, hρB_ne, hρB_fix⟩ :=
    exists_posSemidef_fixedPoint B hB_left hD₂pos
  have hρA_pd : ρA.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible A hIrrA ρA hρA_psd hρA_ne hρA_fix
  have hρB_pd : ρB.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible B hIrrB ρB hρB_psd hρB_ne hρB_fix
  rcases CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hρA_pd.isStrictlyPositive with
    ⟨S0A, hS0A_unit, hρA_eq⟩
  rcases CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hρB_pd.isStrictlyPositive with
    ⟨S0B, hS0B_unit, hρB_eq⟩
  let SA : Matrix (Fin D₁) (Fin D₁) ℂ := S0Aᴴ
  let SB : Matrix (Fin D₂) (Fin D₂) ℂ := S0Bᴴ
  have hSA_det : SA.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A := SA)).1
      (by simpa [SA, Matrix.star_eq_conjTranspose] using IsUnit.star hS0A_unit)).ne_zero
  have hSB_det : SB.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A := SB)).1
      (by simpa [SB, Matrix.star_eq_conjTranspose] using IsUnit.star hS0B_unit)).ne_zero
  have hSA_u := Ne.isUnit hSA_det
  have hSB_u := Ne.isUnit hSB_det
  have hSA_unit : IsUnit SA := (Matrix.isUnit_iff_isUnit_det (A := SA)).2 hSA_u
  have hSB_unit : IsUnit SB := (Matrix.isUnit_iff_isUnit_det (A := SB)).2 hSB_u
  have hSAh_det : (SAᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSA_det
  have hSBh_det : (SBᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSB_det
  have hSAh_u := Ne.isUnit hSAh_det
  have hSBh_u := Ne.isUnit hSBh_det
  have hSA_inv_mul : SA⁻¹ * SA = (1 : Matrix (Fin D₁) (Fin D₁) ℂ) :=
    Matrix.nonsing_inv_mul SA hSA_u
  have hSA_mul_inv : SA * SA⁻¹ = (1 : Matrix (Fin D₁) (Fin D₁) ℂ) :=
    Matrix.mul_nonsing_inv SA hSA_u
  have hSB_inv_mul : SB⁻¹ * SB = (1 : Matrix (Fin D₂) (Fin D₂) ℂ) :=
    Matrix.nonsing_inv_mul SB hSB_u
  have hSB_mul_inv : SB * SB⁻¹ = (1 : Matrix (Fin D₂) (Fin D₂) ℂ) :=
    Matrix.mul_nonsing_inv SB hSB_u
  have hSAh_inv_mul : (SAᴴ)⁻¹ * SAᴴ = (1 : Matrix (Fin D₁) (Fin D₁) ℂ) :=
    Matrix.nonsing_inv_mul SAᴴ hSAh_u
  have hSAh_mul_inv : SAᴴ * (SAᴴ)⁻¹ = (1 : Matrix (Fin D₁) (Fin D₁) ℂ) :=
    Matrix.mul_nonsing_inv SAᴴ hSAh_u
  have hSBh_inv_mul : (SBᴴ)⁻¹ * SBᴴ = (1 : Matrix (Fin D₂) (Fin D₂) ℂ) :=
    Matrix.nonsing_inv_mul SBᴴ hSBh_u
  have hSBh_mul_inv : SBᴴ * (SBᴴ)⁻¹ = (1 : Matrix (Fin D₂) (Fin D₂) ℂ) :=
    Matrix.mul_nonsing_inv SBᴴ hSBh_u
  have hSA_mul : SA * SAᴴ = ρA := by
    calc SA * SAᴴ = S0Aᴴ * S0A := by simp [SA]
    _ = ρA := by simpa using hρA_eq.symm
  have hSB_mul : SB * SBᴴ = ρB := by
    calc SB * SBᴴ = S0Bᴴ * S0B := by simp [SB]
    _ = ρB := by simpa using hρB_eq.symm
  let A' : MPSTensor d D₁ := fun i => SA⁻¹ * A i * SA
  let B' : MPSTensor d D₂ := fun i => SB⁻¹ * B i * SB
  have hA'unital : ∑ i : Fin d, (A' i) * (A' i)ᴴ = 1 := by
    simpa [A'] using gauged_unital A SA ρA hSA_det hSA_mul hρA_fix
  have hB'unital : ∑ i : Fin d, (B' i) * (B' i)ᴴ = 1 := by
    simpa [B'] using gauged_unital B SB ρB hSB_det hSB_mul hρB_fix
  let X' : Matrix (Fin D₁) (Fin D₂) ℂ := SA⁻¹ * X * (SBᴴ)⁻¹
  have hX'ne : X' ≠ 0 := by
    intro h0
    apply hX
    have key : SA * X' * SBᴴ = X := by
      simp only [X', Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u,
          Matrix.nonsing_inv_mul _ hSBh_u, Matrix.mul_one]
    rw [← key, h0, Matrix.mul_zero, Matrix.zero_mul]
  have hFXsum : ∑ i : Fin d, A i * X * (B i)ᴴ = μ • X := by
    simpa [mixedTransferMap₂_apply] using hFX
  have hFX' : ∑ i : Fin d, A' i * X' * (B' i)ᴴ = μ • X' := by
    have hterm : ∀ i : Fin d,
        (A' i) * X' * (B' i)ᴴ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
      intro i
      have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
        simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
      calc (A' i) * X' * (B' i)ᴴ
          = (SA⁻¹ * A i * SA) * (SA⁻¹ * X * (SBᴴ)⁻¹) * (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) := by
            simp [A', X', hBstar]
        _ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
            simp only [Matrix.mul_assoc]
            rw [Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u,
                Matrix.nonsing_inv_mul_cancel_left _ _ hSBh_u]
    simp_rw [hterm]
    simp_rw [← Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => SA⁻¹ * (A i * X * (B i)ᴴ)) (M := (SBᴴ)⁻¹)]
    simp_rw [← Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => A i * X * (B i)ᴴ) (M := SA⁻¹)]
    rw [hFXsum]
    have h1 : SA⁻¹ * (μ • X) = μ • (SA⁻¹ * X) := by
      simp [Matrix.mul_smul]
    rw [h1]
    have h2 : (μ • (SA⁻¹ * X)) * (SBᴴ)⁻¹ = μ • ((SA⁻¹ * X) * (SBᴴ)⁻¹) := by
      simp [Matrix.smul_mul]
    rw [h2]
  let K : Fin d → Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    fun i => Matrix.fromBlocks (A' i) 0 0 (B' i)
  let M : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    Matrix.fromBlocks 0 X' 0 0
  have hK_unital : Kraus.IsUnital K := by
    change (∑ i, K i * (K i)ᴴ) = 1
    have hsum : ∑ i : Fin d, K i * (K i)ᴴ =
        Matrix.fromBlocks (∑ i, (A' i) * (A' i)ᴴ) 0 0 (∑ i, (B' i) * (B' i)ᴴ) := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [K, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    simp [hsum, hA'unital, hB'unital]
  have hEigM : Kraus.map K M = μ • M := by
    have hmap : Kraus.map K M =
        Matrix.fromBlocks 0 (∑ i : Fin d, A' i * X' * (B' i)ᴴ) 0 0 := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [Kraus.map, K, M, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    simp [hmap, hFX', M, Matrix.fromBlocks_smul]
  let rhoT : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    Matrix.fromBlocks (SAᴴ * SA) 0 0 (SBᴴ * SB)
  have hrhoT_pd : rhoT.PosDef := by
    let Sblock : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
      Matrix.fromBlocks SA 0 0 SB
    refine (Matrix.isStrictlyPositive_iff_posDef).1 ?_
    refine (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).2 ?_
    refine ⟨Sblock, ?_, ?_⟩
    · exact (isUnit_iff_exists_inv).2
        ⟨Matrix.fromBlocks SA⁻¹ 0 0 SB⁻¹, by
          simp [Sblock, Matrix.fromBlocks_multiply,
            Matrix.mul_nonsing_inv _ hSA_u, Matrix.mul_nonsing_inv _ hSB_u]⟩
    · simp [rhoT, Sblock, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
  have hrhoT_fix : Kraus.adjointMap K rhoT = rhoT := by
    have hAblock : ∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * SA := by
      have hterm : ∀ i : Fin d,
          (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * ((A i)ᴴ * A i) * SA := by
        intro i
        have hAstar : (A' i)ᴴ = SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹ := by
          simp [A', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
        calc (A' i)ᴴ * (SAᴴ * SA) * (A' i)
            = (SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹) * (SAᴴ * SA) * (SA⁻¹ * A i * SA) := by
                simp [A', hAstar]
          _ = SAᴴ * ((A i)ᴴ * A i) * SA := by
                simp only [Matrix.mul_assoc]
                rw [Matrix.nonsing_inv_mul_cancel_left _ _ hSAh_u,
                    Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u]
      simp_rw [hterm, ← Finset.sum_mul, ← Finset.mul_sum, hA_left, Matrix.mul_one]
    have hBblock : ∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * SB := by
      have hterm : ∀ i : Fin d,
          (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * ((B i)ᴴ * B i) * SB := by
        intro i
        have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
          simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
        calc (B' i)ᴴ * (SBᴴ * SB) * (B' i)
            = (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) * (SBᴴ * SB) * (SB⁻¹ * B i * SB) := by
                simp [B', hBstar]
          _ = SBᴴ * ((B i)ᴴ * B i) * SB := by
                simp only [Matrix.mul_assoc]
                rw [Matrix.nonsing_inv_mul_cancel_left _ _ hSBh_u,
                    Matrix.mul_nonsing_inv_cancel_left _ _ hSB_u]
      simp_rw [hterm, ← Finset.sum_mul, ← Finset.mul_sum, hB_left, Matrix.mul_one]
    have hAdj : Kraus.adjointMap K rhoT =
        Matrix.fromBlocks (∑ i, (A' i)ᴴ * (SAᴴ * SA) * (A' i)) 0 0
          (∑ i, (B' i)ᴴ * (SBᴴ * SB) * (B' i)) := by
      ext a b
      rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    simp [hAdj, rhoT, hAblock, hBblock]
  have hKS_M : Kraus.map K (Mᴴ * M) = (Kraus.map K M)ᴴ * Kraus.map K M :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hK_unital hrhoT_pd hrhoT_fix M μ hEigM hμ
  have hComm_M : ∀ i : Fin d, M * (K i)ᴴ = (K i)ᴴ * Kraus.map K M :=
    Kraus.kraus_commute_of_ks_equality K hK_unital M hKS_M
  have hInter1 : ∀ k : Fin d, X' * (B' k)ᴴ = μ • ((A' k)ᴴ * X') := by
    intro k
    have h' : M * (K k)ᴴ = (K k)ᴴ * (μ • M) := by
      rw [hComm_M k, hEigM]
    have hL : M * (K k)ᴴ = Matrix.fromBlocks 0 (X' * (B' k)ᴴ) 0 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K k)ᴴ * (μ • M) = Matrix.fromBlocks 0 (μ • ((A' k)ᴴ * X')) 0 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_smul]
    have h_eq := hL ▸ hR ▸ h'
    exact (Matrix.fromBlocks_inj.1 h_eq).2.1
  have hμ_conj : ‖(starRingEnd ℂ) μ‖ = 1 := by
    rwa [Complex.norm_conj]
  have hEigMstar : Kraus.map K Mᴴ = (starRingEnd ℂ μ) • Mᴴ := by
    calc Kraus.map K Mᴴ = (Kraus.map K M)ᴴ := by
          simpa using (Kraus.map_conjTranspose (K := K) M).symm
      _ = (starRingEnd ℂ μ) • Mᴴ := by simp [hEigM, Matrix.conjTranspose_smul]
  have hKS_Ms : Kraus.map K (Mᴴᴴ * Mᴴ) = (Kraus.map K Mᴴ)ᴴ * Kraus.map K Mᴴ :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hK_unital hrhoT_pd hrhoT_fix Mᴴ (starRingEnd ℂ μ) hEigMstar hμ_conj
  have hComm_Ms : ∀ i : Fin d, Mᴴ * (K i)ᴴ = (K i)ᴴ * Kraus.map K Mᴴ :=
    Kraus.kraus_commute_of_ks_equality K hK_unital Mᴴ hKS_Ms
  have hInter2h : ∀ k : Fin d, X'ᴴ * (A' k)ᴴ = (starRingEnd ℂ μ) • ((B' k)ᴴ * X'ᴴ) := by
    intro k
    have h' : Mᴴ * (K k)ᴴ = (K k)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) := by
      rw [hComm_Ms k, hEigMstar]
    have hL : Mᴴ * (K k)ᴴ =
        Matrix.fromBlocks 0 0 (X'ᴴ * (A' k)ᴴ) 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K k)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) =
        Matrix.fromBlocks 0 0 ((starRingEnd ℂ μ) • ((B' k)ᴴ * X'ᴴ)) 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_smul]
    have h_eq := hL ▸ hR ▸ h'
    exact (Matrix.fromBlocks_inj.1 h_eq).2.2.1
  have hInter2 : ∀ k : Fin d, A' k * X' = μ • X' * B' k := by
    intro k
    have h22 := congrArg Matrix.conjTranspose (hInter2h k)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, starRingEnd_apply, star_star] at h22
    simpa [smul_mul_assoc] using h22
  have hInter1c : ∀ k : Fin d, B' k * X'ᴴ = (starRingEnd ℂ μ) • X'ᴴ * A' k := by
    intro k
    have h22 := congrArg Matrix.conjTranspose (hInter1 k)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul] at h22
    simpa [smul_mul_assoc] using h22
  have hμ_star_mul : star μ * μ = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hμ]
  have hμ_mul_star : μ * star μ = 1 := by
    simpa [mul_comm] using hμ_star_mul
  have hμ_starRing_mul : ((starRingEnd ℂ) μ) * μ = 1 := by
    simpa [Complex.star_def] using hμ_star_mul
  have hμ_mul_starRing : μ * ((starRingEnd ℂ) μ) = 1 := by
    simpa [Complex.star_def] using hμ_mul_star
  have hsmul_self_mul_conjTranspose :
      ∀ N : Matrix (Fin D₁) (Fin D₂) ℂ, (μ • N) * (μ • N)ᴴ = N * Nᴴ := by
    intro N
    calc
      (μ • N) * (μ • N)ᴴ = (((starRingEnd ℂ) μ) * μ) • (N * Nᴴ) := by
        simp [Matrix.conjTranspose_smul, Matrix.mul_smul, smul_smul, mul_comm]
      _ = N * Nᴴ := by simp [hμ_starRing_mul]
  have hsmul_star_self_mul_conjTranspose :
      ∀ N : Matrix (Fin D₂) (Fin D₁) ℂ,
        ((starRingEnd ℂ μ) • N) * (((starRingEnd ℂ μ) • N)ᴴ) = N * Nᴴ := by
    intro N
    calc
      ((starRingEnd ℂ μ) • N) * (((starRingEnd ℂ μ) • N)ᴴ)
          = (μ * (starRingEnd ℂ μ)) • (N * Nᴴ) := by
              simp [Matrix.conjTranspose_smul, Matrix.mul_smul, smul_smul]
      _ = N * Nᴴ := by simp [hμ_mul_starRing]
  let σA : Matrix (Fin D₁) (Fin D₁) ℂ := X' * X'ᴴ
  let σB : Matrix (Fin D₂) (Fin D₂) ℂ := X'ᴴ * X'
  have hσA_psd : σA.PosSemidef := by
    simpa [σA] using Matrix.posSemidef_self_mul_conjTranspose X'
  have hσB_psd : σB.PosSemidef := by
    simpa [σB] using Matrix.posSemidef_conjTranspose_mul_self X'
  have hσA_ne : σA ≠ 0 := by
    intro h
    apply hX'ne
    exact Matrix.self_mul_conjTranspose_eq_zero.mp (by simpa [σA] using h)
  have hσB_ne : σB ≠ 0 := by
    intro h
    apply hX'ne
    exact Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa [σB] using h)
  have hσA_fix : transferMap (d := d) (D := D₁) A' σA = σA := by
    have hAX : ∀ i : Fin d, A' i * X' = μ • (X' * B' i) := by
      intro i
      simpa [smul_mul_assoc] using hInter2 i
    have hterm : ∀ i : Fin d, A' i * σA * (A' i)ᴴ = X' * (B' i * (B' i)ᴴ) * X'ᴴ := by
      intro i
      calc
        A' i * σA * (A' i)ᴴ = (A' i * X') * (A' i * X')ᴴ := by
          simp [σA, Matrix.mul_assoc, Matrix.conjTranspose_mul]
        _ = (μ • (X' * B' i)) * (μ • (X' * B' i))ᴴ := by
          simp [hAX i]
        _ = (X' * B' i) * (X' * B' i)ᴴ := hsmul_self_mul_conjTranspose (X' * B' i)
        _ = X' * (B' i * (B' i)ᴴ) * X'ᴴ := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    calc
      transferMap A' σA = ∑ i : Fin d, A' i * σA * (A' i)ᴴ := by
        simp [transferMap_apply]
      _ = ∑ i : Fin d, X' * (B' i * (B' i)ᴴ) * X'ᴴ := by
        simp [hterm]
      _ = (∑ i : Fin d, X' * (B' i * (B' i)ᴴ)) * X'ᴴ := by
        simpa using (Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
          (f := fun i : Fin d => X' * (B' i * (B' i)ᴴ)) (M := X'ᴴ)).symm
      _ = (X' * (∑ i : Fin d, B' i * (B' i)ᴴ)) * X'ᴴ := by
        exact congrArg (fun T => T * X'ᴴ) <|
          (Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
            (f := fun i : Fin d => B' i * (B' i)ᴴ) (M := X')).symm
      _ = X' * (∑ i : Fin d, B' i * (B' i)ᴴ) * X'ᴴ := by
        simp [Matrix.mul_assoc]
      _ = X' * X'ᴴ := by rw [hB'unital]; simp
      _ = σA := rfl
  have hσB_fix : transferMap (d := d) (D := D₂) B' σB = σB := by
    have hBX : ∀ i : Fin d, B' i * X'ᴴ = (starRingEnd ℂ μ) • (X'ᴴ * A' i) := by
      intro i
      simpa [smul_mul_assoc] using hInter1c i
    have hterm : ∀ i : Fin d, B' i * σB * (B' i)ᴴ = X'ᴴ * (A' i * (A' i)ᴴ) * X' := by
      intro i
      calc
        B' i * σB * (B' i)ᴴ = (B' i * X'ᴴ) * (B' i * X'ᴴ)ᴴ := by
          simp [σB, Matrix.mul_assoc, Matrix.conjTranspose_mul]
        _ = ((starRingEnd ℂ μ) • (X'ᴴ * A' i)) * (((starRingEnd ℂ μ) • (X'ᴴ * A' i))ᴴ) := by
          simp [hBX i]
        _ = (X'ᴴ * A' i) * (X'ᴴ * A' i)ᴴ := hsmul_star_self_mul_conjTranspose (X'ᴴ * A' i)
        _ = X'ᴴ * (A' i * (A' i)ᴴ) * X' := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    calc
      transferMap B' σB = ∑ i : Fin d, B' i * σB * (B' i)ᴴ := by
        simp [transferMap_apply]
      _ = ∑ i : Fin d, X'ᴴ * (A' i * (A' i)ᴴ) * X' := by
        simp [hterm]
      _ = (∑ i : Fin d, X'ᴴ * (A' i * (A' i)ᴴ)) * X' := by
        simpa using (Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
          (f := fun i : Fin d => X'ᴴ * (A' i * (A' i)ᴴ)) (M := X')).symm
      _ = (X'ᴴ * (∑ i : Fin d, A' i * (A' i)ᴴ)) * X' := by
        exact congrArg (fun T => T * X') <|
          (Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
            (f := fun i : Fin d => A' i * (A' i)ᴴ) (M := X'ᴴ)).symm
      _ = X'ᴴ * (∑ i : Fin d, A' i * (A' i)ᴴ) * X' := by
        simp [Matrix.mul_assoc]
      _ = X'ᴴ * X' := by rw [hA'unital]; simp
      _ = σB := rfl
  let YA : Matrix (Fin D₁) (Fin D₁) ℂ := SA * σA * SAᴴ
  let YB : Matrix (Fin D₂) (Fin D₂) ℂ := SB * σB * SBᴴ
  have hYA_psd : YA.PosSemidef := by
    simpa [YA, Matrix.star_eq_conjTranspose] using
      (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hSA_unit).2 hσA_psd
  have hYB_psd : YB.PosSemidef := by
    simpa [YB, Matrix.star_eq_conjTranspose] using
      (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hSB_unit).2 hσB_psd
  have hYA_ne : YA ≠ 0 := by
    simpa [YA] using mul_mul_conjTranspose_ne_zero_of_ne_zero SA hSA_u (M := σA) hσA_ne
  have hYB_ne : YB ≠ 0 := by
    simpa [YB] using mul_mul_conjTranspose_ne_zero_of_ne_zero SB hSB_u (M := σB) hσB_ne
  have hYA_fix : transferMap (d := d) (D := D₁) A YA = YA := by
    have hAiSA : ∀ i : Fin d, A i * SA = SA * A' i := by
      intro i
      simpa [A', Matrix.mul_assoc] using
        (Matrix.mul_nonsing_inv_cancel_left (A := SA) (B := A i * SA) hSA_u).symm
    have hSAhAiH : ∀ i : Fin d, SAᴴ * (A i)ᴴ = (A' i)ᴴ * SAᴴ := by
      intro i
      simp [A', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
        Matrix.mul_assoc, hSAh_inv_mul]
    have hterm : ∀ i : Fin d, A i * YA * (A i)ᴴ = SA * (A' i * σA * (A' i)ᴴ) * SAᴴ := by
      intro i
      calc
        A i * YA * (A i)ᴴ = (A i * SA) * σA * (SAᴴ * (A i)ᴴ) := by
          simp [YA, Matrix.mul_assoc]
        _ = (SA * A' i) * σA * ((A' i)ᴴ * SAᴴ) := by
          rw [hAiSA i, hSAhAiH i]
        _ = SA * (A' i * σA * (A' i)ᴴ) * SAᴴ := by
          simp [Matrix.mul_assoc]
    calc
      transferMap A YA = ∑ i : Fin d, A i * YA * (A i)ᴴ := by
        simp [transferMap_apply]
      _ = ∑ i : Fin d, SA * (A' i * σA * (A' i)ᴴ) * SAᴴ := by
        simp [hterm]
      _ = SA * (∑ i : Fin d, A' i * σA * (A' i)ᴴ) * SAᴴ := by
        simpa using
          (sum_sandwich (L := SA) (R := SAᴴ)
            (M := fun i : Fin d => A' i * σA * (A' i)ᴴ))
      _ = SA * transferMap A' σA * SAᴴ := by
        simp [transferMap_apply]
      _ = SA * σA * SAᴴ := by rw [hσA_fix]
      _ = YA := rfl
  have hYB_fix : transferMap (d := d) (D := D₂) B YB = YB := by
    have hBiSB : ∀ i : Fin d, B i * SB = SB * B' i := by
      intro i
      simpa [B', Matrix.mul_assoc] using
        (Matrix.mul_nonsing_inv_cancel_left (A := SB) (B := B i * SB) hSB_u).symm
    have hSBhBiH : ∀ i : Fin d, SBᴴ * (B i)ᴴ = (B' i)ᴴ * SBᴴ := by
      intro i
      simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
        Matrix.mul_assoc, hSBh_inv_mul]
    have hterm : ∀ i : Fin d, B i * YB * (B i)ᴴ = SB * (B' i * σB * (B' i)ᴴ) * SBᴴ := by
      intro i
      calc
        B i * YB * (B i)ᴴ = (B i * SB) * σB * (SBᴴ * (B i)ᴴ) := by
          simp [YB, Matrix.mul_assoc]
        _ = (SB * B' i) * σB * ((B' i)ᴴ * SBᴴ) := by
          rw [hBiSB i, hSBhBiH i]
        _ = SB * (B' i * σB * (B' i)ᴴ) * SBᴴ := by
          simp [Matrix.mul_assoc]
    calc
      transferMap B YB = ∑ i : Fin d, B i * YB * (B i)ᴴ := by
        simp [transferMap_apply]
      _ = ∑ i : Fin d, SB * (B' i * σB * (B' i)ᴴ) * SBᴴ := by
        simp [hterm]
      _ = SB * (∑ i : Fin d, B' i * σB * (B' i)ᴴ) * SBᴴ := by
        simpa using
          (sum_sandwich (L := SB) (R := SBᴴ)
            (M := fun i : Fin d => B' i * σB * (B' i)ᴴ))
      _ = SB * transferMap B' σB * SBᴴ := by
        simp [transferMap_apply]
      _ = SB * σB * SBᴴ := by rw [hσB_fix]
      _ = YB := rfl
  obtain ⟨cA, hYA_eq⟩ :=
    posSemidef_fixedPoint_unique_of_irreducible
      (A := A) hIrrA ρA YA hρA_psd hρA_ne hYA_psd hρA_fix hYA_fix
  obtain ⟨cB, hYB_eq⟩ :=
    posSemidef_fixedPoint_unique_of_irreducible
      (A := B) hIrrB ρB YB hρB_psd hρB_ne hYB_psd hρB_fix hYB_fix
  have hσA_scalar : σA = cA • (1 : Matrix (Fin D₁) (Fin D₁) ℂ) := by
    have hYA_scalar' : SA * σA * SAᴴ = cA • (SA * SAᴴ) := by
      simpa [YA, hSA_mul] using hYA_eq
    have hcancel := congrArg (fun T => SA⁻¹ * T * (SAᴴ)⁻¹) hYA_scalar'
    calc
      σA = (SA⁻¹ * SA) * σA := by simp [hSA_inv_mul]
      _ = SA⁻¹ * (SA * σA) := by simp [Matrix.mul_assoc]
      _ = SA⁻¹ * (SA * σA * SAᴴ) * (SAᴴ)⁻¹ := by
        simp [Matrix.mul_assoc, hSAh_mul_inv]
      _ = SA⁻¹ * (cA • (SA * SAᴴ)) * (SAᴴ)⁻¹ := hcancel
      _ = cA • (SA⁻¹ * (SA * SAᴴ) * (SAᴴ)⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = cA • (1 : Matrix (Fin D₁) (Fin D₁) ℂ) := by
        simp [Matrix.mul_assoc, hSA_inv_mul, hSAh_mul_inv]
  have hσB_scalar : σB = cB • (1 : Matrix (Fin D₂) (Fin D₂) ℂ) := by
    have hYB_scalar' : SB * σB * SBᴴ = cB • (SB * SBᴴ) := by
      simpa [YB, hSB_mul] using hYB_eq
    have hcancel := congrArg (fun T => SB⁻¹ * T * (SBᴴ)⁻¹) hYB_scalar'
    calc
      σB = (SB⁻¹ * SB) * σB := by simp [hSB_inv_mul]
      _ = SB⁻¹ * (SB * σB) := by simp [Matrix.mul_assoc]
      _ = SB⁻¹ * (SB * σB * SBᴴ) * (SBᴴ)⁻¹ := by
        simp [Matrix.mul_assoc, hSBh_mul_inv]
      _ = SB⁻¹ * (cB • (SB * SBᴴ)) * (SBᴴ)⁻¹ := hcancel
      _ = cB • (SB⁻¹ * (SB * SBᴴ) * (SBᴴ)⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = cB • (1 : Matrix (Fin D₂) (Fin D₂) ℂ) := by
        simp [Matrix.mul_assoc, hSB_inv_mul, hSBh_mul_inv]
  have hcA_ne : cA ≠ 0 := by
    intro hcA
    apply hσA_ne
    simp [hσA_scalar, hcA]
  have hcB_ne : cB ≠ 0 := by
    intro hcB
    apply hσB_ne
    simp [hσB_scalar, hcB]
  have hσA_unit : IsUnit σA := by
    rw [hσA_scalar]
    exact (isUnit_iff_exists).2 ⟨cA⁻¹ • (1 : Matrix (Fin D₁) (Fin D₁) ℂ), by
      simp [hcA_ne]⟩
  have hσB_unit : IsUnit σB := by
    rw [hσB_scalar]
    exact (isUnit_iff_exists).2 ⟨cB⁻¹ • (1 : Matrix (Fin D₂) (Fin D₂) ℂ), by
      simp [hcB_ne]⟩
  have hσA_pd : σA.PosDef := (Matrix.PosSemidef.posDef_iff_isUnit hσA_psd).2 hσA_unit
  have hσB_pd : σB.PosDef := (Matrix.PosSemidef.posDef_iff_isUnit hσB_psd).2 hσB_unit
  have hX'inj : ∀ v : Fin D₂ → ℂ, X' *ᵥ v = 0 → v = 0 :=
    injective_of_posDef_conjTranspose_mul_self X' (by simpa [σB] using hσB_pd)
  have hX'hinj : ∀ v : Fin D₁ → ℂ, X'ᴴ *ᵥ v = 0 → v = 0 :=
    injective_of_posDef_conjTranspose_mul_self X'ᴴ (by simpa [σA] using hσA_pd)
  have h_D₂_le : D₂ ≤ D₁ :=
    dim_le_of_injective_matrix X' hX'inj
  have h_D₁_le : D₁ ≤ D₂ :=
    dim_le_of_injective_matrix X'ᴴ hX'hinj
  exact le_antisymm h_D₁_le h_D₂_le

/--
**Rectangular strict spectral gap** for irreducible left-canonical blocks of different bond
sizes.

The intended proof follows the same Cauchy--Schwarz rigidity mechanism as
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`, but in the rectangular setting:
a modulus-one peripheral eigenvector produces an isometry `X`, swapping the roles of `A`
and `B` upgrades this to a unitary, and hence forces equality of bond dimensions.
-/
theorem mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    mixedTransferSpectralRadius₂ A B < 1 := by
  classical
  have hle : mixedTransferSpectralRadius₂ A B ≤ 1 :=
    spectralRadius_mixedTransfer₂_le_one (A := A) (B := B) hA_left hB_left
  refine lt_of_le_of_ne hle ?_
  intro hEq
  unfold mixedTransferSpectralRadius₂ at hEq
  set F : (Matrix (Fin D₁) (Fin D₂) ℂ) →L[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ :=
    (Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ)) (mixedTransferMap₂ A B)
  have hEqF : spectralRadius ℂ F = 1 := by
    simpa [F] using hEq
  obtain ⟨μ, hμ_spec, hμ_rad⟩ := spectrum.exists_nnnorm_eq_spectralRadius (a := F)
  have hμ_one : (↑‖μ‖₊ : ENNReal) = 1 := by
    simpa [hEqF] using hμ_rad
  have hμ_nnn : ‖μ‖₊ = (1 : NNReal) := (ENNReal.coe_eq_one).1 hμ_one
  have hμ_norm : ‖μ‖ = 1 := by
    have : (‖μ‖₊ : ℝ) = (1 : ℝ) := by
      exact_mod_cast hμ_nnn
    simpa [coe_nnnorm] using this
  have h_spec :=
    AlgEquiv.spectrum_eq
      (Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ)) (mixedTransferMap₂ A B)
  have hμ_spec' : μ ∈ spectrum ℂ (mixedTransferMap₂ A B) := by
    have : μ ∈ spectrum ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
          (mixedTransferMap₂ A B)) := by
      simpa [F] using hμ_spec
    simpa [h_spec] using this
  have hHas : Module.End.HasEigenvalue (mixedTransferMap₂ A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec'
  obtain ⟨X, hX_mem, hX_ne⟩ := hHas.exists_hasEigenvector
  have hFX : mixedTransferMap₂ A B X = μ • X :=
    (Module.End.mem_eigenspace_iff).1 hX_mem
  have hDim : D₁ = D₂ :=
    dim_eq_of_modulus_one_eigenvector_of_irreducible_TP
      A B hA_irr hB_irr hA_left hB_left X μ hFX hμ_norm hX_ne
  exact hD hDim

/--
**Overlap decay** for irreducible left-canonical blocks of different bond dimensions.
-/
theorem mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  exact mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B) <| by
    simpa [mixedTransferSpectralRadius₂] using
      mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
        A B hA_irr hB_irr hA_left hB_left hD

end DifferentDimensions

end MPSTensor
