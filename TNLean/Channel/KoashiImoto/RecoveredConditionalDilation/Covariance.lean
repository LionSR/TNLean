/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KoashiImoto.RecoveredConditionalDilation.Basic

/-!
# Coordinate covariance of pure-ancilla recovery

This file proves that pure-ancilla recovery commutes with a unitary change of
system coordinates.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace Matrix

open RecoveredConditionalDilationInternal

/-- A pure-ancilla recovery transported to unitary system coordinates is the
recovery of the inverse-coordinate dilation, followed by the corresponding
output coordinate change. -/
theorem RecoveredConditionalDilationInternal.pureAncillaRecovery_inverse_coordinate
    {B C R : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (c₀ : C) (r₀ : R)
    (V : Matrix B B ℂ) (hV : V ∈ Matrix.unitaryGroup B ℂ)
    (Uphysical Ucoordinate :
      Matrix (B × (C × R)) (B × (C × R)) ℂ)
    (hcoordinate :
      star (V ⊗ₖ (1 : Matrix (C × R) (C × R) ℂ)) *
          Uphysical *
          (V ⊗ₖ (1 : Matrix (C × R) (C × R) ℂ)) =
        Ucoordinate)
    (X : Matrix B B ℂ) :
    pureAncillaRecovery c₀ r₀ Ucoordinate (star V * X * V) =
      star (V ⊗ₖ (1 : Matrix C C ℂ)) *
        pureAncillaRecovery c₀ r₀ Uphysical X *
          (V ⊗ₖ (1 : Matrix C C ℂ)) := by
  let liftR := V ⊗ₖ (1 : Matrix (C × R) (C × R) ℂ)
  let liftC := V ⊗ₖ (1 : Matrix C C ℂ)
  have hliftR : liftR ∈ Matrix.unitaryGroup (B × (C × R)) ℂ :=
    Matrix.kronecker_mem_unitary hV (Submonoid.one_mem _)
  have hliftR_left : star liftR * liftR = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hliftR
  have hliftR_right : liftR * star liftR = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hliftR
  have hliftC : liftC ∈ Matrix.unitaryGroup (B × C) ℂ :=
    Matrix.kronecker_mem_unitary hV (Submonoid.one_mem _)
  have hliftC_left : star liftC * liftC = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hliftC
  change star liftR * Uphysical * liftR = Ucoordinate at hcoordinate
  have hphysical : Uphysical = liftR * Ucoordinate * star liftR := by
    calc
      Uphysical = 1 * Uphysical * 1 := by simp
      _ = (liftR * star liftR) * Uphysical *
          (liftR * star liftR) := by
        rw [hliftR_right]
      _ = liftR * (star liftR * Uphysical * liftR) *
          star liftR := by simp only [Matrix.mul_assoc]
      _ = liftR * Ucoordinate * star liftR := by rw [hcoordinate]
  have hisometry :=
    physicalDilation_mul_fixedEnvEmbedding_mul_support
      (c₀, r₀) V hV Ucoordinate
      (1 : Matrix B B ℂ)
  dsimp only at hisometry
  change
    (liftR * Ucoordinate * star liftR) *
          fixedEnvEmbedding (S := B) (c₀, r₀) * (V * 1) =
      liftR *
        (Ucoordinate * fixedEnvEmbedding (S := B) (c₀, r₀) * 1)
    at hisometry
  rw [← hphysical] at hisometry
  have hslices : ∀ r : R,
      rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Uphysical) r * V =
        liftC *
          rightOutputSlice
            (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r := by
    intro r
    ext bc b
    rcases bc with ⟨b', c⟩
    have hraw := congrArg
      (fun W ↦ rightOutputSlice W (c, r)) hisometry
    simp only [Matrix.mul_one] at hraw
    have hraw' :
        rightOutputSlice
            (Uphysical * fixedEnvEmbedding (S := B) (c₀, r₀) * V)
            (c, r) =
          V * rightOutputSlice
            (Ucoordinate * fixedEnvEmbedding (S := B) (c₀, r₀))
            (c, r) := by
      simpa only [liftR] using hraw.trans
        (rightOutputSlice_kronecker_one_mul V
          (Ucoordinate * fixedEnvEmbedding (S := B) (c₀, r₀))
          (c, r))
    have hentry := congrFun (congrFun hraw' b') b
    simpa [pureAncillaDilationIsometry, rightOutputSlice,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodAssoc,
      Matrix.mul_apply, liftC, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Fintype.sum_prod_type] using hentry
  rw [pureAncillaRecovery, pureAncillaRecovery,
    LinearMap.comp_apply, LinearMap.comp_apply, singleKrausMap_apply,
    singleKrausMap_apply]
  change
    partialTraceRight
        (pureAncillaDilationIsometry c₀ r₀ Ucoordinate *
          (star V * X * V) *
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate)ᴴ) =
      star liftC *
        partialTraceRight
          (pureAncillaDilationIsometry c₀ r₀ Uphysical * X *
            (pureAncillaDilationIsometry c₀ r₀ Uphysical)ᴴ) *
        liftC
  have hpure (U : Matrix (B × (C × R)) (B × (C × R)) ℂ)
      (Y : Matrix B B ℂ) :
      partialTraceRight
          (pureAncillaDilationIsometry c₀ r₀ U * Y *
            (pureAncillaDilationIsometry c₀ r₀ U)ᴴ) =
        rectangularKrausMap
          (fun r ↦ rightOutputSlice
            (pureAncillaDilationIsometry c₀ r₀ U) r) Y := by
    ext bc bc'
    simp only [partialTraceRight_apply, rectangularKrausMap,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
    rfl
  rw [hpure, hpure]
  change
    (∑ r, rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r *
        (star V * X * V) *
        (rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r)ᴴ) =
      star liftC *
        (∑ r, rightOutputSlice
            (pureAncillaDilationIsometry c₀ r₀ Uphysical) r * X *
            (rightOutputSlice
              (pureAncillaDilationIsometry c₀ r₀ Uphysical) r)ᴴ) *
        liftC
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  have hs := hslices r
  have hs' :
      rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r * star V =
        star liftC *
          rightOutputSlice
            (pureAncillaDilationIsometry c₀ r₀ Uphysical) r := by
    calc
      rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r * star V =
        (star liftC * liftC) *
            rightOutputSlice
              (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r *
            star V := by rw [hliftC_left]; simp
      _ = star liftC *
            (liftC *
              rightOutputSlice
                (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r) *
            star V := by simp only [Matrix.mul_assoc]
      _ = star liftC *
          rightOutputSlice
            (pureAncillaDilationIsometry c₀ r₀ Uphysical) r := by
          rw [← hs]
          simp only [Matrix.mul_assoc]
          rw [Matrix.mem_unitaryGroup_iff.mp hV, Matrix.mul_one]
  calc
    rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r *
        (star V * X * V) *
        (rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r)ᴴ =
      (rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r * star V) *
        X *
        (rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Ucoordinate) r * star V)ᴴ := by
            simp only [star_eq_conjTranspose, Matrix.conjTranspose_mul,
              Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (star liftC *
          rightOutputSlice
            (pureAncillaDilationIsometry c₀ r₀ Uphysical) r) *
        X *
        (star liftC *
          rightOutputSlice
            (pureAncillaDilationIsometry c₀ r₀ Uphysical) r)ᴴ := by
          rw [hs']
    _ = star liftC *
        (rightOutputSlice
          (pureAncillaDilationIsometry c₀ r₀ Uphysical) r * X *
          (rightOutputSlice
            (pureAncillaDilationIsometry c₀ r₀ Uphysical) r)ᴴ) *
        liftC := by
          simp only [star_eq_conjTranspose, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end Matrix
