/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.QuadraticPhysicalCutWindow
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.Irreducible.PerronGauge
import QICLean.Kraus.Wielandt.Primitivity.EasyDirections
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity

/-!
# Perron normalization inside quadratic reconstruction

An arbitrary condition-C1 tensor with a nonzero letter has a unital
Perron gauge. C1 transfers to that gauge, extends there to all longer
lengths, and transfers back to the original tensor. The actual physical
cut spaces and window are retained. Amplifying the Perron gauge and
rescaling geometrically along the derived window gauges supplies a
normalized quadratic solution without a canonical-form premise.

The nonzero-letter condition follows from any actual nonzero state of
positive length. It also handles a possible zero C1 length without
silently adding a positive-length hypothesis.

Source: PGVWC07, arXiv:quant-ph/0608197, the normalization in the proof of
Theorem 4, lines 765--770, and first clause of Theorem 8, lines 1139--1169.
-/

open Matrix MPSPreparation
open scoped BigOperators Kronecker

namespace MPSTensor

variable {d D N L m : ℕ}

/-- C1 and a nonzero letter supply an actual unital Perron gauge, and
C1 propagates to every longer length of the original tensor. No spectral
or canonical hypothesis is supplied. The irreducibility argument applies
even when the supplied C1 length is zero.
Source: PGVWC07, MPSarchive.tex lines 765--770 and 889--909. -/
theorem exists_unital_gauge_of_isNBlkInjective [NeZero D] (A : MPSTensor d D)
    (hC1 : Kraus.IsNBlkInjective A L) (hletter : ∃ i, A i ≠ 0) :
    ∃ (B : MPSTensor d D) (ζ : ℂ), ζ ≠ 0 ∧
      (∑ i, B i * (B i)ᴴ = 1) ∧ GaugeEquiv (ζ • A) B ∧
      ∀ n, L ≤ n → Kraus.IsNBlkInjective A n := by
  classical
  have hIrr : Kraus.IsIrreducibleFamily A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
      (Kraus.isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top A
        (fun φ hφ ↦ Kraus.vectorSpreadSpan_eq_top_of_wordSpan_eq_top A hC1 φ hφ))
  obtain ⟨B, r, ρ, _, hr, _, hrow, hgauge⟩ :=
    exists_unital_data_of_irreducible A hIrr hletter
  let ζ : ℂ := ((Real.sqrt r)⁻¹ : ℝ)
  have hζ : ζ ≠ 0 := by
    have hsqrt : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
    dsimp [ζ]
    exact_mod_cast (inv_ne_zero hsqrt)
  have hBL : Kraus.IsNBlkInjective B L :=
    isNBlkInjective_of_gaugeEquiv (isNBlkInjective_smul ζ hζ hC1) hgauge
  refine ⟨B, ζ, hζ, hrow, hgauge, fun n hn ↦ ?_⟩
  exact (isNBlkInjective_smul_iff hζ A n).mp
    (isNBlkInjective_of_gaugeEquiv (isNBlkInjective_of_le_of_unital hrow hBL hn) hgauge.symm)

/-- Nonvanishing of the actual positive-length physical vector supplies
a nonzero tensor letter, with no injectivity or canonical condition.
Source: the nonzero state represented in PGVWC07, lines 1139--1169. -/
theorem exists_apply_ne_zero_of_mpv_ne_zero (A : MPSTensor d D) (hN : 0 < N)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) : ∃ i, A i ≠ 0 := by
  classical
  by_contra hzero
  push_neg at hzero
  obtain ⟨σ, hσ⟩ := hnonzero
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  apply hσ
  simp only [mpv, coeff, List.ofFn_succ, Kraus.evalWord_cons, hzero,
    Matrix.zero_mul, Matrix.trace_zero]

/-- The endpoint-inclusive reconstruction cuts have exactly squared
virtual rank for any C1 tensor with a nonzero letter. Perron normalization
is internal; canonical form is not required of the original tensor.
Source: PGVWC07, MPSarchive.tex lines 911--931 and 1139--1169. -/
theorem quadraticWindow_cutCoefficientRank_eq_of_isNBlkInjective [NeZero D]
    (A : MPSTensor d D) (hC1 : Kraus.IsNBlkInjective A L) (hletter : ∃ i, A i ≠ 0)
    (hN : 2 * L + D ^ 4 < N) (j : Fin (D ^ 4 + 1)) :
    cutCoefficientRank (mpv A (N := N)) (L + j.val) = D * D := by
  obtain ⟨_, _, _, _, _, hlong⟩ := exists_unital_gauge_of_isNBlkInjective A hC1 hletter
  have hj := j.isLt
  rw [cutCoefficientRank_eq_cutRank _ (by omega)]
  exact cutRank_mpv_eq_of_isNBlkInjective (by omega) (hlong _ (by omega)) (hlong _ (by omega))

/-- Any actual physical cut-basis window of a nonzero condition-C1 tensor
admits a normalized quadratic solution. Perron normalization and its
amplified gauge are derived internally; the window and its original
physical coefficient spaces are retained.
Source: PGVWC07, first clause of Theorem 8, lines 1139--1169. -/
theorem exists_quadraticSolution_physicalCutWindow_of_isNBlkInjective [NeZero D]
    (A : MPSTensor d D) (hC1 : Kraus.IsNBlkInjective A L)
    (hletter : ∃ i, A i ≠ 0) (hN : 2 * L + m ≤ N)
    (C : (j : Fin (m + 1)) → Module.Basis (Fin D × Fin D) ℂ
      (cutColumnSpace (mpv A (N := N)) (L + j.val))) :
    Nonempty (QuadraticReconstructionSolution (quadraticPhysicalCutWindow (mpv A) C)) := by
  classical
  obtain ⟨B, ζ, hζ, hrow, hgauge, hlong⟩ :=
    exists_unital_gauge_of_isNBlkInjective A hC1 hletter
  have hcut (j : Fin (m + 1)) : L + j.val ≤ N := by have := j.isLt; omega
  have hleft (j : Fin (m + 1)) : Kraus.IsNBlkInjective A (L + j.val) := hlong _ (by omega)
  have hright (j : Fin (m + 1)) : Kraus.IsNBlkInjective A (N - (L + j.val)) := by
    have := j.isLt
    exact hlong _ (by omega)
  obtain ⟨Y, Z, hlocal, hinverse⟩ := exists_physicalCutWindow_gauges hcut hleft hright C
  obtain ⟨X, hX⟩ := hgauge
  let P : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    (X : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)
  let P' : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
      (1 : Matrix (Fin D) (Fin D) ℂ)
  have hPP' : P * P' = 1 := by
    simp only [P, P', ← Matrix.mul_kronecker_mul, Units.mul_inv, Matrix.one_mul,
      Matrix.one_kronecker_one]
  have hconj (i : Fin d) :
      P * (A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * P' =
        ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ⊗ₖ
          (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simp only [P, P', ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hratio (n : ℕ) : (ζ⁻¹) ^ n * ζ ^ (n + 1) = ζ := by
    rw [pow_succ, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero n hζ)]
  refine ⟨{
    leftGauge := fun j ↦ (ζ⁻¹) ^ j.val • (P * Y j)
    rightGauge := fun j ↦ ζ ^ (j.val + 1) • (Z j * P')
    tensor := B
    kronecker_eq := ?_
    leftGauge_mul_rightGauge := ?_
    sum_mul_conjTranspose := hrow }⟩
  · intro i j
    have hproduct : (P * Y j) * quadraticPhysicalCutWindow (mpv A) C j i * (Z j * P') =
        P * (Y j * quadraticPhysicalCutWindow (mpv A) C j i * Z j) * P' := by
      simp only [Matrix.mul_assoc]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hratio, hproduct, hlocal, hconj, hX]
    simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_kronecker]
  · intro j hj
    have hproduct : (P * Y ⟨j.val + 1, hj⟩) * (Z j * P') = P * P' := by
      calc _ = P * (Y ⟨j.val + 1, hj⟩ * Z j) * P' := by simp only [Matrix.mul_assoc]
        _ = P * P' := by rw [hinverse j hj, Matrix.mul_one]
    change (ζ⁻¹) ^ (j.val + 1) • (P * Y ⟨j.val + 1, hj⟩) *
      (ζ ^ (j.val + 1) • (Z j * P')) = 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hproduct, hPP', ← mul_pow, inv_mul_cancel₀ hζ, one_pow, one_smul]

end MPSTensor
