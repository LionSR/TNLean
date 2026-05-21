/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Algebra.MatrixFunctionalCalculus
import TNLean.MPS.Irreducible.ScalarFixedPoint
import TNLean.MPS.Core.Blocking
import TNLean.MPS.SharedInfra.Scaling
import TNLean.MPS.CanonicalForm.Existence
import TNLean.PiAlgebra.CanonicalFormSep

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNMatrixCFC

/-!
# TP-gauge reduction for normal canonical-form construction

This module gives the TP-gauge normalization part of the normal-canonical-form
reduction.

Its public outputs are:

* `MPSTensor.exists_pgvwc07_unital_dualDiag_data_of_irreducible` — the
  single-block PGVWC07 unital gauge, scalar fixed-point, and dual
  diagonalization package.
* `MPSTensor.exists_pgvwc07_unital_dualDiag_blockwise` — the same PGVWC07
  package applied blockwise to a prepared nonzero irreducible decomposition.
* `MPSTensor.exists_tp_gauge_blockwise` — blockwise Perron--Frobenius / TP-gauge
  normalization for an irreducible block decomposition.
* `MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail` — the corresponding
  arbitrary-input result obtained after zero-block separation.

The auxiliary declarations stay file-local because they are elementary lemmas for
rescaling, gauge transport, and the final zero-block identity (the paper calls
this the ``zero block'' case).
-/

namespace MPSTensor

variable {d D : ℕ}

private noncomputable def gaugeMulVecLinearEquiv {D : ℕ} (X : GL (Fin D) ℂ) :
    (Fin D → ℂ) ≃ₗ[ℂ] (Fin D → ℂ) where
  toFun v := (X : Matrix (Fin D) (Fin D) ℂ) *ᵥ v
  invFun v := (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *ᵥ v)
  left_inv := by
    intro v
    calc
      (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *ᵥ
          ((X : Matrix (Fin D) (Fin D) ℂ) *ᵥ v))
          = ((((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
              (X : Matrix (Fin D) (Fin D) ℂ)) *ᵥ v) := by
              simp [Matrix.mulVec_mulVec]
      _ = v := by
            simp
  right_inv := by
    intro v
    calc
      ((X : Matrix (Fin D) (Fin D) ℂ) *ᵥ
          ((((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *ᵥ v)))
          = (((X : Matrix (Fin D) (Fin D) ℂ) *
              (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) *ᵥ v) := by
              simp [Matrix.mulVec_mulVec]
      _ = v := by
            simp
  map_add' := by
    intro v w
    simp [Matrix.mulVec_add]
  map_smul' := by
    intro c v
    simp [Matrix.mulVec_smul]

private theorem isIrreducibleAction_gaugeEquiv
    {D : ℕ} {A B : MPSTensor d D}
    (hGauge : GaugeEquiv (d := d) (D := D) A B)
    (hIrr : IsIrreducibleAction (d := d) (D := D) A) :
    IsIrreducibleAction (d := d) (D := D) B := by
  classical
  rcases hGauge with ⟨X, hX⟩
  let T : (Fin D → ℂ) ≃ₗ[ℂ] (Fin D → ℂ) := gaugeMulVecLinearEquiv X
  intro W hW
  let W' : Submodule ℂ (Fin D → ℂ) := W.map T.symm.toLinearMap
  have hW' : IsInvariantSubmodule (d := d) (D := D) A W' := by
    intro i v hv
    rcases (Submodule.mem_map).1 hv with ⟨u, huW, rfl⟩
    refine (Submodule.mem_map).2 ?_
    refine ⟨(B i).mulVec u, hW i u huW, ?_⟩
    change (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *ᵥ ((B i) *ᵥ u)) =
      (A i) *ᵥ ((((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *ᵥ u))
    calc
      (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *ᵥ ((B i) *ᵥ u))
          = ((((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * B i) *ᵥ u) := by
              simp [Matrix.mulVec_mulVec]
      _ = ((A i * (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ) *ᵥ u) := by
            rw [hX i]
            simp [Matrix.mul_assoc]
      _ = (A i) *ᵥ ((((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *ᵥ u)) := by
            simp [Matrix.mulVec_mulVec]
  rcases hIrr W' hW' with hW'bot | hW'top
  · left
    exact (Submodule.map_eq_bot_iff (p := W) (e := T.symm)).1 (by simpa [W'] using hW'bot)
  · right
    exact (Submodule.map_eq_top_iff (p := W) (e := T.symm)).1 (by simpa [W'] using hW'top)

/-- Positive-definite TP gauge preserves tensor irreducibility. -/
private theorem isIrreducibleTensor_tpGauge_of_isIrreducibleTensor
    {D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosDef)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A) :
    IsIrreducibleTensor (d := d) (D := D) (tpGauge (d := d) (D := D) A σ) := by
  have hAction : IsIrreducibleAction (d := d) (D := D) A :=
    isIrreducibleAction_of_isIrreducibleTensor (d := d) (D := D) A hIrr
  have hGauge : GaugeEquiv (d := d) (D := D) A (tpGauge (d := d) (D := D) A σ) :=
    gaugeEquiv_tpGauge (d := d) (D := D) A σ hσ
  have hActionGauge :
      IsIrreducibleAction (d := d) (D := D) (tpGauge (d := d) (D := D) A σ) :=
    isIrreducibleAction_gaugeEquiv (d := d) (D := D) hGauge hAction
  exact
    isIrreducibleTensor_of_isIrreducibleAction
      (d := d) (D := D) (tpGauge (d := d) (D := D) A σ) hActionGauge

/-- **Single irreducible-block PGVWC07 canonical-form data.**

Pérez-García, Verstraete, Wolf, and Cirac, Theorem `Th:TIcanonical`, proof
lines 765--770 and 816--832.  For one irreducible nonzero block, the
Perron--Frobenius eigenvector gives the source theorem's unital gauge.  In
that unital gauge every fixed point is scalar, and a final unitary conjugation
diagonalizes a positive-definite fixed point of the dual transfer map.

This is still a single-block statement.  It does not yet thread the construction
through the recursive finite-ring block decomposition, nor does it prove the
total bond-dimension bound of the full translation-invariant canonical-form
theorem. -/
theorem exists_pgvwc07_unital_dualDiag_data_of_irreducible
    [NeZero D]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A)
    (hA : ∃ i, A i ≠ 0) :
    ∃ (B C : MPSTensor d D)
      (r : ℝ)
      (ρ Λ : Matrix (Fin D) (Fin D) ℂ)
      (U : Matrix.unitaryGroup (Fin D) ℂ),
        ρ.PosDef ∧
        0 < r ∧
        (∀ i : Fin d,
          B i =
            (↑((Real.sqrt r)⁻¹) : ℂ) •
              ((CFC.sqrt ρ)⁻¹ * A i * CFC.sqrt ρ)) ∧
        GaugeEquiv (d := d) (D := D)
          (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) B ∧
        (∑ i : Fin d, B i * (B i)ᴴ = 1) ∧
        (∀ X : Matrix (Fin D) (Fin D) ℂ,
          transferMap (d := d) (D := D) B X = X →
            ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ)) ∧
        (let C' : MPSTensor d D :=
          fun i =>
            (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * B i *
              (↑U : Matrix (Fin D) (Fin D) ℂ);
          C = C' ∧
          SameMPV₂ B C ∧
          Λ.PosDef ∧
          Λ.IsDiag ∧
          (∑ i : Fin d, C i * (C i)ᴴ = 1) ∧
          transferMap (d := d) (D := D) (fun i => (C i)ᴴ) Λ = Λ) := by
  classical
  obtain ⟨B, r, ρ, hρ, hr, hB_form, hB_unital, hGauge⟩ :=
    exists_unital_data_of_irreducible (d := d) (D := D) A hIrr hA
  let c : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ)
  have hroot_ne : (↑(Real.sqrt r) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hr)
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    simp [hroot_ne]
  have hIrr_scaled :
      IsIrreducibleTensor (d := d) (D := D) (fun i => c • A i) :=
    isIrreducibleTensor_smul (d := d) (D := D) hc_ne A hIrr
  have hActionScaled :
      IsIrreducibleAction (d := d) (D := D) (fun i => c • A i) :=
    isIrreducibleAction_of_isIrreducibleTensor
      (d := d) (D := D) (fun i => c • A i) hIrr_scaled
  have hActionB : IsIrreducibleAction (d := d) (D := D) B :=
    isIrreducibleAction_gaugeEquiv (d := d) (D := D) hGauge hActionScaled
  have hIrrB : IsIrreducibleTensor (d := d) (D := D) B :=
    isIrreducibleTensor_of_isIrreducibleAction (d := d) (D := D) B hActionB
  have hB_unital_map : transferMap (d := d) (D := D) B 1 = 1 := by
    simpa [transferMap_apply, Matrix.mul_one] using hB_unital
  haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
  have hScalar :
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        transferMap (d := d) (D := D) B X = X →
          ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    intro X hX
    exact fixed_eq_scalar_of_isIrreducibleTensor_unital
      (d := d) (D := D) B hIrrB hB_unital_map X hX
  obtain ⟨U, Λ, hSame, hΛ_pd, hΛ_diag, hC_unital, hΛ_fix⟩ :=
    exists_unitary_diag_posDef_adjointFixedPoint_of_unital_of_isIrreducibleTensor
      (d := d) (D := D) B hB_unital hIrrB (NeZero.pos D)
  let C : MPSTensor d D :=
    fun i =>
      (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * B i *
        (↑U : Matrix (Fin D) (Fin D) ℂ)
  refine ⟨B, C, r, ρ, Λ, U, hρ, hr, hB_form, ?_, hB_unital, hScalar, ?_⟩
  · simpa [c] using hGauge
  · exact ⟨rfl, hSame, hΛ_pd, hΛ_diag, hC_unital, hΛ_fix⟩

private theorem scalar_fixedPoints_unitaryConj
    {D : ℕ}
    (A : MPSTensor d D)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hScalar :
      ∀ X : Matrix (Fin D) (Fin D) ℂ,
        transferMap (d := d) (D := D) A X = X →
          ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      transferMap (d := d) (D := D)
          (fun i =>
            (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i *
              (↑U : Matrix (Fin D) (Fin D) ℂ)) X = X →
        ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  intro X hX
  let V : Matrix (Fin D) (Fin D) ℂ := ↑U
  let Y : Matrix (Fin D) (Fin D) ℂ := V * X * Vᴴ
  have hVV : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.UnitaryGroup.star_mul_self U
  have hVV' : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem U.prop
  have hconj :
      transferMap (d := d) (D := D)
          (fun i =>
            (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i *
              (↑U : Matrix (Fin D) (Fin D) ℂ)) X =
        Vᴴ * transferMap (d := d) (D := D) A Y * V := by
    simpa [V, Y] using transferMap_unitaryConj (d := d) (D := D) A U X
  have hmiddle :
      Vᴴ * transferMap (d := d) (D := D) A Y * V = X := by
    calc
      Vᴴ * transferMap (d := d) (D := D) A Y * V
          = transferMap (d := d) (D := D)
              (fun i =>
                (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i *
                  (↑U : Matrix (Fin D) (Fin D) ℂ)) X := hconj.symm
      _ = X := hX
  have hYfix : transferMap (d := d) (D := D) A Y = Y := by
    calc
      transferMap (d := d) (D := D) A Y
          = (V * Vᴴ) * transferMap (d := d) (D := D) A Y * (V * Vᴴ) := by
              simp [hVV']
      _ = V * (Vᴴ * transferMap (d := d) (D := D) A Y * V) * Vᴴ := by
              simp [Matrix.mul_assoc]
      _ = V * X * Vᴴ := by rw [hmiddle]
      _ = Y := rfl
  obtain ⟨c, hc⟩ := hScalar Y hYfix
  refine ⟨c, ?_⟩
  calc
    X = (Vᴴ * V) * X * (Vᴴ * V) := by simp [hVV]
    _ = Vᴴ * Y * V := by simp [Y, Matrix.mul_assoc]
    _ = Vᴴ * (c • (1 : Matrix (Fin D) (Fin D) ℂ)) * V := by rw [hc]
    _ = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
          simp [hVV]

/-- **Blockwise PGVWC07 unital and dual-diagonal package.**

Pérez-García, Verstraete, Wolf, and Cirac, Theorem `Th:TIcanonical`, proof
lines 765--770 and 816--832, after the recursive invariant-subspace splitting
has already produced a nonzero irreducible block family.  The theorem applies
`exists_pgvwc07_unital_dualDiag_data_of_irreducible` to every block, records
the positive spectral-radius weights, and preserves the finite-ring MPV family
through the weighted direct sum.

This is still a prepared-block statement.  It does not start from an arbitrary
translation-invariant representation, does not separate all-zero blocks, and
does not prove the total bond-dimension bound of the full source theorem. -/
theorem exists_pgvwc07_unital_dualDiag_blockwise
    (A : MPSTensor d D)
    {r0 : ℕ} {dim0 : Fin r0 → ℕ}
    (blocks0 : (k : Fin r0) → MPSTensor d (dim0 k))
    (hIrr0 : ∀ k, IsIrreducibleTensor (blocks0 k))
    (hSame0 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0))
    (hNonzero0 : ∀ k, ∃ i, blocks0 k i ≠ 0) :
    ∃ r1 : ℕ,
      ∃ dim1 : Fin r1 → ℕ,
      ∃ μ1 : Fin r1 → ℂ,
      ∃ blocks1 : (k : Fin r1) → MPSTensor d (dim1 k),
        SameMPV₂ A
          (toTensorFromBlocks (d := d) (μ := μ1) blocks1) ∧
        (∀ k,
          ∃ Λ : Matrix (Fin (dim1 k)) (Fin (dim1 k)) ℂ,
            Λ.PosDef ∧
            Λ.IsDiag ∧
            (∑ i : Fin d, blocks1 k i * (blocks1 k i)ᴴ = 1) ∧
            transferMap (d := d) (D := dim1 k) (fun i => (blocks1 k i)ᴴ) Λ = Λ) ∧
        (∀ k,
          ∀ X : Matrix (Fin (dim1 k)) (Fin (dim1 k)) ℂ,
            transferMap (d := d) (D := dim1 k) (blocks1 k) X = X →
              ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim1 k)) (Fin (dim1 k)) ℂ)) ∧
        (∀ k, ∃ a : ℝ, 0 < a ∧ μ1 k = (a : ℂ)) ∧
        (∀ k, μ1 k ≠ 0) ∧
        (∀ k, 0 < dim1 k) := by
  classical
  have hdim0_ne : ∀ k : Fin r0, dim0 k ≠ 0 := by
    intro k hk0
    rcases hNonzero0 k with ⟨i, hi⟩
    have hzero : blocks0 k i = 0 := by
      ext a b
      exfalso
      have ha : (a : ℕ) < 0 := by
        simpa [hk0] using a.2
      omega
    exact hi hzero
  have hcanon :
      ∀ k : Fin r0,
        ∃ (B C : MPSTensor d (dim0 k))
          (r : ℝ)
          (ρ Λ : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ)
          (U : Matrix.unitaryGroup (Fin (dim0 k)) ℂ),
            ρ.PosDef ∧
            0 < r ∧
            (∀ i : Fin d,
              B i =
                (↑((Real.sqrt r)⁻¹) : ℂ) •
                  ((CFC.sqrt ρ)⁻¹ * blocks0 k i * CFC.sqrt ρ)) ∧
            GaugeEquiv (d := d) (D := dim0 k)
              (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • blocks0 k i) B ∧
            (∑ i : Fin d, B i * (B i)ᴴ = 1) ∧
            (∀ X : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ,
              transferMap (d := d) (D := dim0 k) B X = X →
                ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ)) ∧
            (let C' : MPSTensor d (dim0 k) :=
              fun i =>
                (↑U : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ)ᴴ * B i *
                  (↑U : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ);
              C = C' ∧
              SameMPV₂ B C ∧
              Λ.PosDef ∧
              Λ.IsDiag ∧
              (∑ i : Fin d, C i * (C i)ᴴ = 1) ∧
              transferMap (d := d) (D := dim0 k) (fun i => (C i)ᴴ) Λ = Λ) := by
    intro k
    letI : NeZero (dim0 k) := ⟨hdim0_ne k⟩
    exact exists_pgvwc07_unital_dualDiag_data_of_irreducible
      (A := blocks0 k) (hIrr := hIrr0 k) (hA := hNonzero0 k)
  choose blocksB blocks1 r1 ρ1 Λ1 U1 hρpd1 hrpos1 hform1 hGauge1 hUnitalB1
    hScalarB1 hFinal1 using hcanon
  let μ1 : Fin r0 → ℂ := fun k => (↑(Real.sqrt (r1 k)) : ℂ)
  have hSameBlocks :
      SameMPV₂
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0)
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1) := by
    intro N σ
    calc
      mpv (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0) σ
          = ∑ k : Fin r0, (1 : ℂ) ^ N * mpv (blocks0 k) σ := by
              simpa [smul_eq_mul] using
                (mpv_toTensorFromBlocks_eq_sum
                  (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) (A := blocks0) (σ := σ))
      _ = ∑ k : Fin r0, (μ1 k) ^ N * mpv (blocks1 k) σ := by
            refine Finset.sum_congr rfl ?_
            intro k _
            let c : ℂ := (↑((Real.sqrt (r1 k))⁻¹) : ℂ)
            have hGaugeSame : SameMPV (fun i => c • blocks0 k i) (blocksB k) :=
              GaugeEquiv.sameMPV (hGauge1 k)
            have hSameBC : SameMPV₂ (blocksB k) (blocks1 k) := (hFinal1 k).2.1
            have hscale : mpv (blocks1 k) σ = c ^ N * mpv (blocks0 k) σ := by
              calc
                mpv (blocks1 k) σ = mpv (blocksB k) σ := (hSameBC N σ).symm
                _ = mpv (fun i => c • blocks0 k i) σ := (hGaugeSame N σ).symm
                _ = c ^ N * mpv (blocks0 k) σ := mpv_smul c (blocks0 k) σ
            have hroot_ne : (↑(Real.sqrt (r1 k)) : ℂ) ≠ 0 := by
              exact_mod_cast (Real.sqrt_ne_zero'.mpr (hrpos1 k))
            have hμc : μ1 k * c = 1 := by
              dsimp [μ1, c]
              simp [hroot_ne]
            have hmulpow : (μ1 k) ^ N * c ^ N = 1 := by
              rw [← mul_pow, hμc, one_pow]
            have hmulpow_apply :
                (μ1 k) ^ N * (c ^ N * mpv (blocks0 k) σ) = mpv (blocks0 k) σ := by
              calc
                (μ1 k) ^ N * (c ^ N * mpv (blocks0 k) σ)
                    = ((μ1 k) ^ N * c ^ N) * mpv (blocks0 k) σ := by ring
                _ = mpv (blocks0 k) σ := by simp [hmulpow]
            calc
              (1 : ℂ) ^ N * mpv (blocks0 k) σ = mpv (blocks0 k) σ := by simp
              _ = (μ1 k) ^ N * (c ^ N * mpv (blocks0 k) σ) := hmulpow_apply.symm
              _ = (μ1 k) ^ N * mpv (blocks1 k) σ := by rw [hscale]
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ1) blocks1) σ := by
            symm
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μ1) (A := blocks1) (σ := σ))
  have hSame1 :
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := μ1) blocks1) := by
    intro N σ
    calc
      mpv A σ
          = mpv (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0) σ :=
              hSame0 N σ
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ1) blocks1) σ := hSameBlocks N σ
  have hΛData :
      ∀ k : Fin r0,
        ∃ Λ : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ,
          Λ.PosDef ∧
          Λ.IsDiag ∧
          (∑ i : Fin d, blocks1 k i * (blocks1 k i)ᴴ = 1) ∧
          transferMap (d := d) (D := dim0 k) (fun i => (blocks1 k i)ᴴ) Λ = Λ := by
    intro k
    exact ⟨Λ1 k, (hFinal1 k).2.2.1, (hFinal1 k).2.2.2.1,
      (hFinal1 k).2.2.2.2.1, (hFinal1 k).2.2.2.2.2⟩
  have hScalarC :
      ∀ k : Fin r0,
        ∀ X : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ,
          transferMap (d := d) (D := dim0 k) (blocks1 k) X = X →
            ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ) := by
    intro k
    have hCeq := (hFinal1 k).1
    rw [hCeq]
    exact scalar_fixedPoints_unitaryConj (d := d) (D := dim0 k)
      (blocksB k) (U1 k) (hScalarB1 k)
  have hμpos1 : ∀ k : Fin r0, ∃ a : ℝ, 0 < a ∧ μ1 k = (a : ℂ) := by
    intro k
    exact ⟨Real.sqrt (r1 k), Real.sqrt_pos.2 (hrpos1 k), rfl⟩
  have hμne1 : ∀ k : Fin r0, μ1 k ≠ 0 := by
    intro k
    dsimp [μ1]
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (hrpos1 k))
  have hDim1 : ∀ k : Fin r0, 0 < dim0 k := by
    intro k
    exact Nat.pos_of_ne_zero (hdim0_ne k)
  exact ⟨r0, dim0, μ1, blocks1, hSame1, hΛData, hScalarC, hμpos1, hμne1, hDim1⟩

/-- Blockwise Perron--Frobenius / TP-gauge stage for an irreducible block decomposition.

This theorem is the blockwise TP-normalization step used by
`exists_tp_gauge_from_arbitrary_with_zeroTail`, and it also gives the earlier
TP-normalization route on a fixed irreducible decomposition. Its extra
nonzero-block hypothesis lives on a chosen decomposition, so it still does not
by itself give an unconditional arbitrary-input theorem under the current
`SameMPV₂` relation. Concretely, every input block is assumed to have some
nonzero Kraus operator, excluding the all-zero scalar counterexample and
matching the hypotheses of the corresponding irreducible-to-TP result from
`Existence.lean`. It remains separate from the later normal-canonical-form theorem
in `NormalReduction/Main.lean`. -/
theorem exists_tp_gauge_blockwise
    (A : MPSTensor d D)
    {r0 : ℕ} {dim0 : Fin r0 → ℕ}
    (blocks0 : (k : Fin r0) → MPSTensor d (dim0 k))
    (hIrr0 : ∀ k, IsIrreducibleTensor (blocks0 k))
    (hSame0 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0))
    (hNonzero0 : ∀ k, ∃ i, blocks0 k i ≠ 0) :
    ∃ r1 : ℕ,
      ∃ dim1 : Fin r1 → ℕ,
      ∃ μ1 : Fin r1 → ℂ,
      ∃ blocks1 : (k : Fin r1) → MPSTensor d (dim1 k),
        SameMPV₂ A
          (toTensorFromBlocks (d := d) (μ := μ1) blocks1) ∧
        (∀ k, IsIrreducibleTensor (blocks1 k)) ∧
        (∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1) ∧
        (∀ k, μ1 k ≠ 0) ∧
        (∀ k, 0 < dim1 k) := by
  classical
  have hdim0_ne : ∀ k : Fin r0, dim0 k ≠ 0 := by
    intro k hk0
    rcases hNonzero0 k with ⟨i, hi⟩
    have hzero : blocks0 k i = 0 := by
      ext a b
      exfalso
      have ha : (a : ℕ) < 0 := by
        simpa [hk0] using a.2
      omega
    exact hi hzero
  have htp :
      ∀ k : Fin r0,
        ∃ (B : MPSTensor d (dim0 k)) (r : ℝ) (σ : Matrix (Fin (dim0 k)) (Fin (dim0 k)) ℂ),
          σ.PosDef ∧ 0 < r ∧
          (∀ i : Fin d,
            B i = CFC.sqrt σ *
              ((↑((Real.sqrt r)⁻¹) : ℂ) • blocks0 k i) * (CFC.sqrt σ)⁻¹) ∧
          (∑ i : Fin d, (B i)ᴴ * B i = 1) ∧
          GaugeEquiv (d := d) (D := dim0 k)
            (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • blocks0 k i) B := by
    intro k
    letI : NeZero (dim0 k) := ⟨hdim0_ne k⟩
    exact
      exists_tp_data_of_irreducible
        (A := blocks0 k) (hIrr := hIrr0 k) (hA := hNonzero0 k)
  choose blocks1 r1 σ1 hσpd1 hrpos1 hform1 hLeft1 hGauge1 using htp
  let μ1 : Fin r0 → ℂ := fun k => (↑(Real.sqrt (r1 k)) : ℂ)
  have hIrr1 : ∀ k : Fin r0, IsIrreducibleTensor (blocks1 k) := by
    intro k
    letI : NeZero (dim0 k) := ⟨hdim0_ne k⟩
    let c : ℂ := (↑((Real.sqrt (r1 k))⁻¹) : ℂ)
    have hroot_ne : (↑(Real.sqrt (r1 k)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (hrpos1 k))
    have hc_ne : c ≠ 0 := by
      dsimp [c]
      simp [hroot_ne]
    have hIrr_scaled :
        IsIrreducibleTensor (d := d) (D := dim0 k) (fun i => c • blocks0 k i) :=
      isIrreducibleTensor_smul (d := d) (D := dim0 k) hc_ne (blocks0 k) (hIrr0 k)
    have hIrr_gauge :
        IsIrreducibleTensor (d := d) (D := dim0 k)
          (tpGauge (d := d) (D := dim0 k) (fun i => c • blocks0 k i) (σ1 k)) :=
      isIrreducibleTensor_tpGauge_of_isIrreducibleTensor
        (d := d) (D := dim0 k)
        (A := fun i => c • blocks0 k i) (σ := σ1 k) (hσ := hσpd1 k) hIrr_scaled
    have hEq :
        blocks1 k = tpGauge (d := d) (D := dim0 k) (fun i => c • blocks0 k i) (σ1 k) := by
      funext i
      simpa [tpGauge, c] using hform1 k i
    simpa [hEq] using hIrr_gauge
  have hSameBlocks :
      SameMPV₂
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0)
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1) := by
    intro N σ
    calc
      mpv (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0) σ
          = ∑ k : Fin r0, (1 : ℂ) ^ N * mpv (blocks0 k) σ := by
              simpa [smul_eq_mul] using
                (mpv_toTensorFromBlocks_eq_sum
                  (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) (A := blocks0) (σ := σ))
      _ = ∑ k : Fin r0, (μ1 k) ^ N * mpv (blocks1 k) σ := by
            refine Finset.sum_congr rfl ?_
            intro k _
            let c : ℂ := (↑((Real.sqrt (r1 k))⁻¹) : ℂ)
            have hGaugeSame : SameMPV (fun i => c • blocks0 k i) (blocks1 k) :=
              GaugeEquiv.sameMPV (hGauge1 k)
            have hscale : mpv (blocks1 k) σ = c ^ N * mpv (blocks0 k) σ := by
              calc
                mpv (blocks1 k) σ = mpv (fun i => c • blocks0 k i) σ :=
                  (hGaugeSame N σ).symm
                _ = c ^ N * mpv (blocks0 k) σ := mpv_smul c (blocks0 k) σ
            have hroot_ne : (↑(Real.sqrt (r1 k)) : ℂ) ≠ 0 := by
              exact_mod_cast (Real.sqrt_ne_zero'.mpr (hrpos1 k))
            have hμc : μ1 k * c = 1 := by
              dsimp [μ1, c]
              simp [hroot_ne]
            have hmulpow : (μ1 k) ^ N * c ^ N = 1 := by
              rw [← mul_pow, hμc, one_pow]
            have hmulpow_apply :
                (μ1 k) ^ N * (c ^ N * mpv (blocks0 k) σ) = mpv (blocks0 k) σ := by
              calc
                (μ1 k) ^ N * (c ^ N * mpv (blocks0 k) σ)
                    = ((μ1 k) ^ N * c ^ N) * mpv (blocks0 k) σ := by ring
                _ = mpv (blocks0 k) σ := by simp [hmulpow]
            calc
              (1 : ℂ) ^ N * mpv (blocks0 k) σ = mpv (blocks0 k) σ := by simp
              _ = (μ1 k) ^ N * (c ^ N * mpv (blocks0 k) σ) := hmulpow_apply.symm
              _ = (μ1 k) ^ N * mpv (blocks1 k) σ := by rw [hscale]
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ1) blocks1) σ := by
            symm
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μ1) (A := blocks1) (σ := σ))
  have hSame1 :
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := μ1) blocks1) := by
    intro N σ
    calc
      mpv A σ
          = mpv (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0) σ :=
              hSame0 N σ
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ1) blocks1) σ := hSameBlocks N σ
  have hμne1 : ∀ k : Fin r0, μ1 k ≠ 0 := by
    intro k
    dsimp [μ1]
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (hrpos1 k))
  have hDim1 : ∀ k : Fin r0, 0 < dim0 k := by
    intro k
    exact Nat.pos_of_ne_zero (hdim0_ne k)
  exact ⟨r0, dim0, μ1, blocks1, hSame1, hIrr1, hLeft1, hμne1, hDim1⟩

/-!
## Zero-block separation and trace-preserving gauge threading

This section composes the zero-block separation from `Existence.lean` with the
blockwise Perron–Frobenius / TP-gauge theorem `exists_tp_gauge_blockwise`, producing an
arbitrary-input result: from any `A : MPSTensor d D`, we obtain:

* a zero-block dimension `zeroTailDim` (accumulating all-zero irreducible blocks --
  the Lean formalization uses "zero tail" as a bookkeeping name; the source paper says
  "there can be zero blocks"), and
* a TP-gauged family of irreducible blocks with nonzero weights.

The MPV relationship accounts exactly for both contributions:

  `mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ + mpv (toTensorFromBlocks μ blocks) σ`

This is the furthest unconditional arbitrary-input step available before periodicity removal and
the cyclic-sector and equal-weight arguments.
-/

/-- **Arbitrary-input trace-preserving gauge reduction.**

This combines the invariant-subspace splitting of arXiv:1606.00608,
lines 201-219, with zero-block separation and the canonical-form-II gauge
passage at lines 1058-1077 for the nonzero irreducible blocks.

From any `A : MPSTensor d D`, produce:
* a zero block of dimension `zeroTailDim` accumulating all-zero irreducible blocks
  (the paper calls these "zero blocks"; the Lean formalization uses "zero tail" as
  a bookkeeping name);
* TP-gauged irreducible blocks `blocks k` with nonzero weights `μ k`.

Every nonzero block satisfies:
* `IsIrreducibleTensor`;
* left-canonical normalization `∑ᵢ (Bᵢ)ᴴ Bᵢ = I`;
* positive bond dimension;
* nonzero weight.

The MPV of `A` equals the zero-block contribution plus the weighted nonzero-block sum.

**Scope restriction (translation-invariant canonical-form proof step):**
Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
lines 765--770 use a full-rank positive fixed point to gauge a block into the
unital orientation `∑ i, B i * (B i)ᴴ = 1`. This theorem supplies the dual
left-canonical trace-preserving orientation after the all-zero-block
separation. It is therefore not the full translation-invariant canonical form
theorem of Pérez-García, Verstraete, Wolf, and Cirac: it does not also prove the
source theorem's unital orientation, diagonal full-rank dual fixed points,
uniqueness of the identity fixed point, or total bond-dimension bound. The
boundary is recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem exists_tp_gauge_from_arbitrary_with_zeroTail (A : MPSTensor d D) :
    ∃ (zeroTailDim : ℕ) (r : ℕ) (dim : Fin r → ℕ)
      (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      (∀ k, IsIrreducibleTensor (blocks k)) ∧
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      (∀ k, μ k ≠ 0) ∧
      (∀ k, 0 < dim k) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ) := by
  classical
  -- Step 1: Obtain the zero-block-separated irreducible decomposition.
  obtain ⟨zeroTailDim, r₀, dim₀, blocks₀, hIrr₀, hNonzero₀, hDim₀, hMPV₀⟩ :=
    exists_irreducible_blockDecomp_nonzeroBlocks (d := d) (D := D) A
  -- Step 2: Apply blockwise TP gauge to the nonzero blocks.
  -- We feed `A_nonzero := toTensorFromBlocks μ=1 blocks₀` as the input tensor.
  -- The SameMPV₂ hypothesis for `exists_tp_gauge_blockwise` holds by reflexivity.
  let A_nonzero := toTensorFromBlocks (d := d) (μ := fun _ : Fin r₀ => (1 : ℂ)) blocks₀
  have hSame_refl : SameMPV₂ A_nonzero
      (toTensorFromBlocks (d := d) (μ := fun _ : Fin r₀ => (1 : ℂ)) blocks₀) :=
    fun _ _ => rfl
  obtain ⟨r₁, dim₁, μ₁, blocks₁, hSame₁, hIrr₁, hLeft₁, hμNe₁, hDim₁⟩ :=
    exists_tp_gauge_blockwise A_nonzero blocks₀ hIrr₀ hSame_refl hNonzero₀
  -- Step 3: Assemble the result.
  refine ⟨zeroTailDim, r₁, dim₁, μ₁, blocks₁, hIrr₁, hLeft₁, hμNe₁, hDim₁, ?_⟩
  -- The MPV relationship chains through the zero-block separation and TP gauge.
  intro N σ
  calc mpv A σ
      = mpv (zeroMPSTensor d zeroTailDim) σ + mpv A_nonzero σ := hMPV₀ N σ
    _ = mpv (zeroMPSTensor d zeroTailDim) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μ₁) blocks₁) σ := by
        congr 1
        exact hSame₁ N σ


end MPSTensor
