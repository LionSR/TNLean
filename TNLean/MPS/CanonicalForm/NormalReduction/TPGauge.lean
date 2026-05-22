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

* `MPSTensor.exists_tp_gauge_blockwise` — blockwise Perron--Frobenius / TP-gauge
  normalization for an irreducible block decomposition.
* `MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail` — the arbitrary-input
  TP-gauge normalization, keeping the explicit zero-block summand.  This is the
  TP-gauge result consumed by `SectorComparison/` to supply the trace-preserving
  block decomposition used in Chapter~12 of the blueprint.
* The source-faithful PGVWC07 unital and dual-diagonal chain:
  `MPSTensor.exists_pgvwc07_unital_dualDiag_data_of_irreducible` (single
  irreducible block), then
  `MPSTensor.exists_pgvwc07_unital_dualDiag_blockwise` (blockwise composition),
  then
  `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail`
  (arbitrary input with explicit zero summand), then
  `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound`
  (length-zero dimension identity), then
  `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound`
  (positive-length form).
* The structure `MPSTensor.PGVWC07PositiveLengthWitness` and the
  witness-existence theorem `MPSTensor.exists_pgvwc07_positiveLengthWitness`,
  which bundle the positive-length form for use in `WeightNormalization.lean`.

These declarations correspond one-to-one to the intermediate construction
steps of \cite[Theorem~Th:TIcanonical]{PerezGarcia2007Matrix} and are exposed
in the blueprint as the source-faithful PGVWC07 chain.

The remaining declarations in this file (gauge-transport and irreducibility
preservation lemmas, the scalar fixed-point unitary-conjugation transport)
remain `private`: they are elementary supporting lemmas with no external
mathematical role.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Witness for the exact positive-length form of the PGVWC07
translation-invariant canonical-form construction.

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
lines 742--763, for nonempty rings and exact MPV equality.  The fields record
the weighted nonzero-block direct sum, the unital block condition, the
diagonal positive-definite dual fixed point, the scalar fixed-point conclusion,
positive weights, positive block dimensions, and the total bond-dimension
bound.

This witness is the unnormalized positive-length form.  The source theorem also
writes the weights with `1 ≥ λ_j > 0`, after the proof says that the spectral
radius is normalized without loss of generality at lines 765--766.  That global
normalization is supplied by the finite-family weight-normalization theorem.
The positive-length convention is recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
structure PGVWC07PositiveLengthWitness (A : MPSTensor d D) where
  /-- Number of nonzero canonical blocks. -/
  r : ℕ
  /-- Bond dimension of each nonzero canonical block. -/
  dim : Fin r → ℕ
  /-- Positive block weights. -/
  weights : Fin r → ℂ
  /-- Nonzero canonical blocks in the unital orientation. -/
  blocks : (k : Fin r) → MPSTensor d (dim k)
  /-- Each block has a diagonal positive-definite fixed point for the adjoint
  transfer map and satisfies the unital condition. -/
  dual_fixed :
    ∀ k,
      ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
        Λ.PosDef ∧
        Λ.IsDiag ∧
        (∑ i : Fin d, blocks k i * (blocks k i)ᴴ = 1) ∧
        transferMap (d := d) (D := dim k) (fun i => (blocks k i)ᴴ) Λ = Λ
  /-- The fixed points of each block transfer map are exactly the scalar
  multiples of the identity. -/
  scalar_fixed :
    ∀ k,
      ∀ X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
        transferMap (d := d) (D := dim k) (blocks k) X = X →
          ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
  /-- Every block weight is a positive real number, embedded into `ℂ`. -/
  weight_pos : ∀ k, ∃ a : ℝ, 0 < a ∧ weights k = (a : ℂ)
  /-- Every nonzero block has positive bond dimension. -/
  dim_pos : ∀ k, 0 < dim k
  /-- On nonempty rings, the original tensor and the weighted block tensor have
  the same MPV coefficients. -/
  sameMPV_pos : SameMPV₂Pos A (toTensorFromBlocks (d := d) (μ := weights) blocks)
  /-- The total bond dimension of the nonzero canonical blocks is at most the
  original bond dimension. -/
  bondDim_le : ∑ k : Fin r, dim k ≤ D

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

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, proof
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

/-- **Blockwise PGVWC07 unital and dual-diagonal theorem.**

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, proof
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
## Zero-block separation and blockwise gauge threading

This section composes the zero-block separation from `Existence.lean` with the
blockwise Perron--Frobenius gauge theorems above, producing arbitrary-input
results: from any `A : MPSTensor d D`, we obtain:

* a zero-block dimension `zeroTailDim`, equal to the total bond dimension of the
  all-zero irreducible blocks, and
* a weighted family of nonzero blocks in either the PGVWC07 unital orientation
  with dual-diagonal fixed points or the older TP-gauge orientation.

The MPV relationship accounts exactly for both contributions:

  `mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ + mpv (toTensorFromBlocks μ blocks) σ`

The PGVWC07 unital statement below is the strongest unconditional arbitrary-input
step available here before the final total bond-dimension bound is threaded
through the construction.
-/

/-- **Arbitrary-input PGVWC07 unital dual-diagonal form with zero blocks.**

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, proof
lines 765--770 and 816--832, after the recursive invariant-subspace splitting
and all-zero-block separation have been carried out.  From any tensor `A`, the
theorem separates a zero-block contribution and applies
`exists_pgvwc07_unital_dualDiag_blockwise` to the remaining nonzero irreducible
blocks.

Every nonzero output block is in the source's unital orientation
`∑ i, C i * (C i)ᴴ = 1`, has only scalar fixed points for its transfer map, and
has a diagonal positive-definite fixed point for the adjoint transfer map.  The
weights are positive real spectral-radius weights, and the MPV family of `A`
is the sum of the zero-block contribution and the weighted nonzero-block
direct sum.

**Scope restriction:** This is still not the full Th:TIcanonical statement:
the zero block is kept explicitly, and the final total bond-dimension bound is
not included.  The boundary is recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail
    (A : MPSTensor d D) :
    ∃ (zeroTailDim : ℕ) (r : ℕ) (dim : Fin r → ℕ)
      (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      (∀ k,
        ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          Λ.PosDef ∧
          Λ.IsDiag ∧
          (∑ i : Fin d, blocks k i * (blocks k i)ᴴ = 1) ∧
          transferMap (d := d) (D := dim k) (fun i => (blocks k i)ᴴ) Λ = Λ) ∧
      (∀ k,
        ∀ X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          transferMap (d := d) (D := dim k) (blocks k) X = X →
            ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) ∧
      (∀ k, ∃ a : ℝ, 0 < a ∧ μ k = (a : ℂ)) ∧
      (∀ k, μ k ≠ 0) ∧
      (∀ k, 0 < dim k) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ) := by
  classical
  obtain ⟨zeroTailDim, r₀, dim₀, blocks₀, hIrr₀, hNonzero₀, _hDim₀, hMPV₀⟩ :=
    exists_irreducible_blockDecomp_nonzeroBlocks (d := d) (D := D) A
  let A_nonzero := toTensorFromBlocks (d := d) (μ := fun _ : Fin r₀ => (1 : ℂ)) blocks₀
  have hSame_refl : SameMPV₂ A_nonzero
      (toTensorFromBlocks (d := d) (μ := fun _ : Fin r₀ => (1 : ℂ)) blocks₀) :=
    fun _ _ => rfl
  obtain ⟨r₁, dim₁, μ₁, blocks₁, hSame₁, hΛData₁, hScalar₁, hμPos₁, hμNe₁,
    hDim₁⟩ :=
    exists_pgvwc07_unital_dualDiag_blockwise A_nonzero blocks₀ hIrr₀ hSame_refl
      hNonzero₀
  refine ⟨zeroTailDim, r₁, dim₁, μ₁, blocks₁, hΛData₁, hScalar₁, hμPos₁, hμNe₁,
    hDim₁, ?_⟩
  intro N σ
  calc
    mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ + mpv A_nonzero σ := hMPV₀ N σ
    _ = mpv (zeroMPSTensor d zeroTailDim) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μ₁) blocks₁) σ := by
        congr 1
        exact hSame₁ N σ

/-- **Bond-dimension identity for the arbitrary-input PGVWC07 zero-block form.**

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, lines
761--762, after the zero-block contribution has been retained explicitly.
The length-zero coefficient of the MPV identity gives
$D_0 + \sum_k D_k = D$; therefore the total bond dimension of the nonzero
blocks is at most the original bond dimension.

**Scope restriction:** This theorem still keeps the zero block as an explicit
summand.  Removing the explicit zero-block summand from the existential
conclusion is the remaining statement-level step, recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound
    (A : MPSTensor d D) :
    ∃ (zeroTailDim : ℕ) (r : ℕ) (dim : Fin r → ℕ)
      (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      (∀ k,
        ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          Λ.PosDef ∧
          Λ.IsDiag ∧
          (∑ i : Fin d, blocks k i * (blocks k i)ᴴ = 1) ∧
          transferMap (d := d) (D := dim k) (fun i => (blocks k i)ᴴ) Λ = Λ) ∧
      (∀ k,
        ∀ X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          transferMap (d := d) (D := dim k) (blocks k) X = X →
            ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) ∧
      (∀ k, ∃ a : ℝ, 0 < a ∧ μ k = (a : ℂ)) ∧
      (∀ k, μ k ≠ 0) ∧
      (∀ k, 0 < dim k) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ) ∧
      zeroTailDim + ∑ k : Fin r, dim k = D ∧
      ∑ k : Fin r, dim k ≤ D := by
  classical
  obtain ⟨zeroTailDim, r, dim, μ, blocks, hΛ, hScalar, hμPos, hμNe, hDim, hMPV⟩ :=
    exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail (d := d) (D := D) A
  let σ0 : Fin 0 → Fin d := Fin.elim0
  have hZero :
      (D : ℂ) = (zeroTailDim + ∑ k : Fin r, dim k : ℕ) := by
    calc
      (D : ℂ) = mpv A σ0 := (mpv_zero_length A σ0).symm
      _ = mpv (zeroMPSTensor d zeroTailDim) σ0 +
            mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ0 := hMPV 0 σ0
      _ = (zeroTailDim : ℂ) + (∑ k : Fin r, dim k : ℂ) := by
            simp
      _ = (zeroTailDim + ∑ k : Fin r, dim k : ℕ) := by
            simp
  have hBond : zeroTailDim + ∑ k : Fin r, dim k = D := by
    exact_mod_cast hZero.symm
  have hBound : ∑ k : Fin r, dim k ≤ D := by
    omega
  exact ⟨zeroTailDim, r, dim, μ, blocks, hΛ, hScalar, hμPos, hμNe, hDim, hMPV,
    hBond, hBound⟩

/-- **Positive-length PGVWC07 unital dual-diagonal form.**

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical, lines
761--762 and 816--832.  This is the zero-block theorem above after omitting the
explicit zero summand from the displayed MPV identity.  The omission is valid for
nonempty rings because the all-zero summand has zero MPV coefficient in positive
length.

The theorem keeps the mathematically relevant bond-dimension estimate
\(\sum_k D_k\leq D\).  The canonical-form existence theorem is stated with this
positive-length convention; the explicit zero-block theorem records the
length-zero bookkeeping separately. -/
theorem exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound
    (A : MPSTensor d D) :
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      (∀ k,
        ∃ Λ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          Λ.PosDef ∧
          Λ.IsDiag ∧
          (∑ i : Fin d, blocks k i * (blocks k i)ᴴ = 1) ∧
          transferMap (d := d) (D := dim k) (fun i => (blocks k i)ᴴ) Λ = Λ) ∧
      (∀ k,
        ∀ X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          transferMap (d := d) (D := dim k) (blocks k) X = X →
            ∃ c : ℂ, X = c • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) ∧
      (∀ k, ∃ a : ℝ, 0 < a ∧ μ k = (a : ℂ)) ∧
      (∀ k, 0 < dim k) ∧
      SameMPV₂Pos A (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      ∑ k : Fin r, dim k ≤ D := by
  classical
  obtain ⟨zeroTailDim, r, dim, μ, blocks, hΛ, hScalar, hμPos, _hμNe, hDim, hMPV,
    _hBond, hBound⟩ :=
    exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound
      (d := d) (D := D) A
  refine ⟨r, dim, μ, blocks, hΛ, hScalar, hμPos, hDim, ?_, hBound⟩
  intro N hN σ
  calc
    mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ +
        mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := hMPV N σ
    _ = 0 + mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
        rw [mpv_zeroMPSTensor]
        simp [Nat.ne_of_gt hN]
    _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
        simp

/-- **Structured positive-length PGVWC07 canonical-form witness.**

Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
lines 742--763, after omitting the explicit zero block from positive-length
MPV coefficients.  This theorem is the corresponding structured form of
`exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound`.

This is the unnormalized positive-length witness.  The source theorem's
normalization `1 ≥ λ_j > 0` is supplied later by the finite-family
weight-normalization theorem, following the global spectral-radius
normalization convention from lines 765--766.
The positive-length convention is recorded in
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem exists_pgvwc07_positiveLengthWitness
    (A : MPSTensor d D) :
    Nonempty (PGVWC07PositiveLengthWitness (d := d) (D := D) A) := by
  classical
  obtain ⟨r, dim, μ, blocks, hΛ, hScalar, hμPos, hDim, hSame, hBound⟩ :=
    exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound
      (d := d) (D := D) A
  exact ⟨
    { r := r
      dim := dim
      weights := μ
      blocks := blocks
      dual_fixed := hΛ
      scalar_fixed := hScalar
      weight_pos := hμPos
      dim_pos := hDim
      sameMPV_pos := hSame
      bondDim_le := hBound }⟩

/-- **Arbitrary-input trace-preserving gauge reduction.**

This combines the invariant-subspace splitting of arXiv:1606.00608,
lines 201-219, with zero-block separation and the canonical-form-II gauge
passage at lines 1058-1077 for the nonzero irreducible blocks.

From any `A : MPSTensor d D`, produce:
* a zero block of dimension `zeroTailDim`, equal to the total bond dimension of
  the all-zero irreducible blocks;
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
left-canonical trace-preserving orientation after the all-zero-block separation.
The PGVWC07 unital-orientation analogue is
`exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail` above.  This
theorem remains useful as a TP-gauge reduction, but it is not the canonical-form
statement matching PGVWC07 Theorem Th:TIcanonical.  The boundary is recorded in
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
