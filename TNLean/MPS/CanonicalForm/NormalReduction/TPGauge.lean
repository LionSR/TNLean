/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Algebra.MatrixFunctionalCalculus
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
* `MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail` — the corresponding
  arbitrary-input result obtained after zero-block separation.

The auxiliary declarations stay file-local because they are elementary lemmas for
rescaling, gauge transport, and the final zero-tail identity.
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

/-- Blockwise Perron--Frobenius / TP-gauge stage for an irreducible block decomposition.

This theorem is the blockwise TP-normalization step used by
`exists_tp_gauge_from_arbitrary_with_zeroTail`, and it also gives the earlier
TP-normalization route on a fixed irreducible decomposition. Its extra
nonzero-block hypothesis lives on a chosen decomposition, so it still does not
by itself give an unconditional arbitrary-input theorem under the current
`SameMPV₂` interface. Concretely, every input block is assumed to have some
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
                mpv (blocks1 k) σ = mpv (fun i => c • blocks0 k i) σ := by
                  exact (hGaugeSame N σ).symm
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
## Zero-block separation + TP gauge threading (1606.00608 §2.3 + App. A)

This section composes the zero-block separation from `Existence.lean` with the
blockwise Perron–Frobenius / TP-gauge theorem `exists_tp_gauge_blockwise`, producing an
arbitrary-input result: from any `A : MPSTensor d D`, we obtain:

* a zero-tail dimension `zeroTailDim` (accumulating all-zero irreducible blocks), and
* a TP-gauged family of irreducible blocks with nonzero weights.

The MPV relationship accounts exactly for both contributions:

  `mpv A σ = mpv (zeroMPSTensor d zeroTailDim) σ + mpv (toTensorFromBlocks μ blocks) σ`

This is the furthest unconditional arbitrary-input step available before periodicity removal and
the cyclic-sector and equal-weight arguments.
-/

/-- **Arbitrary-input TP-gauge reduction (1606.00608 §2.3 + App. A, with zero-block separation).**

From any `A : MPSTensor d D`, produce:
* a zero-tail of dimension `zeroTailDim` accumulating all-zero irreducible blocks;
* TP-gauged irreducible blocks `blocks k` with nonzero weights `μ k`.

Every nonzero block satisfies:
* `IsIrreducibleTensor`;
* left-canonical normalization `∑ᵢ (Bᵢ)ᴴ Bᵢ = I`;
* positive bond dimension;
* nonzero weight.

The MPV of `A` equals the zero-tail contribution plus the weighted nonzero-block sum. -/
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
