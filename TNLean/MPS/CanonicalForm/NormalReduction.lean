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
# Normal canonical form construction for primitive block decompositions

This file constructs normal canonical form from already-primitive block decompositions.

The main output is `MPSTensor.exists_normalCanonicalForm_of_primitive_blockDecomp`, which starts
from a weighted family of irreducible, left-canonical, primitive blocks with pairwise distinct
nonzero weight moduli and produces a blocked normal canonical form.

The intermediate private lemmas isolate the bookkeeping steps that remain valid under the current
API: a documentary TP-normalization stage for irreducible nonzero blocks, trivial blocking at
length `p = 1`, and sorting by decreasing weight norm.

Because `SameMPV₂` records the `N = 0` sector, zero irreducible scalar blocks cannot be discarded
without additional hypotheses. Combined with the post-blocking cyclic-sector / equal-weight issues,
this is why the file does not state an unconditional wrapper from an arbitrary tensor.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Nonzero scalar rescaling preserves tensor irreducibility. -/
private theorem isIrreducibleTensor_smul
    {D : ℕ} {c : ℂ} (hc : c ≠ 0)
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A) :
    IsIrreducibleTensor (d := d) (D := D) (fun i => c • A i) := by
  intro hHas
  apply hIrr
  rcases hHas with ⟨P, hPproj, hP0, hP1, hLower⟩
  refine ⟨P, hPproj, hP0, hP1, ?_⟩
  intro i
  have h : c • ((1 - P) * A i * P) = 0 := by
    calc
      c • ((1 - P) * A i * P) = (1 - P) * (c • A i) * P := by
        simp [Matrix.mul_assoc]
      _ = 0 := hLower i
  exact (smul_eq_zero.mp h).resolve_left hc

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

/-- Documentary blockwise Perron--Frobenius / TP-gauge stage for an irreducible block
decomposition.

This theorem is currently unused by the public endpoint below, which starts later from blocks that
are already primitive and left-canonical. We keep it as a public record of the earlier TP
normalization route: its extra nonzero-block hypothesis lives on a chosen decomposition, so it
still does not by itself give an unconditional arbitrary-input endpoint under the current `SameMPV₂`
interface. Concretely, every input block is assumed to have some nonzero Kraus operator, excluding
the all-zero scalar counterexample and matching the hypotheses of the
corresponding irreducible-to-TP wrapper from `Existence.lean`. -/
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

private noncomputable def singleBlockEquiv (d : ℕ) : Fin (blockPhysDim d 1) ≃ Fin d :=
  (Fintype.equivFin (Fin 1 → Fin d)).symm.trans (Equiv.funUnique (Fin 1) (Fin d))

@[simp] private lemma wordOfBlock_one (i : Fin (blockPhysDim d 1)) :
    wordOfBlock d 1 i = [singleBlockEquiv d i] := by
  rfl

@[simp] private lemma blockTensor_one_apply (A : MPSTensor d D) (i : Fin (blockPhysDim d 1)) :
    blockTensor (d := d) (D := D) A 1 i = A (singleBlockEquiv d i) := by
  simp [blockTensor, wordOfBlock_one, MPSTensor.evalWord]

@[simp] private lemma flattenBlockedWord_one (w : List (Fin (blockPhysDim d 1))) :
    flattenBlockedWord d 1 w = w.map (singleBlockEquiv d) := by
  induction w with
  | nil => simp [flattenBlockedWord]
  | cons i w ih => simp [flattenBlockedWord_cons, ih, wordOfBlock_one]

private lemma mpv_blockTensor_one (A : MPSTensor d D) {N : ℕ}
    (σ : Fin N → Fin (blockPhysDim d 1)) :
    mpv (blockTensor (d := d) (D := D) A 1) σ =
      mpv A (fun n => singleBlockEquiv d (σ n)) := by
  simp [mpv, coeff, evalWord_blockTensor, flattenBlockedWord_one, List.map_ofFn]
  rfl

private theorem isIrreducibleTensor_blockTensor_one
    (A : MPSTensor d D) (hIrr : IsIrreducibleTensor A) :
    IsIrreducibleTensor (d := blockPhysDim d 1) (D := D)
      (blockTensor (d := d) (D := D) A 1) := by
  intro hHas
  apply hIrr
  rcases hHas with ⟨P, hPproj, hP0, hP1, hLower⟩
  refine ⟨P, hPproj, hP0, hP1, ?_⟩
  intro j
  simpa using hLower ((singleBlockEquiv d).symm j)

private theorem leftCanonical_blockTensor_one
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∑ i : Fin (blockPhysDim d 1),
      (blockTensor (d := d) (D := D) A 1 i)ᴴ *
        blockTensor (d := d) (D := D) A 1 i = 1 := by
  simpa using leftCanonical_blockTensor (d := d) (D := D) (A := A) (L := 1) hLeft

/-- A primitive weighted block family with distinct weight norms is already in common blocking
length `p = 1`. -/
private theorem common_blocking_primitive
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, IsIrreducibleTensor (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := d) (D := dim1 k) (blocks1 k)))
    (hμnorm_ne1 : ∀ j k, j ≠ k → ‖μ1 j‖ ≠ ‖μ1 k‖)
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r2 : ℕ,
      ∃ dim2 : Fin r2 → ℕ,
      ∃ μ2 : Fin r2 → ℂ,
      ∃ blocks2 : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim2 k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2) ∧
        (∀ k, IsIrreducibleTensor (blocks2 k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks2 k i)ᴴ * blocks2 k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim2 k) (blocks2 k))) ∧
        (∀ j k, j ≠ k → ‖μ2 j‖ ≠ ‖μ2 k‖) ∧
        (∀ k, μ2 k ≠ 0) ∧
        (∀ k, 0 < dim2 k) := by
  refine ⟨1, Nat.one_pos, r1, dim1, μ1,
    (fun k => blockTensor (d := d) (D := dim1 k) (blocks1 k) 1), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N σ
    let σ' : Fin N → Fin d := fun n => singleBlockEquiv d (σ n)
    calc
      mpv (blockTensor (d := d) (D := D) A 1) σ = mpv A σ' :=
        mpv_blockTensor_one (d := d) (D := D) (A := A) σ
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ1) blocks1) σ' := hSame1 N σ'
      _ = ∑ k : Fin r1, (μ1 k) ^ N * mpv (blocks1 k) σ' := by
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μ1) (A := blocks1) (σ := σ'))
      _ = ∑ k : Fin r1, (μ1 k) ^ N * mpv (blockTensor (d := d) (D := dim1 k) (blocks1 k) 1) σ := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [mpv_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (σ := σ)]
      _ = mpv (toTensorFromBlocks
            (d := blockPhysDim d 1)
            (μ := μ1)
            (fun k => blockTensor (d := d) (D := dim1 k) (blocks1 k) 1)) σ := by
            symm
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d 1)
                (μ := μ1)
                (A := fun k => blockTensor (d := d) (D := dim1 k) (blocks1 k) 1)
                (σ := σ))
  · intro k
    exact isIrreducibleTensor_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (hIrr1 k)
  · intro k
    exact leftCanonical_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (hLeft1 k)
  · intro k
    simpa [MPSTensor.transferMap_blockTensor (A := blocks1 k) (L := 1)] using hPrim1 k
  · exact hμnorm_ne1
  · exact hμne1
  · exact hDim1

/-- Sort a primitive weighted block family by decreasing weight norm. -/
private theorem sort_blocks_by_weight_norm
    {p Dblk : ℕ}
    (Ablk : MPSTensor (blockPhysDim d p) Dblk)
    {r2 : ℕ} {dim2 : Fin r2 → ℕ}
    (μ2 : Fin r2 → ℂ)
    (blocks2 : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim2 k))
    (hSame2 :
      SameMPV₂ Ablk
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2))
    (hIrr2 : ∀ k, IsIrreducibleTensor (blocks2 k))
    (hLeft2 : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocks2 k i)ᴴ * blocks2 k i = 1)
    (hPrim2 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim2 k) (blocks2 k)))
    (hμnorm_ne2 : ∀ j k, j ≠ k → ‖μ2 j‖ ≠ ‖μ2 k‖)
    (hμne2 : ∀ k, μ2 k ≠ 0)
    (hDim2 : ∀ k, 0 < dim2 k) :
    ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂ Ablk
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
        StrictAnti (fun k : Fin r => ‖μ k‖) ∧
        (∀ k, μ k ≠ 0) ∧
        (∀ k, 0 < dim k) := by
  classical
  let f : Fin r2 → ℝ := fun k => ‖μ2 k‖
  have hf_inj : Function.Injective f := by
    intro j k hfk
    by_contra hjk
    exact hμnorm_ne2 j k hjk hfk
  let s : Finset ℝ := Finset.univ.image f
  have hs : s.card = r2 := by
    simpa [s] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin r2))) hf_inj)
  let vals : Fin r2 → ℝ := fun i => s.orderEmbOfFin hs (Fin.rev i)
  have hvals_strict : StrictAnti vals := by
    have hsmono : StrictMono (s.orderEmbOfFin hs) := (s.orderEmbOfFin hs).strictMono
    simpa [vals] using
      hsmono.comp_strictAnti (Fin.rev_strictAnti : StrictAnti (@Fin.rev r2))
  have hvals_mem : ∀ i : Fin r2, vals i ∈ s := by
    intro i
    dsimp [vals]
    exact Finset.orderEmbOfFin_mem s hs (Fin.rev i)
  have hex : ∀ i : Fin r2, ∃ k : Fin r2, f k = vals i := by
    intro i
    have hmem : vals i ∈ Finset.univ.image f := by
      simpa [s] using hvals_mem i
    rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
    exact ⟨k, hk⟩
  let e₀ : Fin r2 → Fin r2 := fun i => Classical.choose (hex i)
  have he₀_spec : ∀ i : Fin r2, f (e₀ i) = vals i := by
    intro i
    exact Classical.choose_spec (hex i)
  have he₀_inj : Function.Injective e₀ := by
    intro i j hij
    have hvals_eq : vals i = vals j := by
      calc
        vals i = f (e₀ i) := (he₀_spec i).symm
        _ = f (e₀ j) := by simp [hij]
        _ = vals j := he₀_spec j
    exact hvals_strict.injective hvals_eq
  let e : Fin r2 ≃ Fin r2 :=
    Equiv.ofBijective e₀ ⟨he₀_inj, Finite.surjective_of_injective he₀_inj⟩
  have he_spec : ∀ i : Fin r2, f (e i) = vals i := by
    intro i
    exact he₀_spec i
  let dim : Fin r2 → ℕ := fun i => dim2 (e i)
  let μ : Fin r2 → ℂ := fun i => μ2 (e i)
  let blocks : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim k) :=
    fun i => blocks2 (e i)
  refine ⟨r2, dim, μ, blocks, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N σ
    calc
      mpv Ablk σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2) σ := hSame2 N σ
      _ = ∑ k : Fin r2, (μ2 k) ^ N * mpv (blocks2 k) σ := by
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d p) (μ := μ2) (A := blocks2) (σ := σ))
      _ = ∑ i : Fin r2, (μ2 (e i)) ^ N * mpv (blocks2 (e i)) σ := by
            symm
            simpa using (e.sum_comp (fun k : Fin r2 => (μ2 k) ^ N * mpv (blocks2 k) σ))
      _ = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) σ := by
            symm
            simpa [μ, blocks, smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d p) (μ := μ) (A := blocks) (σ := σ))
  · intro i
    exact hIrr2 (e i)
  · intro i
    exact hLeft2 (e i)
  · intro i
    exact hPrim2 (e i)
  · intro i j hij
    have hi : ‖μ i‖ = vals i := by
      simpa [μ, f] using he_spec i
    have hj : ‖μ j‖ = vals j := by
      simpa [μ, f] using he_spec j
    calc
      ‖μ j‖ = vals j := hj
      _ < vals i := hvals_strict hij
      _ = ‖μ i‖ := hi.symm
  · intro i
    exact hμne2 (e i)
  · intro i
    exact hDim2 (e i)

/-- Package a primitive weighted block family into separated blocked data for
`IsNormalCanonicalForm`. -/
private theorem exists_blocked_normal_data_of_primitive_blockDecomp
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, IsIrreducibleTensor (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := d) (D := dim1 k) (blocks1 k)))
    (hμnorm_ne1 : ∀ j k, j ≠ k → ‖μ1 j‖ ≠ ‖μ1 k‖)
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
        StrictAnti (fun k : Fin r => ‖μ k‖) ∧
        (∀ k, μ k ≠ 0) ∧
        (∀ k, 0 < dim k) := by
  obtain ⟨p, hp, r2, dim2, μ2, blocks2, hSame2, hIrr2, hLeft2, hPrim2, hμnorm_ne2, hμne2,
      hDim2⟩ :=
    common_blocking_primitive
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hPrim1 hμnorm_ne1 hμne1 hDim1
  obtain ⟨r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    sort_blocks_by_weight_norm
      (d := d)
      (p := p)
      (Ablk := blockTensor (d := d) (D := D) A p)
      (r2 := r2) (dim2 := dim2) (μ2 := μ2) blocks2
      hSame2 hIrr2 hLeft2 hPrim2 hμnorm_ne2 hμne2 hDim2
  exact ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩

/-- A primitive weighted block decomposition admits a blocked normal canonical form.

Hypotheses:

* `A` is `SameMPV₂`-equivalent to the weighted block tensor `toTensorFromBlocks μ1 blocks1`;
* each block `blocks1 k` is irreducible;
* each block is left-canonical: `∑ i, (blocks1 k i)ᴴ * blocks1 k i = 1`;
* each block transfer map is primitive;
* the weight norms `‖μ1 k‖` are pairwise distinct;
* each weight `μ1 k` is nonzero;
* each bond dimension `dim1 k` is positive.

Conclusion: after a common blocking (currently `p = 1`) and reordering by decreasing weight norm,
`blockTensor A p` is `SameMPV₂`-equivalent to a weighted block family in
`IsNormalCanonicalForm`. -/
theorem exists_normalCanonicalForm_of_primitive_blockDecomp
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, IsIrreducibleTensor (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := d) (D := dim1 k) (blocks1 k)))
    (hμnorm_ne1 : ∀ j k, j ≠ k → ‖μ1 j‖ ≠ ‖μ1 k‖)
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        IsNormalCanonicalForm (d := blockPhysDim d p) μ blocks := by
  obtain ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    exists_blocked_normal_data_of_primitive_blockDecomp
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hPrim1 hμnorm_ne1 hμne1 hDim1
  refine ⟨p, hp, r, dim, μ, blocks, hSame, ?_⟩
  let hμ : HasStrictOrderedNonzeroWeights μ := {
    mu_strict_anti := hμanti
    mu_ne_zero := hμne
  }
  exact
    IsNormalCanonicalForm.ofStrictSeparatedData
      (d := blockPhysDim d p)
      (A := blocks)
      (μ := μ)
      (HasIrreducibleBlocks.ofForall hIrr)
      (IsLeftCanonicalBlockFamily.ofForall hLeft)
      (HasPrimitiveBlocks.ofForall hPrim)
      hμ
      hDim

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
cyclic-sector / equal-weight bookkeeping.
-/

/-- **Arbitrary-input TP-gauge reduction (1606.00608 §2.3 + App. A, with zero-block separation).**

From any `A : MPSTensor d D`, produce:
* a zero-tail of dimension `zeroTailDim` accumulating all-zero irreducible blocks;
* TP-gauged irreducible blocks `blocks k` with nonzero weights `μ k`.

Every live block satisfies:
* `IsIrreducibleTensor`;
* left-canonical normalization `∑ᵢ (Bᵢ)ᴴ Bᵢ = I`;
* positive bond dimension;
* nonzero weight.

The MPV of `A` equals the zero-tail contribution plus the weighted live-block sum. -/
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
    exists_irreducible_blockDecomp_liveBlocks (d := d) (D := D) A
  -- Step 2: Apply blockwise TP gauge to the live blocks.
  -- We feed `A_live := toTensorFromBlocks μ=1 blocks₀` as the input tensor.
  -- The SameMPV₂ hypothesis for `exists_tp_gauge_blockwise` holds by reflexivity.
  let A_live := toTensorFromBlocks (d := d) (μ := fun _ : Fin r₀ => (1 : ℂ)) blocks₀
  have hSame_refl : SameMPV₂ A_live
      (toTensorFromBlocks (d := d) (μ := fun _ : Fin r₀ => (1 : ℂ)) blocks₀) :=
    fun _ _ => rfl
  obtain ⟨r₁, dim₁, μ₁, blocks₁, hSame₁, hIrr₁, hLeft₁, hμNe₁, hDim₁⟩ :=
    exists_tp_gauge_blockwise A_live blocks₀ hIrr₀ hSame_refl hNonzero₀
  -- Step 3: Assemble the result.
  refine ⟨zeroTailDim, r₁, dim₁, μ₁, blocks₁, hIrr₁, hLeft₁, hμNe₁, hDim₁, ?_⟩
  -- The MPV relationship chains through the zero-block separation and TP gauge.
  intro N σ
  calc mpv A σ
      = mpv (zeroMPSTensor d zeroTailDim) σ + mpv A_live σ := hMPV₀ N σ
    _ = mpv (zeroMPSTensor d zeroTailDim) σ +
          mpv (toTensorFromBlocks (d := d) (μ := μ₁) blocks₁) σ := by
        congr 1
        exact hSame₁ N σ

/-!
## Scope of this file

This file collects the construction of normal canonical form from primitive weighted block decompositions and provides
the unconditional arbitrary-input TP-gauge reduction (with zero-block separation).

A full wrapper to the endpoint canonical form would still require:
* periodicity removal by blocking (applying the irreducible-to-primitive blocking theorem to each
  TP-gauged block);
* cyclic-sector decomposition after blocking;
* equal-weight merging or grouping for strict weight ordering.
-/

end MPSTensor
