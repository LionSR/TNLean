/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Channel.CyclicDecomposition
import TNLean.MPS.Blocking
import TNLean.MPS.CanonicalFormExistence1606
import TNLean.MPS.TransferNormalization
import TNLean.PiAlgebra.CanonicalFormSep

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Normal canonical form existence pipeline

This file records the intended end-to-end assembly

$$A \leadsto \text{irreducible blocks} \leadsto \text{left-canonical / TP gauge}
   \leadsto \text{period blocking + cyclic sector decomposition}
   \leadsto \text{IsNormalCanonicalForm}.$$

The key point is that the periodicity-removal step changes the physical dimension from `d` to
`d^p = blockPhysDim d p`. Consequently, the clean existence statement is formulated **after a
common physical blocking** of the original tensor.

At present the file provides:

* a blockwise Perron--Frobenius / TP-gauge step under an explicit nonzero-block hypothesis,
* a family-level blocked-primitive handoff theorem (still incomplete), and
* a proved final sorting theorem `weight_assignment` for a blocked primitive family whose weight
  moduli are already pairwise distinct.

Because `SameMPV₂` remembers the `N = 0` sector, zero irreducible scalar blocks cannot simply be
thrown away. Consequently the unconditional wrapper from an arbitrary tensor `A` is **not** stated
here: the current reduction API does not rule out such blocks. The public theorem below is therefore
formulated relative to a chosen irreducible block decomposition with every block explicitly nonzero.
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

/-- Blockwise Perron--Frobenius / TP gauge step for an irreducible block decomposition.

Compared with the original version, we explicitly assume that every input block has some nonzero
Kraus operator. This excludes the all-zero scalar counterexample and is exactly the hypothesis
needed by `exists_tp_data_of_irreducible_pipeline1606`. -/
private theorem tp_gauge_blockwise
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
      exists_tp_data_of_irreducible_pipeline1606
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

/-- Single-block bridge from Wolf Theorem 6.6 to the normal-form pipeline.

Starting from a left-canonical irreducible block, first use
`exists_blockTensor_isPrimitive_pipeline1606` to find a period. Then apply
`exists_cyclic_decomposition_of_irreducible_schwarz` together with
`isIrreducible_restriction_of_cyclic_decomp` and
`isPrimitive_restriction_of_cyclic_decomp` to split the blocked tensor into primitive
irreducible sectors. The output is repackaged as a finite block family with unit weights. -/
private theorem cyclic_redecomp_to_NT
    [NeZero D]
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleTensor A)
    (hDim : 0 < D) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks
            (d := blockPhysDim d p)
            (μ := fun _ : Fin r => (1 : ℂ))
            blocks) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
        (∀ k, 0 < dim k) := by
  /-
  Missing bridge, not just local tactic work:

  * `exists_blockTensor_isPrimitive_pipeline1606` only yields peripheral-spectrum primitivity of
    `transferMap (blockTensor A p)`.
  * `CyclicDecomposition.lean` currently proves irreducibility / primitivity for the abstract
    corner restrictions `cornerRestriction (P k) (T ^ m) ...`, not for concrete MPS tensors.
  * To finish this theorem one still needs a substantial construction turning the cyclic
    projections into actual blocked Kraus families `blocks k`, together with:
      1. a `SameMPV₂` decomposition of `blockTensor A p` into those sectors, and
      2. an identification of each sector transfer map with the corresponding corner restriction.

  So the remaining gap here is a missing formal API between Wolf's cyclic decomposition and the
  MPS block constructor, not an isolated unfinished tactic proof.
  -/
  sorry

/-- Family-level periodicity removal, cyclic re-decomposition, and equal-weight consolidation.

This maps `cyclic_redecomp_to_NT` over the TP-gauged irreducible blocks, chooses a common
blocking length, reblocks all sector tensors to the same physical dimension, concatenates the
resulting families, and is also the designated place where equal-modulus weights must be merged (or
otherwise eliminated) before the final sorting step. Accordingly the conclusion now includes the
pairwise-distinctness certificate needed by `weight_assignment`. -/
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
  /-
  This family-level theorem depends on the missing single-block sector construction above and then
  adds a second layer of genuinely nontrivial bookkeeping:

  * choose a common blocking length from the blockwise witnesses,
  * compare iterated blocking with reblocking of each sector family,
  * concatenate the resulting families while transporting all dependent dimensions,
  * thread `SameMPV₂` through the entire direct-sum / weight bookkeeping, and
  * merge or otherwise eliminate equal-modulus sectors so that the final family has pairwise
    distinct weight norms.

  Without a concrete proof of `cyclic_redecomp_to_NT`, this theorem cannot currently be completed;
  even after that, one still needs additional lemmas about common blocking, concatenation of block
  families, and the equal-weight merging step.
  -/
  sorry

/-- Final strict-weight packaging step.

The only new input compared with the original version is the explicit pairwise-distinctness
hypothesis on the weight moduli. Under that assumption, the theorem simply sorts the blocks by
`‖μ2 k‖` in decreasing order and reindexes the family. -/
private theorem weight_assignment
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

/-- Handoff lemma isolating the remaining gap after the irreducible block decomposition.

Starting from a fixed irreducible block decomposition of `A` whose blocks are all nonzero, the
remaining assembly tasks are now split into the helper lemmas `tp_gauge_blockwise`,
`cyclic_redecomp_to_NT`, `common_blocking_primitive`, and `weight_assignment`. The present theorem
simply composes those stages into the separated data needed for `IsNormalCanonicalForm`. -/
private theorem exists_blocked_normal_data_of_irreducible_blockDecomp
    (A : MPSTensor d D)
    {r0 : ℕ} {dim0 : Fin r0 → ℕ}
    (blocks0 : (k : Fin r0) → MPSTensor d (dim0 k))
    (hIrr0 : ∀ k, IsIrreducibleTensor (blocks0 k))
    (hSame0 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0))
    (hNonzero0 : ∀ k, ∃ i, blocks0 k i ≠ 0) :
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
  obtain ⟨r1, dim1, μ1, blocks1, hSame1, hIrr1, hLeft1, hμne1, hDim1⟩ :=
    tp_gauge_blockwise (A := A) (r0 := r0) (dim0 := dim0)
      blocks0 hIrr0 hSame0 hNonzero0
  obtain ⟨p, hp, r2, dim2, μ2, blocks2, hSame2, hIrr2, hLeft2, hPrim2, hμnorm_ne2, hμne2,
      hDim2⟩ :=
    common_blocking_primitive
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hμne1 hDim1
  obtain ⟨r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    weight_assignment
      (d := d)
      (p := p)
      (Ablk := blockTensor (d := d) (D := D) A p)
      (r2 := r2) (dim2 := dim2) (μ2 := μ2) blocks2
      hSame2 hIrr2 hLeft2 hPrim2 hμnorm_ne2 hμne2 hDim2
  exact ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩

/-- Package the separated blocked data into the bundled `IsNormalCanonicalForm` predicate.

This is the current public handoff theorem for the pipeline: it starts from a **chosen**
irreducible block decomposition of `A` whose blocks are all nonzero, then threads that data through
TP gauging, periodicity removal, equal-weight consolidation, and final weight sorting. -/
theorem exists_normalCanonicalForm_of_irreducible_blockDecomp
    (A : MPSTensor d D)
    {r0 : ℕ} {dim0 : Fin r0 → ℕ}
    (blocks0 : (k : Fin r0) → MPSTensor d (dim0 k))
    (hIrr0 : ∀ k, IsIrreducibleTensor (blocks0 k))
    (hSame0 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := fun _ : Fin r0 => (1 : ℂ)) blocks0))
    (hNonzero0 : ∀ k, ∃ i, blocks0 k i ≠ 0) :
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
    exists_blocked_normal_data_of_irreducible_blockDecomp
      (A := A) (r0 := r0) (dim0 := dim0) blocks0 hIrr0 hSame0 hNonzero0
  refine ⟨p, hp, r, dim, μ, blocks, hSame, ?_⟩
  let hμ : HasStrictOrderedNonzeroWeights μ := {
    mu_strict_anti := hμanti
    mu_ne_zero := hμne
  }
  exact
    IsNormalCanonicalForm.ofSeparatedData
      (d := blockPhysDim d p)
      (A := blocks)
      (μ := μ)
      (HasIrreducibleBlocks.ofForall hIrr)
      (IsLeftCanonicalBlockFamily.ofForall hLeft)
      (HasPrimitiveBlocks.ofForall hPrim)
      hμ
      hDim

/-!
## Omitted unconditional wrapper

The original theorem asserting `exists_normalCanonicalForm (A : MPSTensor d D)` from arbitrary
input `A` is intentionally omitted at present.

Two genuine issues remain before such a wrapper can be stated honestly:

1. `exists_irreducible_blockDecomp_pipeline1606` does not exclude all-zero irreducible scalar
   blocks, while the current `SameMPV₂` relation remembers the `N = 0` sector.
2. After cyclic decomposition one still needs a formal equal-weight merging step (or an equivalent
   replacement) before the final `StrictAnti` weight profile is available.

The theorem `exists_normalCanonicalForm_of_irreducible_blockDecomp` above is therefore the current
honest handoff point for downstream work.
-/

end MPSTensor
