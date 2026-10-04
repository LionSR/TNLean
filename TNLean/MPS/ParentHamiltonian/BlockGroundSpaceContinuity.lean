/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces
import TNLean.MPS.SharedInfra.WordTupleGauge

/-!
# Continuity of local ground spaces for several normal blocks

The joint boundary map uses only the diagonal virtual matrix blocks.
Simultaneous spanning by word evaluations makes this map injective, although
an assembled tensor with several blocks is never injective on the full
virtual matrix algebra. The inverse-Gram formula therefore gives continuity
of its local ground-space projection. This is the finite-window continuity
step in arXiv:1010.3732, Appendix A, lines 2575--2578.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The joint boundary map on diagonal virtual matrix blocks,
\(\Gamma_L((X_j)_j)=\sum_j\Gamma_L^{A_j}(X_j)\), realized between Euclidean spaces.
Source: PGVWC07, Theorem 12, proof lines 1430--1434. -/
noncomputable def blockGroundSpaceMapES
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    EuclideanSpace ℂ ((j : Fin r) × (Fin (dim j) × Fin (dim j))) →L[ℂ]
      EuclideanSpace ℂ (Cfg d L) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toLinearMap.comp
      (show EuclideanSpace ℂ ((j : Fin r) × (Fin (dim j) × Fin (dim j))) →ₗ[ℂ]
        NSiteSpace d L from
      { toFun := fun v => ∑ j, groundSpaceMap (A j) L
          (Matrix.of fun a b => v ⟨j, b, a⟩)
        map_add' := by
          intro v w
          simp only [WithLp.ofLp_add, Pi.add_apply]
          change (∑ j, groundSpaceMap (A j) L
            (Matrix.of (fun a b => v ⟨j, b, a⟩) +
              Matrix.of (fun a b => w ⟨j, b, a⟩))) = _
          simp only [map_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c v
          simp only [WithLp.ofLp_smul, Pi.smul_apply]
          change (∑ j, groundSpaceMap (A j) L
            (c • Matrix.of (fun a b => v ⟨j, b, a⟩))) = _
          simp only [map_smul, Finset.smul_sum, RingHom.id_apply] })

@[simp]
theorem blockGroundSpaceMapES_apply
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ)
    (v : EuclideanSpace ℂ ((j : Fin r) × (Fin (dim j) × Fin (dim j))))
    (σ : Cfg d L) :
    blockGroundSpaceMapES A L v σ =
      ∑ j, (groundSpaceMap (A j) L (Matrix.of fun a b => v ⟨j, b, a⟩)) σ := by
  simp [blockGroundSpaceMapES, Finset.sum_apply]

/-- The diagonal-block boundary map depends continuously on the block tensors.
Source: arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem continuous_blockGroundSpaceMapES_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) (L : ℕ) :
    Continuous fun x => blockGroundSpaceMapES (A x) L := by
  apply continuous_clm_apply.2
  refine fun v => (EuclideanSpace.equiv (Cfg d L) ℂ).symm.continuous.comp ?_
  change Continuous fun x => ∑ j,
    groundSpaceMap (A x j) L (Matrix.of fun a b => v ⟨j, b, a⟩)
  apply continuous_finsetSum _ fun j _ => ?_
  exact continuous_pi fun σ => ((continuous_evalWord_family (fun x => A x j) (hA j)
    (List.ofFn σ)).matrix_mul continuous_const).matrix_trace

/-- Simultaneous spanning by length-\(L\) words makes the diagonal-block
boundary map injective. Source: PGVWC07, Theorem 12, proof lines 1430--1434. -/
theorem blockGroundSpaceMapES_injective_of_wordTupleSpanTop
    (A : (j : Fin r) → MPSTensor d (dim j)) {L : ℕ}
    (hSpan : WordTupleSpanTop A L) :
    Function.Injective (blockGroundSpaceMapES A L) := by
  refine (injective_iff_map_eq_zero (blockGroundSpaceMapES A L)).2 fun v hv => ?_
  have htrace (σ : Cfg d L) :
      (∑ j, Matrix.trace (Matrix.of (fun a b => v ⟨j, b, a⟩) *
        Kraus.evalWord (A j) (List.ofFn σ))) = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => Matrix.trace_mul_comm
      (Matrix.of fun a b => v ⟨j, b, a⟩)
      (Kraus.evalWord (A j) (List.ofFn σ)))]
    simpa only [blockGroundSpaceMapES_apply, groundSpaceMap_apply,
      PiLp.zero_apply] using congrArg (fun z => z σ) hv
  have hzero := block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan
    (fun j => Matrix.of fun a b => v ⟨j, b, a⟩) htrace
  exact PiLp.ext fun ⟨j, b, a⟩ => congrArg (fun X => X a b) (hzero j)

/-- The range of the joint boundary map is the sum of the block local spaces.
Source: PGVWC07, Theorem 12, proof lines 1430--1434. -/
theorem range_blockGroundSpaceMapES
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    (blockGroundSpaceMapES A L).range = ⨆ j, groundSpaceES (A j) L := by
  apply le_antisymm
  · rintro ψ ⟨v, rfl⟩
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
      (∑ j, groundSpaceMap (A j) L (Matrix.of fun a b => v ⟨j, b, a⟩)) ∈ _
    rw [map_sum]
    exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j
      ⟨_, ⟨_, rfl⟩, rfl⟩
  · refine iSup_le fun j ψ hψ => ?_
    rcases hψ with ⟨φ, ⟨X, rfl⟩, rfl⟩
    let Y : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ := Pi.single j X
    refine ⟨WithLp.toLp 2 (fun ⟨k, b, a⟩ => Y k a b), ?_⟩
    apply PiLp.ext
    intro σ
    simp only [ContinuousLinearMap.coe_coe, blockGroundSpaceMapES_apply,
      LinearEquiv.coe_coe, WithLp.linearEquiv_symm_apply,
      groundSpaceMap_apply]
    change (∑ k, Matrix.trace (Kraus.evalWord (A k) (List.ofFn σ) * Y k)) =
      Matrix.trace (Kraus.evalWord (A j) (List.ofFn σ) * X)
    rw [Finset.sum_eq_single j]
    · simp [Y]
    · intro k _ hkj
      simp [Y, Pi.single_eq_of_ne hkj]
    · simp

/-- The orthogonal projection onto the sum of the block local spaces is
continuous when the simultaneous word span is full at that length.
Source: arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem continuous_iSup_groundSpaceES_starProjection_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) (L : ℕ)
    (hSpan : ∀ x, WordTupleSpanTop (A x) L) :
    Continuous fun x => (⨆ j, groundSpaceES (A x j) L).starProjection := by
  have hInj (x : X) := blockGroundSpaceMapES_injective_of_wordTupleSpanTop (A x) (hSpan x)
  have hProj := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun x => blockGroundSpaceMapES (A x) L)
    (continuous_blockGroundSpaceMapES_family A hA L) hInj
  simpa only [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection,
    range_blockGroundSpaceMapES] using hProj

/-- Nonzero weights do not affect continuity of the local projection of a
block sum. Only the block tensors need to vary continuously.
Source: arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    {X : Type*} [TopologicalSpace X]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    (L : ℕ) (hSpan : ∀ x, WordTupleSpanTop (A x) L) :
    Continuous fun x =>
      (groundSpaceES (toTensorFromBlocks (d := d) (μ := μ x) (A x)) L).starProjection := by
  have hEq (x : X) := groundSpaceES_toTensorFromBlocks_eq_iSup (μ x) (A x) (hμ x) L
  simpa only [hEq] using
    continuous_iSup_groundSpaceES_starProjection_family A hA L hSpan

/-- At a fixed injective window, the overlap \(\|P_{G_L^i}P_{G_L^j}\|\)
between two block local spaces depends continuously on the tensor family.
Source: arXiv:1010.3732, Appendix A, lines 2510--2533. -/
theorem continuous_norm_groundSpaceES_overlap_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) (L : ℕ)
    (hInj : ∀ x j, Kraus.IsNBlkInjective (A x j) L) (i j : Fin r) :
    Continuous fun x => ‖(groundSpaceES (A x i) L).starProjection.comp
      (groundSpaceES (A x j) L).starProjection‖ :=
  ((continuous_groundSpaceES_starProjection_family (fun x => A x i) (hA i) L
    (fun x => hInj x i)).clm_comp
      (continuous_groundSpaceES_starProjection_family (fun x => A x j) (hA j) L
        (fun x => hInj x j))).norm

end MPSTensor
