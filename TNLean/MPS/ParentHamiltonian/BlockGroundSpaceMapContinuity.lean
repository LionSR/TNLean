/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.GroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces
import TNLean.MPS.SharedInfra.WordTupleGauge

/-!
# Continuity of ground spaces for several tensor blocks

For fixed block dimensions, the joint boundary map is
\(\Gamma_L((X_j)_j)=\sum_j\Gamma_L^{A_j}(X_j)\).
Its range is the sum of the block ground spaces. A full simultaneous word
span makes this map injective, so the inverse-Gram formula gives a continuous
orthogonal projector along a continuous family with one such window length.
The canonical local interactions and finite-volume open and periodic
Hamiltonians consequently vary continuously.

Nonzero block coefficients do not change these ground spaces. Their
continuity is therefore unnecessary for the statements below.

These are finite-window ingredients in arXiv:1010.3732, Appendix A,
lines 2499–2503 and 2575–2578. A gap uniform both in the parameter and
in chain length requires further spectral estimates.
-/

open scoped Matrix Topology

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The diagonal virtual boundary space in finite Hilbert coordinates. The coordinate \( (j,b,a)
\) records the matrix entry \( (X_j)_{ab} \).
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
noncomputable def blockBoundaryEquiv :
    EuclideanSpace ℂ ((j : Fin r) × (Fin (dim j) × Fin (dim j))) ≃ₗ[ℂ]
      ((j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) where
  toFun x j a b := x ⟨j, (b, a)⟩
  invFun X := WithLp.toLp 2 fun ⟨j, b, a⟩ => X j a b
  left_inv x := by rfl
  right_inv X := by rfl
  map_add' x y := by rfl
  map_smul' c x := by rfl

/-- The joint boundary map \(\Gamma_L((X_j)_j)=\sum_j\Gamma_L^{A_j}(X_j)\).
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
noncomputable def blockGroundSpaceMap
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    ((j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) →ₗ[ℂ] NSiteSpace d L :=
  LinearMap.lsum ℂ (fun j => Matrix (Fin (dim j)) (Fin (dim j)) ℂ) ℂ
    (fun j => groundSpaceMap (A j) L)

/-- The joint boundary map with Hilbert–Schmidt coordinates on the diagonal virtual boundaries.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
noncomputable def blockGroundSpaceMapES
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    EuclideanSpace ℂ ((j : Fin r) × (Fin (dim j) × Fin (dim j))) →L[ℂ]
      EuclideanSpace ℂ (Cfg d L) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toLinearMap.comp
      ((blockGroundSpaceMap A L).comp blockBoundaryEquiv.toLinearMap)

/-- The joint boundary map is the sum of the individual block boundary maps.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
@[simp]
theorem blockGroundSpaceMap_apply
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    blockGroundSpaceMap A L X = ∑ j, groundSpaceMap (A j) L (X j) := by
  simp [blockGroundSpaceMap, LinearMap.lsum_apply]

/-- The joint boundary map has the sum of the block ground spaces as its range.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem range_blockGroundSpaceMap
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    (blockGroundSpaceMap A L).range = ⨆ j, groundSpace (A j) L := by
  apply le_antisymm
  · rintro ψ ⟨X, rfl⟩
    rw [blockGroundSpaceMap_apply]
    exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨X j, rfl⟩
  · refine iSup_le fun j => ?_
    rintro ψ ⟨X, rfl⟩
    refine ⟨Pi.single j X, ?_⟩
    exact LinearMap.lsum_piSingle ℂ
      (fun j => Matrix (Fin (dim j)) (Fin (dim j)) ℂ) ℂ
      (fun j => groundSpaceMap (A j) L) j X

/-- The Hilbert realization has the sum of the physical block ground spaces as its range.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem range_blockGroundSpaceMapES
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    (blockGroundSpaceMapES A L).range = ⨆ j, groundSpaceES (A j) L := by
  simp only [blockGroundSpaceMapES, LinearMap.coe_toContinuousLinearMap,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    range_blockGroundSpaceMap, Submodule.map_iSup, groundSpaceES]

/-- A full simultaneous word span separates all diagonal virtual boundaries by trace pairing.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem blockGroundSpaceMap_injective_of_wordTupleSpanTop
    {A : (j : Fin r) → MPSTensor d (dim j)} {L : ℕ}
    (hSpan : WordTupleSpanTop A L) : Function.Injective (blockGroundSpaceMap A L) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro Δ hΔ
  apply funext
  apply block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan Δ
  intro w
  have hw := congrFun hΔ w
  simp only [blockGroundSpaceMap_apply, Finset.sum_apply, groundSpaceMap_apply,
    Pi.zero_apply] at hw
  simp_rw [Matrix.trace_mul_comm (Δ _) (Kraus.evalWord _ _)]
  exact hw

/-- A full simultaneous word span makes the joint Hilbert boundary map injective.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem blockGroundSpaceMapES_injective_of_wordTupleSpanTop
    {A : (j : Fin r) → MPSTensor d (dim j)} {L : ℕ}
    (hSpan : WordTupleSpanTop A L) : Function.Injective (blockGroundSpaceMapES A L) := by
  exact (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.injective.comp
    ((blockGroundSpaceMap_injective_of_wordTupleSpanTop hSpan).comp
      blockBoundaryEquiv.injective)

/-- The joint boundary map varies continuously with a fixed finite family of tensor blocks.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem continuous_blockGroundSpaceMapES_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) (L : ℕ) :
    Continuous fun x => blockGroundSpaceMapES (A x) L := by
  apply continuous_clm_apply.2
  intro y
  apply (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.toContinuousLinearEquiv.continuous.comp
  simp only [LinearMap.comp_apply, blockGroundSpaceMap_apply]
  apply continuous_finsetSum _
  intro j _
  exact continuous_pi fun σ => by
    simpa only [groundSpaceMap_apply] using
      ((continuous_evalWord_family (fun x => A x j) (hA j) (List.ofFn σ)).matrix_mul
        (continuous_const (y := (blockBoundaryEquiv (dim := dim)).toLinearMap y j))).matrix_trace

/-- At a common simultaneous injectivity length, the projector onto the sum of the block ground
spaces is continuous.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem continuous_iSup_groundSpaceES_starProjection_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) (L : ℕ)
    (hInj : ∀ x, Function.Injective (blockGroundSpaceMapES (A x) L)) :
    Continuous fun x => (⨆ j, groundSpaceES (A x j) L).starProjection := by
  have hT := continuous_blockGroundSpaceMapES_family A hA L
  have hP := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun x => blockGroundSpaceMapES (A x) L) hT hInj
  simpa only [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection,
    range_blockGroundSpaceMapES] using hP

/-- The ground-space projector of a weighted block sum is continuous when the block family is
continuous and simultaneously injective. Nonzero weights need not vary continuously.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j)
    (μ : X → Fin r → ℂ) (hμ : ∀ x j, μ x j ≠ 0) (L : ℕ)
    (hInj : ∀ x, Function.Injective (blockGroundSpaceMapES (A x) L)) :
    Continuous fun x =>
      (groundSpaceES (toTensorFromBlocks (d := d) (μ := μ x) (A x)) L).starProjection := by
  simpa only [groundSpaceES_toTensorFromBlocks_eq_iSup _ _ (hμ _) L] using
    continuous_iSup_groundSpaceES_starProjection_family A hA L hInj

/-- The canonical parent interaction of a weighted block sum varies continuously at a common
simultaneous injectivity length.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem continuous_parentInteractionES_toTensorFromBlocks_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j)
    (μ : X → Fin r → ℂ) (hμ : ∀ x j, μ x j ≠ 0) (L : ℕ)
    (hInj : ∀ x, Function.Injective (blockGroundSpaceMapES (A x) L)) :
    Continuous fun x => LinearMap.toContinuousLinearMap
      (parentInteractionES (toTensorFromBlocks (d := d) (μ := μ x) (A x)) L) := by
  have hP := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    A hA μ hμ L hInj
  have hDiff : Continuous fun x =>
      (1 : EuclideanSpace ℂ (Cfg d L) →L[ℂ] EuclideanSpace ℂ (Cfg d L)) -
        (groundSpaceES (toTensorFromBlocks (d := d) (μ := μ x) (A x)) L).starProjection :=
    continuous_const.sub hP
  convert hDiff using 1
  ext x v
  simp only [parentInteractionES, Submodule.starProjection_orthogonal]
  rfl

/-- The open-chain parent Hamiltonian of a weighted block sum is continuous at fixed range and
volume.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem continuous_openParentHamiltonianES_toTensorFromBlocks_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j)
    (μ : X → Fin r → ℂ) (hμ : ∀ x j, μ x j ≠ 0) {L N : ℕ}
    (hLN : L ≤ N) (hInj : ∀ x, Function.Injective (blockGroundSpaceMapES (A x) L)) :
    Continuous fun x => LinearMap.toContinuousLinearMap
      (openParentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ x) (A x)) L N) :=
  continuous_openParentHamiltonianES_of_parentInteractionES_family _ hLN
    (continuous_parentInteractionES_toTensorFromBlocks_family A hA μ hμ L hInj)

/-- The periodic parent Hamiltonian of a weighted block sum is continuous at fixed range and volume.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem continuous_parentHamiltonianES_toTensorFromBlocks_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j)
    (μ : X → Fin r → ℂ) (hμ : ∀ x j, μ x j ≠ 0) {L N : ℕ}
    (hLN : L ≤ N) (hInj : ∀ x, Function.Injective (blockGroundSpaceMapES (A x) L)) :
    Continuous fun x => LinearMap.toContinuousLinearMap
      (parentHamiltonianES (toTensorFromBlocks (d := d) (μ := μ x) (A x)) L N) :=
  continuous_parentHamiltonianES_of_parentInteractionES_family _ hLN
    (continuous_parentInteractionES_toTensorFromBlocks_family A hA μ hμ L hInj)

/-- Injectivity of the joint boundary map at a fixed length is an open condition on a continuous
block family.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem isOpen_setOf_blockGroundSpaceMapES_injective_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) (L : ℕ) :
    IsOpen {x | Function.Injective (blockGroundSpaceMapES (A x) L)} :=
  ContinuousLinearMap.isOpen_injective.preimage
    (continuous_blockGroundSpaceMapES_family A hA L)

/-- For trace-preserving blocks, injectivity of the joint boundary map persists after adjoining
one physical site.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem blockGroundSpaceMap_injective_succ_of_tracePreserving
    (A : (j : Fin r) → MPSTensor d (dim j)) {L : ℕ}
    (hInj : Function.Injective (blockGroundSpaceMap A L))
    (hTP : ∀ j, ∑ i, (A j i)ᴴ * A j i = 1) :
    Function.Injective (blockGroundSpaceMap A (L + 1)) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro Δ hΔ
  have hleft (i : Fin d) : blockGroundSpaceMap A L (fun j => A j i * Δ j) = 0 := by
    ext w
    have hw := congrFun hΔ (Fin.append w (fun _ : Fin 1 => i))
    simp only [blockGroundSpaceMap_apply, Finset.sum_apply, groundSpaceMap_apply,
      Pi.zero_apply, List.ofFn_fin_append, Kraus.evalWord_append] at hw
    simpa only [blockGroundSpaceMap_apply, Finset.sum_apply, groundSpaceMap_apply,
      Pi.zero_apply, List.ofFn_succ, List.ofFn_zero,
      Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one,
      Matrix.mul_assoc] using hw
  have hzero (i : Fin d) (j : Fin r) : A j i * Δ j = 0 :=
    congrFun (hInj ((hleft i).trans (map_zero _).symm)) j
  funext j
  calc
    Δ j = (∑ i, (A j i)ᴴ * A j i) * Δ j := by rw [hTP j, Matrix.one_mul]
    _ = ∑ i, (A j i)ᴴ * (A j i * Δ j) := by
      rw [Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    _ = 0 := by simp only [hzero, Matrix.mul_zero, Finset.sum_const_zero]

/-- Hilbert coordinates preserve injectivity of the joint boundary map.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem blockGroundSpaceMapES_injective_iff
    (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ) :
    Function.Injective (blockGroundSpaceMapES A L) ↔
      Function.Injective (blockGroundSpaceMap A L) := by
  constructor
  · intro h X Y hXY
    apply blockBoundaryEquiv.symm.injective
    apply h
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
        (blockGroundSpaceMap A L (blockBoundaryEquiv (blockBoundaryEquiv.symm X))) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm
        (blockGroundSpaceMap A L (blockBoundaryEquiv (blockBoundaryEquiv.symm Y)))
    simp only [LinearEquiv.apply_symm_apply, hXY]
  · intro h
    exact (WithLp.linearEquiv 2 ℂ (NSiteSpace d L)).symm.injective.comp
      (h.comp blockBoundaryEquiv.injective)

/-- For trace-preserving blocks, joint boundary injectivity persists at every larger length.
Source: arXiv:1010.3732, Appendix A, lines 2499–2503 and 2575–2578. -/
theorem blockGroundSpaceMapES_injective_of_ge_of_tracePreserving
    (A : (j : Fin r) → MPSTensor d (dim j)) {L n : ℕ}
    (hInj : Function.Injective (blockGroundSpaceMapES A L))
    (hTP : ∀ j, ∑ i, (A j i)ᴴ * A j i = 1) (hLn : L ≤ n) :
    Function.Injective (blockGroundSpaceMapES A n) := by
  rw [blockGroundSpaceMapES_injective_iff] at hInj ⊢
  exact Nat.le_induction hInj
    (fun _ _ h => blockGroundSpaceMap_injective_succ_of_tracePreserving A h hTP) n hLn

end MPSTensor
