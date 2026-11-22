/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.CompactKernelGap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceAtInjectivityLength
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceContinuity
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpaceAtSimultaneousInjectivity
import TNLean.MPS.ParentHamiltonian.PeriodicShortGapContinuity

/-!
# Continuity of periodic ground spaces for several normal blocks

At a positive simultaneous injectivity length, the periodic component vectors
are linearly independent. Their linear combination map therefore gives a
continuous orthogonal projection onto the periodic ground space, including
at the shortest ring containing the parent interaction. A compact family has
one positive gap at each such fixed volume.

Source: arXiv:1010.3732, Appendix A, lines 2575--2578; arXiv:2011.12127,
Section IV.C, lines 2114--2129.

**Transitional (#10948).**
`ker_parentHamiltonianES_toTensorFromBlocks_eq_range_blockPeriodicMpvMapES` and
`continuous_parentHamiltonianES_toTensorFromBlocks_kernelProjection_family`,
stated for the Euclidean-space operator, are kept until their users are converted; the last
section states them for the Hamiltonian of the parent interaction on the ring.
-/

open scoped BigOperators Matrix Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The linear combination map of the periodic component vectors,
\(c\mapsto\sum_j c_j V^{(N)}(A_j)\), in Euclidean coordinates.
Source: arXiv:2011.12127, Section IV.C, lines 2126--2129. -/
noncomputable def blockPeriodicMpvMapES
    (A : (j : Fin r) → MPSTensor d (dim j)) (N : ℕ) :
    EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap.comp
      ((Fintype.linearCombination ℂ (fun j => (mpv (A j) : NSiteSpace d N))).comp
        (WithLp.linearEquiv 2 ℂ (Fin r → ℂ)).toLinearMap)

@[simp]
theorem blockPeriodicMpvMapES_apply
    (A : (j : Fin r) → MPSTensor d (dim j)) (N : ℕ)
    (c : EuclideanSpace ℂ (Fin r)) (σ : Cfg d N) :
    blockPeriodicMpvMapES A N c σ = ∑ j, c j * mpv (A j) σ := by
  simp [blockPeriodicMpvMapES, Fintype.linearCombination, Finset.sum_apply]

/-- The periodic linear combination map is the joint boundary map
restricted to scalar identity matrices on the diagonal virtual blocks.
Source: arXiv:2011.12127, Section IV.C, lines 2126--2129. -/
theorem blockPeriodicMpvMapES_eq_blockGroundSpaceMapES
    (A : (j : Fin r) → MPSTensor d (dim j)) (N : ℕ)
    (c : EuclideanSpace ℂ (Fin r)) :
    blockPeriodicMpvMapES A N c = blockGroundSpaceMapES A N
      (WithLp.toLp 2 (fun ⟨j, b, a⟩ =>
        (c j • (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) a b)) := by
  apply PiLp.ext
  intro σ
  simp only [blockPeriodicMpvMapES_apply, blockGroundSpaceMapES_apply]
  apply Finset.sum_congr rfl
  intro j _
  change c j * mpv (A j) σ = (groundSpaceMap (A j) N (c j • 1)) σ
  rw [map_smul, ← mpv_eq_groundSpaceMap_one]
  rfl

/-- Simultaneous word spanning makes the periodic component vectors
linearly independent. The map is the restriction of the injective joint
boundary map to scalar identity matrices. Source: arXiv:2011.12127,
Section IV.C, lines 2114--2129. -/
theorem blockPeriodicMpvMapES_injective_of_wordTupleSpanTop
    [∀ j, NeZero (dim j)]
    (A : (j : Fin r) → MPSTensor d (dim j)) {N : ℕ}
    (hSpan : WordTupleSpanTop A N) :
    Function.Injective (blockPeriodicMpvMapES A N) := by
  refine (injective_iff_map_eq_zero (blockPeriodicMpvMapES A N)).2 fun c hc => ?_
  let v : EuclideanSpace ℂ ((j : Fin r) × (Fin (dim j) × Fin (dim j))) :=
    WithLp.toLp 2 (fun ⟨j, b, a⟩ =>
      (c j • (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) a b)
  have hBoundary : v = 0 := by
    apply blockGroundSpaceMapES_injective_of_wordTupleSpanTop A hSpan
    rw [map_zero]
    change blockGroundSpaceMapES A N
      (WithLp.toLp 2 (fun ⟨j, b, a⟩ =>
        (c j • (1 : Matrix (Fin (dim j)) (Fin (dim j)) ℂ)) a b)) = 0
    rw [← blockPeriodicMpvMapES_eq_blockGroundSpaceMapES]
    exact hc
  apply PiLp.ext
  intro j
  have h := congrArg (fun w => w ⟨j, (0 : Fin (dim j)), (0 : Fin (dim j))⟩) hBoundary
  simpa [v] using h

/-- The range of the periodic linear combination map is the span of
component MPS vectors, expressed in Euclidean coordinates. Source:
arXiv:2011.12127, Section IV.C, lines 2126--2129. -/
theorem range_blockPeriodicMpvMapES
    (A : (j : Fin r) → MPSTensor d (dim j)) (N : ℕ) :
    (blockPeriodicMpvMapES A N).range = (bntMPSVectorSpan A N).map
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap := by
  change LinearMap.range
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap.comp
      ((Fintype.linearCombination ℂ (fun j => (mpv (A j) : NSiteSpace d N))).comp
        (WithLp.linearEquiv 2 ℂ (Fin r → ℂ)).toLinearMap)) = _
  rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, Fintype.range_linearCombination]
  rfl

/-- The periodic linear combination map depends continuously on the
component tensors. Source: arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem continuous_blockPeriodicMpvMapES_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hA : ∀ j, Continuous fun x => A x j) (N : ℕ) :
    Continuous fun x => blockPeriodicMpvMapES (A x) N := by
  apply continuous_clm_apply.2
  intro c
  have h : Continuous fun x => ∑ j, c j •
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv (A x j)) :=
    continuous_finsetSum _ fun j _ =>
      (continuous_mpvES_family (fun x => A x j) (hA j) N).const_smul (c j)
  convert h using 1
  ext x σ
  simp [blockPeriodicMpvMapES, Fintype.linearCombination, Finset.sum_apply]

/-- Above a simultaneous injectivity length, the periodic parent kernel
is the range of the component-vector map, including at the shortest ring
containing the interaction. Source: arXiv:2011.12127, Section IV.C,
lines 2114--2129. -/
theorem ker_parentHamiltonianES_toTensorFromBlocks_eq_range_blockPeriodicMpvMapES
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R N : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop A S)
    (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    LinearMap.ker (parentHamiltonianES
      (toTensorFromBlocks (d := d) (μ := μ) A) R N) =
      (blockPeriodicMpvMapES A N).range := by
  rw [range_blockPeriodicMpvMapES,
    ← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_toTensorFromBlocks_eq_of_wordTupleSpanTop μ A hμ hS hSpan hR hRN]

/-- The periodic ground-space projection is continuous for a family with
one common positive simultaneous injectivity length. The nonzero weights
may vary arbitrarily, since they leave the periodic component span unchanged.
Source: arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem continuous_parentHamiltonianES_toTensorFromBlocks_kernelProjection_family
    {X : Type*} [TopologicalSpace X] [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    {S R N : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    Continuous fun x => (LinearMap.ker (parentHamiltonianES
      (toTensorFromBlocks (d := d) (μ := μ x) (A x)) R N)).starProjection := by
  have hInj (x : X) : Function.Injective (blockPeriodicMpvMapES (A x) N) :=
    blockPeriodicMpvMapES_injective_of_wordTupleSpanTop (A x)
      (wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega : S ≤ N))
  have hProj := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun x => blockPeriodicMpvMapES (A x) N)
    (continuous_blockPeriodicMpvMapES_family A hA N) hInj
  have hKernel (x : X) :=
    ker_parentHamiltonianES_toTensorFromBlocks_eq_range_blockPeriodicMpvMapES
      (μ x) (A x) (hμ x) hS (hSpan x) hR hRN
  simpa only [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection,
    ← hKernel] using hProj

/-! ### The parent interaction on the ring -/

/-- Above a simultaneous injectivity length, the kernel of the Hamiltonian of the parent
interaction on the ring is the range of the component-vector map, including at the shortest ring
containing the interaction. Source: arXiv:2011.12127, Section IV.C, lines 2114--2129. -/
theorem ker_hamiltonian_parentRingInteraction_toTensorFromBlocks_eq_range_blockPeriodicMpvMapES
    [NeZero d] [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0) {S R N : ℕ}
    (hS : 0 < S) (hSpan : WordTupleSpanTop A S)
    (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (parentRingInteraction (toTensorFromBlocks μ A) R N).hamiltonian) =
      (blockPeriodicMpvMapES A N).range := by
  have : NeZero N := ⟨by omega⟩
  rw [range_blockPeriodicMpvMapES,
    ← ManyBody.groundSpace_zero,
    groundSpace_hamiltonian_parentRingInteraction_eq_map_ker,
    ker_parentHamiltonian_toTensorFromBlocks_eq_of_wordTupleSpanTop μ A hμ hS hSpan hR hRN]

/-- The projection onto the kernel of the Hamiltonian of the parent interaction on the ring is
continuous for a family with one common positive simultaneous injectivity length. The nonzero
weights may vary arbitrarily, since they leave the periodic component span unchanged.
Source: arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem continuous_hamiltonian_parentRingInteraction_toTensorFromBlocks_kernelProjection_family
    {X : Type*} [TopologicalSpace X] [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    {S R N : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Continuous fun x =>
      (LinearMap.ker (Matrix.toEuclideanLin (parentRingInteraction
        (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian)).starProjection := by
  have : NeZero N := ⟨by omega⟩
  have hInj (x : X) : Function.Injective (blockPeriodicMpvMapES (A x) N) :=
    blockPeriodicMpvMapES_injective_of_wordTupleSpanTop (A x)
      (wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega : S ≤ N))
  have hProj := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun x => blockPeriodicMpvMapES (A x) N)
    (continuous_blockPeriodicMpvMapES_family A hA N) hInj
  have hKernel (x : X) :=
    ker_hamiltonian_parentRingInteraction_toTensorFromBlocks_eq_range_blockPeriodicMpvMapES
      (μ x) (A x) (hμ x) hS (hSpan x) hR hRN
  simpa only [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection,
    ← hKernel] using hProj

/-- At every fixed periodic volume containing an interaction longer than a common simultaneous
injectivity length, a continuous compact family of block tensors has one positive gap above the
kernel of the Hamiltonian of the parent interaction on the ring: every eigenvalue is `0` or at
least the gap. Nonzero weights need no continuity assumption. Source: arXiv:1010.3732,
Appendix A, lines 2575--2578. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_of_wordTupleSpanTop
    {X : Type*} [TopologicalSpace X] [NeZero d] [∀ j, NeZero (dim j)]
    (μ : X → Fin r → ℂ) (A : X → (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ x j, μ x j ≠ 0) (hA : ∀ j, Continuous fun x => A x j)
    {S R N : ℕ} (hS : 0 < S) (hSpan : ∀ x, WordTupleSpanTop (A x) S)
    {K : Set X} (hK : IsCompact K) (hR : S + 1 ≤ R) (hRN : R ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ ν : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (parentRingInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian) ν →
        ν = 0 ∨ (δ : ℂ) ≤ ν := by
  have : NeZero N := ⟨by omega⟩
  suffices hnorm : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian))ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
          (parentRingInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian v‖ by
    obtain ⟨δ, hδ, hgap⟩ := hnorm
    exact ⟨δ, hδ, fun x hx ↦ (ManyBody.forall_hasEigenvalue_iff_norm
      (posSemidef_hamiltonian_parentRingInteraction _ _ _)).mpr (hgap x hx)⟩
  have hSpanR (x : X) : WordTupleSpanTop (A x) R :=
    wordTupleSpanTop_of_ge (A x) hS (hSpan x) (by omega : S ≤ R)
  have hGround := continuous_groundSpaceES_toTensorFromBlocks_starProjection_family
    μ A hμ hA R hSpanR
  let e := (Matrix.toEuclideanCLM : Matrix (Cfg d N) (Cfg d N) ℂ ≃⋆ₐ[ℂ] _)
  have hH : Continuous fun x ↦
      e (parentRingInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian :=
    e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_hamiltonian_parentRingInteraction_family_of_groundProjection
        (fun x => toTensorFromBlocks (μ x) (A x)) hRN hGround)
  have hKernel :=
    continuous_hamiltonian_parentRingInteraction_toTensorFromBlocks_kernelProjection_family
      μ A hμ hA hS hSpan hR hRN
  simp only [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at hKernel ⊢
  exact ContinuousLinearMap.exists_uniform_norm_gap_of_compact
    (X := X) (E := EuclideanSpace ℂ (Cfg d N))
    (fun x ↦ e (parentRingInteraction (toTensorFromBlocks (μ x) (A x)) R N).hamiltonian)
    hH hKernel hK

end MPSTensor
