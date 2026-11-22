/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Joint.JointMixedEndpointPeriodicSectors
import TNLean.MPS.ParentHamiltonian.Gap.PrimitiveBlockGapThreshold
import TNLean.MPS.ParentHamiltonian.Continuity.BlockPeriodicGroundSpaceContinuity
import TNLean.MPS.FundamentalTheorem.Compression.AbsorbingCompression

/-!
# Periodic kernel and uniform gap of the actual joint mixed endpoint

The actual extended Hamiltonian agrees with the full joint canonical
endpoint Hamiltonian on the all-zero phase sector. Every other phase
configuration violates a cyclic constraint, giving energy at least one
half. The two Hamiltonians have the same kernel, and the common canonical
gap therefore transfers with constant \(\min(\delta,1/2)\).

The comparison uses the joint block support and its simultaneous span;
it makes no physical orthogonality assumption on the individual endpoint
blocks. Both directed bonds are retained on a two-site ring. Empty block
families and a zero physical alphabet are included.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777. These results
concern the first endpoint on periodic chains. They assert no open-chain
comparison, near-endpoint uniform gap, or classification of phases.
-/

open scoped Matrix BigOperators InnerProductSpace ComplexOrder MatrixOrder
open ManyBody.Interaction (translationInvariant)

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- The Hamiltonian of the translates of the extended joint endpoint interaction lies below
the Hamiltonian of the parent interaction of the joint canonical tensor, whose excess is
bounded by the explicit cyclic phase penalty.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_comparison
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian ≤
        Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (μ := fun _ => 1)
          (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 N).hamiltonian ∧
      Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (μ := fun _ => 1)
          (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 N).hamiltonian ≤
        Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian +
          jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N := by
  have : NeZero N := ⟨by omega⟩
  let Rm : Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)
      (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) ℂ :=
    Matrix.diagonal fun ω => jointMixedRowWeight (ω 0)
  let Cm : Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)
      (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) ℂ :=
    Matrix.diagonal fun ω => jointMixedColumnWeight (ω 1)
  have hone : Matrix.toEuclideanLin (1 : Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)
      (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) ℂ) = 1 :=
    LinearMap.ext fun v => Matrix.toEuclideanLin_one_apply v
  have hlocal : LinearMap.toMatrix' (parentInteraction (toTensorFromBlocks (μ := fun _ => 1)
      (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2) ≤
      jointMixedEndpointParentInteraction A₀ A₁ 0 + (1 - Rm) + (1 - Cm) := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    simpa only [map_add, map_sub, hone,
      show Matrix.toEuclideanLin Rm = jointMixedRowSector d₀ d₁ D₀ D₁ 0 from rfl,
      show Matrix.toEuclideanLin Cm = jointMixedColumnSector d₀ d₁ D₀ D₁ 1 from rfl] using
      parentInteraction_jointMixedEndpointLeftTensor_le A₀ A₁
  constructor
  · exact Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr
      (ManyBody.Interaction.hamiltonian_translationInvariant_mono
        (Matrix.toEuclideanLin_le_toEuclideanLin_iff.mp
          (jointMixedEndpointParentInteraction_zero_le_parentInteraction A₀ A₁)))
  · have h := Finset.sum_le_sum fun (i : Fin N) (_ : i ∈ Finset.univ) =>
      Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr
        (ManyBody.Interaction.translationInvariant_term_mono (N := N) hlocal i)
    simp only [ManyBody.Interaction.translationInvariant_term_add, map_add,
      Finset.sum_add_distrib] at h
    rw [jointMixedPeriodicPhasePenalty_eq_sum_outer hN]
    change Matrix.toEuclideanLin (∑ i, (parentRingInteraction (toTensorFromBlocks
      (μ := fun _ => 1) (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 N).term i) ≤
      Matrix.toEuclideanLin (∑ i, (translationInvariant N
        (jointMixedEndpointParentInteraction A₀ A₁ 0)).term i) + _
    simpa only [map_sum, Finset.sum_add_distrib, add_assoc] using h

/-- On the actual all-zero phase subspace the Hamiltonian of the translates of the extended
interaction agrees exactly with the Hamiltonian of the parent interaction of the joint
canonical tensor. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_mul_activeProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian *
        jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N =
      Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (μ := fun _ => 1)
          (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 N).hamiltonian *
          jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hLower, hUpper⟩ := jointMixedEndpoint_periodic_comparison A₀ A₁ hN
  have hDifference : Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (μ := fun _ => 1)
          (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 N).hamiltonian -
      Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian ≤
      jointMixedPeriodicPhasePenalty d₀ d₁ D₀ D₁ N := by
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hUpper)
  apply LinearMap.ext
  intro v
  exact LinearMap.apply_eq_of_le_of_sub_le_of_apply_eq_zero hLower hDifference
    (LinearMap.congr_fun jointMixedPeriodicPhasePenalty_activeProjection v)

/-- Every actual zero-energy state is supported on all-zero physical
phases, as a consequence of the cyclic penalty.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_active_of_mem_ker
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N))
    (hv : haveI : NeZero N := ⟨by omega⟩;
      v ∈ LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian)) :
    jointMixedPeriodicActiveProjection d₀ d₁ D₀ D₁ N v = v :=
  LinearMap.IsSymmetricProjection.apply_eq_self_of_one_sub_le_twice_of_mem_ker
    jointMixedPeriodicActiveProjection_isSymmetricProjection
    (one_sub_jointMixedPeriodicActiveProjection_le_twice A₀ A₁ hN) hv

/-- The Hamiltonian of the translates of the extended joint endpoint interaction and the
Hamiltonian of the parent interaction of the joint canonical tensor have equal kernels. No
injectivity is required for this identity.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_ker_eq
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) =
        LinearMap.ker (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (μ := fun _ => 1)
          (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 N).hamiltonian) :=
  have : NeZero N := ⟨by omega⟩
  (Matrix.isPositive_toEuclideanLin_iff.mpr
    (ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant
      (posSemidef_jointMixedEndpointParentInteraction A₀ A₁ 0))).ker_eq_of_le_of_eq_on_projection
      jointMixedPeriodicActiveProjection_isSymmetricProjection
      (jointMixedEndpoint_periodic_comparison A₀ A₁ hN).1
      (jointMixedEndpoint_periodic_mul_activeProjection A₀ A₁ hN)
      (one_sub_jointMixedPeriodicActiveProjection_le_twice A₀ A₁ hN)

/-- If every nonzero eigenvalue of the Hamiltonian of the parent interaction of the joint
canonical tensor is at least `δ`, every nonzero eigenvalue of the Hamiltonian of the translates
of the extended interaction is at least the minimum of `δ` and the derived inactive-sector
penalty one half. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_gap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (hN : 2 ≤ N)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (parentRingInteraction (toTensorFromBlocks (μ := fun _ => 1)
          (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 N).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ) :
    haveI : NeZero N := ⟨by omega⟩;
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) μ →
      μ = 0 ∨ ((min δ (1 / 2) : ℝ) : ℂ) ≤ μ := by
  have : NeZero N := ⟨by omega⟩
  have hH := ManyBody.Interaction.posSemidef_hamiltonian_translationInvariant (N := N)
    (posSemidef_jointMixedEndpointParentInteraction A₀ A₁ 0)
  have hK := posSemidef_hamiltonian_parentRingInteraction (toTensorFromBlocks (μ := fun _ => 1)
    (jointMixedEndpointLeftTensor A₀ d₁ D₁)) 2 N
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr hH).forall_hasEigenvalue_of_reducing_projection
    (Matrix.isPositive_toEuclideanLin_iff.mpr hK)
    jointMixedPeriodicActiveProjection_isSymmetricProjection
    (jointMixedPeriodicActiveProjection_commute A₀ A₁ hN)
    (jointMixedEndpoint_periodic_comparison A₀ A₁ hN).1
    (jointMixedEndpoint_periodic_mul_activeProjection A₀ A₁ hN)
    (one_sub_jointMixedPeriodicActiveProjection_le_twice A₀ A₁ hN) hδ hGap

private theorem jointMixed_chain_eq_zero_of_physicalDim_eq_zero
    (hd : jointMixedPhysicalDim d₀ d₁ D₀ D₁ = 0) (hN : 0 < N)
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N)) : v = 0 := by
  ext σ
  have h := (σ ⟨0, hN⟩).isLt
  omega

/-- Each actual zero-parameter periodic vector is its embedded first
endpoint vector. The trace compression respects every block label and
requires only a positive chain length.
Source: arXiv:2203.12563, Section 5, lines 1695–1704 and 1777. -/
theorem mpv_jointMixedEndpointInterpolation_zero
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (x : Fin r) (hN : 0 < N) :
    (mpv (jointMixedEndpointInterpolation A₀ A₁ 0 x) :
      NSiteSpace (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N) =
        mpv (jointMixedEndpointLeftTensor A₀ d₁ D₁ x) := by
  let V := Matrix.coordinateInclusion
    (Fin.castAddEmb (D₁ x) : Fin (D₀ x) ↪ Fin (D₀ x + D₁ x))
  have hiso : Vᴴ * V = 1 := Matrix.coordinateInclusion_isometry _
  have hweight : bondInterpolationMatrix (D₀ x) (D₁ x) 0 = V * Vᴴ :=
    coordinateInclusion_first_projection_eq_bondWeight.symm
  have habs (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
      jointMixedEndpointInterpolation A₀ A₁ 0 x p * (V * Vᴴ) =
        jointMixedEndpointInterpolation A₀ A₁ 0 x p := by
    simp only [jointMixedEndpointInterpolation, hweight]
    calc
      jointMixedEndpointBase A₀ A₁ x p * (V * Vᴴ) * (V * Vᴴ) =
          jointMixedEndpointBase A₀ A₁ x p * V * (Vᴴ * V) * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = jointMixedEndpointBase A₀ A₁ x p * (V * Vᴴ) := by
        rw [hiso, Matrix.mul_one, Matrix.mul_assoc]
  have hcompress (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
      Vᴴ * jointMixedEndpointInterpolation A₀ A₁ 0 x p * V =
        jointMixedEndpointLeftTensor A₀ d₁ D₁ x p := by
    simp only [jointMixedEndpointInterpolation, hweight]
    calc
      Vᴴ * (jointMixedEndpointBase A₀ A₁ x p * (V * Vᴴ)) * V =
          (Vᴴ * jointMixedEndpointBase A₀ A₁ x p * V) * (Vᴴ * V) := by
        simp only [Matrix.mul_assoc]
      _ = jointMixedEndpointLeftTensor A₀ d₁ D₁ x p := by
        rw [hiso, Matrix.mul_one]
        exact jointMixedEndpointBase_first_compression A₀ A₁ x p
  funext σ
  have htrace := Kraus.trace_evalWord_compress_of_right_absorb
    (jointMixedEndpointInterpolation A₀ A₁ 0 x) Vᴴ V habs (List.ofFn σ)
    (mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hN))
  rw [show (fun p => Vᴴ * jointMixedEndpointInterpolation A₀ A₁ 0 x p * V) =
      jointMixedEndpointLeftTensor A₀ d₁ D₁ x from funext hcompress] at htrace
  exact htrace.symm


/-- The kernel of the Hamiltonian of the translates of the extended joint endpoint interaction
is exactly the span of its embedded component MPS vectors, including the two-site ring.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_groundSpace_eq
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) =
        (blockPeriodicMpvMapES (jointMixedEndpointLeftTensor A₀ d₁ D₁) N).range := by
  have : NeZero N := ⟨by omega⟩
  by_cases hd : jointMixedPhysicalDim d₀ d₁ D₀ D₁ = 0
  · ext v
    rw [jointMixed_chain_eq_zero_of_physicalDim_eq_zero hd (by omega) v]
    simp
  · let : NeZero (jointMixedPhysicalDim d₀ d₁ D₀ D₁) := ⟨hd⟩
    let : ∀ x, NeZero (D₀ x) := fun x => ⟨Nat.ne_of_gt (hD₀ x)⟩
    rw [jointMixedEndpoint_periodic_ker_eq A₀ A₁ hN]
    exact ker_hamiltonian_parentRingInteraction_toTensorFromBlocks_eq_range_blockPeriodicMpvMapES
      (fun _ => 1) (jointMixedEndpointLeftTensor A₀ d₁ D₁) (fun _ => one_ne_zero)
      (by decide : 0 < 1) (wordTupleSpanTop_jointMixedEndpointLeftTensor A₀ A₁ h₀ h₁)
      (by decide : 1 + 1 ≤ 2) hN

/-- The kernel of the Hamiltonian of the translates of the extended joint endpoint interaction
is precisely the span of the component periodic vectors of the actual path tensor at parameter
zero. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_periodic_groundSpace_eq_actual
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) =
        (blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ 0) N).range := by
  have hMap : blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ 0) N =
      blockPeriodicMpvMapES (jointMixedEndpointLeftTensor A₀ d₁ D₁) N := by
    apply ContinuousLinearMap.ext
    intro c
    apply PiLp.ext
    intro σ
    simp only [blockPeriodicMpvMapES_apply]
    apply Finset.sum_congr rfl
    intro x _
    exact congrArg
      (fun w : NSiteSpace (jointMixedPhysicalDim d₀ d₁ D₀ D₁) N => c x * w σ)
      (mpv_jointMixedEndpointInterpolation_zero A₀ A₁ x (by omega))
  rw [hMap]
  exact jointMixedEndpoint_periodic_groundSpace_eq A₀ A₁ h₀ h₁ hD₀ hN

/-- Simultaneous one-site spanning supplies an intrinsic gap for the Hamiltonian of the
translates of the extended joint endpoint interaction, uniform over all rings of at least two
sites: every nonzero eigenvalue is at least one positive constant. This uses one common joint
canonical gap, not separate gaps for individual blocks. No nonzero physical-dimension
assumption is added, so the kernel may be zero and the statement is in eigenvalue form.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem exists_uniform_jointMixedEndpoint_periodic_gap
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    (hD₀ : ∀ x, 0 < D₀ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (hN : 2 ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      (translationInvariant N (jointMixedEndpointParentInteraction A₀ A₁ 0)).hamiltonian) μ →
        μ = 0 ∨ (δ : ℂ) ≤ μ := by
  by_cases hd : jointMixedPhysicalDim d₀ d₁ D₀ D₁ = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro N hN μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    exact absurd (jointMixed_chain_eq_zero_of_physicalDim_eq_zero hd (by omega) v) hv.2
  · let : NeZero (jointMixedPhysicalDim d₀ d₁ D₀ D₁) := ⟨hd⟩
    let : ∀ x, NeZero (D₀ x) := fun x => ⟨Nat.ne_of_gt (hD₀ x)⟩
    obtain ⟨δ, hδ, hGap⟩ :=
      exists_hamiltonian_parentRingInteraction_toTensorFromBlocks_uniform_gap_of_wordTupleSpanTop
        (fun _ => 1) (jointMixedEndpointLeftTensor A₀ d₁ D₁) (fun _ => one_ne_zero)
        (by decide : 0 < 1) (wordTupleSpanTop_jointMixedEndpointLeftTensor A₀ A₁ h₀ h₁)
        (by decide : 1 + 1 ≤ 2)
    exact ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun N hN =>
      haveI : NeZero N := ⟨by omega⟩
      jointMixedEndpoint_periodic_gap A₀ A₁ hN hδ.le (hGap N)⟩

end MPSTensor.MPOSymmetry
