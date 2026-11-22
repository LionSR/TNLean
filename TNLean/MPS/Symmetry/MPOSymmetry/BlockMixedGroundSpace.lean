/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.BlockMixedMPOFusion
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointPeriodicStateContinuity
import TNLean.MPS.ParentHamiltonian.CompactBlockParentGap

/-!
# The ground space of the block-injective mixed path

GLM23 closes the block-injective interpolation with (`REsubmission.tex`,
line 1777):

> The injectivity of every block of $A(\gamma)$ and the injectivity of $T_a$
> is justified in the same way as in the previous case. Moreover, $H(\gamma)$
> is well-behaved in the whole path its ground space is spanned by
> $\{ |\psi_{A_x(\gamma)}\rangle\}$.

Here `H(γ)` is the two-site canonical parent Hamiltonian of
`A(γ) = ⊕ₓ A_x(γ)`, as in the injective case (line 1691:
"the parent Hamiltonian $H_{A(\gamma)} \equiv H(\gamma)$"). For every
parameter in the open interval and every ring of length at least two:

* the periodic ground space of `H(γ)` is spanned by the block states
  `|ψ_{A_x(γ)}⟩`, and these states are linearly independent;
* the ground projection depends continuously on the parameter;
* on every compact subset of the open interval there is one positive gap
  bound for all rings of length at least two.

The block states remain linearly independent on the closed interval, so as
the parameter tends to an endpoint, or to any point of the closed interval,
the ground projections converge to the projection onto the span of the block
states at that point. At an endpoint the block states are the periodic states
of the endpoint blocks, embedded in the enlarged space
(`mpv_mixedEndpointInterpolation_zero`). Neither the kernel of the endpoint
Hamiltonian nor a gap at the endpoints is asserted here.

All blocks lie in disjoint physical sectors, so their one-site letters already
span the block-diagonal virtual algebra: the simultaneous injectivity length
is one, and the block-injective parent Hamiltonian theory applies with the
two-site interaction of the source.

**Scope restriction (sector-separated blocks):** every result of this module
concerns endpoint blocks that are square-alphabet tensors placed in disjoint
physical sectors, that is, the local Hilbert space is already the span
`⊕ₓ ℂ^{D^p_x} ⊗ ℂ^{D^p_x}` of the block-diagonal tensor. The source takes this
restriction without loss of generality (lines 317 and 1584--1586); its
derivation from block-injective tensors on an arbitrary common physical
alphabet is not formalized. The commutation of `H(γ)` with the common MPO is
not asserted; it needs the restrictions of
`docs/paper-gaps/glm23_mixed_path_parent_commutation.tex`. See
`docs/paper-gaps/glm23_block_injective_mixed_path.tex`.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
lines 1691 and 1695--1777.
-/

open scoped Matrix BigOperators Topology

open Filter

namespace MPSTensor.MPOSymmetry

section SectorStates

variable {s : ℕ} {n D : Fin s → ℕ}

/-- Placing a block in its physical sector does not change its word
products. -/
theorem evalWord_sectorTensor_map (A : ∀ y, MPSTensor (n y) (D y)) (x : Fin s)
    (w : List (Fin (n x))) :
    Kraus.evalWord (sectorTensor A x) (w.map fun t => finSigmaFinEquiv ⟨x, t⟩) =
      Kraus.evalWord (A x) w := by
  induction w with
  | nil => simp
  | cons t w ih => simp [Kraus.evalWord_cons, ih]

/-- On a configuration inside its own sector, a placed block has the periodic
coefficients of the block. -/
theorem mpv_sectorTensor_self (A : ∀ y, MPSTensor (n y) (D y)) (x : Fin s) {N : ℕ}
    (τ : Fin N → Fin (n x)) :
    mpv (sectorTensor A x) (fun i => finSigmaFinEquiv ⟨x, τ i⟩) = mpv (A x) τ := by
  simp only [mpv_eq, coeff]
  rw [← evalWord_sectorTensor_map A x (List.ofFn τ), List.map_ofFn]
  rfl

/-- On a nonempty configuration inside another sector, a placed block has
vanishing periodic coefficients. -/
theorem mpv_sectorTensor_of_ne (A : ∀ y, MPSTensor (n y) (D y)) {x y : Fin s}
    (hxy : y ≠ x) {N : ℕ} (hN : 0 < N) (τ : Fin N → Fin (n y)) :
    mpv (sectorTensor A x) (fun i => finSigmaFinEquiv ⟨y, τ i⟩) = 0 := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simp [coeff, List.ofFn_succ, Kraus.evalWord_cons, sectorTensor_of_ne A hxy]

/-- Blocks in disjoint physical sectors with nonzero periodic states have
linearly independent periodic states, at every positive length. -/
theorem blockPeriodicMpvMapES_sectorTensor_injective
    (A : ∀ y, MPSTensor (n y) (D y)) {N : ℕ} (hN : 0 < N)
    (hA : ∀ y, (mpv (A y) : NSiteSpace (n y) N) ≠ 0) :
    Function.Injective (blockPeriodicMpvMapES (sectorTensor A) N) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
  apply PiLp.ext
  intro y
  obtain ⟨τ, hτ⟩ := Function.ne_iff.mp (hA y)
  have h := congrArg (fun v => v (fun i => finSigmaFinEquiv ⟨y, τ i⟩)) hc
  simp only [blockPeriodicMpvMapES_apply, PiLp.zero_apply] at h
  rw [Fintype.sum_eq_single y fun x hx => by
    rw [mpv_sectorTensor_of_ne A (Ne.symm hx) hN, mul_zero],
    mpv_sectorTensor_self] at h
  exact (mul_eq_zero.mp h).resolve_right hτ

end SectorStates

section Block

variable {s : ℕ} {D₀ D₁ : Fin s → ℕ}
  (A₀ : ∀ x, MPSTensor (D₀ x * D₀ x) (D₀ x)) (A₁ : ∀ x, MPSTensor (D₁ x * D₁ x) (D₁ x))

private theorem neZero_blockMixedBond [∀ x, NeZero (D₀ x)] (x : Fin s) :
    NeZero (D₀ x + D₁ x) :=
  ⟨by have := NeZero.ne (D₀ x); omega⟩

private theorem neZero_blockMixedPhysicalDim [NeZero s] [∀ x, NeZero (D₀ x)] :
    NeZero (blockMixedPhysicalDim D₀ D₁) := by
  refine ⟨(Finset.sum_pos (fun x _ => ?_) Finset.univ_nonempty).ne'⟩
  have := NeZero.ne (D₀ x)
  positivity

/-- In the open interval the blocks of the path have full simultaneous
one-letter span. Source: GLM23, `REsubmission.tex`, line 1777. -/
theorem wordTupleSpanTop_blockMixedInterpolation
    (h₀ : ∀ x, Kraus.IsInjective (A₀ x)) (h₁ : ∀ x, Kraus.IsInjective (A₁ x))
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    WordTupleSpanTop (blockMixedInterpolation A₀ A₁ γ) 1 :=
  wordTupleSpanTop_sectorTensor _ fun y =>
    isInjective_mixedEndpointInterpolation (A₀ y) (A₁ y) (h₀ y) (h₁ y) hγ

/-- On the closed interval the block states of the path are linearly
independent at every ring of length at least two, including both endpoints.
Source: GLM23, `REsubmission.tex`, lines 1696--1701 and 1777. -/
theorem blockPeriodicMpvMapES_blockMixedInterpolation_injective
    [∀ x, NeZero (D₀ x)] [∀ x, NeZero (D₁ x)]
    (h₀ : ∀ x, Kraus.IsInjective (A₀ x)) (h₁ : ∀ x, Kraus.IsInjective (A₁ x))
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Function.Injective (blockPeriodicMpvMapES (blockMixedInterpolation A₀ A₁ γ) N) :=
  blockPeriodicMpvMapES_sectorTensor_injective _ (by omega) fun y =>
    mpv_mixedEndpointInterpolation_ne_zero (A₀ y) (A₁ y) (h₀ y) (h₁ y) γ hN

/-- In the open interval, the periodic ground space of the two-site canonical
parent Hamiltonian of `A(γ) = ⊕ₓ A_x(γ)` is spanned by the block states
`|ψ_{A_x(γ)}⟩`, for every ring of length at least two. Source: GLM23,
`REsubmission.tex`, line 1777: "its ground space is spanned by
$\{ |\psi_{A_x(\gamma)}\rangle\}$". -/
theorem ker_parentHamiltonianES_blockMixedTensor
    [NeZero s] [∀ x, NeZero (D₀ x)]
    (h₀ : ∀ x, Kraus.IsInjective (A₀ x)) (h₁ : ∀ x, Kraus.IsInjective (A₁ x))
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {N : ℕ} (hN : 2 ≤ N) :
    LinearMap.ker (parentHamiltonianES (blockMixedTensor A₀ A₁ γ) 2 N) =
      (bntMPSVectorSpan (blockMixedInterpolation A₀ A₁ γ) N).map
        (WithLp.linearEquiv 2 ℂ (NSiteSpace (blockMixedPhysicalDim D₀ D₁) N)).symm.toLinearMap := by
  have := neZero_blockMixedPhysicalDim (D₀ := D₀) (D₁ := D₁)
  have := neZero_blockMixedBond (D₀ := D₀) (D₁ := D₁)
  rw [← range_blockPeriodicMpvMapES]
  exact ker_parentHamiltonianES_toTensorFromBlocks_eq_range_blockPeriodicMpvMapES
    (fun _ => 1) _ (fun _ => one_ne_zero) one_pos
    (wordTupleSpanTop_blockMixedInterpolation A₀ A₁ h₀ h₁ hγ) le_rfl hN

/-- The block states `|ψ_{A_x(γ)}⟩` are linearly independent on the closed
interval, at every ring of length at least two. With
`ker_parentHamiltonianES_blockMixedTensor` they form a basis of the periodic
ground space in the open interval. Source: GLM23, `REsubmission.tex`,
line 1777. -/
theorem linearIndependent_mpv_blockMixedInterpolation
    [∀ x, NeZero (D₀ x)] [∀ x, NeZero (D₁ x)]
    (h₀ : ∀ x, Kraus.IsInjective (A₀ x)) (h₁ : ∀ x, Kraus.IsInjective (A₁ x))
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    LinearIndependent ℂ (fun x =>
      (mpv (blockMixedInterpolation A₀ A₁ γ x) :
        NSiteSpace (blockMixedPhysicalDim D₀ D₁) N)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg x
  have hinj := blockPeriodicMpvMapES_blockMixedInterpolation_injective A₀ A₁ h₀ h₁ γ hN
  have h0 : blockPeriodicMpvMapES (blockMixedInterpolation A₀ A₁ γ) N (WithLp.toLp 2 g) = 0 := by
    apply PiLp.ext
    intro σ
    have := congrFun hg σ
    simpa [Finset.sum_apply] using this
  have := congrArg (fun c : EuclideanSpace ℂ (Fin s) => c x) (hinj (h0.trans (map_zero _).symm))
  simpa using this

/-- In the open interval the ground projection of the two-site canonical
parent Hamiltonian depends continuously on the parameter, for every ring of
length at least two. Source: GLM23, `REsubmission.tex`, line 1777:
"$H(\gamma)$ is well-behaved in the whole path". -/
theorem continuous_blockMixed_groundSpace_starProjection
    [NeZero s] [∀ x, NeZero (D₀ x)]
    (h₀ : ∀ x, Kraus.IsInjective (A₀ x)) (h₁ : ∀ x, Kraus.IsInjective (A₁ x))
    {N : ℕ} (hN : 2 ≤ N) :
    Continuous fun γ : Set.Ioo (0 : ℝ) 1 =>
      (LinearMap.ker (parentHamiltonianES (blockMixedTensor A₀ A₁ γ) 2 N)).starProjection := by
  have := neZero_blockMixedPhysicalDim (D₀ := D₀) (D₁ := D₁)
  have := neZero_blockMixedBond (D₀ := D₀) (D₁ := D₁)
  exact continuous_parentHamiltonianES_toTensorFromBlocks_kernelProjection_family
    (fun _ _ => 1) (fun γ : Set.Ioo (0 : ℝ) 1 => blockMixedInterpolation A₀ A₁ γ)
    (fun _ _ => one_ne_zero)
    (fun x => (continuous_blockMixedInterpolation A₀ A₁ x).comp continuous_subtype_val)
    one_pos (fun γ => wordTupleSpanTop_blockMixedInterpolation A₀ A₁ h₀ h₁ γ.2) le_rfl hN

/-- On every compact subset of the open interval, the two-site canonical
parent Hamiltonians of the path have one positive gap bound, uniform over the
subset and over all rings of length at least two. Source: GLM23,
`REsubmission.tex`, line 1777: "$H(\gamma)$ is well-behaved in the whole
path"; the compactness argument is arXiv:1010.3732, Appendix A,
lines 2575--2578. -/
theorem exists_uniform_blockMixed_parentHamiltonianES_gap
    [NeZero s] [∀ x, NeZero (D₀ x)]
    (h₀ : ∀ x, Kraus.IsInjective (A₀ x)) (h₁ : ∀ x, Kraus.IsInjective (A₁ x))
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Set.Ioo 0 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ K, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (blockMixedTensor A₀ A₁ γ) 2 N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (blockMixedTensor A₀ A₁ γ) 2 N v‖ := by
  have := neZero_blockMixedPhysicalDim (D₀ := D₀) (D₁ := D₁)
  have := neZero_blockMixedBond (D₀ := D₀) (D₁ := D₁)
  have hK' : IsCompact ((↑) ⁻¹' K : Set (Set.Ioo (0 : ℝ) 1)) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_of_subset (by rwa [Subtype.range_coe])]
    exact hK
  obtain ⟨δ, hδ, hgap⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_toTensorFromBlocks_gap_all_lengths
      (fun _ _ => 1) (fun γ : Set.Ioo (0 : ℝ) 1 => blockMixedInterpolation A₀ A₁ γ)
      (fun _ _ => one_ne_zero)
      (fun x => (continuous_blockMixedInterpolation A₀ A₁ x).comp continuous_subtype_val)
      one_pos (fun γ => wordTupleSpanTop_blockMixedInterpolation A₀ A₁ h₀ h₁ γ.2) le_rfl hK'
  refine ⟨δ, hδ, fun γ hγ N hN => ?_⟩
  have : NeZero N := ⟨by omega⟩
  rw [parentHamiltonianES, parentHamiltonian_eq_toLin'_hamiltonian]
  exact (ManyBody.forall_hasEigenvalue_iff_norm
    (posSemidef_hamiltonian_parentRingInteraction _ 2 N)).mp (hgap ⟨γ, hKI hγ⟩ hγ N hN)

/-- As the parameter tends within the open interval to any point of the closed
interval, in particular to either endpoint, the ground projections of the
two-site canonical parent Hamiltonians converge to the projection onto the
span of the block states at that point. At an endpoint these are the periodic
states of the endpoint blocks, embedded in the enlarged physical space.
Source: GLM23, `REsubmission.tex`, line 1777, with the endpoint limit of the
injective case at line 1692. -/
theorem tendsto_blockMixed_groundSpace_starProjection
    [NeZero s] [∀ x, NeZero (D₀ x)] [∀ x, NeZero (D₁ x)]
    (h₀ : ∀ x, Kraus.IsInjective (A₀ x)) (h₁ : ∀ x, Kraus.IsInjective (A₁ x))
    (γ₀ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun γ : ℝ =>
      (LinearMap.ker (parentHamiltonianES (blockMixedTensor A₀ A₁ γ) 2 N)).starProjection)
      (𝓝[Set.Ioo 0 1] (γ₀ : ℝ))
      (𝓝 (blockPeriodicMpvMapES (blockMixedInterpolation A₀ A₁ γ₀) N).range.starProjection) := by
  have := neZero_blockMixedBond (D₀ := D₀) (D₁ := D₁)
  have hT : Continuous fun γ : ℝ => blockPeriodicMpvMapES (blockMixedInterpolation A₀ A₁ γ) N :=
    continuous_blockPeriodicMpvMapES_family (fun γ : ℝ => blockMixedInterpolation A₀ A₁ γ)
      (fun x => continuous_blockMixedInterpolation A₀ A₁ x) N
  have hlim := ContinuousLinearMap.continuousAt_range_starProjection_of_injective
    (fun γ : ℝ => blockPeriodicMpvMapES (blockMixedInterpolation A₀ A₁ γ) N)
    hT.continuousAt (blockPeriodicMpvMapES_blockMixedInterpolation_injective A₀ A₁ h₀ h₁ γ₀ hN)
  refine (hlim.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  rw [ker_parentHamiltonianES_blockMixedTensor A₀ A₁ h₀ h₁ hγ hN, ← range_blockPeriodicMpvMapES]

end Block

end MPSTensor.MPOSymmetry
