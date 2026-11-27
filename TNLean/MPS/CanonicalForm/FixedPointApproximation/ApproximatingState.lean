/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import QICLean.Analysis.FunctionalCalculus.CfcConjugation
import QICLean.Circuit.Gate.PartialIsometryDilation
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.Tensor.Physical.PhysicalMatrix
import TNLean.MPS.Tensor.Physical.BlockedPolar
import TNLean.MPS.Transfer.RenormalizationFixedPoint.BlockIsometryState
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import QICLean.Spectral.Radius.PowerDecay
import QICLean.Channel.Peripheral.Irreducible.IrreducibleChannel
import QICLean.Channel.FixedPoint.MeanErgodic.FixedPointProjection
import QICLean.Channel.Irreducible.InvariantProjection
import QICLean.Algebra.Matrix.MatrixCyclicPathSum
import TNLean.MPS.Tensor.Physical.BlockingTransfer
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.Tensor.Words.CyclicTrace
import TNLean.MPS.Transfer.RenormalizationFixedPoint.Defs
import TNLean.MPS.Transfer.RenormalizationFixedPoint.FixedPointPairState

/-!
# The approximating state of the log-depth preparation

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696) approximate the periodic state of a normal
tensor `A` on `N = qM` sites as follows. The `q`-site blocked tensor `B` is read as a map
`ℂ^{D²} → ℂ^{d^q}` with polar decomposition `B = V P`. As `q → ∞`, the positive factor `P`
converges to the fixed-point tensor `P_∞` (the limit in eq. (8)), and replacing `P` by `P_∞` while
keeping `V` gives the tensor `B' = V P_∞` of eq. (9), whose periodic state is
`V^{⊗M} ⊗ₖ |ω⟩_{R_k L_{k+1}}` (eq. (10)). Each copy of `V` is implemented by a unitary `U` on
the `q` sites of a block acting on an input in which the central sites are in `|0⟩` (eq. (11)).

This file proves these three steps.

## Main declarations

* `MPSTensor.tendsto_polarPosTensor_block_of_isNormal` — for a normal tensor in the gauge
  `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1`, the positive factor of the `q`-site
  blocked tensor converges to `P_∞` (arXiv:2307.01696, eq. (8)).
  The general form `MPSTensor.tendsto_polarPosTensor_of_tendsto_transferMap` only assumes the
  convergence `E_{B_q}(X) → Tr(X) σ`.
* `MPSTensor.approximatingTensor` — the tensor `B' = V P_∞` of eq. (9).
* `MPSTensor.mpv_approximatingTensor` — its periodic state is `V^{⊗M}` applied to the product of
  the pairs `ω` (eq. (10)).
* `MPSTensor.mpv_approximatingTensor_norm_sq` — for injective `B` that state is normalized.
* `MPSTensor.exists_unitary_mpv_approximatingTensor` — the periodic state of `B'` is
  `(⊗ₖ Uₖ) ⊗ₖ (|ω⟩_{R_k L_{k+1}} |0⟩_{C_k})` (eqs. (10) and (11)).
* `MPSTensor.tendsto_transferMap_block_of_spectralRadius_lt_one`,
  `MPSTensor.tendsto_transferMap_block_of_isPrimitive`: convergence to the fixed-point
  transfer map.

## References

* arXiv:2307.01696, paragraph "Approximation through the fixed-point state" (eqs. (8) and (9)) and
  paragraph "Preparing the approximate state" (eqs. (10), (11), and (12)), and Supplemental
  Material, "Proof of Lemma 1 and extension to non-normal tensors" and proof of Lemma 1'(i).
-/

open MPTensor

section FixedPointPairs

/-!
## Convergence to the fixed-point transfer map

The concrete fixed-point tensor, its cyclic pair state and their algebraic identities are
re-exported from `TNLean.MPS.Preparation.FixedPointPairState`. This module adds the spectral
convergence statements used in the log-depth preparation of arXiv:2307.01696.

The blocked transfer map converges to the rank-one map `X ↦ Tr(X) σ` when the complementary
map has spectral radius below one. For a normal left-canonical tensor, the peripheral gap
supplies that hypothesis. These are the transfer-map limits in eqs. `eq:Ek_decomp` and
`eq:B_TM`; the positive polar-factor limit is proved in
`TNLean.MPS.Preparation.ApproximatingState`.

The original import path retains the concrete pair-state API as well as these convergence
results.
-/

open scoped Kronecker Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.Operator
open Matrix Finset Filter

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

namespace MPSTensor

variable {d D : ℕ}

/-! ## Convergence of the blocked transfer map -/

/-- The blocked transfer map converges to the transfer map of `P_∞`, from the
decomposition `E_A = |ρ⟩⟨1| + R` of arXiv:2307.01696, eq. `eq:Ek_decomp`: here `A`
is left canonical, `σ` is a unit-trace fixed point, and `R = E_A - E_{P_∞}` has
spectral radius less than one. This is the limit `E_B = E_A^q → E_{P_∞}` of
eq. `eq:B_TM`, for the blocked tensor `B` of eq. `eq:B`. -/
theorem tendsto_transferMap_block_of_spectralRadius_lt_one
    (A : MPSTensor d D) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ)
    (hR : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A - Kraus.transferMap (fixedPointTensor σ))) < 1)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun q : ℕ => Kraus.transferMap (Kraus.block A q) X) atTop
      (nhds (Kraus.transferMap (fixedPointTensor σ) X)) := by
  have htr' : σ.trace ≠ 0 := by simp [htr]
  set E := Kraus.transferMap A
  set P := fixedPointProj σ htr'
  have hEP : Kraus.transferMap (fixedPointTensor σ) = P :=
    transferMap_fixedPointTensor hσ htr
  rw [hEP] at hR ⊢
  have hpow := pow_tendsto_zero_of_spectralRadius_lt_one _ hR
  have happ : Tendsto (fun q : ℕ => ((E - P) ^ q) X) atTop (nhds 0) := by
    have := ((LinearMap.toContinuousLinearMap
      ({ toFun := fun T => T X
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } :
        (Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ) →ₗ[ℂ]
          Matrix (Fin D) (Fin D) ℂ)).continuous.tendsto 0).comp hpow
    convert this using 1
    · funext q
      simp only [← map_pow]
      rfl
    · simp only [map_zero]
  have hTP : IsTracePreservingMap E := Kraus.isTracePreservingMap_mapLM_of_isTP A hA
  have hlim : Tendsto (fun q : ℕ => P X + ((E - P) ^ q) X) atTop (nhds (P X)) := by
    simpa using (tendsto_const_nhds (x := P X)).add happ
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with q hq
  rw [Kraus.transferMap_block,
    pow_eq_fixedPointProj_add_compl_pow E htr' hTP hfix hq]
  rfl

/-- For a normal tensor in the gauge of arXiv:2307.01696, eq. `eq:Ek_decomp`, the
blocked transfer map converges to the transfer map `|ρ⟩⟨1|` of `P_∞`: the limit
of eq. `eq:B_TM`. Normality is the source's definition after
eq. `eq:transfer_matrix`: the letters have no nontrivial common invariant
subspace, and `1` is the only eigenvalue of `E_A` of modulus one.

Normality is taken as `MPTensor.IsNormalTensor`; the proof uses its fields
`no_invariant_proj` and `primitive_transfer`. Its remaining field `spectral_radius_one` adds
nothing to the source's hypotheses here: in the left-canonical gauge `hA` the transfer map is a
channel, so a caller holding only the source's two conditions obtains `IsNormalTensor A` from
`MPSTensor.isNormalTensor_of_isIrreducibleFamily_leftCanonical`. -/
theorem tendsto_transferMap_block_of_isPrimitive
    (A : MPSTensor d D) (hN : IsNormalTensor A) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun q : ℕ => Kraus.transferMap (Kraus.block A q) X) atTop
      (nhds (Kraus.transferMap (fixedPointTensor σ) X)) := by
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  obtain ⟨htr', hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.transferMap A) (Kraus.isChannel_mapLM A hA)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hN.no_invariant_proj)
      hN.primitive_transfer σ hσ.posSemidef
      (by rintro rfl; simp at htr) hfix
  refine tendsto_transferMap_block_of_spectralRadius_lt_one A hA hσ.posSemidef htr hfix
    ?_ X
  rwa [transferMap_fixedPointTensor hσ.posSemidef htr]

end MPSTensor

end FixedPointPairs

section ApproximatingState

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators
open Filter Topology


namespace MPSTensor

/-! ### The Gram matrix of a tensor as a rearranged transfer map -/

variable {d D : ℕ} {α : Type*} [Fintype α]

/-- If the transfer maps of a family of tensors converge to `X ↦ Tr(X) σ`, their Gram matrices
converge to `σᵀ ⊗ 1`.

arXiv:2307.01696, eq. (8): `E_B = P† P → E_{P_∞}` with `E_{P_∞} = |ρ⟩⟨1|`. -/
theorem tendsto_gram_physicalMatrix_of_tendsto_transferMap {nq : ℕ → Type*} [∀ q, Fintype (nq q)]
    (B : ∀ q, MPTensor (nq q) (Fin D)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hlim : ∀ X, Tendsto (fun q => Kraus.transferMap (B q) X) atTop (𝓝 (X.trace • σ))) :
    Tendsto (fun q => (physicalMatrix (B q))ᴴ * physicalMatrix (B q)) atTop
      (𝓝 (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) := by
  refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
  simp_rw [conjTranspose_physicalMatrix_mul_apply]
  have h := ((continuous_apply a.1).comp (continuous_apply b.1)).tendsto _ |>.comp
    (hlim (Matrix.single b.2 a.2 1))
  have hval : (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) a b =
      ((Matrix.single b.2 a.2 (1 : ℂ)).trace • σ) b.1 a.1 := by
    by_cases hab : a.2 = b.2
    · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hab, Matrix.trace_single_eq_same]
    · simp [Matrix.kroneckerMap_apply, hab, Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]
  rw [hval]
  exact h

/-- If the transfer maps of a family of tensors converge to `X ↦ Tr(X) σ`, the positive factors
`P = (Bᴴ B)^{1/2}` of their polar decompositions converge to `(√σ)ᵀ ⊗ 1`, the map
`|α, β⟩ ↦ ∑_γ (√σ)_{αγ} |γ, β⟩`.

arXiv:2307.01696, eq. (8): `P → P_∞` as `q → ∞`. -/
theorem tendsto_polarPos_physicalMatrix_of_tendsto_transferMap {nq : ℕ → Type*} [∀ q, Fintype (nq q)]
    (B : ∀ q, MPTensor (nq q) (Fin D)) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef)
    (hlim : ∀ X, Tendsto (fun q => Kraus.transferMap (B q) X) atTop (𝓝 (X.trace • σ))) :
    Tendsto (fun q => Matrix.polarPos (physicalMatrix (B q))) atTop
      (𝓝 ((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) := by
  rw [← hσ.sqrt_transpose, ← CFC.sqrt_one (A := Matrix (Fin D) (Fin D) ℂ),
    ← (Matrix.posSemidef_transpose_iff.2 hσ).sqrt_kronecker Matrix.PosSemidef.one]
  have hmem : σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) ∈ {a | 0 ≤ a} :=
    ((Matrix.posSemidef_transpose_iff.2 hσ).kronecker Matrix.PosSemidef.one).nonneg
  have hsqrt : ContinuousOn (CFC.sqrt : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ → _)
      {a | 0 ≤ a} := by
    open scoped Matrix.Norms.L2Operator in exact CFC.continuousOn_sqrt
  exact (hsqrt _ hmem).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨tendsto_gram_physicalMatrix_of_tendsto_transferMap B hlim,
      Eventually.of_forall fun q => (Matrix.posSemidef_conjTranspose_mul_self _).nonneg⟩)

/-- The fixed-point tensor `P_∞` is the tensor whose physical matrix consists of the rows of
`(√σ)ᵀ ⊗ 1` (arXiv:2307.01696, eq. (9): `P_∞` is `√ρ` with an identity wire). -/
theorem ofPhysicalMatrix_sqrt_transpose_kronecker_one (σ : Matrix (Fin D) (Fin D) ℂ) :
    ofPhysicalMatrix (((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).submatrix
      (virtualPairEquiv D) id) = fixedPointTensor σ := by
  rw [← fixedPointTensor_reshape_eq]
  funext i α β
  simp only [ofPhysicalMatrix, virtualPairEquiv, Matrix.submatrix_apply, id]
  rw [← Equiv.apply_symm_apply finProdFinEquiv i]
  simp

/-- **Convergence of the positive part**, general form: if the transfer maps of a family of
tensors `B_q` converge to `X ↦ Tr(X) σ` with `σ ≥ 0`, the positive-part tensors `P_q` of their
polar decompositions `B_q = V_q P_q` converge to the fixed-point tensor `P_∞`.

arXiv:2307.01696, eq. (8): `E_B = E_P → E_{P_∞}` and `P → P_∞` as `q → ∞`. -/
theorem tendsto_polarPosTensor_of_tendsto_transferMap {nq : ℕ → Type*} [∀ q, Fintype (nq q)]
    (B : ∀ q, MPTensor (nq q) (Fin D)) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef)
    (hlim : ∀ X, Tendsto (fun q => Kraus.transferMap (B q) X) atTop (𝓝 (X.trace • σ))) :
    Tendsto (fun q => polarPosTensor (B q)) atTop (𝓝 (fixedPointTensor σ)) := by
  have hcont : Continuous fun G : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ =>
      ofPhysicalMatrix (G.submatrix (virtualPairEquiv D) id) :=
    continuous_pi fun i => continuous_pi fun α => continuous_pi fun β =>
      (continuous_apply (α, β)).comp (continuous_apply (virtualPairEquiv D i))
  rw [← ofPhysicalMatrix_sqrt_transpose_kronecker_one]
  exact (hcont.tendsto _).comp (tendsto_polarPos_physicalMatrix_of_tendsto_transferMap B hσ hlim)

/-- **Convergence of the positive part** (arXiv:2307.01696, eq. (8)). Let `A` be normal and in
the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` (eq. (5)). Then the positive-part
tensor `P_q` of the polar decomposition `B_q = V_q P_q` of the `q`-site blocked tensor converges
to the fixed-point tensor `P_∞` as `q → ∞`. -/
theorem tendsto_polarPosTensor_block_of_isNormal (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) :
    Tendsto (fun q => polarPosTensor (Kraus.block A q)) atTop (𝓝 (fixedPointTensor σ)) := by
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  refine tendsto_polarPosTensor_of_tendsto_transferMap (fun q => Kraus.block A q)
    hσ.posSemidef fun X => ?_
  have h := tendsto_transferMap_block_of_isPrimitive A hNT hA hσ htr hfix X
  rwa [transferMap_fixedPointTensor_apply hσ.posSemidef] at h

/-! ### The approximating tensor and its periodic state -/

/-- The **approximating tensor** `B' = V P_∞`: the isometric factor `V` of the polar
decomposition `B = V P` of a tensor `B`, applied to the physical leg of the fixed-point tensor
`P_∞` built from `σ`.

arXiv:2307.01696, eq. (9): `B = V P ≈ V P_∞ = B'`. -/
noncomputable def approximatingTensor (B : MPTensor α (Fin D)) (σ : Matrix (Fin D) (Fin D) ℂ) :
    MPTensor α (Fin D) :=
  rotatePhysical (polarIsoMatrix B) (fixedPointTensor σ)

/-- **The approximating state.** The periodic state of `B' = V P_∞` on `M ≥ 1` blocks is
`V^{⊗M}` applied to the product `⊗ₖ |ω⟩_{R_k L_{k+1}}` of the pairs of eq. (12).

arXiv:2307.01696, eqs. (9) and (10). -/
theorem mpv_approximatingTensor (B : MPTensor α (Fin D)) (σ : Matrix (Fin D) (Fin D) ℂ) {M : ℕ}
    [NeZero M] (s : Fin M → α) :
    mpv (approximatingTensor B σ) s =
      ∑ τ : Fin M → Fin (D * D), (∏ j, polarIsoMatrix B (s j) (τ j)) *
        pairProductState (fixedPointPair σ) (fun k => finProdFinEquiv.symm (τ k)) := by
  rw [approximatingTensor, mpv_rotatePhysical]
  simp_rw [mpv_fixedPointTensor]

/-- For injective `B` and `σ ≥ 0` with `Tr σ = 1`, the periodic state of `B' = V P_∞` is
normalized, so it is the approximating state `|φ'_N⟩` itself.

arXiv:2307.01696, eq. (10): `|φ'_N⟩` is `V^{⊗M}` applied to the normalized state `|Ω⟩`. -/
theorem mpv_approximatingTensor_norm_sq {B : MPTensor α (Fin D)}
    (hB : Kraus.IsInjective B) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) {M : ℕ} [NeZero M] :
    ∑ s : Fin M → α,
      star (mpv (approximatingTensor B σ) s) * mpv (approximatingTensor B σ) s = 1 := by
  simp_rw [mpv_approximatingTensor]
  rw [(isIsometry_polarIsoMatrix_of_isInjective hB).sum_star_mul_prod_const]
  rw [← pairProductState_fixedPointPair_norm_sq (N := M) hσ htr]
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _
    fun _ => rfl

/-! ### A unitary implementing the isometry -/

/-- The input state `⊗ₖ (|ω⟩_{R_k L_{k+1}} |0⟩_{C_k})` of the preparation, on `M` blocks each
with physical space `ℂ^α`. The placement `ι` sends the pair `(l, r)` of left and right
indices of a block to a basis vector of `ℂ^α`; in the source, where `D = d` so that `L` and `R`
are single sites, it is `(l, r) ↦ |l⟩_L |0⟩_C |r⟩_R`.

arXiv:2307.01696, eq. (10). -/
noncomputable def embeddedPairState [DecidableEq α] (ι : Fin D × Fin D → α) (σ : Matrix (Fin D) (Fin D) ℂ)
    {M : ℕ} (t : Fin M → α) : ℂ :=
  ∑ c : Fin M → Fin D × Fin D,
    if (fun j => ι (c j)) = t then pairProductState (fixedPointPair σ) c else 0

/-- **Product formula.** If a matrix `U` on `ℂ^α` sends the placed basis vector `|ι(l, r)⟩` to
`V |l, r⟩`, then the periodic state of `B' = V P_∞` on `M ≥ 1` blocks is
`(⊗ₖ Uₖ) ⊗ₖ (|ω⟩_{R_k L_{k+1}} |0⟩_{C_k})`.

arXiv:2307.01696, eqs. (10) and (11). -/
theorem mpv_approximatingTensor_eq_sum_embeddedPairState [DecidableEq α] (B : MPTensor α (Fin D))
    (σ : Matrix (Fin D) (Fin D) ℂ) (ι : Fin D × Fin D → α) (U : Matrix (α) (α) ℂ)
    (hU : ∀ i p, U i (ι p) = polarIsoMatrix B i (finProdFinEquiv p)) {M : ℕ} [NeZero M]
    (s : Fin M → α) :
    mpv (approximatingTensor B σ) s =
      ∑ t : Fin M → α, (∏ j, U (s j) (t j)) * embeddedPairState ι σ t := by
  rw [mpv_approximatingTensor]
  simp_rw [embeddedPairState, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true, hU]
  refine (Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _
    fun τ => ?_)
  simp only [Equiv.piCongrRight_apply, Pi.map_apply, Equiv.apply_symm_apply]
  rfl

/-- **A unitary implementing the isometry** (arXiv:2307.01696, eqs. (10) and (11)). Let the
tensor `B` be injective and let `ι` be an injective placement of the pairs `(l, r)` among the
basis vectors of `ℂ^α`, for instance `(l, r) ↦ |l⟩_L |0⟩_C |r⟩_R`. Then there is a
unitary `U` on `ℂ^α` with `U |ι(l, r)⟩ = V |l, r⟩`, and for every `M ≥ 1` the periodic state of
`B' = V P_∞` on `M` blocks is `(⊗ₖ Uₖ) ⊗ₖ (|ω⟩_{R_k L_{k+1}} |0⟩_{C_k})`. -/
theorem exists_unitary_mpv_approximatingTensor [DecidableEq α] {B : MPTensor α (Fin D)}
    (hB : Kraus.IsInjective B) (ι : Fin D × Fin D ↪ α)
    (σ : Matrix (Fin D) (Fin D) ℂ) :
    ∃ U ∈ Matrix.unitaryGroup (α) ℂ,
      (∀ i p, U i (ι p) = polarIsoMatrix B i (finProdFinEquiv p)) ∧
      ∀ (M : ℕ) [NeZero M] (s : Fin M → α),
        mpv (approximatingTensor B σ) s =
          ∑ t : Fin M → α, (∏ j, U (s j) (t j)) * embeddedPairState ι σ t := by
  obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq
    (isIsometry_polarIsoMatrix_of_isInjective hB) (finProdFinEquiv.symm.toEmbedding.trans ι)
  have hUV' : ∀ i p, U i (ι p) = polarIsoMatrix B i (finProdFinEquiv p) := fun i p => by
    simpa using hUV i (finProdFinEquiv p)
  exact ⟨U, hU, hUV', fun M _ s =>
    mpv_approximatingTensor_eq_sum_embeddedPairState B σ ι U hUV' s⟩

end MPSTensor

end ApproximatingState
