/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Analysis.SpectralRadiusPowerDecay
import QICLean.Channel.Peripheral.IrreducibleChannel
import QICLean.Channel.Primitive
import QICLean.Kraus.InvariantProjection
import TNLean.Algebra.MatrixCyclicPathSum
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.Core.CanonicalNormalization
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.RFP.Defs

/-!
# The fixed-point pair state of a normal tensor

In the log-depth preparation algorithm of Malz, Styliaris, Wei, and Cirac
(arXiv:2307.01696), a normal tensor is first brought into the gauge
`E_A = |ρ⟩⟨1| + R` of eq. `eq:Ek_decomp`: the identity is the left fixed point of
the transfer map, `ρ > 0` with `Tr ρ = 1` is the right fixed point, and `R` has
spectral radius less than one. After blocking `q` sites the positive part `P` of
the polar decomposition `B = V P` has transfer map `E_A^q`, which converges to the
rank-one map `|ρ⟩⟨1|` as `q → ∞` (the limit in eq. `eq:B_TM`). The source replaces
`P` by a fixed-point tensor `P_∞` with this rank-one transfer map; the periodic
state it generates is the product of nearest-neighbour entangled pairs
`|ω⟩ = (1 ⊗ √ρ) ∑ᵢ |ii⟩` of eq. `eq:normal_fp_local`, which is the state
`|Ω⟩ = ⊗ᵢ |ω⟩_{R_i L_{i+1}}` acted on by isometries in eq. `eq:phi_tilde`.

This file constructs `P_∞` and `ω` and proves the properties the source uses.

## Conventions

The transfer map is `Kraus.transferMap A X = ∑ᵢ Aⁱ X (Aⁱ)†`. In this convention
the gauge of eq. `eq:Ek_decomp` reads: `A` is left canonical (`∑ᵢ (Aⁱ)† Aⁱ = 1`,
so the identity is the left fixed point), and `Kraus.transferMap A σ = σ` for a
positive definite `σ` of unit trace. The rank-one map `|ρ⟩⟨1|` is
`X ↦ Tr X • σ`, which is `fixedPointProj σ`.

The physical space of `P_∞` is `ℂ^D ⊗ ℂ^D = L ⊗ R`, indexed by `Fin (D * D)`
through `finProdFinEquiv`: the letter at `(l, r)` is `√σ · |l⟩⟨r|`. Its left
virtual leg is joined to the physical leg `l` through `√σ`, and its physical
leg `r` is wired to the right virtual leg, as in the tensor `√ρ` with an
identity wire drawn in eq. `eq:key_approximation`.

The pair `ω` on `R_k ⊗ L_{k+1}` has coefficient `(√σ)_{r l}` at `(r, l)`. The
source writes `(1 ⊗ √ρ) ∑ᵢ |ii⟩`, whose coefficient at `(r, l)` is `(√ρ)_{l r}`;
the two agree under the identification `ρ = σᵀ` induced by the source's
vectorization `E_A = ∑ᵢ (Aⁱ)^* ⊗ Aⁱ` of eq. `eq:transfer_matrix`, because
`√σ` is Hermitian.

## Main declarations

* `MPSTensor.fixedPointTensor σ` — the fixed-point tensor `P_∞`.
* `MPSTensor.fixedPointPair σ` — the entangled pair `ω` of eq. `eq:normal_fp_local`.
* `MPSTensor.pairProductState ω` — the product `⊗ₖ ω_{R_k L_{k+1}}` over a ring.
* `MPSTensor.transferMap_fixedPointTensor` — `E_{P_∞} = |ρ⟩⟨1|`.
* `MPSTensor.mpv_fixedPointTensor` — the periodic state of `P_∞` on `N` sites is
  the product of the `N` nearest-neighbour pairs, with cyclic pairing.
* `MPSTensor.isTransferIdempotent_fixedPointTensor`,
  `MPSTensor.hasPhysicalBlockingIsometry_fixedPointTensor` — `P_∞` is a
  renormalization fixed point.
* `MPSTensor.fixedPointPair_norm_sq` — `⟨ω|ω⟩ = Tr ρ = 1`.
* `MPSTensor.tendsto_transferMap_blockTensor_of_spectralRadius_lt_one`,
  `MPSTensor.tendsto_transferMap_blockTensor_of_isPrimitive` — the blocked
  transfer map converges to `E_{P_∞}` (the limit in eq. `eq:B_TM`).

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696: eq. `eq:transfer_matrix`, eq. `eq:Ek_decomp`, eq. `eq:B_TM`,
  eq. `eq:key_approximation`, eq. `eq:phi_tilde`, eq. `eq:normal_fp_local`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.Operator
open Matrix Finset Filter

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

namespace MPSTensor

variable {d D : ℕ}

/-! ## The fixed-point tensor and the pair state -/

/-- The fixed-point tensor `P_∞` of arXiv:2307.01696, eq. `eq:B_TM` and
eq. `eq:key_approximation`: a tensor with physical space `ℂ^D ⊗ ℂ^D`, whose
letter at the physical pair `(l, r)` is `√σ · |l⟩⟨r|`. Its transfer map is the
rank-one map `|ρ⟩⟨1|` (`transferMap_fixedPointTensor`). -/
noncomputable def fixedPointTensor (σ : Matrix (Fin D) (Fin D) ℂ) : MPSTensor (D * D) D :=
  fun i => CFC.sqrt σ *
    Matrix.single (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 (1 : ℂ)

@[simp] lemma fixedPointTensor_finProdFinEquiv (σ : Matrix (Fin D) (Fin D) ℂ)
    (l r : Fin D) :
    fixedPointTensor σ (finProdFinEquiv (l, r)) = CFC.sqrt σ * Matrix.single l r (1 : ℂ) := by
  simp [fixedPointTensor]

/-- The entangled pair `|ω⟩ = (1 ⊗ √ρ) ∑ᵢ |ii⟩` of arXiv:2307.01696,
eq. `eq:normal_fp_local`, as a vector on `R ⊗ L = ℂ^D ⊗ ℂ^D`: its coefficient at
`(r, l)` is `(√σ)_{r l}`. See the module docstring for the identification of the
source's `ρ` with `σᵀ`. -/
noncomputable def fixedPointPair (σ : Matrix (Fin D) (Fin D) ℂ) : Fin D × Fin D → ℂ :=
  fun p => CFC.sqrt σ p.1 p.2

/-- The product of nearest-neighbour pairs `|Ω⟩ = ⊗ₖ |ω⟩_{R_k L_{k+1}}` on a ring
of `N` sites, arXiv:2307.01696, the state `|Ω⟩` following eq. `eq:unitary` and
the states `|Ω_j⟩` after eq. `eq:app_tidle_phi_1`.

The physical space of site `k` is `L_k ⊗ R_k`, and `c k = (l_k, r_k)` records the
two indices. The pair `ω` joins the right space `R_k` of site `k` to the left
space `L_{k+1}` of the next site, cyclically: the last right space `R_{N-1}` is
paired with the first left space `L_0` (`finRotate N` is `k ↦ k + 1 mod N`). -/
def pairProductState {N : ℕ} (ω : Fin D × Fin D → ℂ) (c : Fin N → Fin D × Fin D) : ℂ :=
  ∏ k : Fin N, ω ((c k).2, (c (finRotate N k)).1)

/-! ## The transfer map of the fixed-point tensor -/

private lemma single_mul_mul_conjTranspose_single (X : Matrix (Fin D) (Fin D) ℂ)
    (l r : Fin D) :
    Matrix.single l r (1 : ℂ) * X * (Matrix.single l r (1 : ℂ))ᴴ =
      X r r • Matrix.single l l (1 : ℂ) := by
  rw [Matrix.conjTranspose_single, Matrix.single_mul_mul_single, Matrix.smul_single]
  simp

private lemma mul_single_apply' (M : Matrix (Fin D) (Fin D) ℂ) (a b i j : Fin D) :
    (M * Matrix.single a b (1 : ℂ)) i j = if j = b then M i a else 0 := by
  split_ifs with h
  · subst h; simp
  · exact Matrix.mul_single_apply_of_ne (hbj := h) ..

private lemma sum_single_diag_one :
    ∑ l : Fin D, Matrix.single l l (1 : ℂ) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [Matrix.sum_apply, Matrix.single_apply]
  · simp [Matrix.sum_apply, Matrix.single_apply, h]

/-- The transfer map of `P_∞` is the rank-one map `|ρ⟩⟨1|`: every `X` is sent to
`Tr X • σ`. This is the identity `E_{P_∞} = |ρ⟩⟨1|` of arXiv:2307.01696,
eq. `eq:B_TM`. -/
theorem transferMap_fixedPointTensor_apply {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (X : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.transferMap (fixedPointTensor σ) X = X.trace • σ := by
  set S := CFC.sqrt σ
  have hS : Sᴴ = S := Matrix.conjTranspose_cfc_sqrt σ
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  rw [Kraus.transferMap_apply, ← Fintype.sum_equiv finProdFinEquiv
    (fun p => fixedPointTensor σ (finProdFinEquiv p) * X *
      (fixedPointTensor σ (finProdFinEquiv p))ᴴ) _ (fun _ => rfl)]
  have hterm : ∀ l r : Fin D,
      S * Matrix.single l r (1 : ℂ) * X * (S * Matrix.single l r (1 : ℂ))ᴴ =
        X r r • (S * Matrix.single l l (1 : ℂ) * S) := by
    intro l r
    rw [Matrix.conjTranspose_mul, hS]
    calc S * Matrix.single l r (1 : ℂ) * X * ((Matrix.single l r (1 : ℂ))ᴴ * S)
        = S * (Matrix.single l r (1 : ℂ) * X * (Matrix.single l r (1 : ℂ))ᴴ) * S := by
          simp only [Matrix.mul_assoc]
      _ = X r r • (S * Matrix.single l l (1 : ℂ) * S) := by
          rw [single_mul_mul_conjTranspose_single, Matrix.mul_smul, Matrix.smul_mul]
  have hsum : ∀ p : Fin D × Fin D,
      fixedPointTensor σ (finProdFinEquiv p) * X * (fixedPointTensor σ (finProdFinEquiv p))ᴴ =
        X p.2 p.2 • (S * Matrix.single p.1 p.1 (1 : ℂ) * S) := fun p => by
    rw [fixedPointTensor_finProdFinEquiv]; exact hterm p.1 p.2
  rw [Finset.sum_congr rfl (fun p _ => hsum p), Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_single_diag_one,
    Matrix.mul_one, hSS, ← Finset.sum_smul]
  rfl

/-- For a unit-trace `σ`, the transfer map of `P_∞` is the fixed-point projection
onto `σ`, the map `|ρ⟩⟨1|` of arXiv:2307.01696, eq. `eq:Ek_decomp` and
eq. `eq:B_TM`. -/
theorem transferMap_fixedPointTensor {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    Kraus.transferMap (fixedPointTensor σ) = fixedPointProj σ (by simp [htr]) := by
  ext1 X
  simp [transferMap_fixedPointTensor_apply hσ, fixedPointProj, htr]

/-! ## The periodic state of the fixed-point tensor -/

/-- The periodic state generated by `P_∞` on `N ≥ 1` sites is the product of the
`N` nearest-neighbour pairs `ω_{R_k L_{k+1}}`, with the cyclic pairing of `R_{N-1}`
and `L_0`: arXiv:2307.01696, eq. `eq:normal_fp_local` and the fixed-point state
`|Ω⟩ = ⊗ᵢ |ω⟩_{R_i L_{i+1}}` of eq. `eq:phi_tilde`. The physical index of site `k`
is regrouped as `(l_k, r_k) = finProdFinEquiv.symm (τ k)`. -/
theorem mpv_fixedPointTensor (σ : Matrix (Fin D) (Fin D) ℂ) {N : ℕ} [NeZero N]
    (τ : Fin N → Fin (D * D)) :
    mpv (fixedPointTensor σ) τ =
      pairProductState (fixedPointPair σ) (fun k => finProdFinEquiv.symm (τ k)) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  set S := CFC.sqrt σ
  set l : Fin (L + 1) → Fin D := fun k => (finProdFinEquiv.symm (τ k)).1
  set r : Fin (L + 1) → Fin D := fun k => (finProdFinEquiv.symm (τ k)).2
  have hletter : ∀ k, fixedPointTensor σ (τ k) = S * Matrix.single (l k) (r k) (1 : ℂ) :=
    fun k => rfl
  rw [mpv_eq, coeff_eq, evalWord_ofFn_eq_prod, Matrix.trace_ofFn_prod_eq_sum_cyclic]
  simp only [hletter, mul_single_apply']
  rw [Finset.sum_eq_single (fun m => r ((finRotate (L + 1)).symm m))]
  · simp only [Equiv.symm_apply_apply, ite_true]
    rw [pairProductState]
    exact (Fintype.prod_equiv (finRotate (L + 1)) _ _ (fun k => by
      simp only [Equiv.symm_apply_apply]; rfl)).symm
  · intro t _ ht
    have : ∃ n, t (finRotate (L + 1) n) ≠ r n := by
      by_contra h
      push Not at h
      exact ht (funext fun m => by
        simpa using h ((finRotate (L + 1)).symm m))
    obtain ⟨n, hn⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ n) (ite_eq_right_iff.2 fun h => absurd h hn)
  · simp

/-! ## Renormalization fixed point -/

/-- `P_∞` is a renormalization fixed point in the transfer-map sense: its
transfer map `|ρ⟩⟨1|` is idempotent (arXiv:2307.01696, eq. `eq:B_TM`, where
`P_∞` is the `q → ∞` fixed point of blocking). -/
theorem isTransferIdempotent_fixedPointTensor {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    IsTransferIdempotent (fixedPointTensor σ) := by
  rw [IsTransferIdempotent, transferMap_fixedPointTensor hσ htr]
  exact LinearMap.ext fun X => fixedPointProj_idempotent σ _ X

/-- `P_∞` satisfies the renormalization fixed-point relation `P_∞ P_∞ = P_∞` of
arXiv:1606.00608, Definition `defRFP`, via a physical blocking isometry. -/
theorem hasPhysicalBlockingIsometry_fixedPointTensor {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    HasPhysicalBlockingIsometry (fixedPointTensor σ) :=
  (isTransferIdempotent_iff_hasPhysicalBlockingIsometry _).1
    (isTransferIdempotent_fixedPointTensor hσ htr)

/-! ## Normalization of the pair -/

/-- The pair `ω` is normalized: `⟨ω|ω⟩ = Tr ρ`, which is `1` in the gauge of
arXiv:2307.01696, eq. `eq:Ek_decomp` (the pairs are called normalized after
eq. `eq:app_tidle_phi_1`). -/
theorem fixedPointPair_norm_sq {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) :
    ∑ p, star (fixedPointPair σ p) * fixedPointPair σ p = σ.trace := by
  set S := CFC.sqrt σ
  have hSS : Sᴴ * S = σ := by
    rw [Matrix.conjTranspose_cfc_sqrt]; exact CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  calc ∑ p, star (fixedPointPair σ p) * fixedPointPair σ p = (Sᴴ * S).trace := by
        rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Matrix.mul_apply, fixedPointPair, S]
    _ = σ.trace := by rw [hSS]

/-- Regrouping a ring of `N` sites into its `N` nearest-neighbour bonds: the
configuration `c k = (l_k, r_k)` is sent to the bond configuration
`k ↦ (r_k, l_{k+1})`, cyclically. This is the site regrouping behind
`|Ω⟩ = ⊗ᵢ |ω⟩_{R_i L_{i+1}}` in arXiv:2307.01696, eq. `eq:phi_tilde`. -/
def bondRegrouping (N D : ℕ) : (Fin N → Fin D × Fin D) ≃ (Fin N → Fin D × Fin D) where
  toFun c k := ((c k).2, (c (finRotate N k)).1)
  invFun p k := ((p ((finRotate N).symm k)).2, (p k).1)
  left_inv c := by funext k; simp only [Equiv.apply_symm_apply]
  right_inv p := by funext k; simp only [Equiv.symm_apply_apply]

/-- The product of pairs is normalized whenever each pair is: `⟨Ω|Ω⟩ = ⟨ω|ω⟩^N`
for `|Ω⟩ = ⊗ᵢ |ω⟩_{R_i L_{i+1}}` on a ring of `N` sites (arXiv:2307.01696,
eq. `eq:phi_tilde` and the normalized states `|Ω_j⟩` after
eq. `eq:app_tidle_phi_1`). -/
theorem pairProductState_norm_sq {N : ℕ} (ω : Fin D × Fin D → ℂ) :
    ∑ c : Fin N → Fin D × Fin D, star (pairProductState ω c) * pairProductState ω c =
      (∑ p, star (ω p) * ω p) ^ N := by
  rw [← Fin.prod_const, Fintype.prod_sum,
    ← (bondRegrouping N D).sum_comp (fun x => ∏ i, star (ω (x i)) * ω (x i))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pairProductState, star_prod, ← Finset.prod_mul_distrib]
  rfl

/-- The fixed-point state `|Ω⟩ = ⊗ᵢ |ω⟩_{R_i L_{i+1}}` is normalized:
`⟨Ω|Ω⟩ = (Tr ρ)^N = 1` (arXiv:2307.01696, eq. `eq:normal_fp_local` and
eq. `eq:phi_tilde`). -/
theorem pairProductState_fixedPointPair_norm_sq {N : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    ∑ c : Fin N → Fin D × Fin D,
      star (pairProductState (fixedPointPair σ) c) * pairProductState (fixedPointPair σ) c =
        1 := by
  rw [pairProductState_norm_sq, fixedPointPair_norm_sq hσ, htr, one_pow]

/-! ## Convergence of the blocked transfer map -/

/-- The blocked transfer map converges to the transfer map of `P_∞`, from the
decomposition `E_A = |ρ⟩⟨1| + R` of arXiv:2307.01696, eq. `eq:Ek_decomp`: here `A`
is left canonical, `σ` is a unit-trace fixed point, and `R = E_A - E_{P_∞}` has
spectral radius less than one. This is the limit `E_B = E_A^q → E_{P_∞}` of
eq. `eq:B_TM`, for the blocked tensor `B` of eq. `eq:B`. -/
theorem tendsto_transferMap_blockTensor_of_spectralRadius_lt_one
    (A : MPSTensor d D) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ)
    (hR : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A - Kraus.transferMap (fixedPointTensor σ))) < 1)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun q : ℕ => Kraus.transferMap (blockTensor A q) X) atTop
      (nhds (Kraus.transferMap (fixedPointTensor σ) X)) := by
  have htr' : σ.trace ≠ 0 := by simp [htr]
  set E := Kraus.transferMap A
  set P := fixedPointProj σ htr'
  have hEP : Kraus.transferMap (fixedPointTensor σ) = P :=
    transferMap_fixedPointTensor hσ htr
  rw [hEP] at hR ⊢
  have hpow := pow_tendsto_zero_of_spectralRadius_lt_one _ hR
  have happ : Tendsto (fun q : ℕ => ((E - P) ^ q) X) atTop (nhds 0) := by
    have := ((ContinuousLinearMap.apply ℂ _ X).continuous.tendsto 0).comp hpow
    convert this using 1
    · funext q
      simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, ← map_pow]
      rfl
    · simp only [map_zero]
      rfl
  have hTP : IsTracePreservingMap E := Kraus.isTracePreservingMap_mapLM_of_isTP A hA
  have hlim : Tendsto (fun q : ℕ => P X + ((E - P) ^ q) X) atTop (nhds (P X)) := by
    simpa using (tendsto_const_nhds (x := P X)).add happ
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with q hq
  rw [transferMap_blockTensor_apply,
    pow_eq_fixedPointProj_add_compl_pow E htr' hTP hfix hq]
  rfl

/-- For a normal tensor in the gauge of arXiv:2307.01696, eq. `eq:Ek_decomp`, the
blocked transfer map converges to the transfer map `|ρ⟩⟨1|` of `P_∞`: the limit
of eq. `eq:B_TM`. Normality is the source's definition after
eq. `eq:transfer_matrix`: the letters have no nontrivial common invariant
subspace, and `1` is the only eigenvalue of `E_A` of modulus one. -/
theorem tendsto_transferMap_blockTensor_of_isPrimitive
    (A : MPSTensor d D) (hIrr : Kraus.IsIrreducibleFamily A)
    (hPrim : IsPrimitive (Kraus.transferMap A)) (hA : IsLeftCanonical A)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun q : ℕ => Kraus.transferMap (blockTensor A q) X) atTop
      (nhds (Kraus.transferMap (fixedPointTensor σ) X)) := by
  have : NeZero D := ⟨by rintro rfl; simp at htr⟩
  obtain ⟨htr', hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.transferMap A) (Kraus.isChannel_mapLM A hA)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr) hPrim σ hσ.posSemidef
      (by rintro rfl; simp at htr) hfix
  refine tendsto_transferMap_blockTensor_of_spectralRadius_lt_one A hA hσ.posSemidef htr hfix
    ?_ X
  rwa [transferMap_fixedPointTensor hσ.posSemidef htr]

end MPSTensor
