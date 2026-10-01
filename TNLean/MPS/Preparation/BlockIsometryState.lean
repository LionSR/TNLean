/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker
import TNLean.MPS.Chain.BlockTensor
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.Preparation.ApproximatingState
import TNLean.MPS.Preparation.BlockSites
import TNLean.Spectral.MPVOverlapTrace

/-!
# The approximating state for blocks of prescribed lengths

Cut a ring of `N` sites into `M` blocks of lengths `ℓ 0, …, ℓ (M - 1)`
(`TNLean.MPS.Preparation.BlockSites`). Blocking a tensor `A` over block `k` gives a tensor
`B_k` of physical dimension `d^{ℓ k}` with polar decomposition `B_k = V_k P_k`. For a vector
`ω` on the pair space `ℂ^D ⊗ ℂ^D`, the state

`|ψ⟩ = (⊗ₖ V_k) ⊗ₖ |ω⟩_{R_k L_{k+1}}`

(`MPSTensor.blockIsometryState`) is the approximating state of arXiv:2307.01696, eq. (10), when
`ω` is the pair of the fixed point and every block has the same length. The Supplemental Material,
proof of Theorem 1, blocks the chain into blocks "all of the same size, `q_N`, except for the last
one, which may be larger"; the present file allows any lengths.

**Scope restriction (common bond dimension):** the site-dependent declarations
`MPSTensor.chainBlockTensor`, `MPSTensor.coeff_eq_mpvFamily_chainBlockTensor`,
`MPSTensor.pairFamilyVector`, `MPSTensor.pairFamilyVector_apply`,
`MPSTensor.norm_pairFamilyVector`, `MPSTensor.blockIsoVector`, `MPSTensor.blockIsoVector_apply`,
`MPSTensor.inner_blockIsoVector`, `MPSTensor.norm_blockIsoVector`,
`MPSTensor.chainBlockIsometryState` and `MPSTensor.chainBlockIsometryState_apply` model the inhomogeneous
matrix product states of arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS",
with the same square bond dimension `D` at every site, while the source allows "bond dimension at
most `D`" varying along the ring. The translation-invariant declarations of this file are not
affected. Documented in `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## Main declarations

* `MPSTensor.mpvFamily` — the periodic state `Tr(B_0^{t_0} ⋯ B_{M-1}^{t_{M-1}})` of a family of
  tensors, one for each block.
* `MPSTensor.mpv_eq_mpvFamily_blockTensor` — the periodic state of `A` on the ring is the
  periodic state of the family of blocked tensors.
* `MPSTensor.sum_mpvFamily_mul_star_mpv` — the overlap of the periodic state of a family with a
  periodic state is the trace of the ordered product of the mixed transfer matrices.
* `MPSTensor.sum_star_blockIsometryState` — `⟨ψ|ψ⟩ = ⟨ω|ω⟩^M` when every blocked tensor is
  injective.
* `MPSTensor.inner_blockIsometryState_mpvState` — for the fixed-point pair,
  `⟨ψ|φ_N(A)⟩ = Tr ∏ₖ τ_k`, with `τ_k` the mixed transfer matrix of `P_k` against `P_∞`.
* `MPSTensor.chainBlockIsometryState` — the same state for site-dependent tensors and
  site-dependent pairs, `(⊗ₖ V_k) ⊗ₖ |ω^k⟩_{R_k L_{k+1}}`, arXiv:2307.01696, paragraph
  "Inhomogeneous short-range correlated MPS"; `MPSTensor.inner_blockIsoVector` — the
  isometries `⊗ₖ V_k` preserve inner products when every blocked tensor is injective.

## References

* arXiv:2307.01696, eqs. (9) and (10), the paragraph "Inhomogeneous short-range correlated MPS",
  and Supplemental Material, proof of Lemma 1'(i) and proof of Theorem 1.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

open MPSPreparation

variable {d D M : ℕ}

/-! ### Periodic states of families of tensors -/

/-- The periodic state of a family of tensors on a ring of `M` sites, where site `k` carries the
tensor `B k` with physical dimension `n k`: the coefficient of `t` is
`Tr(B_0^{t_0} B_1^{t_1} ⋯ B_{M-1}^{t_{M-1}})`. -/
noncomputable def mpvFamily {n : Fin M → ℕ} (B : ∀ k, MPSTensor (n k) D)
    (t : ∀ k, Fin (n k)) : ℂ :=
  Matrix.trace (List.ofFn fun k => B k (t k)).prod

/-- A constant family generates the periodic state of its tensor. -/
theorem mpvFamily_const {κ : ℕ} (C : MPSTensor κ D) (u : Fin M → Fin κ) :
    mpvFamily (n := fun _ => κ) (fun _ => C) u = mpv C u := by
  rw [mpvFamily, mpv_eq, coeff_eq, evalWord_ofFn_eq_prod]

/-- Physical maps on the sites of a family pull out of its periodic state. -/
theorem mpvFamily_rotatePhysical {κ : ℕ} {n : Fin M → ℕ}
    (W : ∀ k, Matrix (Fin (n k)) (Fin κ) ℂ) (C : Fin M → MPSTensor κ D) (t : ∀ k, Fin (n k)) :
    mpvFamily (fun k => rotatePhysical (W k) (C k)) t =
      ∑ u : Fin M → Fin κ, (∏ k, W k (t k) (u k)) * mpvFamily (n := fun _ => κ) C u := by
  simp only [mpvFamily, rotatePhysical_apply]
  exact Matrix.trace_prod_ofFn_sum_smul (fun k j => W k (t k) j) (fun k j => C k j)

/-- A configuration of the ring, read block by block as blocked physical indices. -/
noncomputable def blockIndexEquiv (d : ℕ) {N : ℕ} {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) :
    Cfg d N ≃ ∀ k, Fin (blockPhysDim d (ℓ k)) :=
  (blockCfgEquiv d hN).trans (Equiv.piCongrRight fun k => (decodeBlockEquiv d (ℓ k)).symm)

@[simp] theorem blockIndexEquiv_apply {N : ℕ} {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (s : Cfg d N) (k : Fin M) :
    blockIndexEquiv d hN s k = (decodeBlockEquiv d (ℓ k)).symm (s ∘ blockSite hN k) := by
  simp [blockIndexEquiv]

/-- **Blocking into blocks of prescribed lengths.** The periodic state of `A` on the ring is the
periodic state of the family of blocked tensors `B_k = A^{⊗ ℓ k}` on the blocks. -/
theorem mpv_eq_mpvFamily_blockTensor (A : MPSTensor d D) {N : ℕ} {ℓ : Fin M → ℕ}
    (hN : ∑ k, ℓ k = N) (s : Cfg d N) :
    mpv A s = mpvFamily (fun k => blockTensor A (ℓ k)) (blockIndexEquiv d hN s) := by
  rw [mpv_eq, coeff_eq, evalWord_ofFn_eq_prod, prod_ofFn_blockSite ℓ hN, mpvFamily]
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => ?_)
  rw [blockIndexEquiv_apply]
  change _ = Kraus.evalWord A (Kraus.wordOfBlock d (ℓ k) _)
  rw [Kraus.wordOfBlock, Kraus.decodeBlock_decodeBlockEquiv_symm, evalWord_ofFn_eq_prod]
  rfl

/-- The entries of the mixed transfer matrix: `τ_{(j,i),(l,m)} = ∑ₐ (X^a)_{im} (Y^a)*_{jl}`. -/
theorem transferMatrix_mixedMapLM_apply {κ : ℕ} (X Y : MPSTensor κ D) (p p' : Fin D × Fin D) :
    transferMatrix (Kraus.mixedMapLM X Y) p p' =
      ∑ a, X a p.2 p'.2 * star (Y a p.1 p'.1) := by
  obtain ⟨j, i⟩ := p
  obtain ⟨l, m⟩ := p'
  rw [transferMatrix_apply, Kraus.mixedMapLM_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and,
    Finset.sum_ite_eq, ite_mul]

/-- **Overlaps of families as traces of transfer matrices.** For a family `X` of tensors on a
ring of `M ≥ 1` sites and a tensor `Y`,
`∑ᵤ Tr(X_0^{u_0} ⋯ X_{M-1}^{u_{M-1}}) Tr(Y^{u_0} ⋯ Y^{u_{M-1}})^* = Tr(τ_0 ⋯ τ_{M-1})`, where
`τ_k` is the transfer matrix of the mixed map of `X_k` against `Y`.

arXiv:2103.13367, the mixed transfer matrices `τ_{AB} = A†B` after eq. `eq:a_tensor`, here with a
different tensor on each site. -/
theorem sum_mpvFamily_mul_star_mpv [NeZero M] {κ : ℕ} (X : Fin M → MPSTensor κ D)
    (Y : MPSTensor κ D) :
    ∑ u : Fin M → Fin κ, mpvFamily (n := fun _ => κ) X u * star (mpv Y u) =
      Matrix.trace (List.ofFn fun k => transferMatrix (Kraus.mixedMapLM (X k) Y)).prod := by
  classical
  obtain ⟨L, rfl⟩ : ∃ L, M = L + 1 := ⟨M - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne M)).symm⟩
  rw [Matrix.trace_ofFn_prod_eq_sum_cyclic]
  simp_rw [transferMatrix_mixedMapLM_apply, Fintype.prod_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [mpvFamily, Matrix.trace_ofFn_prod_eq_sum_cyclic, mpv_eq, coeff_eq, evalWord_ofFn_eq_prod,
    Matrix.trace_ofFn_prod_eq_sum_cyclic, star_sum, Finset.sum_mul_sum,
    ← (Equiv.arrowProdEquivProdArrow (Fin (L + 1)) (fun _ => Fin D) (fun _ => Fin D)).symm.sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_prod, ← Finset.prod_mul_distrib]
  rfl

/-! ### The state `(⊗ₖ V_k) ⊗ₖ |ω⟩` -/

/-- **The state `(⊗ₖ V_k) ⊗ₖ |ω⟩_{R_k L_{k+1}}`** for blocks of lengths `ℓ`: `V_k` is the
isometric factor of the polar decomposition of the tensor `A` blocked over block `k`, and `ω` is a
vector on the pair space `ℂ^D ⊗ ℂ^D` joining the right leg of each block to the left leg of the
next one, cyclically.

arXiv:2307.01696, eq. (10), where `ω` is the pair of the fixed point and all blocks have the same
length `q`; Supplemental Material, proof of Theorem 1, where the last block "may be larger". -/
noncomputable def blockIsometryState (A : MPSTensor d D) (ω : Fin D × Fin D → ℂ) {N : ℕ}
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) : MPVSpace d N :=
  (EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm fun s =>
    ∑ τ : Fin M → Fin (D * D),
      (∏ k, polarIsoMatrix (blockTensor A (ℓ k)) (blockIndexEquiv d hN s k) (τ k)) *
        pairProductState ω (fun k => finProdFinEquiv.symm (τ k))

@[simp] theorem blockIsometryState_apply (A : MPSTensor d D) (ω : Fin D × Fin D → ℂ) {N : ℕ}
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) (s : Cfg d N) :
    blockIsometryState A ω hN s = ∑ τ : Fin M → Fin (D * D),
      (∏ k, polarIsoMatrix (blockTensor A (ℓ k)) (blockIndexEquiv d hN s k) (τ k)) *
        pairProductState ω (fun k => finProdFinEquiv.symm (τ k)) := by
  simp [blockIsometryState, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- **Norm of the state.** If every blocked tensor is injective, then `⟨ψ|ψ⟩ = ⟨ω|ω⟩^M`.

arXiv:2307.01696, eq. (10): the isometries on the blocks preserve the norm of the product of the
pairs. -/
theorem sum_star_blockIsometryState (A : MPSTensor d D) (ω : Fin D × Fin D → ℂ) {N : ℕ}
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) (hB : ∀ k, Kraus.IsInjective (blockTensor A (ℓ k))) :
    ∑ s : Cfg d N, star (blockIsometryState A ω hN s) * blockIsometryState A ω hN s =
      (∑ p, star (ω p) * ω p) ^ M := by
  classical
  simp_rw [blockIsometryState_apply]
  rw [Fintype.sum_equiv (blockIndexEquiv d hN) _ (fun t => star (∑ τ : Fin M → Fin (D * D),
      (∏ k, polarIsoMatrix (blockTensor A (ℓ k)) (t k) (τ k)) *
        pairProductState ω (fun k => finProdFinEquiv.symm (τ k))) *
      ∑ τ : Fin M → Fin (D * D), (∏ k, polarIsoMatrix (blockTensor A (ℓ k)) (t k) (τ k)) *
        pairProductState ω (fun k => finProdFinEquiv.symm (τ k))) fun _ => rfl,
    Matrix.IsIsometry.sum_star_mul_prod
      (fun k => isIsometry_polarIsoMatrix_of_isInjective (hB k)),
    ← pairProductState_norm_sq (N := M) ω]
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _ fun _ => rfl

/-- **Overlap with the periodic state.** If every blocked tensor is injective, the overlap of
`(⊗ₖ V_k) ⊗ₖ |ω⟩`, with `ω` the pair of the fixed point, with the periodic state of `A` is the
trace of the ordered product of the mixed transfer matrices `τ_k` of the positive parts `P_k`
against the fixed-point tensor `P_∞`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i): the isometries cancel and the
overlap is that of the positive parts with the fixed point, `Tr ∏ₖ τ_{AB}` in the notation of
arXiv:2103.13367. -/
theorem inner_blockIsometryState_mpvState [NeZero M] [NeZero D] (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ) {N : ℕ} {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (hB : ∀ k, Kraus.IsInjective (blockTensor A (ℓ k))) :
    ⟪blockIsometryState A (fixedPointPair σ) hN, mpvState A N⟫_ℂ =
      Matrix.trace (List.ofFn fun k => transferMatrix (Kraus.mixedMapLM
        (polarPosTensor (blockTensor A (ℓ k))) (fixedPointTensor σ))).prod := by
  classical
  rw [← sum_mpvFamily_mul_star_mpv, PiLp.inner_apply]
  simp only [RCLike.inner_apply, mpvState_apply, blockIsometryState_apply]
  have hB' : ∀ t : ∀ k, Fin (blockPhysDim d (ℓ k)),
      mpvFamily (fun k => blockTensor A (ℓ k)) t =
        ∑ u : Fin M → Fin (D * D), (∏ k, polarIsoMatrix (blockTensor A (ℓ k)) (t k) (u k)) *
          mpvFamily (n := fun _ => D * D) (fun k => polarPosTensor (blockTensor A (ℓ k))) u :=
    fun t => by
      conv_lhs => rw [show (fun k => blockTensor A (ℓ k)) = fun k => rotatePhysical
        (polarIsoMatrix (blockTensor A (ℓ k))) (polarPosTensor (blockTensor A (ℓ k))) from
          funext fun k => (rotatePhysical_polarIsoMatrix_polarPosTensor _).symm]
      exact mpvFamily_rotatePhysical _ _ t
  have hpp : ∀ τ : Fin M → Fin (D * D),
      pairProductState (fixedPointPair σ) (fun k => finProdFinEquiv.symm (τ k)) =
        mpv (fixedPointTensor σ) τ := fun τ => (mpv_fixedPointTensor σ τ).symm
  simp_rw [hpp]
  rw [Fintype.sum_equiv (blockIndexEquiv d hN) _ (fun t => star
      (∑ τ : Fin M → Fin (D * D), (∏ k, polarIsoMatrix (blockTensor A (ℓ k)) (t k) (τ k)) *
        mpv (fixedPointTensor σ) τ) * mpvFamily (fun k => blockTensor A (ℓ k)) t)
      fun s => by rw [mpv_eq_mpvFamily_blockTensor A hN, mul_comm]; rfl]
  simp_rw [hB']
  rw [Matrix.IsIsometry.sum_star_mul_prod
    (fun k => isIsometry_polarIsoMatrix_of_isInjective (hB k))]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-! ### Site-dependent tensors and pairs -/

/-- The blocked tensor of block `k` of a chain of site-dependent tensors: the tensor
`B_k` with `B_k^{σ} = A_{o_k}^{σ₀} ⋯ A_{o_k + ℓ_k - 1}^{σ_{ℓ_k - 1}}`.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": the tensors after
"blocking `q`" sites of a matrix product state that is not translation invariant. -/
noncomputable def chainBlockTensor {N : ℕ} {ℓ : Fin M → ℕ} (A : MPSChainTensor d D N)
    (hN : ∑ k, ℓ k = N) (k : Fin M) : MPSTensor (blockPhysDim d (ℓ k)) D :=
  MPSChainTensor.blockTensor fun j => A (blockSite hN k j)

/-- For a constant chain the blocked tensors are those of its tensor. -/
theorem chainBlockTensor_const (A : MPSTensor d D) {N : ℕ} {ℓ : Fin M → ℕ}
    (hN : ∑ k, ℓ k = N) (k : Fin M) :
    chainBlockTensor (fun _ => A) hN k = blockTensor A (ℓ k) :=
  MPSChainTensor.blockTensor_const A

/-- **Blocking a site-dependent chain.** The periodic state of a chain of site-dependent
tensors is the periodic state of the family of its blocked tensors. -/
theorem coeff_eq_mpvFamily_chainBlockTensor {N : ℕ} {ℓ : Fin M → ℕ} (A : MPSChainTensor d D N)
    (hN : ∑ k, ℓ k = N) (s : Cfg d N) :
    MPSChainTensor.coeff A s = mpvFamily (chainBlockTensor A hN) (blockIndexEquiv d hN s) := by
  rw [MPSChainTensor.coeff_eq, MPSChainTensor.eval_eq_prod_ofFn,
    prod_ofFn_blockSite ℓ hN (fun i => A i (s i)), mpvFamily]
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => ?_)
  rw [blockIndexEquiv_apply, chainBlockTensor, MPSChainTensor.blockTensor_decodeBlockEquiv_symm,
    MPSChainTensor.eval_eq_prod_ofFn]
  rfl

/-- The product of site-dependent pairs as a vector on `M` sites of dimension `D²`, the site `k`
carrying the pair of indices `(l_k, r_k)`. -/
noncomputable def pairFamilyVector (ω : Fin M → Fin D × Fin D → ℂ) : MPVSpace (D * D) M :=
  (EuclideanSpace.equiv (ι := Cfg (D * D) M) (𝕜 := ℂ)).symm fun τ =>
    pairFamilyState ω fun k => finProdFinEquiv.symm (τ k)

@[simp] theorem pairFamilyVector_apply (ω : Fin M → Fin D × Fin D → ℂ) (τ : Cfg (D * D) M) :
    pairFamilyVector ω τ = pairFamilyState ω fun k => finProdFinEquiv.symm (τ k) := by
  simp [pairFamilyVector, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- A product of unit pairs is a unit vector. -/
theorem norm_pairFamilyVector {ω : Fin M → Fin D × Fin D → ℂ}
    (hω : ∀ k, ∑ p, star (ω k p) * ω k p = 1) : ‖pairFamilyVector ω‖ = 1 := by
  have h := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (pairFamilyVector ω)).symm
  rw [PiLp.inner_apply] at h
  simp only [RCLike.inner_apply] at h
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (Complex.ofReal_injective ?_)
  push_cast
  refine h.trans ?_
  have hsum := pairFamilyState_norm_sq ω
  simp only [hω, Finset.prod_const_one] at hsum
  rw [← hsum, ← Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm)
    (fun τ : Cfg (D * D) M => star (pairFamilyVector ω τ) * pairFamilyVector ω τ) _
    fun _ => by simp only [pairFamilyVector_apply]; rfl]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **The isometries on the blocks**, `(⊗ₖ V_k) x`, for tensors `B_k` on the blocks of a ring
cut into blocks of lengths `ℓ`, with `V_k` the isometric factor of the polar decomposition of
`B_k`, applied to a vector `x` on `M` sites of dimension `D²`.

arXiv:2307.01696, eq. (10) and the paragraph "Inhomogeneous short-range correlated MPS": "the
isometry" `⊗ᵢ V_i` applied to `|Ω⟩`. -/
noncomputable def blockIsoVector {N : ℕ} {ℓ : Fin M → ℕ}
    (B : ∀ k, MPSTensor (blockPhysDim d (ℓ k)) D) (hN : ∑ k, ℓ k = N)
    (x : MPVSpace (D * D) M) : MPVSpace d N :=
  (EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm fun s =>
    ∑ τ : Fin M → Fin (D * D), (∏ k, polarIsoMatrix (B k) (blockIndexEquiv d hN s k) (τ k)) * x τ

@[simp] theorem blockIsoVector_apply {N : ℕ} {ℓ : Fin M → ℕ}
    (B : ∀ k, MPSTensor (blockPhysDim d (ℓ k)) D) (hN : ∑ k, ℓ k = N) (x : MPVSpace (D * D) M)
    (s : Cfg d N) :
    blockIsoVector B hN x s = ∑ τ : Fin M → Fin (D * D),
      (∏ k, polarIsoMatrix (B k) (blockIndexEquiv d hN s k) (τ k)) * x τ := by
  simp [blockIsoVector, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- **The isometries preserve inner products.** If every blocked tensor is injective, then
`⟨(⊗ₖ V_k) x, (⊗ₖ V_k) y⟩ = ⟨x, y⟩`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state": for injective `B`,
`V†V = 1`. -/
theorem inner_blockIsoVector {N : ℕ} {ℓ : Fin M → ℕ}
    {B : ∀ k, MPSTensor (blockPhysDim d (ℓ k)) D} (hN : ∑ k, ℓ k = N)
    (hB : ∀ k, Kraus.IsInjective (B k)) (x y : MPVSpace (D * D) M) :
    ⟪blockIsoVector B hN x, blockIsoVector B hN y⟫_ℂ = ⟪x, y⟫_ℂ := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply, blockIsoVector_apply]
  have h := Matrix.IsIsometry.sum_star_mul_prod
    (fun k => isIsometry_polarIsoMatrix_of_isInjective (hB k)) (fun τ => x τ) (fun τ => y τ)
  rw [← Fintype.sum_equiv (blockIndexEquiv d hN) _ _ fun _ => rfl] at h
  simp only [mul_comm (star _)] at h ⊢
  exact h

/-- The isometries preserve norms: `‖(⊗ₖ V_k) x‖ = ‖x‖` when every blocked tensor is
injective. -/
theorem norm_blockIsoVector {N : ℕ} {ℓ : Fin M → ℕ}
    {B : ∀ k, MPSTensor (blockPhysDim d (ℓ k)) D} (hN : ∑ k, ℓ k = N)
    (hB : ∀ k, Kraus.IsInjective (B k)) (x : MPVSpace (D * D) M) :
    ‖blockIsoVector B hN x‖ = ‖x‖ := by
  have h := inner_blockIsoVector hN hB x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by exact_mod_cast h)

/-- **The state `(⊗ₖ V_k) ⊗ₖ |ω^k⟩_{R_k L_{k+1}}`** for a chain of site-dependent tensors `A`
blocked into blocks of lengths `ℓ`, and site-dependent pairs `ω^k`: `V_k` is the isometric
factor of the polar decomposition of the blocked tensor of block `k`.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": "preparing `|Ω⟩` and
implementing the isometry". -/
noncomputable def chainBlockIsometryState {N : ℕ} {ℓ : Fin M → ℕ} (A : MPSChainTensor d D N)
    (ω : Fin M → Fin D × Fin D → ℂ) (hN : ∑ k, ℓ k = N) : MPVSpace d N :=
  blockIsoVector (chainBlockTensor A hN) hN (pairFamilyVector ω)

@[simp] theorem chainBlockIsometryState_apply {N : ℕ} {ℓ : Fin M → ℕ}
    (A : MPSChainTensor d D N) (ω : Fin M → Fin D × Fin D → ℂ) (hN : ∑ k, ℓ k = N)
    (s : Cfg d N) :
    chainBlockIsometryState A ω hN s = ∑ τ : Fin M → Fin (D * D),
      (∏ k, polarIsoMatrix (chainBlockTensor A hN k) (blockIndexEquiv d hN s k) (τ k)) *
        pairFamilyState ω (fun k => finProdFinEquiv.symm (τ k)) := by
  simp [chainBlockIsometryState]

/-- For a constant chain and equal pairs, the state is `blockIsometryState`. -/
theorem blockIsometryState_eq_chainBlockIsometryState (A : MPSTensor d D)
    (ω : Fin D × Fin D → ℂ) {N : ℕ} {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) :
    blockIsometryState A ω hN = chainBlockIsometryState (fun _ => A) (fun _ => ω) hN := by
  ext s
  simp [chainBlockTensor_const, pairFamilyState_const]

/-- For a unit vector `ω` and injective blocked tensors, `(⊗ₖ V_k) ⊗ₖ |ω⟩` is a unit vector. -/
theorem norm_blockIsometryState (A : MPSTensor d D) {ω : Fin D × Fin D → ℂ}
    (hω : ∑ p, star (ω p) * ω p = 1) {N : ℕ} {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (hB : ∀ k, Kraus.IsInjective (blockTensor A (ℓ k))) :
    ‖blockIsometryState A ω hN‖ = 1 := by
  rw [blockIsometryState_eq_chainBlockIsometryState, chainBlockIsometryState,
    norm_blockIsoVector hN (fun k => by rw [chainBlockTensor_const]; exact hB k),
    norm_pairFamilyVector fun _ => hω]

end MPSTensor
