/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthUpperBound
import TNLean.MPS.Preparation.VaryingBondBlocks

/-!
# Inhomogeneous short-range correlated matrix product states

A chain `A` of site-dependent tensors with bond dimension `D` on a ring of `N` sites, cut into
`M` blocks of lengths `ℓ 0, …, ℓ (M - 1)`, has on block `k` the blocked tensor `B_k` with polar
decomposition `B_k = V_k P_k`. The positive parts `P_k` are tensors of physical dimension `D²`
and bond dimension `D`, and generate the state `|φ_pos⟩` on the `M` blocks
(`MPSPreparation.chainPosState`). The state of the chain is exactly
`|φ_N⟩ = (⊗ₖ V_k) |φ_pos⟩` (`MPSPreparation.chainState_eq_blockIsoVector`). If `B_k` is injective
on a set `S_k` of bond pairs, `V_k` is an isometry on `S_k`, `φ_pos` is supported on the sets
`S_k`, and `⟨(⊗ₖ V_k) Ω, φ_N⟩ = ⟨Ω, φ_pos⟩` for the normalized states
(`MPSPreparation.inner_chainBlockIsometryState_normalize`).

The source's chains have bond dimensions at most `D`, varying along the ring
(`VaryingBondChain`); padded with zeros they are chains of bond dimension `D` with
the same state. For blocks of at least one site, injectivity of the blocked tensors
(`VaryingBondChain.IsBlockInjective`, stated for the padded chain) makes every padded blocked
tensor injective on the rectangle of its bonds. The source calls such a chain short-range correlated
if `|φ_pos⟩` is close to a product `|Ω⟩ = ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` of pairs, each joining the right
leg of one block to the left leg of the next. At a fixed ring this is the statement that the
error `ε(Ω, φ_pos)` is at most `δ` for some unit pairs
(`VaryingBondChain.IsPairApproximable`). When every blocked tensor is injective, the state
`(⊗ₖ V_k) |Ω⟩` is prepared in depth at most `C L` for blocks of lengths at most `L`, with `C`
depending only on `d` and `D`, and its error against `|φ_N⟩` is exactly `ε(Ω, φ_pos)`
(`MPSPreparation.exists_isPreparedInDepth_inhomogeneous`). Without injectivity `V_k` is a
partial isometry and the block unitaries implement isometric extensions of it; that case, and
the preparation under the approximation hypothesis, are in
`TNLean.MPS.Preparation.PartialIsometryPreparation`. The source states a total depth
`O(log(N/ε))`; the bound `C L` gives this depth when `L = O(log(N/ε))`. Neither the choice of
the block lengths nor the asymptotic statement is formalized here.

The error is `ε(φ, ψ) = 1 - |⟨φ|ψ⟩|` of normalized vectors, as displayed in arXiv:2307.01696,
paragraph "Preliminaries".

**Scope restriction (injective blocks of length at least `3D`):** the preparation theorem
`MPSPreparation.exists_isPreparedInDepth_inhomogeneous` assumes that the blocked tensors are
injective, which the source assumes for its polar decompositions (arXiv:2307.01696, the footnote
to the paragraph "Approximation through the fixed-point state") and which makes
`(⊗ₖ V_k) |Ω⟩` itself a unit vector, and that the blocks have lengths at least `3D`, which the
construction of the circuit needs. The bond dimensions are those of the source, at most `D` and
varying along the ring. Documented in `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## Main results

* `MPSPreparation.chainState_eq_blockIsoVector` — `|φ_N⟩ = (⊗ₖ V_k) |φ_pos⟩`.
* `MPSPreparation.norm_chainState_eq` — `‖φ_N‖ = ‖φ_pos‖` for every chain.
* `MPSPreparation.inner_chainBlockIsometryState_normalize` — the isometries preserve the
  overlap: `⟨(⊗ₖ V_k) Ω, φ_N⟩ = ⟨Ω, φ_pos⟩` for the normalized states.
* `MPSPreparation.exists_isPreparedInDepth_inhomogeneous` — preparation in depth `O(L)` with
  error `ε(Ω, φ_pos)` for injective blocked tensors.

## References

* arXiv:2307.01696, paragraphs "Preliminaries", "Approximation through the fixed-point state"
  (with its footnote) and "Inhomogeneous short-range correlated MPS", eq. `eq:phi_pos`, and
  Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors".
-/

open Matrix MPSTensor
open scoped BigOperators InnerProductSpace
open QuantumCircuit

namespace MPSPreparation

variable {d D M N : ℕ} {ℓ : Fin M → ℕ}

/-! ### The states -/

/-- The unnormalized state `|φ_N⟩` of a chain of site-dependent tensors on a ring of `N` sites:
the coefficient of `s` is `Tr(A_0^{s_0} ⋯ A_{N-1}^{s_{N-1}})`. -/
noncomputable def chainState (A : MPSChainTensor d D N) : MPVSpace d N :=
  (EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm fun s => MPSChainTensor.coeff A s

@[simp] theorem chainState_apply (A : MPSChainTensor d D N) (s : Cfg d N) :
    chainState A s = MPSChainTensor.coeff A s := by
  simp [chainState, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- **The state of the positive parts**, `|φ_pos⟩`, on the `M` blocks: block `k` carries the
positive part `P_k` of the polar decomposition of the blocked tensor of block `k`, read as a
tensor of physical dimension `D²`, and the coefficient of `τ` is
`Tr(P_0^{τ_0} ⋯ P_{M-1}^{τ_{M-1}})`.

arXiv:2307.01696, eq. `eq:phi_pos`: the state that "arises after blocking `q` sites and keeping
the positive part of the decomposition of `|φ_N⟩`". -/
noncomputable def chainPosState (A : MPSChainTensor d D N) (hN : ∑ k, ℓ k = N) :
    MPVSpace (D * D) M :=
  (EuclideanSpace.equiv (ι := Cfg (D * D) M) (𝕜 := ℂ)).symm fun τ =>
    mpvFamily (n := fun _ => D * D) (fun k => polarPosTensor (chainBlockTensor A hN k)) τ

@[simp] theorem chainPosState_apply (A : MPSChainTensor d D N) (hN : ∑ k, ℓ k = N)
    (τ : Cfg (D * D) M) :
    chainPosState A hN τ =
      mpvFamily (n := fun _ => D * D) (fun k => polarPosTensor (chainBlockTensor A hN k)) τ := by
  simp [chainPosState, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- **The state is the isometries applied to the positive parts:** `|φ_N⟩ = (⊗ₖ V_k) |φ_pos⟩`,
for every cutting of the ring into blocks. No injectivity is needed.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": the states after
blocking are approximated "up to quasi-local isometries", the isometries `V_k` of the polar
decompositions `B_k = V_k P_k`. -/
theorem chainState_eq_blockIsoVector (A : MPSChainTensor d D N) (hN : ∑ k, ℓ k = N) :
    chainState A = blockIsoVector (chainBlockTensor A hN) hN (chainPosState A hN) := by
  ext s
  have h := mpvFamily_rotatePhysical (fun k => polarIsoMatrix (chainBlockTensor A hN k))
    (fun k => polarPosTensor (chainBlockTensor A hN k)) (blockIndexEquiv d hN s)
  simp only [rotatePhysical_polarIsoMatrix_polarPosTensor] at h
  rw [chainState_apply, coeff_eq_mpvFamily_chainBlockTensor A hN, h, blockIsoVector_apply]
  simp only [chainPosState_apply]

/-- The isometries on the blocks commute with scalars. -/
theorem blockIsoVector_smul {B : ∀ k, MPSTensor (blockPhysDim d (ℓ k)) D} (hN : ∑ k, ℓ k = N)
    (c : ℂ) (x : MPVSpace (D * D) M) :
    blockIsoVector B hN (c • x) = c • blockIsoVector B hN x := by
  ext s
  simp only [blockIsoVector_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

/-- The state of the positive parts has no component outside the sets `S_k` when every blocked
tensor `B_k` is injective on `S_k`: the positive part `P_k` vanishes outside `S_k`. -/
theorem chainPosState_eq_zero {A : MPSChainTensor d D N} (hN : ∑ k, ℓ k = N)
    {S : Fin M → Set (Fin D × Fin D)} (hB : ∀ k, IsInjectiveOn (chainBlockTensor A hN k) (S k))
    {τ : Cfg (D * D) M} (hτ : ∃ k, virtualPairEquiv D (τ k) ∉ S k) : chainPosState A hN τ = 0 := by
  obtain ⟨k, hk⟩ := hτ
  rw [chainPosState_apply, mpvFamily]
  have h0 : (List.ofFn fun j => polarPosTensor (chainBlockTensor A hN j) (τ j)).prod = 0 :=
    List.prod_eq_zero (List.mem_ofFn.mpr ⟨k, polarPosTensor_eq_zero (hB k) hk⟩)
  rw [h0, Matrix.trace_zero]

/-- **The norm of the state is the norm of the state of the positive parts**, for every chain
and every cutting into blocks: `‖φ_N‖ = ‖φ_pos‖`. The isometric factors are partial isometries,
`V_k†V_k = Π_k`, and `|φ_pos⟩` is fixed by `⊗ₖ Π_k` because `Π_k P_k = P_k`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `V†V = Π` with `Π` the projector onto the image of `P`. -/
theorem norm_chainState_eq (A : MPSChainTensor d D N) (hN : ∑ k, ℓ k = N) :
    ‖chainState A‖ = ‖chainPosState A hN‖ := by
  classical
  -- `⊗ₖ Π_k` fixes `φ_pos`
  have hfix : ∀ τ, ∑ τ', (∏ j, polarSupportMatrix (chainBlockTensor A hN j) (τ j) (τ' j)) *
      chainPosState A hN τ' = chainPosState A hN τ := fun τ => by
    have h := mpvFamily_rotatePhysical (fun k => polarSupportMatrix (chainBlockTensor A hN k))
      (fun k => polarPosTensor (chainBlockTensor A hN k)) τ
    simp only [rotatePhysical_polarSupportMatrix] at h
    simp only [chainPosState_apply]
    exact h.symm
  have key : ⟪chainState A, chainState A⟫_ℂ = ⟪chainPosState A hN, chainPosState A hN⟫_ℂ := by
    rw [chainState_eq_blockIsoVector A hN]
    simp only [PiLp.inner_apply, RCLike.inner_apply, blockIsoVector_apply]
    rw [Fintype.sum_equiv (blockIndexEquiv d hN) _ (fun s => star (∑ τ,
      (∏ j, polarIsoMatrix (chainBlockTensor A hN j) (s j) (τ j)) * chainPosState A hN τ) *
      ∑ τ, (∏ j, polarIsoMatrix (chainBlockTensor A hN j) (s j) (τ j)) * chainPosState A hN τ)
      fun s => by rw [mul_comm]; rfl,
      Matrix.sum_star_mul_prod_eq_sum_conjTranspose_mul]
    simp only [conjTranspose_polarIsoMatrix_mul_polarIsoMatrix]
    refine Finset.sum_congr rfl fun τ _ => ?_
    calc _ = star (chainPosState A hN τ) * ∑ τ',
          (∏ j, polarSupportMatrix (chainBlockTensor A hN j) (τ j) (τ' j)) *
            chainPosState A hN τ' := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
          rw [hfix τ]
          exact mul_comm _ _
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by exact_mod_cast key)

/-- **The isometries preserve the overlap.** If every blocked tensor `B_k` is injective on a set
`S_k` of bond pairs, then for every family of pairs, `⟨(⊗ₖ V_k) Ω, φ_N⟩ = ⟨Ω, φ_pos⟩`, where
`φ_N` and `φ_pos` are the normalized states.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": the scheme has "error
`ε(Ω, φ_pos)`"; here `V_k†V_k` is the projector onto `S_k` (Supplemental Material, "Proof of
Lemma 1 and extension to non-normal tensors"), and `φ_pos` lies in its range. For `S_k` the set
of all pairs, injectivity gives `V_k† V_k = 1`, as assumed in the footnote to the paragraph
"Approximation through the fixed-point state". -/
theorem inner_chainBlockIsometryState_normalize {A : MPSChainTensor d D N} (hN : ∑ k, ℓ k = N)
    {S : Fin M → Set (Fin D × Fin D)} (hB : ∀ k, IsInjectiveOn (chainBlockTensor A hN k) (S k))
    (ω : Fin M → Fin D × Fin D → ℂ) :
    ⟪chainBlockIsometryState A ω hN, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ =
      ⟪pairFamilyVector ω, (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ := by
  rw [norm_chainState_eq A hN, chainState_eq_blockIsoVector A hN, ← blockIsoVector_smul,
    chainBlockIsometryState, inner_blockIsoVector_of_isInjectiveOn hN hB _ _ fun τ hτ => by
      rw [PiLp.smul_apply, chainPosState_eq_zero hN hB hτ, smul_zero, mul_zero]]

end MPSPreparation

/-! ### Bond dimensions at most `D` -/

namespace VaryingBondChain

open MPSPreparation

variable {d D M N : ℕ} {ℓ : Fin M → ℕ}

/-- The state of the chain is the state of the zero-padded chain. -/
theorem state_eq_chainState [NeZero N] (A : VaryingBondChain d D N) :
    state A = chainState (zeroPad A) := by
  ext s
  rw [state_eq_chainState_zeroPad, chainState_apply]

/-- The padded pairs form a vector supported on the rectangles of the blocks. -/
theorem pairFamilyVector_padPairs_eq_zero [NeZero N] (A : VaryingBondChain d D N)
    (ω : ∀ k, Fin (rightBond A ℓ k) × Fin (rightBond A ℓ k) → ℂ) {τ : Cfg (D * D) M}
    (hτ : ∃ k, virtualPairEquiv D (τ k) ∉ blockCorner A ℓ k) :
    pairFamilyVector (padPairs A ℓ ω) τ = 0 := by
  by_contra h
  obtain ⟨k, hk⟩ := hτ
  rw [pairFamilyVector_apply] at h
  exact hk (mem_blockCorner_of_pairFamilyState_ne_zero A ℓ ω h k)

/-- **Approximation of the positive parts by pairs**, at a fixed ring, for a chain of bond
dimensions at most `D`: the state `φ_pos` of the positive parts of the blocked tensors is
nonzero, and there are unit vectors `ω^k` on `ℂ^{D_j} ⊗ ℂ^{D_j}`, `j` the bond joining block `k`
to block `k + 1`, whose product `|Ω⟩ = ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` has error
`ε(Ω, φ_pos) = 1 - |⟨Ω|φ_pos⟩| ≤ δ` against the normalized state of the positive parts. The
blocked tensors, their positive parts and the pairs are those of the zero-padded chain; their
identification with the rectangular objects of the source is not proved (see the paper-gap note
cited below).

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": a sequence of matrix
product states "with bond dimension at most `D`" has finite correlation length if, after
blocking `q = O(log N)` sites, the states can be approximated by
`|Ω⟩ = ⊗_{i=1}^{N/q} |ω^i⟩_{R_i L_{i+1}}` "with an error `ε(Ω, φ_pos) → 0` as `N → ∞`". This is
the condition for one member of the sequence.

**Local fix (nonzero positive-part state):** the source's error `ε(Ω, φ_pos)` compares `|Ω⟩`
with the normalized state `φ_pos / ‖φ_pos‖`, which presupposes `φ_pos ≠ 0`; the condition
`chainPosState (zeroPad A) hN ≠ 0` makes this explicit. Documented in
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`. -/
def IsPairApproximable [NeZero N] (A : VaryingBondChain d D N) (hN : ∑ k, ℓ k = N)
    (δ : ℝ) : Prop :=
  chainPosState (zeroPad A) hN ≠ 0 ∧
    ∃ ω : ∀ k, Fin (rightBond A ℓ k) × Fin (rightBond A ℓ k) → ℂ,
      (∀ k, ∑ p, star (ω k p) * ω k p = 1) ∧
      1 - ‖⟪pairFamilyVector (padPairs A ℓ ω),
        (‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ • chainPosState (zeroPad A) hN⟫_ℂ‖ ≤ δ

end VaryingBondChain

namespace MPSPreparation

variable {d D M N : ℕ} {ℓ : Fin M → ℕ}

/-! ### The preparation -/

open VaryingBondChain in
/-- **Preparation of an inhomogeneous matrix product state.** There is `C`, depending only on
`d` and `D`, such that the following holds. Cut a ring of `N ≥ 1` sites into `M ≥ 1` blocks of
lengths `3D ≤ ℓ k ≤ L`, let `A` be a chain of site-dependent tensors with bond dimensions
`D_0, …, D_{N-1}` at most `D` whose blocked tensors are all injective, and let `ω^k` be unit
vectors on `ℂ^{D_j} ⊗ ℂ^{D_j}`, `j` the bond joining block `k` to block `k + 1`. Then
`|ψ⟩ = (⊗ₖ V_k) ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` is a unit vector prepared in depth at most `C L`, and
its error against the normalized state `|φ_N⟩` of the chain is the error of `|Ω⟩` against
`|φ_pos⟩`: `ε(ψ, φ_N) = ε(Ω, φ_pos)`. The isometries, positive parts and pairs are those of the
zero-padded chain; `V_k` is then a partial isometry, an isometry on the rectangle of the block.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": "the preparation scheme
consists of preparing `|Ω⟩` and implementing the isometry", with "error `ε(Ω, φ_pos)`", and
"the resulting total depth is again `O(log (N/ε))`". The bound `C L` gives this depth when
`L = O(log(N/ε))`; the source's definition fixes `q = O(log N)`, and the choice of `L` is not
made here. -/
theorem exists_isPreparedInDepth_inhomogeneous (d D : ℕ) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : VaryingBondChain d D N) (ω : ∀ k, Fin (rightBond A ℓ k) × Fin (rightBond A ℓ k) → ℂ),
      (∀ k, ∑ p, star (ω k p) * ω k p = 1) → ∀ L : ℕ,
        (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) → IsBlockInjective A hN →
          ‖chainBlockIsometryState (zeroPad A) (padPairs A ℓ ω) hN‖ = 1 ∧
          IsPreparedInDepth (C * L)
            (fun s => chainBlockIsometryState (zeroPad A) (padPairs A ℓ ω) hN s) ∧
          1 - ‖⟪chainBlockIsometryState (zeroPad A) (padPairs A ℓ ω) hN,
              (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ =
            1 - ‖⟪pairFamilyVector (padPairs A ℓ ω),
              (‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ • chainPosState (zeroPad A) hN⟫_ℂ‖ := by
  classical
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_chainBlockIsometryState_of_isInjectiveOn d D
  refine ⟨C, fun {M} _ ℓ N _ hN A ω hω L hℓ hL hB => ?_⟩
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · set k₀ : Fin M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
      have h0 := hω k₀
      have hr : rightBond A ℓ k₀ = 0 := Nat.le_zero.mp (hD ▸ rightBond_le A ℓ k₀)
      have : IsEmpty (Fin (rightBond A ℓ k₀) × Fin (rightBond A ℓ k₀)) :=
        ⟨fun p => (Fin.cast hr p.1).elim0⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty] at h0
      exact absurd h0 zero_ne_one
    · exact hD
  have hℓ0 : ∀ k, 0 < ℓ k := fun k => by have := hℓ k; omega
  have hinj := hB.isInjectiveOn hℓ0
  set S : Fin M → Finset (Fin D × Fin D) := fun k => Finset.univ.filter (· ∈ blockCorner A ℓ k)
  have hS : ∀ k, (S k : Set (Fin D × Fin D)) = blockCorner A ℓ k := fun k => by ext; simp [S]
  have hΩ : ∀ {τ : Cfg (D * D) M}, (∃ k, virtualPairEquiv D (τ k) ∉ blockCorner A ℓ k) →
      pairFamilyVector (padPairs A ℓ ω) τ = 0 := fun hτ => pairFamilyVector_padPairs_eq_zero A ω hτ
  refine ⟨?_, ?_, ?_⟩
  · rw [chainBlockIsometryState, norm_blockIsoVector_of_isInjectiveOn hN hinj _ fun τ hτ => hΩ hτ,
      norm_pairFamilyVector (sum_star_padPairs_mul_self A ℓ hω)]
  · exact hC ℓ hN (zeroPad A) S (padPairs A ℓ ω) (sum_star_padPairs_mul_self A ℓ hω)
      (fun c hc k => by simpa [S] using mem_blockCorner_of_pairFamilyState_ne_zero A ℓ ω hc k)
      L hℓ hL fun k => by rw [hS]; exact hinj k
  · rw [state_eq_chainState, inner_chainBlockIsometryState_normalize hN hinj]

end MPSPreparation
