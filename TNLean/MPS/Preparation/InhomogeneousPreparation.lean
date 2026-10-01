/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthUpperBound

/-!
# Inhomogeneous short-range correlated matrix product states

A chain `A` of site-dependent tensors with bond dimension `D` on a ring of `N` sites, cut into
`M` blocks of lengths `ℓ 0, …, ℓ (M - 1)`, has on block `k` the blocked tensor `B_k` with polar
decomposition `B_k = V_k P_k`. The positive parts `P_k` are tensors of physical dimension `D²`
and bond dimension `D`, and generate the state `|φ_pos⟩` on the `M` blocks
(`MPSPreparation.chainPosState`). The state of the chain is exactly
`|φ_N⟩ = (⊗ₖ V_k) |φ_pos⟩` (`MPSPreparation.chainState_eq_blockIsoVector`).

The source calls such a chain short-range correlated if `|φ_pos⟩` is close to a product
`|Ω⟩ = ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` of pairs, each joining the right leg of one block to the left leg
of the next. At a fixed ring this is the statement that the error `ε(Ω, φ_pos)` is at most `δ`
for some unit pairs (`MPSPreparation.IsPairApproximable`). The state `(⊗ₖ V_k) |Ω⟩` is prepared
in depth at most `C L` for blocks of lengths at most `L`, with `C` depending only on `d` and
`D`, and when every blocked tensor is injective its error against `|φ_N⟩` is exactly
`ε(Ω, φ_pos)` (`MPSPreparation.exists_isPreparedInDepth_inhomogeneous`). Blocks of length
`q = O(log N)` then give depth `O(log N)`.

The error is `ε(φ, ψ) = 1 - |⟨φ|ψ⟩|` of normalized vectors, as displayed in arXiv:2307.01696,
paragraph "The algorithm".

**Scope restriction (common bond dimension):** the source takes a sequence of matrix product
states "with bond dimension at most `D`", which allows the bond dimension to vary along the
ring; here every bond has the same dimension `D`. The blocked tensors are also assumed injective,
which the source assumes for its polar decompositions (arXiv:2307.01696, the footnote to the
paragraph "Approximation through the fixed-point state"), and of lengths at least `3D`, which the
construction of the circuit needs. Documented in
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## Main results

* `MPSPreparation.chainState_eq_blockIsoVector` — `|φ_N⟩ = (⊗ₖ V_k) |φ_pos⟩`.
* `MPSPreparation.inner_chainBlockIsometryState_normalize` — the isometries preserve the
  overlap: `⟨(⊗ₖ V_k) Ω, φ_N⟩ = ⟨Ω, φ_pos⟩` for the normalized states.
* `MPSPreparation.exists_isPreparedInDepth_inhomogeneous` — preparation in depth `O(L)` with
  error `ε(Ω, φ_pos)`.
* `MPSPreparation.exists_isPreparedInDepth_of_isPairApproximable` — the same under the
  approximation hypothesis with error `δ`.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS" and eq. `eq:phi_pos`.
-/

open Matrix MPSTensor
open scoped BigOperators InnerProductSpace

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

/-- The norm of the state is the norm of the state of the positive parts when every blocked
tensor is injective. -/
theorem norm_chainState {A : MPSChainTensor d D N} (hN : ∑ k, ℓ k = N)
    (hB : ∀ k, Kraus.IsInjective (chainBlockTensor A hN k)) :
    ‖chainState A‖ = ‖chainPosState A hN‖ := by
  rw [chainState_eq_blockIsoVector A hN, norm_blockIsoVector hN hB]

/-- **The isometries preserve the overlap.** If every blocked tensor is injective, then for
every family of pairs, `⟨(⊗ₖ V_k) Ω, φ_N⟩ = ⟨Ω, φ_pos⟩`, where `φ_N` and `φ_pos` are the
normalized states.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": the scheme has "error
`ε(Ω, φ_pos)`"; injectivity gives `V_k† V_k = 1`, as assumed in the footnote to the paragraph
"Approximation through the fixed-point state". -/
theorem inner_chainBlockIsometryState_normalize {A : MPSChainTensor d D N} (hN : ∑ k, ℓ k = N)
    (hB : ∀ k, Kraus.IsInjective (chainBlockTensor A hN k)) (ω : Fin M → Fin D × Fin D → ℂ) :
    ⟪chainBlockIsometryState A ω hN, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ =
      ⟪pairFamilyVector ω, (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ := by
  rw [norm_chainState hN hB, chainState_eq_blockIsoVector A hN, ← blockIsoVector_smul,
    chainBlockIsometryState, inner_blockIsoVector hN hB]

/-! ### The approximation hypothesis and the preparation -/

/-- **Approximation of the positive parts by pairs**, at a fixed ring: there are unit vectors
`ω^k` on `ℂ^D ⊗ ℂ^D` whose product `|Ω⟩ = ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` has error
`ε(Ω, φ_pos) = 1 - |⟨Ω|φ_pos⟩| ≤ δ` against the normalized state of the positive parts.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": a sequence of matrix
product states has finite correlation length if, after blocking `q = O(log N)` sites, the states
can be approximated by `|Ω⟩ = ⊗_{i=1}^{N/q} |ω^i⟩_{R_i L_{i+1}}` "with an error
`ε(Ω, φ_pos) → 0` as `N → ∞`". This is the condition for one member of the sequence. -/
def IsPairApproximable (A : MPSChainTensor d D N) (hN : ∑ k, ℓ k = N) (δ : ℝ) : Prop :=
  ∃ ω : Fin M → Fin D × Fin D → ℂ, (∀ k, ∑ p, star (ω k p) * ω k p = 1) ∧
    1 - ‖⟪pairFamilyVector ω, (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ‖ ≤ δ

/-- **Preparation of an inhomogeneous matrix product state.** There is `C`, depending only on
`d` and `D`, such that the following holds. Cut a ring of `N ≥ 1` sites into `M ≥ 1` blocks of
lengths `3D ≤ ℓ k ≤ L`, let `A` be a chain of site-dependent tensors of bond dimension `D` whose
blocked tensors are all injective, and let `ω^k` be unit vectors on `ℂ^D ⊗ ℂ^D`. Then
`|ψ⟩ = (⊗ₖ V_k) ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` is a unit vector prepared in depth at most `C L`, and
its error against the normalized state `|φ_N⟩` of the chain is the error of `|Ω⟩` against
`|φ_pos⟩`: `ε(ψ, φ_N) = ε(Ω, φ_pos)`.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": "the preparation scheme
consists of preparing `|Ω⟩` and implementing the isometry", with "error `ε(Ω, φ_pos)`"; for
blocks of length `q = O(log N)` the depth is `O(log N)`. -/
theorem exists_isPreparedInDepth_inhomogeneous (d D : ℕ) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : MPSChainTensor d D N) (ω : Fin M → Fin D × Fin D → ℂ),
      (∀ k, ∑ p, star (ω k p) * ω k p = 1) → ∀ L : ℕ,
        (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) → (∀ k, Kraus.IsInjective (chainBlockTensor A hN k)) →
          ‖chainBlockIsometryState A ω hN‖ = 1 ∧
          IsPreparedInDepth (C * L) (fun s => chainBlockIsometryState A ω hN s) ∧
          1 - ‖⟪chainBlockIsometryState A ω hN, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ‖ =
            1 - ‖⟪pairFamilyVector ω, (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ‖ := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_chainBlockIsometryState d D
  refine ⟨C, fun ℓ N _ hN A ω hω L hℓ hL hB => ⟨?_, hC ℓ hN A ω hω L hℓ hL hB, ?_⟩⟩
  · rw [chainBlockIsometryState, norm_blockIsoVector hN hB, norm_pairFamilyVector hω]
  · rw [inner_chainBlockIsometryState_normalize hN hB]

/-- **Preparation under the approximation hypothesis.** There is `C`, depending only on `d` and
`D`, such that if a ring of `N ≥ 1` sites is cut into `M ≥ 1` blocks of lengths `3D ≤ ℓ k ≤ L`,
the chain `A` has injective blocked tensors, and its positive parts are approximated by pairs
with error at most `δ`, then some unit vector `|ψ⟩` prepared in depth at most `C L` has error
`ε(ψ, φ_N) ≤ δ` against the normalized state of the chain.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": "If the finite
correlation assumption is satisfied, then the preparation scheme consists of preparing `|Ω⟩`
and implementing the isometry". -/
theorem exists_isPreparedInDepth_of_isPairApproximable (d D : ℕ) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : MPSChainTensor d D N) (L : ℕ) (δ : ℝ),
        (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) → (∀ k, Kraus.IsInjective (chainBlockTensor A hN k)) →
          IsPairApproximable A hN δ →
          ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧ IsPreparedInDepth (C * L) (fun s => ψ s) ∧
            1 - ‖⟪ψ, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ‖ ≤ δ := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous d D
  refine ⟨C, fun ℓ N _ hN A L δ hℓ hL hB ⟨ω, hω, hδ⟩ => ?_⟩
  obtain ⟨hn, hprep, herr⟩ := hC ℓ hN A ω hω L hℓ hL hB
  exact ⟨_, hn, hprep, herr ▸ hδ⟩

end MPSPreparation
