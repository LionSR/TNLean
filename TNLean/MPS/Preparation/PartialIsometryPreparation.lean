/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousPreparation
import TNLean.MPS.Preparation.IsometricExtension

/-!
# Preparation without injectivity: isometric extensions of the partial isometries

For a blocked tensor `B_k = V_k P_k` that is not injective, the isometric factor `V_k` is a
partial isometry, `V_k†V_k = Π_k` with `Π_k` the projector onto the range of `P_k`
(arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors"). The source's circuit implements `V_k` by a unitary on the block; its footnote to
the paragraph "The sequential-RG circuit" states that the derivation "remains valid also for
non-injective tensors `B`", with `P⁻¹` read as the pseudo-inverse.

This file carries this out. The block unitary implements an isometry `W_k` with
`W_k Π_k = V_k`, an isometric extension of `V_k`
(`MPSPreparation.exists_blockUnitary_isometricExtension`): a unitary on the pair space whose
first columns span the range of `Π_k` (`Matrix.exists_unitary_mul_diagonal_of_isHermitian`)
turns the range into the span of the first inputs, the sequential factorization of `V_k` on those
inputs gives a staircase, and a gate on the input pair undoes the change of basis
(`MPSPreparation.exists_blockUnitary_of_equiv_mul`). Since `B_k = W_k P_k` with `W_k` an
isometry, `|φ_N⟩ = (⊗ₖ W_k) |φ_pos⟩` and the isometries preserve the overlap
(`MPSPreparation.inner_blockMatVector_chainState_normalize`), so the prepared state
`(⊗ₖ W_k) |Ω⟩` has error exactly `ε(Ω, φ_pos)` against `|φ_N⟩`, with no injectivity
(`MPSPreparation.exists_isPreparedInDepth_inhomogeneous_isometricExtension`,
`MPSPreparation.exists_isPreparedInDepth_of_isPairApproximable`). Since `W_k Π_k = V_k`,
`(⊗ₖ W_k)(⊗ₖ Π_k)|Ω⟩ = (⊗ₖ V_k)|Ω⟩`.

**Scope restriction (blocks of length at least `3D`):** the preparation theorems
`MPSPreparation.exists_isPreparedInDepth_blockMatVector`,
`MPSPreparation.exists_isPreparedInDepth_inhomogeneous_isometricExtension` and
`MPSPreparation.exists_isPreparedInDepth_of_isPairApproximable` assume blocks of at least `3D`
sites, which the circuit needs to hold the two bond indices of a block in registers of `D` sites
and route them together. The first two also assume `D² ≤ d^{3D}`, which the source's requirement
`d^q ≥ D²` for its polar decompositions (footnote to the paragraph "Approximation through the
fixed-point state") implies for blocks of `q ≥ 3D ≥ 1` sites, and which holds for every `D` when
`d ≥ 2`. The source holds the legs `R_i`, `L_{i+1}` of dimension `D` on the sites of the blocks
(eq. `eq:phi_tilde`), but states no bound `3D`. Documented in
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## Main results

* `MPSPreparation.inner_blockMatVector_chainState_normalize` — isometric extensions preserve the
  overlap.
* `MPSPreparation.exists_isPreparedInDepth_inhomogeneous_isometricExtension` — preparation in
  depth `O(L)` with error exactly `ε(Ω, φ_pos)`, for chains with bond dimensions at most `D`.
* `MPSPreparation.exists_isPreparedInDepth_of_isPairApproximable` — the same with error at most
  `δ` under the approximation hypothesis.

## References

* arXiv:2307.01696, paragraphs "Approximation through the fixed-point state" (with its footnote),
  "Preparing the approximate state" (eq. `eq:phi_tilde`), "The sequential-RG circuit" (with its
  footnote) and "Inhomogeneous short-range correlated MPS", and Supplemental Material, "Proof of
  Lemma 1 and extension to non-normal tensors".
-/

open Matrix MPSTensor
open MPSChainTensor (eval)
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

variable {d D : ℕ}

/-! ### The state and its overlap -/

variable {M N : ℕ} {ℓ : Fin M → ℕ}

/-- Matrices on the blocks commute with scalars. -/
theorem blockMatVector_smul {W : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ}
    (hN : ∑ k, ℓ k = N) (c : ℂ) (x : MPVSpace (D * D) M) :
    blockMatVector W hN (c • x) = c • blockMatVector W hN x := by
  ext s
  simp only [blockMatVector_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

/-- **The state is an isometric extension applied to the positive parts:** if
`W_k Π_k = V_k` for the polar decompositions `B_k = V_k P_k` of the blocked tensors, then
`|φ_N⟩ = (⊗ₖ W_k) |φ_pos⟩`, as `W_k P_k = W_k Π_k P_k = V_k P_k = B_k`.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS" and Supplemental
Material, "Proof of Lemma 1 and extension to non-normal tensors": `Π P = P`. -/
theorem chainState_eq_blockMatVector {A : MPSChainTensor d D N} (hN : ∑ k, ℓ k = N)
    {W : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ}
    (hW : ∀ k, W k * polarSupportMatrix (chainBlockTensor A hN k) =
      polarIsoMatrix (chainBlockTensor A hN k)) :
    chainState A = blockMatVector W hN (chainPosState A hN) := by
  have hrot : ∀ k, rotatePhysical (W k) (polarPosTensor (chainBlockTensor A hN k)) =
      chainBlockTensor A hN k := fun k => by
    conv_lhs => rw [← rotatePhysical_polarSupportMatrix]
    rw [rotatePhysical_rotatePhysical, hW, rotatePhysical_polarIsoMatrix_polarPosTensor]
  ext s
  have h := mpvFamily_rotatePhysical W (fun k => polarPosTensor (chainBlockTensor A hN k))
    (blockIndexEquiv d hN s)
  simp only [hrot] at h
  rw [chainState_apply, coeff_eq_mpvFamily_chainBlockTensor A hN, h, blockMatVector_apply]
  simp only [chainPosState_apply]

/-- **Isometric extensions preserve the overlap.** If every `W_k` is an isometry with
`W_k Π_k = V_k`, then for every family of pairs, `⟨(⊗ₖ W_k) Ω, φ_N⟩ = ⟨Ω, φ_pos⟩`, where `φ_N`
and `φ_pos` are the normalized states. The identity holds for every chain, with the convention
`0⁻¹ = 0`; it is an identity of overlaps with normalized states when `φ_pos ≠ 0`, equivalently
`φ_N ≠ 0`. No injectivity is assumed.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": the scheme has "error
`ε(Ω, φ_pos)`"; Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors",
`V†V = Π`. -/
theorem inner_blockMatVector_chainState_normalize {A : MPSChainTensor d D N}
    (hN : ∑ k, ℓ k = N) {W : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ}
    (hWi : ∀ k, (W k).IsIsometry)
    (hW : ∀ k, W k * polarSupportMatrix (chainBlockTensor A hN k) =
      polarIsoMatrix (chainBlockTensor A hN k)) (ω : Fin M → Fin D × Fin D → ℂ) :
    ⟪blockMatVector W hN (pairFamilyVector ω), (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ =
      ⟪pairFamilyVector ω, (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ := by
  rw [norm_chainState_eq A hN, chainState_eq_blockMatVector hN hW, ← blockMatVector_smul,
    inner_blockMatVector hN hWi]

/-! ### The preparation -/

/-- If `D² ≤ d^{3D}` and `D ≥ 1`, then `d ≥ 1` and `D ≤ d^D`: for `d = 1` the hypothesis forces
`D = 1`, and for `d ≥ 2` the bound `D < 2^D` gives it. -/
private theorem pos_and_le_pow_of_mul_le_pow {d D : ℕ} (hD : 0 < D) (hdD : D * D ≤ d ^ (3 * D)) :
    0 < d ∧ D ≤ d ^ D := by
  rcases Nat.lt_trichotomy d 1 with h | rfl | h
  · obtain rfl : d = 0 := by omega
    rw [zero_pow (by omega)] at hdD
    have := Nat.mul_pos hD hD
    omega
  · refine ⟨one_pos, ?_⟩
    rw [one_pow] at hdD ⊢
    nlinarith
  · exact ⟨by omega, Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left h D)⟩

/-- For `d ≥ 2`, `D² ≤ d^{3D}`. -/
private theorem mul_le_pow_of_two_le {d : ℕ} (hd : 2 ≤ d) (D : ℕ) : D * D ≤ d ^ (3 * D) := by
  have h : D ≤ d ^ D := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hd D)
  calc D * D ≤ d ^ D * d ^ D := Nat.mul_le_mul h h
    _ = d ^ (2 * D) := by rw [← pow_add]; ring_nf
    _ ≤ d ^ (3 * D) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **Preparation in depth `O(L)` with isometric extensions.** Let `D² ≤ d^{3D}`. There is `C`,
depending only on `d` and `D`, such that the following holds. Cut a ring of `N ≥ 1` sites into
`M ≥ 1` blocks of lengths `3D ≤ ℓ k ≤ L`, let `A` be a chain of site-dependent tensors of bond
dimension `D`, and let `ω^k` be unit vectors on the pair space. Then there are isometries
`W_k : ℂ^{D²} → ℂ^{d^{ℓ k}}` with `W_k Π_k = V_k` for the polar decompositions `B_k = V_k P_k` of
the blocked tensors such that `(⊗ₖ W_k) ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` is prepared in depth at most `C L`
from a product state. No injectivity is assumed.

arXiv:2307.01696, paragraph "The sequential-RG circuit", its footnote (the derivation holds "also
for non-injective tensors `B`") and Fig. 1, and the paragraph "Inhomogeneous short-range
correlated MPS". -/
theorem exists_isPreparedInDepth_blockMatVector (d D : ℕ) (hdD : D * D ≤ d ^ (3 * D)) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : MPSChainTensor d D N) (ω : Fin M → Fin D × Fin D → ℂ),
      (∀ k, ∑ p, star (ω k p) * ω k p = 1) → ∀ L : ℕ, (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
        ∃ W : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ,
          (∀ k, (W k).IsIsometry) ∧
          (∀ k, W k * polarSupportMatrix (chainBlockTensor A hN k) =
            polarIsoMatrix (chainBlockTensor A hN k)) ∧
          IsPreparedInDepth (C * L) fun s => blockMatVector W hN (pairFamilyVector ω) s := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · -- no unit pair on the zero space
    refine ⟨0, fun {M} _ ℓ N _ hN A ω hω L _ _ =>
      absurd (hω ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩) ?_⟩
    simp
  obtain ⟨hd0, hDd⟩ := pos_and_le_pow_of_mul_le_pow hD hdD
  obtain ⟨dig⟩ : Nonempty (Fin D ↪ Cfg d D) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hDd)
  have hdig : Function.Injective dig := dig.injective
  obtain ⟨Cb, hCb⟩ := exists_blockUnitary_isometricExtension hd0 hdig hD
  obtain ⟨Kw, hKw⟩ := exists_isPairProduct (n := D + D) hd0 (by omega)
  refine ⟨Cb + Kw, fun {M} _ ℓ N _ hN A ω hω L hℓ hL => ?_⟩
  choose Wp hWu hWp using fun k => exists_pairUnitary hd0 hdig (ω k) (hω k)
  have hr : ∀ k, D + D ≤ ℓ k := fun k => by have := hℓ k; omega
  choose U X hUpp hX hXE hUX using fun k => hCb (ℓ k) (hℓ k) fun j => A (blockSite hN k j)
  have hL1 : 1 ≤ L := by
    have := hℓ ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
    have := hL ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
    omega
  refine ⟨X, hX, hXE, blockLayerOp hN U * pairLayerOp hN hr Wp, ?_,
    fun _ => Pi.single ⟨0, hd0⟩ 1, funext fun s => ?_⟩
  · have hc := (isCircuitOn_pairLayerOp hN hr fun k => hKw (Wp k) (hWu k)).mul
      (isCircuitOn_blockLayerOp hN fun k => (hUpp k).mono (Nat.mul_le_mul_left Cb (hL k)))
    refine (hc.mono ?_).isLocalCircuitOfDepth
    have : Kw ≤ Kw * L := Nat.le_mul_of_pos_right _ hL1
    nlinarith
  · exact blockMatVector_pairFamilyVector_eq_mulVec hd0 hN hr hdig X ω
      (fun c _ k τ => hUX k _ _ τ) hWp s

open VaryingBondChain in
/-- **Preparation of an inhomogeneous matrix product state without injectivity.** Let `D² ≤ d^{3D}`.
There is `C`, depending only on `d` and `D`, such that the following holds. Cut a ring of `N ≥ 1`
sites into `M ≥ 1` blocks of lengths `3D ≤ ℓ k ≤ L`, let `A` be a chain of site-dependent tensors
with bond dimensions `D_0, …, D_{N-1}` at most `D`, and let `ω^k` be unit vectors on
`ℂ^{D_j} ⊗ ℂ^{D_j}`, `j` the bond joining block `k` to block `k + 1`. Then there are isometries
`W_k` with `W_k Π_k = V_k` for the polar decompositions `B_k = V_k P_k` of the blocked tensors such
that `|ψ⟩ = (⊗ₖ W_k) ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` is a unit vector prepared in depth at most `C L`, with
error against the normalized state `|φ_N⟩` of the chain equal to the error of `|Ω⟩` against
`|φ_pos⟩`: `ε(ψ, φ_N) = ε(Ω, φ_pos)` when `φ_pos ≠ 0`. The identity of the overlaps holds for every
chain, with the convention `0⁻¹ = 0`. The blocked tensors, their polar factors and the pairs are
those of the zero-padded chain.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": "the preparation scheme
consists of preparing `|Ω⟩` and implementing the isometry", with "error `ε(Ω, φ_pos)`", and
"the resulting total depth is again `O(log (N/ε))`". The bound `C L` gives this depth when
`L = O(log(N/ε))`; the choice of `L` is not made here. The hypothesis `D² ≤ d^{3D}` follows from
the source's requirement `d^q ≥ D²` (footnote to the paragraph "Approximation through the
fixed-point state") for blocks of `q ≥ 3D ≥ 1` sites. -/
theorem exists_isPreparedInDepth_inhomogeneous_isometricExtension (d D : ℕ)
    (hdD : D * D ≤ d ^ (3 * D)) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : VaryingBondChain d D N) (ω : ∀ k, Fin (rightBond A ℓ k) × Fin (rightBond A ℓ k) → ℂ),
      (∀ k, ∑ p, star (ω k p) * ω k p = 1) → ∀ L : ℕ, (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
        ∃ W : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ,
          (∀ k, (W k).IsIsometry) ∧
          (∀ k, W k * polarSupportMatrix (chainBlockTensor (zeroPad A) hN k) =
            polarIsoMatrix (chainBlockTensor (zeroPad A) hN k)) ∧
          ‖blockMatVector W hN (pairFamilyVector (padPairs A ℓ ω))‖ = 1 ∧
          IsPreparedInDepth (C * L)
            (fun s => blockMatVector W hN (pairFamilyVector (padPairs A ℓ ω)) s) ∧
          1 - ‖⟪blockMatVector W hN (pairFamilyVector (padPairs A ℓ ω)),
              (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ =
            1 - ‖⟪pairFamilyVector (padPairs A ℓ ω),
              (‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ • chainPosState (zeroPad A) hN⟫_ℂ‖ := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_blockMatVector d D hdD
  refine ⟨C, fun {M} _ ℓ N _ hN A ω hω L hℓ hL => ?_⟩
  obtain ⟨W, hWi, hW, hprep⟩ := hC ℓ hN (zeroPad A) (padPairs A ℓ ω)
    (sum_star_padPairs_mul_self A ℓ hω) L hℓ hL
  refine ⟨W, hWi, hW, ?_, hprep, ?_⟩
  · rw [norm_blockMatVector hN hWi, norm_pairFamilyVector (sum_star_padPairs_mul_self A ℓ hω)]
  · rw [state_eq_chainState, inner_blockMatVector_chainState_normalize hN hWi hW]

open VaryingBondChain in
/-- **Preparation under the approximation hypothesis.** There is `C`, depending only on `d` and
`D`, such that if a ring of `N ≥ 1` sites is cut into `M ≥ 1` blocks of lengths `3D ≤ ℓ k ≤ L`
and the positive parts of a chain `A` with bond dimensions at most `D` are approximated by pairs
with error at most `δ`, then some unit vector `|ψ⟩` prepared in depth at most `C L` has error
`ε(ψ, φ_N) ≤ δ` against the normalized state of the chain. No injectivity is assumed.

arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS": "If the finite
correlation assumption is satisfied, then the preparation scheme consists of preparing `|Ω⟩`
and implementing the isometry". For `d ≥ 2` the state is
`MPSPreparation.exists_isPreparedInDepth_inhomogeneous_isometricExtension`; for `d ≤ 1` the ring
has at most one configuration and the normalized state itself is prepared in depth `0`. -/
theorem exists_isPreparedInDepth_of_isPairApproximable (d D : ℕ) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : VaryingBondChain d D N) (L : ℕ) (δ : ℝ),
        (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) → IsPairApproximable A hN δ →
          ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧ IsPreparedInDepth (C * L) (fun s => ψ s) ∧
            1 - ‖⟪ψ, (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ ≤ δ := by
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · refine ⟨0, fun ℓ N _ hN A L δ _ _ ⟨hne, ω, hω, hδ⟩ => ?_⟩
    have hn : ‖state A‖ ≠ 0 := by
      rw [state_eq_chainState, norm_chainState_eq _ hN]
      exact norm_ne_zero_iff.mpr hne
    have hunit : ‖(‖state A‖ : ℂ)⁻¹ • state A‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ hn]
    refine ⟨(‖state A‖ : ℂ)⁻¹ • state A, hunit, by
      rw [zero_mul]; exact isPreparedInDepth_zero_of_le_one (by omega) _, ?_⟩
    rw [inner_self_eq_norm_sq_to_K, hunit]
    have hle := norm_inner_le_norm (𝕜 := ℂ) (pairFamilyVector (padPairs A ℓ ω))
      ((‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ • chainPosState (zeroPad A) hN)
    have hu : ‖(‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ • chainPosState (zeroPad A) hN‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
    rw [hu, norm_pairFamilyVector (sum_star_padPairs_mul_self A ℓ hω), mul_one] at hle
    norm_num
    linarith
  · obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_isometricExtension d D
      (mul_le_pow_of_two_le hd2 D)
    refine ⟨C, fun ℓ N _ hN A L δ hℓ hL ⟨_, ω, hω, hδ⟩ => ?_⟩
    obtain ⟨W, -, -, hn, hprep, herr⟩ := hC ℓ hN A ω hω L hℓ hL
    exact ⟨_, hn, hprep, herr ▸ hδ⟩

end MPSPreparation
