/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.GHZSeedCircuit
import TNLean.MPS.Preparation.PartialIsometryPreparation

/-!
# Inhomogeneous coherent sums of pair products

The last sentence of arXiv:2307.01696, "Long-range MPS using measurements", extends the
construction to inhomogeneous long-range correlated states. The explicit input used here is
`Ω = ∑ j, α j • pairFamilyVector (ω j)`, with orthonormal pairs `ω j k` at each window `k`.
Both the pairs and the tensors of the chain may vary along the ring. Isometric extensions
of the blocked polar factors implement this input without an injectivity assumption and
preserve its overlap with the normalized positive-part state exactly.

**Scope restriction (specified coherent-pair approximation):** the result assumes the
orthonormal pairs explicitly and bounds depth by the largest block length. It does not
derive their existence or a uniform accuracy-dependent blocking scale from the phrase
"inhomogeneous long-range correlated MPS". The source does not define that class separately.
See `docs/paper-gaps/mswc24_inhomogeneous_long_range.tex`.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

variable {d D M N : ℕ} {ℓ : Fin M → ℕ}

/-- A coherent sum of locally orthonormal, site-dependent pair products is a unit vector
when its amplitudes have squared moduli summing to one and there is at least one window.
Source: arXiv:2307.01696, eq. (19) and its concluding inhomogeneous remark. -/
theorem norm_sum_pairFamilyVector [NeZero M] {b : ℕ}
    (ω : Fin b → Fin M → Fin D × Fin D → ℂ)
    (hω : ∀ k j j', ∑ p, star (ω j k p) * ω j' k p = if j = j' then 1 else 0)
    (α : Fin b → ℂ) (hα : ∑ j, star (α j) * α j = 1) :
    ‖∑ j, α j • pairFamilyVector (ω j)‖ = 1 := by
  classical
  have hinner : ∀ i j, ⟪pairFamilyVector (ω i), pairFamilyVector (ω j)⟫_ℂ =
      if i = j then 1 else 0 := by
    intro i j
    calc
      _ = ∑ c : Fin M → Fin D × Fin D,
          star (pairFamilyState (ω i) c) * pairFamilyState (ω j) c := by
        rw [PiLp.inner_apply]
        exact Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm)
          _ _ fun τ => by simp only [RCLike.inner_apply, pairFamilyVector_apply]; ring
      _ = ∏ k, ∑ p, star (ω i k p) * ω j k p := pairFamilyState_inner _ _
      _ = _ := by
        simp_rw [hω]
        split_ifs <;> simp [Fin.prod_const, NeZero.ne M]
  have hself : ⟪∑ j, α j • pairFamilyVector (ω j),
      ∑ j, α j • pairFamilyVector (ω j)⟫_ℂ = 1 := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hinner]
    simpa [Finset.mul_sum, mul_ite] using hα
  rw [inner_self_eq_norm_sq_to_K] at hself
  have hsq : ‖∑ j, α j • pairFamilyVector (ω j)‖ ^ 2 = 1 := by exact_mod_cast hself
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

/-- Isometric extensions preserve the normalized overlap for every input vector, including
coherent sums of site-dependent pair products. Source: arXiv:2307.01696, eqs. (18), (19),
and the concluding inhomogeneous remark in "Long-range MPS using measurements". -/
theorem inner_blockMatVector_normalizedChainState (A : MPSChainTensor d D N)
    (hN : ∑ k, ℓ k = N)
    {X : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ}
    (hX : ∀ k, (X k).IsIsometry)
    (hXE : ∀ k, X k * polarSupportMatrix (chainBlockTensor A hN k) =
      polarIsoMatrix (chainBlockTensor A hN k)) (Ω : MPVSpace (D * D) M) :
    ⟪blockMatVector X hN Ω, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ =
      ⟪Ω, (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ := by
  rw [norm_chainState_eq A hN, chainState_eq_blockMatVector hN hXE,
    ← blockMatVector_smul, inner_blockMatVector hN hX]

private theorem blockMatVector_sum_smul {κ : Type*} [Fintype κ]
    (X : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ)
    (hN : ∑ k, ℓ k = N) (α : κ → ℂ) (x : κ → MPVSpace (D * D) M) :
    blockMatVector X hN (∑ j, α j • x j) = ∑ j, α j • blockMatVector X hN (x j) := by
  ext s
  simp only [blockMatVector_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun τ _ => by ring

section Encodings

variable [NeZero d] {r₁ : ℕ}

private theorem pairLayerOp_mulVec_registerCfg_eq_family
    (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (dig : Fin D → Cfg d r₁) (u₀ : Cfg d r₁)
    (ω : Fin M → Fin D × Fin D → ℂ)
    {W W₀ : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hW : ∀ k u, W k u (windowInput u₀) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω k) 0 u)
    (hW₀ : ∀ k u, W₀ k u (fun _ => ⟨0, NeZero.pos d⟩) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω k) 0 u) :
    pairLayerOp hN hr W *ᵥ Pi.single (registerCfg hN hr u₀) 1 =
      pairLayerOp hN hr W₀ *ᵥ
        productVector fun _ => Pi.single ⟨0, NeZero.pos d⟩ 1 := by
  classical
  have h0 : (⟨0, NeZero.pos d⟩ : Fin d) = 0 := Fin.ext (by simp)
  funext y
  rw [pairLayerOp_mulVec_apply (NeZero.pos d) hN hr W₀ y]
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [pairLayerOp_apply]
  simp only [registerCfg_comp_pairSite, hW, h0]
  refine if_congr ⟨fun h i hi => (h i hi).trans
    (registerCfg_of_forall_pairSite_ne hN hr _ hi),
    fun h i hi => (h i hi).trans
      (registerCfg_of_forall_pairSite_ne hN hr _ hi).symm⟩ ?_ rfl
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← h0, hW₀]

end Encodings

private theorem exists_inhomogeneousLongRange_of_encoding [NeZero d] {b r₁ : ℕ}
    (hr₁ : 2 ≤ r₁) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r₁} (hdig₀ : Function.Injective dig₀) (hD : 0 < D) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
      (hN : ∑ k, ℓ k = N) (A : MPSChainTensor d D N) (L : ℕ),
      (∀ k, 3 * r₁ ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
      ∃ X : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ,
        (∀ k, (X k).IsIsometry) ∧
        (∀ k, X k * polarSupportMatrix (chainBlockTensor A hN k) =
          polarIsoMatrix (chainBlockTensor A hN k)) ∧
        ∀ (ω : Fin b → Fin M → Fin D × Fin D → ℂ),
          (∀ k j j', ∑ p, star (ω j k p) * ω j' k p = if j = j' then 1 else 0) →
          ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
          IsPreparedWithMeasurementsAndCircuitInDepth (C * L)
            (fun s => blockMatVector X hN (∑ j, α j • pairFamilyVector (ω j)) s) := by
  classical
  obtain ⟨Cb, hCb⟩ := exists_blockUnitary_isometricExtension_of_encoding
    (NeZero.pos d) (by omega) hdig hD
  obtain ⟨Kw, hKw⟩ := exists_isPairProduct (n := r₁ + r₁) (NeZero.pos d) (by omega)
  obtain ⟨Cg, hCg⟩ := exists_isPreparedWithMeasurementsInDepth_windowGHZState (d := d) hr₁
  refine ⟨Cg + Kw + Cb, fun {M} _ ℓ N _ hN A L hℓ hL => ?_⟩
  have hr : ∀ k, r₁ + r₁ ≤ ℓ k := fun k => by have := hℓ k; omega
  have hL1 : 1 ≤ L := by have := hℓ 0; have := hL 0; omega
  choose U X hUpp hX hXE hUX using fun k =>
    hCb (ℓ k) (hℓ k) fun i => A (blockSite hN k i)
  refine ⟨X, hX, hXE, fun ω hω α hα => ?_⟩
  choose W hWu hW using fun k => exists_pairFamilyUnitary hdig hdig₀
    (fun j => ω j k) (hω k)
  have hcirc : IsCircuitOn Set.univ (Kw + Cb * L)
      (blockLayerOp hN U * pairLayerOp hN hr W) :=
    (isCircuitOn_pairLayerOp hN hr fun k => hKw (W k) (hWu k)).mul
      (isCircuitOn_blockLayerOp hN (K := Cb * L) fun k =>
        (hUpp k).mono (Nat.mul_le_mul_left Cb (hL k)))
  have hj : ∀ j, (blockLayerOp hN U * pairLayerOp hN hr W) *ᵥ
      Pi.single (registerCfg hN hr (dig₀ j)) 1 =
        fun s => blockMatVector X hN (pairFamilyVector (ω j)) s := by
    intro j
    choose W₀ _ hW₀ using fun k => exists_pairUnitary (NeZero.pos d) hdig (ω j k)
      (by simpa using hω k j j)
    funext s
    rw [blockMatVector_pairFamilyVector_eq_mulVec (NeZero.pos d) hN hr hdig X (ω j)
      (fun c _ k τ => hUX k _ _ τ) hW₀ s, ← mulVec_mulVec, ← mulVec_mulVec,
      pairLayerOp_mulVec_registerCfg_eq_family hN hr dig (dig₀ j) (ω j)
        (fun k u => hW k u j) hW₀]
  let α' : Cfg d r₁ → ℂ := Function.extend dig₀ α 0
  have hα' : ∑ u, star (α' u) * α' u = 1 := by
    rw [sum_extend_zero hdig₀ α (fun _ a => star a * a) (by simp)]
    exact hα
  refine ⟨Cg * L, Kw + Cb * L, windowGHZState hN hr α',
    blockLayerOp hN U * pairLayerOp hN hr W, by nlinarith,
    hCg ℓ hN hr L hℓ hL α' hα', hcirc.isBondCircuitOfDepth, ?_⟩
  change (fun s => blockMatVector X hN (∑ j, α j • pairFamilyVector (ω j)) s) = _
  rw [blockMatVector_sum_smul]
  dsimp only [α']
  rw [windowGHZState_extend hN hr hdig₀ α]
  have hsum : (fun x => ∑ j, α j * if x = registerCfg hN hr (dig₀ j) then (1 : ℂ) else 0) =
      ∑ j, α j • Pi.single (registerCfg hN hr (dig₀ j)) (1 : ℂ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum, mulVec_sum]
  funext s
  simp only [mulVec_smul, hj, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Preparation of a coherent sum of site-dependent pair products followed by the blocked
isometries of an arbitrary inhomogeneous chain. For `d ≥ 2`, `D ≥ 1` and `b` labels, the
constants depend only on `d`, `D`, `b`. There is no injectivity assumption. The isometries
are chosen before the pairs and amplitudes, and the normalized overlap is preserved exactly.

Source: arXiv:2307.01696, eq. (19) and the concluding inhomogeneous remark in "Long-range
MPS using measurements". The input assumption is explicit; the theorem does not assert
an accuracy-dependent scale or the existence of such approximating pairs. -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_inhomogeneousLongRange
    (d D b : ℕ) (hd : 2 ≤ d) (hD : 0 < D) :
    ∃ C L₀ : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
      (hN : ∑ k, ℓ k = N) (A : MPSChainTensor d D N) (L : ℕ),
      (∀ k, L₀ ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
      ∃ X : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ,
        (∀ k, (X k).IsIsometry) ∧
        (∀ k, X k * polarSupportMatrix (chainBlockTensor A hN k) =
          polarIsoMatrix (chainBlockTensor A hN k)) ∧
        ∀ (ω : Fin b → Fin M → Fin D × Fin D → ℂ),
          (∀ k j j', ∑ p, star (ω j k p) * ω j' k p = if j = j' then 1 else 0) →
          ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
          IsPreparedWithMeasurementsAndCircuitInDepth (C * L)
            (fun s => blockMatVector X hN (∑ j, α j • pairFamilyVector (ω j)) s) ∧
          ‖blockMatVector X hN (∑ j, α j • pairFamilyVector (ω j))‖ = 1 ∧
          ⟪blockMatVector X hN (∑ j, α j • pairFamilyVector (ω j)),
              (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ =
            ⟪∑ j, α j • pairFamilyVector (ω j),
              (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ := by
  classical
  have : NeZero d := ⟨by omega⟩
  let r₁ := b + D + 2
  have hpow : r₁ < d ^ r₁ :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hd r₁)
  obtain ⟨dig⟩ : Nonempty (Fin D ↪ Cfg d r₁) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨dig₀⟩ : Nonempty (Fin b ↪ Cfg d r₁) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨C, hC⟩ := exists_inhomogeneousLongRange_of_encoding
    (by dsimp [r₁]; omega) dig.injective dig₀.injective hD
  refine ⟨C, 3 * r₁, fun {M} _ ℓ N _ hN A L hℓ hL => ?_⟩
  obtain ⟨X, hX, hXE, hprep⟩ := hC ℓ hN A L hℓ hL
  refine ⟨X, hX, hXE, fun ω hω α hα => ⟨hprep ω hω α hα, ?_,
    inner_blockMatVector_normalizedChainState A hN hX hXE _⟩⟩
  rw [norm_blockMatVector hN hX, norm_sum_pairFamilyVector ω hω α hα]

end MPSPreparation
