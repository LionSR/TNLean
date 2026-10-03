/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousPreparation
import TNLean.MPS.Preparation.NonNormalMeasurementPreparation
import TNLean.MPS.Preparation.OverlappingBlockStates
import TNLean.MPS.Preparation.ShortChainPreparation

/-!
# Every translation-invariant MPS with measurements in depth `O(log(N/ε))`

arXiv:2307.01696, paragraph "Long-range MPS using measurements", prepares a translation-invariant
MPS that is not normal with measurements: "First create `|χ_{N/q}⟩`, which can be done in
constant depth with measurements ... Subsequently, apply in parallel the isometries
`W : |j⟩ ↦ |ω_j⟩`", and the isometries of the blocked tensor follow; "If instead measurements are
only used for the preparation of `|χ_{N/q}⟩`, the depth is `O(log(N/ε))`", for all
translation-invariant MPS, "short- or long-range correlated". This file proves this for the
canonical form `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` of eq. (S2), with blocks whose
`q`-site states may overlap, every multiplicity, every nonzero complex weight, and every chain
length `N ≥ 2`:

* for a tensor injective on a set `S` of bond pairs and pairs `ω_j` that are orthonormal and
  supported on `S`, the state `∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ |ω_j⟩` is prepared with measurements and a
  circuit in depth `O(L)` for blocks of lengths at most `L`
  (`exists_isPreparedWithMeasurementsAndCircuitInDepth_blockIsometryState_of_isInjectiveOn`):
  the GHZ-type state of the labels with measurements, the isometry `W` on every pair window,
  and on every block one unitary implementing the isometric factor `V_k` on the pairs of `S`;
* on a chain of one block, the normalized target is such a state
  (`MPSPreparation.exists_blockIsometryState_eq_smul`);
* with the error bound for blocks of unequal lengths
  (`MPSTensor.exists_one_sub_norm_inner_sum_blockIsometryState_le`), a unit vector of error at
  most `ε` is prepared with measurements in depth `O(log(N/ε))` for every `N ≥ 2` at which the
  periodic state does not vanish
  (`MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero`),
  and for every `N ≥ N₀` at which the weights `βⱼ = ∑ₖ μ_{j,k}^N` are not all zero
  (`MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log`).

The chain is cut as in the Supplemental Material, proof of Theorem 1: blocks "all of the same
size, `q_N`, except for the last one, which may be larger". The isometries are those of the
direct sum `⊕ⱼ A_j` with unit weights, whose blocked tensors are injective on the bond pairs of
the blocks for large block lengths (`MPSTensor.exists_isInjectiveOn_blockTensor_blockSum`).

**Local fix (isometry of the unweighted direct sum):** the state prepared is
`∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ |ω_j⟩` with `αⱼ = βⱼ / (∑ₗ |βₗ|²)^{1/2}` and `V_k` the isometries of the direct
sum with unit weights, not the isometry of the blocked tensor of `A`, whose positive part does
not have the block form (S5) when the blocks overlap or repeat. Documented in
`docs/paper-gaps/mswc24_measurement_preparation_scope.tex`.

**Local fix (rate of the overlapping blocks):** the block length is chosen at the rate
`e^{-γ q/ξ}` with `ξ` bounding the correlation lengths of the blocks and of the mixed transfer
maps of distinct blocks, whose spectral radius is assumed below one. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Local fix (nonvanishing periodic state):** the source normalizes `|φ_N⟩`, which presupposes
`|φ_N(A)⟩ ≠ 0`; the first main theorem assumes it, and the second assumes `βⱼ` not all zero, for
`N ≥ N₀`. Documented in `docs/paper-gaps/mswc24_depth_upper_bound_nonzero_state.tex`.

**Scope restriction (depth of the GHZ-type state):** the GHZ-type state is prepared in depth
`O(q)` rather than in constant depth. Documented in
`docs/paper-gaps/mswc24_measurement_preparation_scope.tex`.

## Main declarations

* `exists_isPreparedWithMeasurementsAndCircuitInDepth_blockIsometryState_of_isInjectiveOn`
  — the preparation of `∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ |ω_j⟩` in depth `O(L)`.
* `MPSPreparation.exists_blockIsometryState_eq_smul` — a chain of one block.
* `MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero`,
  `MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log` — error `ε` in
  depth `O(log(N/ε))`.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, paragraph "Long-range MPS using measurements", eq. (19), and Supplemental
  Material, eqs. (S2)–(S7), Lemma 1'(ii) and the proof of Theorem 1.
* [PSC21] L. Piroli, G. Styliaris, J. I. Cirac,
  *Quantum circuits assisted by local operations and classical communication:
  transformations and phases of matter*,
  arXiv:2103.13367, paragraph "State transformations with QC and LOCC" and Example 1.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace
open QuantumCircuit

namespace MPSPreparation

variable {d : ℕ}

/-! ### Preparation of the state of a tensor injective on a set of bond pairs -/

section Preparation

variable [NeZero d]

/-- **The state of a tensor injective on a set of bond pairs, with measurements, for given
encodings.** Let the labels `j` be encoded injectively in `r₁ ≥ 2` sites by `dig₀`, and the bond
indices by `dig`. There is `C` such that for every tensor `A`, every set `S` of bond pairs, pairs
`ω_j` that are orthonormal and whose products vanish on the bond configurations leaving `S`, unit
amplitudes `α`, and every cutting of a ring into `M ≥ 1` blocks of lengths `3 r₁ ≤ ℓ_k ≤ L` at
which the blocked tensors are injective on `S`, the state `∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ |ω_j⟩` is prepared
with measurements and a circuit in depth at most `C L`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements": the GHZ-type state of the labels
with measurements, then the isometry `W : |j⟩ ↦ |ω_j⟩` on the pair windows, then on every block a
unitary implementing the isometric factor `V_k` on the pairs of `S` (arXiv:2307.01696,
eqs. (13)–(15), through `exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn`). -/
private theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_of_encoding_of_isInjectiveOn
    {D b : ℕ} {r₁ : ℕ} (hr₁ : 2 ≤ r₁) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r₁} (hdig₀ : Function.Injective dig₀) (hD : 0 < D) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
      (ω : Fin b → Fin D × Fin D → ℂ),
      (∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) →
      (∀ j {M : ℕ} (c : Fin M → Fin D × Fin D), pairProductState (ω j) c ≠ 0 → ∀ k, c k ∈ S) →
      ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        (∀ k, 3 * r₁ ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
        (∀ k, IsInjectiveOn (blockTensor A (ℓ k)) (S : Set (Fin D × Fin D))) →
        IsPreparedWithMeasurementsAndCircuitInDepth (C * L)
          (fun s => ∑ j, α j * blockIsometryState A (ω j) hN s) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have h0 : (⟨0, hd⟩ : Fin d) = 0 := Fin.ext (by simp)
  obtain ⟨CG, hCG⟩ := exists_isPreparedWithMeasurementsInDepth_windowGHZState (d := d) hr₁
  choose Cπ hCπ using fun π : Fin (D * D) ≃ Fin D × Fin D =>
    exists_blockUnitary_of_equiv hd (r₁ := r₁) (by omega) hdig hD π
  set Cb := Finset.univ.sup Cπ
  obtain ⟨KW, hKW⟩ := exists_isPairProduct (n := r₁ + r₁) hd (by omega)
  refine ⟨CG + KW + Cb, fun A S ω hω hωS α hα M _ ℓ N _ hN L hℓ hL hinj => ?_⟩
  have hr : ∀ k, r₁ + r₁ ≤ ℓ k := fun k => by have := hℓ k; omega
  have hL1 : 1 ≤ L := by
    have := hℓ 0
    have := hL 0
    omega
  -- The GHZ-type state.
  set α' : Cfg d r₁ → ℂ := Function.extend dig₀ α 0
  have hα' : ∑ u, star (α' u) * α' u = 1 := by
    rw [sum_extend_zero hdig₀ α (fun _ a => star a * a) (by simp)]
    exact hα
  have hφ := hCG ℓ hN hr L hℓ hL α' hα'
  -- The block unitaries, implementing the isometric factors on the pairs of `S`.
  have hUk : ∀ k, ∃ U : Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ,
      IsPairProduct d (ℓ k) (Cb * ℓ k) U ∧ ∀ l r τ, (l, r) ∈ S →
        U τ (blockInputCfg hd (ℓ k) dig l r) =
          polarIsoMatrix (blockTensor A (ℓ k)) ((decodeBlockEquiv d (ℓ k)).symm τ)
            (finProdFinEquiv (l, r)) := fun k => by
    obtain ⟨π, hπ⟩ := exists_pairEquiv_val_lt_card_iff_mem S
    obtain ⟨bq, Q, hb0, hbq, -, hrow, -, hiso, hVQ⟩ :=
      exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn (fun _ : Fin (ℓ k) => A)
        (by have := hℓ k; omega) (by rw [MPSChainTensor.blockTensor_const]; exact hinj k) π hπ
    obtain ⟨U, hUpp, hUQ⟩ := hCπ π (ℓ k) (hℓ k) bq Q hb0 hrow hiso
    refine ⟨U, hUpp.mono (Nat.mul_le_mul_right _ (Finset.le_sup (Finset.mem_univ π))),
      fun l r τ hlr => ?_⟩
    have hx : (π.symm (l, r)).val < S.card :=
      (hπ (π.symm (l, r))).mpr (by rw [Equiv.apply_symm_apply]; exact hlr)
    have h1 := hUQ (π.symm (l, r)) (by rw [hbq]; exact hx) τ
    have h2 := hVQ τ (π.symm (l, r)) hx
    simp only [Equiv.apply_symm_apply, MPSChainTensor.blockTensor_const] at h1 h2
    rw [h1, ← h2]
    rfl
  choose U hUpp hU using hUk
  -- The window unitary `W : |dig₀ j, 0⟩ ↦ |ω_j⟩`.
  have hs : Function.Injective (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) :=
    fun p p' h => Prod.ext (twoCfg_injective hdig h).1 (twoCfg_injective hdig h).2
  let enc : Fin b → Cfg d (r₁ + r₁) → ℂ := fun j =>
    Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω j) 0
  obtain ⟨W, hWu, hW⟩ : ∃ W ∈ unitary (Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ),
      ∀ u j, W u (windowInput (dig₀ j)) = enc j u := by
    let V : Matrix (Cfg d (r₁ + r₁)) (Fin b) ℂ := Matrix.of fun u j => enc j u
    have hV : V.IsIsometry := by
      ext j j'
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [conjTranspose_apply, V, Matrix.of_apply]
      rw [sum_extend_zero hs (ω j) (fun u a => star a * enc j' u) (by simp)]
      simp only [enc, hs.extend_apply]
      exact hω j j'
    let emb : Fin b ↪ Cfg d (r₁ + r₁) :=
      ⟨fun j => windowInput (dig₀ j), windowInput_injective.comp hdig₀⟩
    obtain ⟨W, hW, hWV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
    exact ⟨W, hW, fun u j => hWV u j⟩
  -- The circuit after the measurement.
  have hcirc : IsCircuitOn Set.univ (KW + Cb * L)
      (blockLayerOp hN U * pairLayerOp hN hr fun _ => W) :=
    (isCircuitOn_pairLayerOp hN hr fun _ => hKW W hWu).mul
      (isCircuitOn_blockLayerOp hN (K := Cb * L) fun k =>
        (hUpp k).mono (Nat.mul_le_mul_left Cb (hL k)))
  refine ⟨CG * L, KW + Cb * L, windowGHZState hN hr α',
    blockLayerOp hN U * pairLayerOp hN hr (fun _ => W),
    by nlinarith, hφ, hcirc.isBondCircuitOfDepth, ?_⟩
  -- The circuit takes each configuration of the GHZ-type state to the state of its label.
  have hj : ∀ j, (blockLayerOp hN U * pairLayerOp hN hr fun _ => W) *ᵥ
      Pi.single (registerCfg hN hr (dig₀ j)) 1 = fun s => blockIsometryState A (ω j) hN s := by
    intro j
    obtain ⟨Wj, -, hWj⟩ := exists_pairUnitary hd hdig (ω j) (by simpa using hω j j)
    funext s
    rw [blockIsometryState_eq_chainBlockIsometryState,
      chainBlockIsometryState_eq_mulVec hd hN hr hdig (fun _ => A) (fun _ => ω j) (U := U)
        (fun c hc k τ => by
          rw [chainBlockTensor_const]
          exact hU k _ _ τ (hωS j c (by rwa [pairFamilyState_const] at hc) k))
        (W := fun _ => Wj) (fun _ => hWj) s,
      ← mulVec_mulVec, ← mulVec_mulVec]
    have key : pairLayerOp hN hr (fun _ => W) *ᵥ Pi.single (registerCfg hN hr (dig₀ j)) 1 =
        pairLayerOp hN hr (fun _ => Wj) *ᵥ productVector fun _ => Pi.single ⟨0, hd⟩ 1 := by
      funext y
      rw [pairLayerOp_mulVec_apply hd hN hr (fun _ => Wj) y]
      simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [pairLayerOp_apply]
      simp only [registerCfg_comp_pairSite, hW, h0]
      refine if_congr ⟨fun h i hi => (h i hi).trans (registerCfg_of_forall_pairSite_ne hN hr _ hi),
        fun h i hi => (h i hi).trans (registerCfg_of_forall_pairSite_ne hN hr _ hi).symm⟩ ?_ rfl
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← h0, hWj]
    rw [key]
  rw [windowGHZState_extend hN hr hdig₀ α]
  have hsum : (fun x => ∑ j, α j * if x = registerCfg hN hr (dig₀ j) then (1 : ℂ) else 0) =
      ∑ j, α j • Pi.single (registerCfg hN hr (dig₀ j)) (1 : ℂ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum, mulVec_sum]
  funext s
  simp only [mulVec_smul, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **The state of a tensor injective on a set of bond pairs, with measurements.** For `d ≥ 2`
and every bond dimension `D` and number of labels `b` there are `C` and `L₀` such that for every
tensor `A`, every set `S` of bond pairs, pairs `ω_j` that are orthonormal and whose products
vanish on the bond configurations leaving `S`, unit amplitudes `α`, and every cutting of a ring
into `M ≥ 1` blocks of lengths `L₀ ≤ ℓ_k ≤ L` at which the blocked tensors are injective on `S`,
the state `∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ |ω_j⟩` is prepared with measurements and a circuit in depth at most
`C L`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements". The labels and the bond indices
are encoded in `r₁ = b + D + 2` sites. -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_blockIsometryState_of_isInjectiveOn
    (hd : 2 ≤ d) (D b : ℕ) :
    ∃ C L₀ : ℕ, ∀ (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
      (ω : Fin b → Fin D × Fin D → ℂ),
      (∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) →
      (∀ j {M : ℕ} (c : Fin M → Fin D × Fin D), pairProductState (ω j) c ≠ 0 → ∀ k, c k ∈ S) →
      ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        (∀ k, L₀ ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
        (∀ k, IsInjectiveOn (blockTensor A (ℓ k)) (S : Set (Fin D × Fin D))) →
        IsPreparedWithMeasurementsAndCircuitInDepth (C * L)
          (fun s => ∑ j, α j * blockIsometryState A (ω j) hN s) := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · -- No unit pair on the zero space; the hypotheses are contradictory.
    refine ⟨0, 0, fun A S ω hω _ α hα M _ ℓ N _ hN L _ _ _ => absurd hα ?_⟩
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have := hω ⟨0, hb⟩ ⟨0, hb⟩
      simp at this
  set r₁ := b + D + 2
  have hpow : r₁ < d ^ r₁ :=
    (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hd r₁)
  obtain ⟨dig⟩ : Nonempty (Fin D ↪ Cfg d r₁) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨dig₀⟩ : Nonempty (Fin b ↪ Cfg d r₁) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨C, hC⟩ :=
    exists_isPreparedWithMeasurementsAndCircuitInDepth_of_encoding_of_isInjectiveOn
      (D := D) (b := b) (r₁ := r₁) (by omega) dig.injective dig₀.injective hD
  exact ⟨C, 3 * r₁, fun A S ω hω hωS α hα M _ ℓ N _ hN L hℓ hL hinj =>
    hC A S ω hω hωS α hα ℓ hN L hℓ hL hinj⟩

end Preparation

/-- **Preparation with measurements contains preparation by circuits.** A nonzero vector
prepared from a product state by a local circuit of depth `T` is prepared with measurements and a
circuit in depth `T`: the measurement stage measures no site, and the circuit after it is
empty. -/
theorem isPreparedWithMeasurementsAndCircuitInDepth_of_isPreparedInDepth {N : ℕ} [NeZero N]
    {T : ℕ} {ψ : Cfg d N → ℂ} (hψ : IsPreparedInDepth T ψ) (hψ0 : ψ ≠ 0) :
    IsPreparedWithMeasurementsAndCircuitInDepth T ψ :=
  ⟨T, 0, ψ, 1, by omega, isPreparedWithMeasurementsInDepth_of_isPreparedInDepth hψ hψ0,
    ⟨[], rfl, rfl⟩, (Matrix.one_mulVec ψ).symm⟩

/-! ### A chain of one block -/

/-- The isometries on the blocks act linearly on the vector of bond pairs. -/
private theorem blockIsoVector_sum_smul {D M N : ℕ} {ℓ : Fin M → ℕ} {κ : Type*}
    [Fintype κ]
    (B : ∀ k, MPSTensor (blockPhysDim d (ℓ k)) D) (hN : ∑ k, ℓ k = N) (c : κ → ℂ)
    (x : κ → MPVSpace (D * D) M) :
    blockIsoVector B hN (∑ i, c i • x i) = ∑ i, c i • blockIsoVector B hN (x i) := by
  ext s
  simp only [blockIsoVector_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun τ _ => by ring

/-- **A chain of one block.** Let the blocked direct sum with unit weights, cut into one block of
`N` sites, be injective on the bond pairs of the blocks, and let `|φ⟩ = ∑ⱼ βⱼ |φ_N(A_j)⟩ ≠ 0`.
Then `|φ⟩/‖φ‖ = V ⊗ |ω⟩` for a unit pair `ω` whose product vanishes on the bond configurations
leaving the pairs of the blocks: `|φ_N(A_j)⟩` is `V` applied to the trace of the tensor
`P K_j K_jᴴ` (`MPSTensor.mpvState_eq_blockIsoVector`), which vanishes outside these pairs. -/
theorem exists_blockIsometryState_eq_smul {D b : ℕ} {Dj : Fin b → ℕ}
    {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (Dj j) → Fin D}
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    {N : ℕ} [NeZero N] (hN1 : ∑ _ : Fin 1, N = N)
    (hinj : IsInjectiveOn (blockTensor (blockSum Aj ι fun _ => 1) N)
      (blockPairs ι : Set (Fin D × Fin D)))
    (β : Fin b → ℂ) (φ : MPVSpace d N) (hφ : ∀ s, φ s = ∑ j, β j * mpv (Aj j) s)
    (hφ0 : φ ≠ 0) :
    ∃ ω : Fin D × Fin D → ℂ, ∑ p, star (ω p) * ω p = 1 ∧
      (∀ c : Fin 1 → Fin D × Fin D, pairFamilyState (fun _ => ω) c ≠ 0 →
        ∀ k, c k ∈ blockPairs ι) ∧
      blockIsometryState (blockSum Aj ι fun _ => 1) ω hN1 = ((‖φ‖ : ℂ)⁻¹) • φ := by
  classical
  set B := blockTensor (blockSum Aj ι fun _ => 1) N
  have hN0 : N ≠ 0 := NeZero.ne N
  set y : Fin b → MPVSpace (D * D) 1 := fun j =>
    (EuclideanSpace.equiv (ι := Cfg (D * D) 1) (𝕜 := ℂ)).symm fun τ =>
      mpvFamily (n := fun _ => D * D) (fun _ => blockPosTensor ι B j) τ
  set Y : MPVSpace (D * D) 1 := ∑ j, β j • y j
  have hφY : φ = blockIsoVector (fun _ : Fin 1 => B) hN1 Y := by
    rw [blockIsoVector_sum_smul]
    ext s
    have h := fun j => congrArg (fun v : MPVSpace d N => v s)
      (mpvState_eq_blockIsoVector (Aj := Aj) hι hdisj j hN1 hN0 fun _ => hN0)
    simp only [mpvState_apply] at h
    rw [hφ]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [h j]
  -- `Y` vanishes outside the pairs of the blocks.
  have hYS : ∀ τ : Cfg (D * D) 1, virtualPairEquiv D (τ 0) ∉ blockPairs ι → Y τ = 0 := by
    intro τ hτ
    have hP := polarPosTensor_eq_zero hinj (x := τ 0) hτ
    have hX : ∀ j, blockPosTensor ι B j (τ 0) = 0 := fun j => by
      ext a c
      have hrow : ∀ r : Fin D × Fin D,
          Matrix.polarPos (physicalMatrix B) (virtualPairEquiv D (τ 0)) r = 0 := fun r => by
        have := congrFun (congrFun hP r.1) r.2
        simpa [polarPosTensor, ofPhysicalMatrix] using this
      change (Matrix.polarPos (physicalMatrix B) *
        (pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ)) (virtualPairEquiv D (τ 0)) (a, c) = 0
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun r _ => by rw [hrow r, zero_mul]
    simp only [Y, y, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [EuclideanSpace.equiv, PiLp.toLp_apply, mpvFamily, hX j]
  have hnorm : ‖φ‖ = ‖Y‖ := by
    rw [hφY]
    exact norm_blockIsoVector_of_isInjectiveOn hN1 (S := fun _ => (blockPairs ι : Set _))
      (fun _ => hinj) Y fun τ ⟨k, hk⟩ => hYS τ (by rwa [Subsingleton.elim k 0] at hk)
  have hY0 : ‖Y‖ ≠ 0 := by rw [← hnorm]; exact norm_ne_zero_iff.2 hφ0
  set e : Fin D × Fin D ≃ Cfg (D * D) 1 :=
    (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (Equiv.funUnique (Fin 1) _).symm)
  have he : ∀ p, e p = fun _ => finProdFinEquiv (p.2, p.1) := fun p => rfl
  refine ⟨fun p => ((‖Y‖ : ℂ)⁻¹) * Y (e p), ?_, ?_, ?_⟩
  · have hY2 : ∑ τ, star (Y τ) * Y τ = ((‖Y‖ ^ 2 : ℝ) : ℂ) := by
      rw [EuclideanSpace.norm_sq_eq, ofReal_sum_norm_sq]
    have hsum : ∑ p, star (Y (e p)) * Y (e p) = ∑ τ, star (Y τ) * Y τ :=
      e.sum_comp fun τ => star (Y τ) * Y τ
    calc ∑ p, star (((‖Y‖ : ℂ)⁻¹) * Y (e p)) * (((‖Y‖ : ℂ)⁻¹) * Y (e p))
        = ((‖Y‖ : ℂ)⁻¹) ^ 2 * ∑ p, star (Y (e p)) * Y (e p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal]
          ring
      _ = 1 := by
          rw [hsum, hY2]
          push_cast
          field_simp
  · intro c hc k
    rw [Subsingleton.elim k 0]
    by_contra hk
    apply hc
    simp only [pairFamilyState, Fin.prod_univ_one]
    have h1 : finRotate 1 0 = 0 := Subsingleton.elim _ _
    rw [h1, hYS, mul_zero]
    simpa [e, virtualPairEquiv] using hk
  · have hpair : pairFamilyVector (fun _ => fun p => ((‖Y‖ : ℂ)⁻¹) * Y (e p)) =
        ((‖Y‖ : ℂ)⁻¹) • Y := by
      ext τ
      rw [pairFamilyVector_apply, PiLp.smul_apply, smul_eq_mul]
      simp only [pairFamilyState, Fin.prod_univ_one]
      have h1 : finRotate 1 0 = 0 := Subsingleton.elim _ _
      have hτ : e ((finProdFinEquiv.symm (τ 0)).2, (finProdFinEquiv.symm (τ 0)).1) = τ := by
        funext k
        rw [Subsingleton.elim k 0, he]
        simp only [Prod.mk.eta, Equiv.apply_symm_apply]
      rw [h1, hτ]
    rw [blockIsometryState_eq_blockIsoVector, hpair, blockIsoVector_smul, ← hφY, hnorm]

/-! ### Error `ε` in depth `O(log(N/ε))` -/

/-- **A common rate for the blocks and their mixed transfer maps.** For finitely many normal
left-canonical blocks whose mixed transfer maps have all eigenvalues of modulus below one, there
is `0 < t < 1` bounding the moduli of the eigenvalues other than `1` of every transfer map and of
all eigenvalues of the mixed transfer maps of distinct blocks (arXiv:2307.01696, eq. (5), and
the spectral radius `τ < 1` of the mixed transfer matrices used in the Supplemental Material,
proof of Lemma 1'(ii)). -/
theorem exists_forall_eigenvalue_norm_le_of_mixed {b : ℕ} [NeZero b] {Dj : Fin b → ℕ}
    {Aj : (j : Fin b) → MPSTensor d (Dj j)} (hN : ∀ j, Kraus.IsNormal (Aj j))
    (hA : ∀ j, IsLeftCanonical (Aj j)) (hD : ∀ j, NeZero (Dj j))
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ < 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' → μ' ≠ 1 →
        ‖μ'‖ ≤ ‖(t : ℂ)‖) ∧
      ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
        ‖μ'‖ ≤ ‖(t : ℂ)‖ := by
  classical
  obtain ⟨t₁, ht₁0, ht₁1, hdiag⟩ := exists_forall_eigenvalue_norm_le hN hA hD
  have hpair : ∀ p : Fin b × Fin b, ∃ s : ℝ, s < 1 ∧ (p.1 ≠ p.2 → ∀ μ',
      Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj p.1) (Aj p.2)) μ' → ‖μ'‖ ≤ s) := by
    rintro ⟨j, j'⟩
    by_cases h : j = j'
    · exact ⟨0, zero_lt_one, fun h' => absurd h h'⟩
    · obtain ⟨δ, hδ, hgap⟩ := uniform_eigenvalue_gap_of_finite_lt_one
        (Module.End.finite_hasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')))
        fun μ' hμ _ => hmix j j' h μ' hμ
      refine ⟨1 - δ, by linarith, fun _ μ' hμ => ?_⟩
      by_cases h1 : μ' = 1
      · have := hmix j j' h μ' hμ
        rw [h1, norm_one] at this
        exact absurd this (lt_irrefl _)
      · exact hgap μ' hμ h1
  choose s hs1 hs using hpair
  set t := max t₁ (Finset.univ.sup' Finset.univ_nonempty s)
  have ht0 : 0 < t := lt_max_of_lt_left ht₁0
  have ht1 : t < 1 := max_lt ht₁1 ((Finset.sup'_lt_iff _).2 fun p _ => hs1 p)
  have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hn₁ : ‖(t₁ : ℂ)‖ = t₁ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₁0]
  refine ⟨t, ht0, ht1, fun j μ' hμ h1 => ?_, fun j j' h μ' hμ => ?_⟩
  · rw [hnt]
    exact (hn₁ ▸ hdiag j μ' hμ h1).trans (le_max_left _ _)
  · rw [hnt]
    exact (hs (j, j') h μ' hμ).trans ((Finset.le_sup' s (Finset.mem_univ (j, j'))).trans
      (le_max_right _ _))

/-- **Every translation-invariant MPS with measurements, in depth `O(log(N/ε))`.** Let
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (arXiv:2307.01696, Supplemental Material,
eq. (S2)) with nonzero complex weights, every block `A_j` normal in the gauge of eq. (5):
`∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`, and let the mixed transfer
maps `E_{jj'}` of distinct blocks have all eigenvalues of modulus below one. There is `c`,
depending only on `A`, with the following property. For every `N ≥ 2` and `0 < ε ≤ 1` at which
the periodic state `|φ_N(A)⟩` does not vanish, some unit vector `|ψ⟩` with
`1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared with measurements and a circuit in depth at most `c log(N/ε)`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements": "If instead measurements are
only used for the preparation of `|χ_{N/q}⟩`, the depth is `O(log(N/ε))`", for MPS
"short- or long-range correlated". The `q`-site states of distinct blocks need not be
orthogonal, the multiplicities and the weights are arbitrary, and `N` need not be a multiple of
the block length: for `q = ⌈a log(N/ε) + b⌉ ≤ N` the chain is cut into blocks "all of the same
size, `q_N`, except for the last one, which may be larger" (Supplemental Material, proof of
Theorem 1), the state `∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ |ω_j⟩` of the direct sum with unit weights has error at
most `ε` (`MPSTensor.exists_one_sub_norm_inner_sum_blockIsometryState_le`) and is prepared in
depth `O(q)`
(`exists_isPreparedWithMeasurementsAndCircuitInDepth_blockIsometryState_of_isInjectiveOn`);
for `N < q`, `|φ_N⟩` itself is prepared, as the state of one block
(`exists_blockIsometryState_eq_smul`) or, below a fixed length, in bounded depth. The periodic
state is assumed nonzero, as the normalization of the source presupposes. -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero
    {D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ < 1) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N →
      mpvState (repeatedBlockSum Aj ι μ) N ≠ 0 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
        IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) N⟫_ℂ‖ ≤ ε := by
  classical
  -- The target itself, used for short chains.
  have hself : ∀ (N : ℕ) (v : MPVSpace d N) (ε : ℝ), 0 < ε → ‖v‖ = 1 →
      1 - ‖⟪v, v⟫_ℂ‖ ≤ ε := fun N v ε hε hv => by
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num [hε.le]
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · -- For `d ≤ 1` the target is prepared in depth `0`.
    refine ⟨0, fun ε hε _ N _ _ h0 => ⟨_, 0, norm_normalizedMPVState h0, by simp, ?_,
      hself N _ ε hε (norm_normalizedMPVState h0)⟩⟩
    refine isPreparedWithMeasurementsAndCircuitInDepth_of_isPreparedInDepth
      (isPreparedInDepth_zero_of_le_one (by omega) _) fun h => ?_
    have h1 := norm_normalizedMPVState h0
    rw [show normalizedMPVState (repeatedBlockSum Aj ι μ) N = 0 from by
      ext s; exact congrFun h s] at h1
    simp at h1
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- Without blocks the periodic state vanishes.
    refine ⟨0, fun ε _ _ N _ _ h0 => absurd ?_ h0⟩
    ext s
    rw [mpvState_apply, mpv_repeatedBlockSum hι hdisj μ (NeZero.ne N)]
    simp
  have : NeZero b := ⟨hb.ne'⟩
  have hd : 0 < d := by omega
  have hDj : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  -- The direct sum of the blocks with unit weights, on the bond dimension `D' = ∑ⱼ Dⱼ`.
  set D' := ∑ j, Dj j
  set ι' : (j : Fin b) → Fin (Dj j) → Fin D' := flatCoord Dj
  have hι' : ∀ j, Function.Injective (ι' j) := fun j => flatCoord_injective j
  have hdisj' : ∀ j j', j ≠ j' → ∀ a a', ι' j a ≠ ι' j' a' := fun j j' h a a' =>
    flatCoord_ne h a a'
  set AJ := MPSTensor.blockSum Aj ι' fun _ => 1
  set ω : Fin b → Fin D' × Fin D' → ℂ := fun j => embedPair (ι' j) (fixedPointPair (σ j))
  have hω : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0 := fun j j' => by
    split_ifs with h
    · subst h
      rw [inner_embedPair_self (hι' j), fixedPointPair_norm_sq (hσ j).posSemidef, htr j]
    · exact inner_embedPair_eq_zero_of_disjoint (hdisj' j j' h) _ _
  have hωS : ∀ j {M : ℕ} (c : Fin M → Fin D' × Fin D'), pairProductState (ω j) c ≠ 0 →
      ∀ k, c k ∈ blockPairs ι' := fun j M c hc k =>
    mem_blockPairs_of_pairProductState_embedPair_ne_zero j _ hc k
  -- A common rate.
  obtain ⟨t, ht0, ht1, hlam, hmixle⟩ :=
    exists_forall_eigenvalue_norm_le_of_mixed hN hA hDj hmix
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  -- The constants.
  obtain ⟨L₀, hL₀⟩ := exists_isInjectiveOn_blockTensor_blockSum hι' hdisj' hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (by rw [hnorm]; exact ht1) hlam hmixle
  obtain ⟨K, hK, herr⟩ := exists_one_sub_norm_inner_sum_blockIsometryState_le hι' hdisj' hN hA hσ
    htr hfix hlam hmixle (γ := 1 / 4) (by norm_num) (by norm_num)
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨Cp, Lp, hCp⟩ :=
    exists_isPreparedWithMeasurementsAndCircuitInDepth_blockIsometryState_of_isInjectiveOn
      hd2 D' b
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_chainBlockIsometryState_of_isInjectiveOn d D'
  set Lmin := L₀ + Lp + 3 * D' + 1
  obtain ⟨Ks, hKs⟩ := exists_isPreparedInDepth_of_norm_eq_one hd Lmin
  set r := -(1 / 4 * Real.log t) with hr
  have hr0 : 0 < r := by
    have := Real.log_neg ht0 ht1
    rw [hr]; linarith
  have hexp : ∀ q : ℕ, Real.exp (-(1 / 4) * q / correlationLength (t : ℂ)) =
      Real.exp (-(r * q)) := fun q => by
    congr 1
    rw [mul_div_right_comm, neg_div_correlationLength, hnorm, hr]
    ring
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a := 1 / r with ha
  set bq : ℝ := max (Real.log K) 0 / r + Lmin with hbq
  have ha0 : 0 < a := by positivity
  have hmax : 0 ≤ max (Real.log K) 0 / r := by positivity
  have hb1 : 1 ≤ bq := by
    have : (1 : ℝ) ≤ Lmin := by exact_mod_cast (show 1 ≤ Lmin by omega)
    linarith
  set c₀ := a + bq / Real.log 2
  have hc₀ : 0 ≤ c₀ := by positivity
  refine ⟨4 * Cp * c₀ + Ce * c₀ + Ks / Real.log 2, fun ε hε hε1 N _ hN2 h0 => ?_⟩
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2'.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 ≤ Real.log (N / ε) := hl2.le.trans hlog
  set Q := a * Real.log (N / ε) + bq with hQ
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ a * Real.log (N / ε) := by positivity
    linarith
  have hQc : Q ≤ c₀ * Real.log (N / ε) := by
    have hbl : bq ≤ bq / Real.log 2 * Real.log (N / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlog (zero_le_one.trans hb1)
    simp only [c₀, add_mul]
    linarith
  -- Each depth bound below is a multiple of `log(N/ε)`.
  have hc : ∀ T : ℕ, ((T : ℝ) ≤ 4 * Cp * c₀ * Real.log (N / ε) ∨
      (T : ℝ) ≤ Ce * c₀ * Real.log (N / ε) ∨ (T : ℝ) ≤ Ks / Real.log 2 * Real.log (N / ε)) →
      (T : ℝ) ≤ (4 * Cp * c₀ + Ce * c₀ + Ks / Real.log 2) * Real.log (N / ε) := by
    intro T hT
    have h1 : 0 ≤ 4 * Cp * c₀ * Real.log (N / ε) := by positivity
    have h2 : 0 ≤ Ce * c₀ * Real.log (N / ε) := by positivity
    have h3 : 0 ≤ Ks / Real.log 2 * Real.log (N / ε) := by positivity
    rw [add_mul, add_mul]
    rcases hT with h | h | h <;> linarith
  -- The target as a combination of the states of the blocks.
  set β := bntWeight μ N
  have hφ : ∀ s, mpvState (repeatedBlockSum Aj ι μ) N s = ∑ j, β j * mpv (Aj j) s := fun s => by
    rw [mpvState_apply, mpv_repeatedBlockSum hι hdisj μ (NeZero.ne N)]
  have hnormφ : normalizedMPVState (repeatedBlockSum Aj ι μ) N =
      ((‖mpvState (repeatedBlockSum Aj ι μ) N‖ : ℂ)⁻¹) • mpvState (repeatedBlockSum Aj ι μ) N :=
    rfl
  set q := ⌈Q⌉₊ with hqdef
  have hQq : Q ≤ q := Nat.le_ceil Q
  have hqQ : (q : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hq0 : 0 < q := by exact_mod_cast (show (0 : ℝ) < q by linarith)
  have hLq : Lmin ≤ q := by
    have : (Lmin : ℝ) ≤ q := by
      have : 0 ≤ a * Real.log (N / ε) + max (Real.log K) 0 / r := by positivity
      linarith
    exact_mod_cast this
  by_cases hqN : q ≤ N
  · -- Long chains: `M - 1` blocks of length `q` and one of length `q' = q + N % q < 2q`.
    obtain ⟨m', hm⟩ : ∃ m', N / q = m' + 1 :=
      ⟨N / q - 1, (Nat.succ_pred_eq_of_pos (Nat.div_pos hqN hq0)).symm⟩
    set q' := q + N % q
    set ℓ : Fin (m' + 1) → ℕ := fun k => if k = Fin.last m' then q' else q
    have hsum : ∑ k, ℓ k = N := by
      rw [Fin.sum_univ_castSucc]
      simp only [ℓ, Fin.castSucc_ne_last, ite_false, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ite_true]
      have := Nat.div_add_mod N q
      rw [hm] at this
      simp only [q']
      linarith
    have hℓq : ∀ k, q ≤ ℓ k := fun k => by simp only [ℓ]; split_ifs <;> omega
    have hℓ2 : ∀ k, ℓ k ≤ 2 * q := fun k => by
      have := Nat.mod_lt N hq0
      simp only [ℓ, q']; split_ifs <;> omega
    have hinjℓ : ∀ k, IsInjectiveOn (blockTensor AJ (ℓ k))
        (blockPairs ι' : Set (Fin D' × Fin D')) := fun k => hL₀ _ (by have := hℓq k; omega)
    have hβ : β ≠ 0 := by
      intro hβ0
      apply h0
      ext s
      rw [hφ s, PiLp.zero_apply]
      simp [hβ0]
    set α := ghzAmplitude β
    have hα : ∑ j, star (α j) * α j = 1 := ghzAmplitude_norm_sq hβ
    set ψ := ∑ j, α j • blockIsometryState AJ (ω j) hsum
    have hψ : (fun s => ψ s) = fun s => ∑ j, α j * blockIsometryState AJ (ω j) hsum s := by
      funext s
      simp only [ψ, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    refine ⟨ψ, Cp * (2 * q), norm_sum_smul_blockIsometryState hι' hdisj'
      (fun j => (hσ j).posSemidef) htr hα hsum hinjℓ, hc _ (Or.inl ?_), ?_, ?_⟩
    · push_cast
      have : (0 : ℝ) ≤ Cp := Nat.cast_nonneg _
      nlinarith
    · rw [hψ]
      exact hCp AJ (blockPairs ι') ω hω hωS α hα ℓ hsum (2 * q)
        (fun k => by have := hℓq k; omega) hℓ2 hinjℓ
    · rw [hnormφ]
      refine (herr β hβ (m' + 1) ℓ hsum q hℓq hinjℓ _ hφ).trans ?_
      rw [hexp]
      -- `K M e^{-r q} ≤ ε` from `M ≤ N` and `r q ≥ log K + log(N/ε)`.
      have hMN : ((m' + 1 : ℕ) : ℝ) ≤ N := by
        rw [← hm]; exact_mod_cast Nat.div_le_self N q
      have hN0 : (0 : ℝ) < N := by linarith
      have hrq : Real.log K + Real.log N - Real.log ε ≤ r * q := by
        have h1 : r * Q ≤ r * q := mul_le_mul_of_nonneg_left hQq hr0.le
        have h2 : r * Q = Real.log (N / ε) + max (Real.log K) 0 + r * Lmin := by
          simp only [Q, bq, a]; field_simp; ring
        rw [Real.log_div hN0.ne' hε.ne'] at h2
        have : 0 ≤ r * Lmin := by positivity
        linarith [le_max_left (Real.log K) 0]
      calc K * (((m' + 1 : ℕ) : ℝ) * Real.exp (-(r * q)))
          ≤ K * (N * Real.exp (-(r * q))) := by gcongr
        _ ≤ ε := mul_mul_exp_neg_le_of_log_le hK hN0 hε hrq
  · -- Short chains: `N < a log(N/ε) + b`, and `|φ_N⟩` is prepared exactly.
    have hNQ : (N : ℝ) < Q := Nat.lt_ceil.mp (not_le.mp hqN)
    have hψ1 := norm_normalizedMPVState h0
    by_cases hNL : Lmin ≤ N
    · have hN1 : ∑ _ : Fin 1, N = N := by simp
      have hinjN : IsInjectiveOn (blockTensor AJ N) (blockPairs ι' : Set (Fin D' × Fin D')) :=
        hL₀ N (by omega)
      obtain ⟨ω₁, hω₁, hω₁S, heq⟩ := exists_blockIsometryState_eq_smul hι' hdisj' hN1 hinjN β _
        hφ h0
      have hprep : IsPreparedInDepth (Ce * N) fun s =>
          normalizedMPVState (repeatedBlockSum Aj ι μ) N s := by
        rw [hnormφ, ← heq, blockIsometryState_eq_chainBlockIsometryState]
        exact hCe (fun _ : Fin 1 => N) hN1 (fun _ => AJ) (fun _ => blockPairs ι')
          (fun _ => ω₁) (fun _ => hω₁) hω₁S N (fun _ => by omega) (fun _ => le_rfl)
          fun _ => by rw [chainBlockTensor_const]; exact hinjN
      refine ⟨normalizedMPVState (repeatedBlockSum Aj ι μ) N, Ce * N, hψ1,
        hc _ (Or.inr (Or.inl ?_)), ?_, hself N _ ε hε hψ1⟩
      · push_cast
        have : (0 : ℝ) ≤ Ce := Nat.cast_nonneg _
        calc (Ce : ℝ) * N ≤ Ce * Q := by gcongr
          _ ≤ Ce * (c₀ * Real.log (N / ε)) := by gcongr
          _ = Ce * c₀ * Real.log (N / ε) := by ring
      · refine isPreparedWithMeasurementsAndCircuitInDepth_of_isPreparedInDepth hprep fun h => ?_
        have h1 := hψ1
        rw [show normalizedMPVState (repeatedBlockSum Aj ι μ) N = 0 from by
          ext s; exact congrFun h s] at h1
        simp at h1
    · refine ⟨normalizedMPVState (repeatedBlockSum Aj ι μ) N, Ks, hψ1,
        hc _ (Or.inr (Or.inr ?_)), ?_, hself N _ ε hε hψ1⟩
      · rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
        exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      · refine isPreparedWithMeasurementsAndCircuitInDepth_of_isPreparedInDepth
          (hKs N hN2 (by omega) _ hψ1) fun h => ?_
        have h1 := hψ1
        rw [show normalizedMPVState (repeatedBlockSum Aj ι μ) N = 0 from by
          ext s; exact congrFun h s] at h1
        simp at h1

/-- **The periodic state does not vanish on long chains.** In the setting of
`exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero`, there is `N₀`
such that `|φ_N(A)⟩ ≠ 0` for every `N ≥ N₀` at which the weights `βⱼ = ∑ₖ μ_{j,k}^N` are not all
zero: the squared norm of `∑ⱼ βⱼ |φ_N(A_j)⟩` is `∑ⱼ |βⱼ|²` up to the relative error
`K e^{-γ N/ξ}` (`MPSTensor.exists_abs_sum_norm_sq_sum_mpv_sub_le`; arXiv:2307.01696,
Supplemental Material, proof of Lemma 1'(ii)). -/
theorem exists_mpvState_repeatedBlockSum_ne_zero
    {D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ < 1) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → bntWeight μ N ≠ 0 → mpvState (repeatedBlockSum Aj ι μ) N ≠ 0 := by
  classical
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact ⟨0, fun N _ hβ => absurd (Subsingleton.elim _ _) hβ⟩
  have : NeZero b := ⟨hb.ne'⟩
  have hDj : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  obtain ⟨t, ht0, ht1, hlam, hmixle⟩ := exists_forall_eigenvalue_norm_le_of_mixed hN hA hDj hmix
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨Kt, hKt, hT⟩ := exists_abs_sum_norm_sq_sum_mpv_sub_le hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (by rw [hnorm]; exact ht1) hlam hmixle (γ := 1 / 4) (by norm_num)
      (by norm_num)
  set x := Real.exp (-(1 / 4) / correlationLength (t : ℂ))
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by
    rw [Real.exp_lt_one_iff, neg_div_correlationLength, hnorm]
    exact mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg ht0 ht1)
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (Kt + 1) by positivity) hx1
  refine ⟨N₀ + 1, fun N hN hβ h0 => ?_⟩
  set β := bntWeight μ N
  set bb : ℝ := ∑ l, ‖β l‖ ^ 2
  have hbb : 0 < bb := sum_norm_sq_pos_of_ne_zero hβ
  have hβle : ∀ j, ‖β j‖ ≤ Real.sqrt bb := fun j =>
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖β j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j))
  have h := hT (Real.sqrt bb) β hβle N
  have hzero : ∑ s : Fin N → Fin d, ‖∑ j, β j * mpv (Aj j) s‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := congrArg (fun v : MPVSpace d N => v s) h0
    simp only [mpvState_apply, mpv_repeatedBlockSum hι hdisj μ (by omega : N ≠ 0),
      PiLp.zero_apply] at this
    rw [this, norm_zero]
    norm_num
  rw [hzero, zero_sub, abs_neg, abs_of_pos hbb, Real.sq_sqrt hbb.le] at h
  have hxN : x ^ N ≤ x ^ N₀ := pow_le_pow_of_le_one hx0 hx1.le (by omega)
  have : Kt * x ^ N < 1 := by
    calc Kt * x ^ N ≤ Kt * x ^ N₀ := mul_le_mul_of_nonneg_left hxN hKt
      _ ≤ (Kt + 1) * x ^ N₀ := by nlinarith [pow_nonneg hx0 N₀]
      _ < (Kt + 1) * (1 / (Kt + 1)) := by gcongr
      _ = 1 := by field_simp
  nlinarith

/-- **Every translation-invariant MPS with measurements, in depth `O(log(N/ε))`, long chains.**
In the setting of `exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero`
there are `c` and `N₀`, depending only on `A`, such that for every `N ≥ N₀` at which the weights
`βⱼ = ∑ₖ μ_{j,k}^N` of eq. (S4) are not all zero and every `0 < ε ≤ 1`, some unit vector `|ψ⟩`
with `1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared with measurements and a circuit in depth at most
`c log(N/ε)`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements"; the condition on the weights is
that of `exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_repeatedBlockSum`, which it
replaces for blocks whose states may overlap and for every chain length, and it implies
`|φ_N(A)⟩ ≠ 0` for `N ≥ N₀` (`exists_mpvState_repeatedBlockSum_ne_zero`). -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log
    {D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ < 1) :
    ∃ (c : ℝ) (N₀ : ℕ), ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      bntWeight μ N ≠ 0 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
        IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) N⟫_ℂ‖ ≤ ε := by
  obtain ⟨c, hc⟩ := exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero
    hι hdisj μ hN hA hσ htr hfix hmix
  obtain ⟨N₀, hN₀⟩ := exists_mpvState_repeatedBlockSum_ne_zero hι hdisj μ hN hA hσ htr hfix hmix
  exact ⟨c, max N₀ 2, fun ε hε hε1 N _ hN hβ =>
    hc ε hε hε1 N (le_of_max_le_right hN) (hN₀ N (le_of_max_le_left hN) hβ)⟩

end MPSPreparation
