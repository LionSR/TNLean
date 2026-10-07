/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockSumUnitary
import TNLean.MPS.Preparation.GHZSeedRegisters

/-!
# Fixed points of tensors that are not normal, prepared with measurements

arXiv:2307.01696, paragraph "Long-range MPS using measurements", prepares the fixed-point state
of a translation-invariant MPS that is not normal as `|Ω'⟩ = W^{⊗N/q} |χ_{N/q}⟩`: "First create
`|χ_{N/q}⟩`, which can be done in constant depth with measurements (following, e.g.,
Ref~\cite{Piroli2021}). Subsequently, apply in parallel the isometries
`W : |j⟩ ↦ |ω_j⟩_{R_i L_{i+1}}` such that `|Ω'⟩ = W^{⊗N/q} |χ_{N/q}⟩`, which also takes constant
depth." The isometries `V` of the blocked tensor then follow, "following the same steps as in the
tree-RG circuit". The circuit applied after the measurement does not depend on its outcomes.

This file proves this two-stage preparation
(`QuantumCircuit.IsPreparedWithMeasurementsAndCircuitInDepth`, defined in
`TNLean.Circuit.Measurement.Protocol`) for the state
`∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` of a family of tensors
`A_j` whose blocked tensors are injective and have orthogonal ranges
(`MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_sum_blockIsometryState`), in
depth `O(L)` for blocks of lengths at most `L`:

* the GHZ-type state on the registers (`MPSPreparation.windowGHZState`), with measurements, in
  depth `O(L)` (`MPSPreparation.exists_isPreparedWithMeasurementsInDepth_windowGHZState`);
* on every pair window, one unitary sending the register value `j` to the pair `ω_j` of block `j`,
  placed on the bond indices of block `j` (the isometry `W` of the source);
* on every block, one unitary implementing all the isometries `V_{j,k}` at once
  (`MPSPreparation.exists_blockSumUnitary`), of depth `O(L)`.

**Scope restriction (orthogonal blocks):** both preparation theorems of this file, with and
without a given encoding of the labels, take the orthogonality `B_jᴴ B_{j'} = 0` of the blocked
states of distinct tensors, which the source does not assume; the block unitary implements the
isometry of the blocked direct sum only under it. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_sum_blockIsometryState` —
  the preparation in depth `O(L)`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Long-range MPS using
  measurements", eq. (19), and the paragraph after it.
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), paragraph "State transformations with QC and LOCC"
  and Example 1.
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

variable {d N : ℕ}

/-! ### The preparation -/

section Preparation

variable [NeZero d] {b : ℕ} {Dj : Fin b → ℕ}

/-- **The fixed-point state of orthogonal blocks with measurements, for given encodings.** Let
the labels `j` of the blocks be encoded injectively in `r₁ ≥ 2` sites by `dig₀`, and the bond
indices of all blocks, `Fin (∑ⱼ Dⱼ)`, by `dig`. There is `C` such that for all tensors `A_j`,
unit pair vectors `ω_j`, unit amplitudes `α`, and every cutting of a chain into `M ≥ 1` blocks of
lengths `3 r₁ ≤ ℓ_k ≤ L` at which every blocked tensor is injective and the physical matrices of
distinct blocks are orthogonal, the state `∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` is
prepared with measurements and a circuit in depth at most `C L`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements": the GHZ-type state `|χ_{N/q}⟩`
with measurements, then the isometries `W : |j⟩ ↦ |ω_j⟩` on the pair windows, then the isometries
of the blocked tensor on the blocks. -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_sum_blockIsometryState_of_encoding
    {r₁ : ℕ} (hr₁ : 2 ≤ r₁) {dig : Fin (∑ j, Dj j) → Cfg d r₁} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r₁} (hdig₀ : Function.Injective dig₀) (hD : 0 < ∑ j, Dj j) :
    ∃ C : ℕ, ∀ (A : (j : Fin b) → MPSTensor d (Dj j))
      (ω : (j : Fin b) → Fin (Dj j) × Fin (Dj j) → ℂ), (∀ j, ∑ p, star (ω j p) * ω j p = 1) →
      ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        (∀ k, 3 * r₁ ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
        (∀ j k, Kraus.IsInjective (blockTensor (A j) (ℓ k))) →
        (∀ j j' k, j ≠ j' → (physicalMatrix (blockTensor (A j) (ℓ k)))ᴴ *
          physicalMatrix (blockTensor (A j') (ℓ k)) = 0) →
        IsPreparedWithMeasurementsAndCircuitInDepth (C * L)
          (fun s => ∑ j, α j * blockIsometryState (A j) (ω j) hN s) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have h0 : (⟨0, hd⟩ : Fin d) = 0 := Fin.ext (by simp)
  obtain ⟨CG, hCG⟩ := exists_isPreparedWithMeasurementsInDepth_windowGHZState (d := d) hr₁
  obtain ⟨CU, hCU⟩ := exists_blockSumUnitary (Dj := Dj) hd (by omega) hdig hD
  obtain ⟨KW, hKW⟩ := exists_isPairProduct (n := r₁ + r₁) hd (by omega)
  refine ⟨CG + KW + CU, fun A ω hω α hα M _ ℓ N _ hN L hℓ hL hinj horth => ?_⟩
  have hr : ∀ k, r₁ + r₁ ≤ ℓ k := fun k => by have := hℓ k; omega
  have hL1 : 1 ≤ L := by have := hℓ 0; have := hL 0; omega
  -- The GHZ-type state.
  set α' : Cfg d r₁ → ℂ := Function.extend dig₀ α 0
  have hα' : ∑ u, star (α' u) * α' u = 1 := by
    rw [sum_extend_zero hdig₀ α (fun _ a => star a * a) (by simp)]
    exact hα
  have hφ := hCG ℓ hN hr L hℓ hL α' hα'
  -- The block unitaries.
  choose U hUpp hU using fun k => hCU A (ℓ k) (hℓ k) (fun j => hinj j k)
    (fun j j' h => horth j j' k h)
  -- The window unitary `W : |dig₀ j, 0⟩ ↦ |ω_j⟩`.
  let enc : (j : Fin b) → Cfg d (r₁ + r₁) → ℂ := fun j =>
    Function.extend (fun p : Fin (Dj j) × Fin (Dj j) =>
      twoCfg dig (flatCoord Dj j p.1) (flatCoord Dj j p.2)) (ω j) 0
  have hencinj : ∀ j, Function.Injective (fun p : Fin (Dj j) × Fin (Dj j) =>
      twoCfg dig (flatCoord Dj j p.1) (flatCoord Dj j p.2)) := fun j p p' h => by
    obtain ⟨h1, h2⟩ := twoCfg_injective hdig h
    exact Prod.ext (flatCoord_injective j h1) (flatCoord_injective j h2)
  obtain ⟨W, hWu, hW⟩ : ∃ W ∈ unitary (Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ),
      ∀ u j, W u (windowInput (dig₀ j)) = enc j u := by
    let V : Matrix (Cfg d (r₁ + r₁)) (Fin b) ℂ := Matrix.of fun u j => enc j u
    have hV : V.IsIsometry := by
      ext j j'
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [conjTranspose_apply, V, Matrix.of_apply]
      rw [sum_extend_zero (hencinj j) (ω j) (fun u a => star a * enc j' u) (by simp)]
      by_cases hjj : j = j'
      · subst hjj
        simp only [enc, (hencinj j).extend_apply]
        rw [hω j]
        simp
      · rw [ite_eq_right hjj]
        refine Finset.sum_eq_zero fun p _ => ?_
        have hne : ¬∃ p' : Fin (Dj j') × Fin (Dj j'),
            twoCfg dig (flatCoord Dj j' p'.1) (flatCoord Dj j' p'.2) =
              twoCfg dig (flatCoord Dj j p.1) (flatCoord Dj j p.2) := fun ⟨p', hp'⟩ =>
          flatCoord_ne (Ne.symm hjj) p'.1 p.1 (twoCfg_injective hdig hp').1
        simp only [enc]
        rw [Function.extend_apply' _ _ _ hne, Pi.zero_apply, mul_zero]
    let emb : Fin b ↪ Cfg d (r₁ + r₁) :=
      ⟨fun j => windowInput (dig₀ j), windowInput_injective.comp hdig₀⟩
    obtain ⟨W, hW, hWV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
    exact ⟨W, hW, fun u j => hWV u j⟩
  -- The circuit after the measurement.
  have hcirc : IsCircuitOn Set.univ (KW + CU * L)
      (blockLayerOp hN U * pairLayerOp hN hr fun _ => W) :=
    (isCircuitOn_pairLayerOp hN hr fun _ => hKW W hWu).mul
      (isCircuitOn_blockLayerOp hN (K := CU * L) fun k =>
        (hUpp k).mono (Nat.mul_le_mul_left CU (hL k)))
  refine ⟨CG * L, KW + CU * L, windowGHZState hN hr α',
    blockLayerOp hN U * pairLayerOp hN hr (fun _ => W),
    by nlinarith, hφ, hcirc.isBondCircuitOfDepth, ?_⟩
  -- The circuit takes each configuration of the GHZ-type state to the state of its block.
  have hj : ∀ j, (blockLayerOp hN U * pairLayerOp hN hr fun _ => W) *ᵥ
      Pi.single (registerCfg hN hr (dig₀ j)) 1 = fun s => blockIsometryState (A j) (ω j) hN s := by
    intro j
    obtain ⟨Wj, -, hWj⟩ := exists_pairUnitary hd (hdig.comp (flatCoord_injective (Dj := Dj) j))
      (ω j) (hω j)
    funext s
    rw [blockIsometryState_eq_mulVec hd hN hr (hdig.comp (flatCoord_injective (Dj := Dj) j))
      (A j) (ω j) (U := U) (fun k l r τ => hU k j l r τ) (W := Wj) hWj s,
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
      rfl
    rw [key]
  rw [windowGHZState_extend hN hr hdig₀ α]
  have hsum : (fun x => ∑ j, α j * if x = registerCfg hN hr (dig₀ j) then (1 : ℂ) else 0) =
      ∑ j, α j • Pi.single (registerCfg hN hr (dig₀ j)) (1 : ℂ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum, mulVec_sum]
  funext s
  simp only [mulVec_smul, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **The fixed-point state of orthogonal blocks with measurements.** For every family of bond
dimensions `D_j` there are `C` and `L₀` such that for all tensors `A_j`, unit pair vectors `ω_j`,
unit amplitudes `α`, and every cutting of a chain into `M ≥ 1` blocks of lengths
`L₀ ≤ ℓ_k ≤ L` at which every blocked tensor is injective and the physical matrices of distinct
blocks are orthogonal, the state `∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` is prepared with
measurements and a circuit in depth at most `C L`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements". The labels of the blocks and the
bond indices are encoded in `r₁ = b + ∑ⱼ Dⱼ + 2` sites; for `d = 1` such encodings exist because
the hypotheses force `∑ⱼ Dⱼ² ≤ 1` (`MPSPreparation.sum_mul_self_le_pow`). -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_sum_blockIsometryState
    (b : ℕ) (Dj : Fin b → ℕ) :
    ∃ C L₀ : ℕ, ∀ (A : (j : Fin b) → MPSTensor d (Dj j))
      (ω : (j : Fin b) → Fin (Dj j) × Fin (Dj j) → ℂ), (∀ j, ∑ p, star (ω j p) * ω j p = 1) →
      ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        (∀ k, L₀ ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
        (∀ j k, Kraus.IsInjective (blockTensor (A j) (ℓ k))) →
        (∀ j j' k, j ≠ j' → (physicalMatrix (blockTensor (A j) (ℓ k)))ᴴ *
          physicalMatrix (blockTensor (A j') (ℓ k)) = 0) →
        IsPreparedWithMeasurementsAndCircuitInDepth (C * L)
          (fun s => ∑ j, α j * blockIsometryState (A j) (ω j) hN s) := by
  classical
  set r₁ := b + ∑ j, Dj j + 2 with hr₁
  have hcard : ∀ n, Fintype.card (Fin n) ≤ d ^ r₁ → Nonempty (Fin n ↪ Cfg d r₁) := fun n h =>
    Function.Embedding.nonempty_of_card_le (by simpa using h)
  -- Every block has a positive bond dimension, and there is a block.
  have hpos : ∀ (ω : (j : Fin b) → Fin (Dj j) × Fin (Dj j) → ℂ),
      (∀ j, ∑ p, star (ω j p) * ω j p = 1) → ∀ j, 0 < Dj j := fun ω hω j => by
    by_contra h
    have h0 : Dj j = 0 := by omega
    have := hω j
    have hE : IsEmpty (Fin (Dj j) × Fin (Dj j)) := by rw [h0]; infer_instance
    simp at this
  have hb : ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 → 0 < b := fun α hα => by
    by_contra h
    obtain rfl : b = 0 := by omega
    simp at hα
  by_cases henc : b ≤ d ^ r₁ ∧ ∑ j, Dj j ≤ d ^ r₁
  · by_cases hD : 0 < ∑ j, Dj j
    · obtain ⟨dig⟩ := hcard _ (by simpa using henc.2)
      obtain ⟨dig₀⟩ := hcard _ (by simpa using henc.1)
      obtain ⟨C, hC⟩ :=
        exists_isPreparedWithMeasurementsAndCircuitInDepth_sum_blockIsometryState_of_encoding
          (Dj := Dj) (r₁ := r₁) (by omega) dig.injective dig₀.injective hD
      exact ⟨C, 3 * r₁, fun A ω hω α hα M _ ℓ N _ hN L hℓ hL hinj horth =>
        hC A ω hω α hα ℓ hN L hℓ hL hinj horth⟩
    · refine ⟨0, 0, fun A ω hω α hα _ _ _ _ _ _ _ _ _ _ _ => ?_⟩
      have := hpos ω hω ⟨0, hb α hα⟩
      exact absurd (lt_of_lt_of_le this (Finset.single_le_sum (fun j _ => Nat.zero_le (Dj j))
        (Finset.mem_univ _))) hD
  · refine ⟨0, 0, fun A ω hω α hα M _ ℓ N _ hN L _ _ hinj horth => ?_⟩
    exfalso
    apply henc
    have hd1 : d = 1 := by
      by_contra hd
      have hd2 : 2 ≤ d := by have := NeZero.ne d; omega
      have h2 : r₁ < d ^ r₁ := (Nat.lt_pow_self (by omega)).trans_le le_rfl
      exact henc ⟨by omega, by omega⟩
    subst hd1
    have h := sum_mul_self_le_pow A (q := ℓ 0) (fun j => hinj j 0) (fun j j' h => horth j j' 0 h)
    rw [one_pow] at h
    have hsq : ∑ j, Dj j ≤ ∑ j, Dj j * Dj j :=
      Finset.sum_le_sum fun j _ => Nat.le_mul_of_pos_left _ (hpos ω hω j)
    have hcount : b ≤ ∑ j, Dj j := by
      calc b = ∑ _j : Fin b, 1 := by simp
        _ ≤ ∑ j, Dj j := Finset.sum_le_sum fun j _ => hpos ω hω j
    rw [one_pow]
    omega

end Preparation

end MPSPreparation
