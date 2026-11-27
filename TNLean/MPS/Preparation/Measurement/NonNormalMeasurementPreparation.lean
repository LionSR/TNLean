/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockSum.SectorSpectralGap
import TNLean.MPS.Preparation.Normal.DepthLogBound
import TNLean.MPS.Preparation.BlockSum.BlockSumError
import TNLean.MPS.Preparation.BlockSum.BlockSumUnitary
import TNLean.MPS.Preparation.Circuit.GHZSeedRegisters

/-!
# Tensors that are not normal, prepared with measurements in depth `O(log(N/ε))`

arXiv:2307.01696, paragraph "Long-range MPS using measurements", prepares every
translation-invariant MPS, "short- or long-range correlated", with measurements: the GHZ-type
state `|χ_{N/q}⟩` is created in constant depth with measurements, the isometries
`W : |j⟩ ↦ |ω_j⟩` and the isometries of the blocked tensor follow as circuits, and with the
block length `q ∝ log(N/ε)` "If instead measurements are only used for the preparation of
`|χ_{N/q}⟩`, the depth is `O(log(N/ε))`."

This file proves this for a direct sum `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` of normal
blocks (eq. (S2)), with the corrected approximating state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` of `TNLean.MPS.Preparation.RepeatedBlockSum`:

* it is prepared with measurements and a circuit in depth `O(q)`
  (`MPSPreparation.exists_isOneRoundConversion_copyApproxVector`), as the
  state `∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩` of the blocks (`MPSPreparation.copyApproxVector_eq_sum`);
* with its error bound (`MPSTensor.exists_approximationError_le_mul_repeatedBlockSum`), a unit
  vector with error at most `ε` is prepared with measurements in depth `O(log(N/ε))`
  (`MPSPreparation.exists_isOneRoundConversion_le_log_repeatedBlockSum`).

Both scope restrictions below are removed, for blocks whose states may overlap and for every
chain length, by
`MPSPreparation.exists_isOneRoundConversion_le_log_of_mpvState_ne_zero`,
which prepares a different approximating state.

**Scope restriction (orthogonal blocks):** both results take, at the block length `q`, the
orthogonality `B_jᴴ B_{j'} = 0` of the `q`-site states of distinct blocks, which the source does
not assume. Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Scope restriction (block length dividing the chain length):** the depth bound
`O(log(N/ε))` is proved for block lengths `q` dividing `N`, the `N/q` equal blocks of eq. (10);
the source lets the last block be larger. The error bound for orthogonal blocks with
multiplicities is proved for equal blocks only. Documented in
`docs/paper-gaps/mswc24_measurement_preparation_scope.tex`.

**Local fix (corrected fixed-point state):** the state prepared is the corrected state of
`TNLean.MPS.Preparation.RepeatedBlockSum`, not the state of eq. (S7), which fails for blocks of
multiplicity `m_j ≥ 2`. Documented in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

## Main declarations

* `MPSPreparation.copyApproxVector_eq_sum` — the corrected approximating state is
  `∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩`.
* `MPSPreparation.sum_norm_sq_copyApproxVector` — it is a unit vector.
* `MPSPreparation.exists_isOneRoundConversion_copyApproxVector` — depth
  `O(q)` with measurements.
* `MPSPreparation.exists_isOneRoundConversion_le_log_repeatedBlockSum` —
  error `ε` in depth `O(log(N/ε))` with measurements.
* `MPSPreparation.exists_isOneRoundConversion_sum_blockIsometryState_of_encoding`,
  `MPSPreparation.exists_isOneRoundConversion_sum_blockIsometryState`: fixed points of tensors that
  are not normal, prepared with measurements.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, paragraph "Long-range MPS using measurements", eq. (19), and Supplemental
  Material, eqs. (S2)–(S7) and Lemma 1'(ii).
-/

open MPTensor

open Matrix MPSTensor

section MeasurementPreparation

/-!
## Fixed points of tensors that are not normal, prepared with measurements

arXiv:2307.01696, paragraph "Long-range MPS using measurements", prepares the fixed-point state
of a translation-invariant MPS that is not normal as `|Ω'⟩ = W^{⊗N/q} |χ_{N/q}⟩`: "First create
`|χ_{N/q}⟩`, which can be done in constant depth with measurements (following, e.g.,
Ref~\cite{Piroli2021}). Subsequently, apply in parallel the isometries
`W : |j⟩ ↦ |ω_j⟩_{R_i L_{i+1}}` such that `|Ω'⟩ = W^{⊗N/q} |χ_{N/q}⟩`, which also takes constant
depth." The isometries `V` of the blocked tensor then follow, "following the same steps as in the
tree-RG circuit". The circuit applied after the measurement does not depend on its outcomes.

This file proves this two-stage preparation, one round of measurements followed by a unitary
circuit (`QuantumCircuit.IsOneRoundConversion` of `QICLean.Circuit.Model.Measurement`, from a
product vector), for the state
`∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` of a family of tensors
`A_j` whose blocked tensors are injective and have orthogonal ranges
(`MPSPreparation.exists_isOneRoundConversion_sum_blockIsometryState`), in
depth `O(L)` for blocks of lengths at most `L`:

* the GHZ-type state on the registers (`MPSPreparation.windowGHZState`), with measurements, in
  depth `O(L)` (`MPSPreparation.exists_isOneRoundConversion_windowGHZState`);
* on every pair window, one unitary sending the register value `j` to the pair `ω_j` of block `j`,
  placed on the bond indices of block `j` (the isometry `W` of the source);
* on every block, one unitary implementing all the isometries `V_{j,k}` at once
  (`MPSPreparation.exists_blockSumUnitary`), of depth `O(L)`.

**Scope restriction (orthogonal blocks):** both preparation theorems of this file, with and
without a given encoding of the labels, take the orthogonality `B_jᴴ B_{j'} = 0` of the blocked
states of distinct tensors, which the source does not assume; the block unitary implements the
isometry of the blocked direct sum only under it. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

### Main declarations

* `MPSPreparation.exists_isOneRoundConversion_sum_blockIsometryState` —
  the preparation in depth `O(L)`.

### References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Long-range MPS using
  measurements", eq. (19), and the paragraph after it.
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), paragraph "State transformations with QC and LOCC"
  and Example 1.
-/

open scoped BigOperators
open QuantumCircuit
open Kraus (blockTensor)

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
theorem exists_isOneRoundConversion_sum_blockIsometryState_of_encoding
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
        ∃ T₁ T₂, T₁ + T₂ ≤ C * L ∧ ∃ v : Fin N → Fin d → ℂ,
          IsOneRoundConversion (Geometry.ring N) T₁ T₂ (fun σ ↦ ∏ s, v s (σ s))
            (fun s => ∑ j, α j * blockIsometryState (A j) (ω j) hN s) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have h0 : (⟨0, hd⟩ : Fin d) = 0 := Fin.ext (by simp)
  obtain ⟨CG, hCG⟩ := exists_isOneRoundConversion_windowGHZState (d := d) hr₁
  obtain ⟨CU, hCU⟩ := exists_blockSumUnitary (Dj := Dj) hd (by omega) hdig hD
  have : NeZero (r₁ + r₁) := ⟨by omega⟩
  obtain ⟨KW, hKW⟩ : ∃ KW, ∀ X : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ,
      X ∈ unitary (Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ) →
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (r₁ + r₁))) KW X :=
    ⟨_, fun X hX ↦ isGateProduct_pathGraph_unitaryGateCount hX⟩
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
  have hcirc : IsUnitaryCircuitOn (Geometry.ring N) Finset.univ (CU * L + KW)
      (blockLayerOp hN U * pairLayerOp hN hr fun _ => W) :=
    (isUnitaryCircuitOn_blockLayerOp hN (K := CU * L) fun k =>
        (hUpp k).mono (Nat.mul_le_mul_left CU (hL k))).mul
      (isUnitaryCircuitOn_pairLayerOp hN hr fun _ => hKW W hWu)
  obtain ⟨v, hv⟩ := hφ
  refine ⟨CG * L, CU * L + KW, by nlinarith, v, ?_⟩
  suffices hψ : (fun s => ∑ j, α j * blockIsometryState (A j) (ω j) hN s) =
      (blockLayerOp hN U * pairLayerOp hN hr fun _ => W) *ᵥ windowGHZState hN hr α' by
    have h := hv.mulVec hcirc.isUnitaryCircuit
    rwa [zero_add, ← hψ] at h
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
        pairLayerOp hN hr (fun _ => Wj) *ᵥ
          fun σ : Cfg d N => ∏ i, (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℂ) : Fin d → ℂ) (σ i) := by
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
theorem exists_isOneRoundConversion_sum_blockIsometryState
    (b : ℕ) (Dj : Fin b → ℕ) :
    ∃ C L₀ : ℕ, ∀ (A : (j : Fin b) → MPSTensor d (Dj j))
      (ω : (j : Fin b) → Fin (Dj j) × Fin (Dj j) → ℂ), (∀ j, ∑ p, star (ω j p) * ω j p = 1) →
      ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        (∀ k, L₀ ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
        (∀ j k, Kraus.IsInjective (blockTensor (A j) (ℓ k))) →
        (∀ j j' k, j ≠ j' → (physicalMatrix (blockTensor (A j) (ℓ k)))ᴴ *
          physicalMatrix (blockTensor (A j') (ℓ k)) = 0) →
        ∃ T₁ T₂, T₁ + T₂ ≤ C * L ∧ ∃ v : Fin N → Fin d → ℂ,
          IsOneRoundConversion (Geometry.ring N) T₁ T₂ (fun σ ↦ ∏ s, v s (σ s))
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
        exists_isOneRoundConversion_sum_blockIsometryState_of_encoding
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

end MeasurementPreparation

section NonNormalMeasurementPreparation

open scoped BigOperators ComplexOrder InnerProductSpace
open QuantumCircuit
open Kraus (blockPhysDim blockPhysDim_eq_pow blockTensor
  isNBlkInjective_iff_blockTensor_isInjective)

namespace MPSPreparation

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}
  {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- **The corrected approximating state as a sum over the blocks.** For blocks with nonzero
weights whose `q`-site blocked tensors are injective and have orthogonal physical matrices,
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`, read on the chain of `M q` sites, is
`∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` with `ω_j` the pair of the fixed point `σ_j`.

arXiv:2307.01696, eq. (10) for each block and Supplemental Material, eq. (S7), corrected as in
`TNLean.MPS.Preparation.RepeatedBlockSum`. -/
theorem copyApproxVector_eq_sum (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : CopyWeights b m} {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1) {q : ℕ} (hq : q ≠ 0)
    (hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q))
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) (M : ℕ) [NeZero M] (α : Fin b → ℂ)
    (hN : ∑ _ : Fin M, q = M * q) (s : Cfg d (M * q)) :
    copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ
        ((blockedConfigEquiv d M q).symm s) =
      ∑ j, α j * blockIsometryState (Aj j) (fixedPointPair (σ j)) hN s := by
  rw [copyApproxVector_repeatedBlockSum hι hdisj hq horth σ M α]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrArg (fun v : MPVSpace d (M * q) => v s)
    (approximatingMPVState_eq_blockIsometryState (Aj j) (hB j) (hσ j) (htr j) M hN)
  simp only [(inner_approximatingMPVState_mpvState (Aj j) (hB j) (hσ j) (htr j) M).1,
    approximatingMPVStateRaw_apply] at h
  rw [h]

/-- **The corrected approximating state is a unit vector** for unit amplitudes `α`, blocks with
injective blocked tensors and orthogonal physical matrices: the approximating states of the
blocks are orthonormal. -/
theorem sum_norm_sq_copyApproxVector (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : CopyWeights b m} {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1) {q : ℕ} (hq : q ≠ 0)
    (hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q))
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) (M : ℕ) [NeZero M] {α : Fin b → ℂ}
    (hα : ∑ j, star (α j) * α j = 1) :
    ∑ τ, ‖copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ τ‖ ^ 2 = 1 := by
  have : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  set s : (j : Fin b) → (Fin M → Fin (blockPhysDim d q)) → ℂ :=
    fun j τ => mpv (approximatingTensor (blockTensor (Aj j) q) (σ j)) τ
  have hss : ∀ j j', ∑ τ, star (s j τ) * s j' τ = if j = j' then 1 else 0 := fun j j' => by
    split_ifs with h
    · subst h; exact mpv_approximatingTensor_norm_sq (hB j) (hσ j) (htr j)
    · have := mpvOverlap_eq_zero (X := approximatingTensor (blockTensor (Aj j') q) (σ j'))
        (Y := approximatingTensor (blockTensor (Aj j) q) (σ j))
        (conjTranspose_physicalMatrix_approximatingTensor_mul (horth j j' h) _ _)
        (NeZero.ne M)
      rw [mpvOverlap] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
  have h := ofReal_sum_norm_sq fun τ =>
    copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ τ
  simp only [copyApproxVector_repeatedBlockSum hι hdisj hq horth σ M α] at h
  rw [sum_star_sum_mul_sum_of_orthogonal _ _ (fun _ => 1) s s hss] at h
  simp only [mul_one, hα] at h
  simp only [copyApproxVector_repeatedBlockSum hι hdisj hq horth σ M α]
  exact_mod_cast h

/-- **The corrected approximating state in depth `O(q)` with measurements.** There are `C` and
`L₀`, depending only on `d`, the number of blocks `b` and their bond dimensions `D_j`, such that
for every direct sum `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` with nonzero weights, all
`σ_j ≥ 0` with `Tr σ_j = 1`, every block length `q ≥ L₀` at which every blocked tensor of the
blocks is injective and the physical matrices of distinct blocks are orthogonal, every number of
blocks `M ≥ 1` and all unit amplitudes `α`, the corrected approximating state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` on `N = M q` sites is prepared with measurements and a circuit in
depth at most `C q`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements" ("First create `|χ_{N/q}⟩`, which
can be done in constant depth with measurements ... Subsequently, apply in parallel the
isometries `W`"), followed by the isometries of the blocked tensor, in the scope of the module
docstring. -/
theorem exists_isOneRoundConversion_copyApproxVector (d b : ℕ)
    (Dj : Fin b → ℕ) :
    ∃ C L₀ : ℕ, ∀ {D : ℕ} {m : Fin b → ℕ} (Aj : (j : Fin b) → MPSTensor d (Dj j))
      (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D), (∀ j k, Function.Injective (ι j k)) →
      (∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a') →
      ∀ (μ : CopyWeights b m) (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ),
      (∀ j, (σ j).PosSemidef) → (∀ j, (σ j).trace = 1) →
      ∀ q, L₀ ≤ q → (∀ j, Kraus.IsInjective (blockTensor (Aj j) q)) →
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      ∀ (M : ℕ) [NeZero (M * q)] (α : Fin b → ℂ), ∑ j, star (α j) * α j = 1 →
        ∃ T₁ T₂, T₁ + T₂ ≤ C * q ∧ ∃ v : Fin (M * q) → Fin d → ℂ,
          IsOneRoundConversion (Geometry.ring (M * q)) T₁ T₂ (fun x ↦ ∏ i, v i (x i)) fun s =>
            copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ
              ((blockedConfigEquiv d M q).symm s) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- No physical states: the hypotheses are contradictory.
    refine ⟨0, 1, fun Aj ι _ _ μ σ _ htr q hq hB _ M _ α hα => ?_⟩
    exfalso
    have hb : 0 < b := by
      by_contra h
      obtain rfl : b = 0 := by omega
      simp at hα
    have hD := Matrix.neZero_of_trace_eq_one (htr ⟨0, hb⟩)
    have : IsEmpty (Fin (blockPhysDim 0 q)) := by
      rw [blockPhysDim_eq_pow, zero_pow (by omega)]; infer_instance
    have h := hB ⟨0, hb⟩
    rw [Kraus.IsInjective, Set.range_eq_empty, Submodule.span_empty] at h
    have h1 : (1 : Matrix (Fin (Dj ⟨0, hb⟩)) (Fin (Dj ⟨0, hb⟩)) ℂ) ∈ (⊥ : Submodule ℂ _) :=
      h ▸ Submodule.mem_top
    exact one_ne_zero ((Submodule.mem_bot ℂ).1 h1)
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨C, L₀, hC⟩ := exists_isOneRoundConversion_sum_blockIsometryState
    (d := d) b Dj
  refine ⟨C, max L₀ 1, fun Aj ι hι hdisj μ σ hσ htr q hq hB horth M _ α hα => ?_⟩
  have hq0 : q ≠ 0 := by have := le_max_right L₀ 1; omega
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hNq : ∑ _ : Fin M, q = M * q := by simp
  have key := hC Aj (fun j => fixedPointPair (σ j))
    (fun j => by rw [fixedPointPair_norm_sq (hσ j), htr j]) α hα (fun _ => q) hNq q
    (fun _ => le_of_max_le_left hq) (fun _ => le_rfl) (fun j _ => hB j)
    (fun j j' _ h => horth j j' h)
  obtain ⟨T₁, T₂, hT, v, hv⟩ := key
  refine ⟨T₁, T₂, hT, v, ?_⟩
  convert hv using 1
  funext s
  exact copyApproxVector_eq_sum hι hdisj hσ htr hq0 hB horth M α hNq s

/-! ### Error `ε` in depth `O(log(N/ε))` -/

/-- **Tensors that are not normal, with measurements, in depth `O(log(N/ε))`.** Let
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (arXiv:2307.01696, Supplemental Material,
eq. (S2)) with nonzero weights, every block `A_j` normal in the gauge of eq. (5):
`∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`. There are `a > 0`,
`b' ≥ 1` and `c`, depending only on `A`, with the following property. For `N ≥ 2`, `0 < ε ≤ 1`,
and a block length `q` dividing `N` with `a log(N/ε) + b' ≤ q ≤ 2 (a log(N/ε) + b')`, at which
the `q`-site states of distinct blocks are orthogonal, and with the weights
`βⱼ = ∑ₖ μ_{j,k}^N` not all zero, some unit vector `|ψ⟩` with `1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared
with measurements and a circuit in depth at most `c log(N/ε)`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements": "If instead measurements are
only used for the preparation of `|χ_{N/q}⟩`, the depth is `O(log(N/ε))`", for the corrected
approximating state and in the scope of the module docstring (orthogonal blocks, block length
dividing `N`). The vector `|ψ⟩` is the corrected approximating state
`V^{⊗N/q} ∑ⱼ αⱼ L_j^{⊗N/q} |Ω_j⟩`, prepared in depth `O(q)`
(`exists_isOneRoundConversion_copyApproxVector`), with the error bound of
Lemma 1'(ii) (`MPSTensor.exists_approximationError_le_mul_repeatedBlockSum`). -/
theorem exists_isOneRoundConversion_le_log_repeatedBlockSum [NeZero b]
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j) :
    ∃ a b' c : ℝ, 0 < a ∧ 1 ≤ b' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (N q : ℕ) [NeZero N], 2 ≤ N → q ∣ N → a * Real.log (N / ε) + b' ≤ q →
        (q : ℝ) ≤ 2 * (a * Real.log (N / ε) + b') →
        (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
          physicalMatrix (blockTensor (Aj j') q) = 0) →
        bntWeight μ N ≠ 0 →
        ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
          (∃ T₁ T₂, T₁ + T₂ ≤ T ∧ ∃ v : Fin N → Fin d → ℂ,
            IsOneRoundConversion (Geometry.ring N) T₁ T₂ (fun x ↦ ∏ i, v i (x i))
              (fun s => ψ s)) ∧
          1 - ‖⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) N⟫_ℂ‖ ≤ ε := by
  classical
  have hDj : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  obtain ⟨t, ht0, ht1, hlam⟩ := exists_forall_eigenvalue_norm_le hN hA hDj
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨K, hK, herr⟩ := exists_approximationError_le_mul_repeatedBlockSum hι hdisj hN
    hA hσ htr hfix (lam₂ := (t : ℂ)) hlam (γ := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨Cp, L₀, hCp⟩ := exists_isOneRoundConversion_copyApproxVector d b Dj
  choose Linj hLpos hLinj using hN
  set Lm : ℕ := ∑ j, Linj j
  set r := -(1 / 4 * Real.log t) with hr
  have hr0 : 0 < r := by
    have := Real.log_neg ht0 ht1
    rw [hr]; linarith
  have hexp : ∀ q : ℕ, Real.exp (-(1 / 4) * q / correlationLength (t : ℂ)) =
      Real.exp (-(r * q)) := fun q => by
    congr 1
    rw [mul_div_right_comm, neg_div_correlationLength, hnorm, hr]
    ring
  set a := 1 / r with ha
  have ha0 : 0 < a := by positivity
  set b' : ℝ := a * max (Real.log K) 0 + L₀ + Lm + 1 with hb'
  have hmax : 0 ≤ a * max (Real.log K) 0 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb1 : 1 ≤ b' := by
    have : (0 : ℝ) ≤ L₀ + Lm := by positivity
    linarith
  refine ⟨a, b', Cp * (2 * a + 2 * b' / Real.log 2), ha0, hb1,
    fun ε hε hε1 N q _ hN2 hqN hq hq2 horth hβ => ?_⟩
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2'.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 ≤ Real.log (N / ε) := hl2.le.trans hlog
  have hbq : b' ≤ q := by
    have : 0 ≤ a * Real.log (N / ε) := by positivity
    linarith
  have hLq : L₀ ≤ q := by
    have : (L₀ : ℝ) ≤ q := by have : (0 : ℝ) ≤ Lm := by positivity
                              linarith
    exact_mod_cast this
  have hLmq : ∀ j, Linj j ≤ q := fun j => by
    have h1 : Linj j ≤ Lm := Finset.single_le_sum (f := Linj) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    have h2 : (Lm : ℝ) ≤ q := by have : (0 : ℝ) ≤ L₀ := by positivity
                                 linarith
    have : Lm ≤ q := by exact_mod_cast h2
    omega
  have hq1 : (1 : ℝ) ≤ q := hb1.trans hbq
  obtain ⟨M, hM⟩ := hqN
  rw [mul_comm] at hM
  subst hM
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q) := fun j =>
    (isNBlkInjective_iff_blockTensor_isInjective (Aj j) q).1
      (isNBlkInjective_of_le (hLpos j) (hLinj j) (hLmq j))
  have hq0 : q ≠ 0 := by
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this.ne'
  set α := ghzAmplitude (bntWeight μ (M * q))
  have hα : ∑ j, star (α j) * α j = 1 := ghzAmplitude_norm_sq hβ
  have hprep := hCp Aj ι hι hdisj μ σ (fun j => (hσ j).posSemidef) htr q hLq hB horth M α hα
  set v : Cfg d (M * q) → ℂ := fun s => copyApproxVector (repeatedBlockSum Aj ι μ) q M α
    (copyIsometry ι μ q) σ ((blockedConfigEquiv d M q).symm s) with hv
  set ψ : MPVSpace d (M * q) := (EuclideanSpace.equiv (ι := Cfg d (M * q)) (𝕜 := ℂ)).symm v
  have hψ : (fun s => ψ s) = v := funext fun s => by
    simp [ψ, PiLp.toLp_apply]
  have hsq := sum_norm_sq_copyApproxVector hι hdisj (μ := μ) (fun j => (hσ j).posSemidef) htr
    hq0 hB horth M hα
  have hψn : ‖ψ‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : ∑ s, ‖ψ s‖ ^ 2 = 1 := by
      rw [← hsq, ← (blockedConfigEquiv d M q).sum_comp]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [show ψ (blockedConfigEquiv d M q τ) = v (blockedConfigEquiv d M q τ) from
        congrFun hψ _, hv]
      simp only [Equiv.symm_apply_apply]
    rw [this, Real.sqrt_one]
  have hinner : ⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) (M * q)⟫_ℂ =
      copyApproxOverlap (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ := by
    rw [copyApproxOverlap, hsq, Real.sqrt_one, Complex.ofReal_one, inv_one, PiLp.inner_apply,
      ← (blockedConfigEquiv d M q).sum_comp]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [RCLike.inner_apply, one_mul, show ψ (blockedConfigEquiv d M q τ) =
      v (blockedConfigEquiv d M q τ) from congrFun hψ _, hv]
    simp only [Equiv.symm_apply_apply]
    rw [mul_comm]
    rfl
  refine ⟨ψ, Cp * q, hψn, ?_, by rw [hψ]; exact hprep, ?_⟩
  · exact natCast_mul_le_mul_log_of_le_two_mul hN2 hε hε1 hb1 hq2
  · rw [hinner]
    refine (herr μ q M horth hβ).trans ?_
    rw [hexp]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
    rw [show r * (q : ℝ) = q / a by rw [ha, div_div_eq_mul_div, div_one, mul_comm]]
    push_cast at hq
    have : (0 : ℝ) ≤ L₀ + Lm + 1 := by positivity
    exact mul_mul_exp_neg_div_le_of_le hK hM1 hq1 ha0 hε (by linarith) hq

end MPSPreparation

end NonNormalMeasurementPreparation
