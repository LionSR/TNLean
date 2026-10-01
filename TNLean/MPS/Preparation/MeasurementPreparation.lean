/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockSumUnitary
import TNLean.MPS.Preparation.WindowGHZ

/-!
# Fixed points of tensors that are not normal, prepared with measurements

arXiv:2307.01696, paragraph "Long-range MPS using measurements", prepares the fixed-point state
of a translation-invariant MPS that is not normal as `|Ω'⟩ = W^{⊗N/q} |χ_{N/q}⟩`: "First create
`|χ_{N/q}⟩`, which can be done in constant depth with measurements (following, e.g.,
Ref~\cite{Piroli2021}). Subsequently, apply in parallel the isometries
`W : |j⟩ ↦ |ω_j⟩_{R_i L_{i+1}}` such that `|Ω'⟩ = W^{⊗N/q} |χ_{N/q}⟩`, which also takes constant
depth." The isometries `V` of the blocked tensor then follow, "following the same steps as in the
tree-RG circuit". The circuit applied after the measurement does not depend on its outcomes.

This file defines this two-stage preparation (`MPSPreparation.IsPreparedWithMeasurementsAndCircuitInDepth`)
and proves it for the state `∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` of a family of tensors
`A_j` whose blocked tensors are injective and have orthogonal ranges
(`MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_sum_blockIsometryState`), in
depth `O(L)` for blocks of lengths at most `L`:

* the GHZ-type state on the registers (`MPSPreparation.windowGHZState`), with measurements, in
  depth `O(L)` (`MPSPreparation.exists_isPreparedWithMeasurementsInDepth_windowGHZState`);
* on every pair window, one unitary sending the register value `j` to the pair `ω_j` of block `j`,
  placed on the bond indices of block `j` (the isometry `W` of the source);
* on every block, one unitary implementing all the isometries `V_{j,k}` at once
  (`MPSPreparation.exists_blockSumUnitary`), of depth `O(L)`.

## Main declarations

* `MPSPreparation.IsPreparedWithMeasurementsAndCircuitInDepth` — a state prepared with
  measurements in depth `T₁`, followed by a local circuit of depth `T₂`, with `T₁ + T₂ ≤ T`.
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

namespace MPSPreparation

variable {d N : ℕ}

/-! ### Preparation with measurements followed by a circuit -/

section TwoStage

variable [NeZero N]

/-- A vector `ψ` is *prepared with measurements and a circuit in depth `T`* when `ψ = U φ` for a
vector `φ` prepared with measurements in depth `T₁` and a local circuit `U` of depth `T₂`, with
`T₁ + T₂ ≤ T`. The circuit `U` is applied after the measurement and its corrections, and does not
depend on the outcomes.

Source: arXiv:2307.01696, paragraph "Long-range MPS using measurements" ("First create
`|χ_{N/q}⟩`, which can be done in constant depth with measurements ... Subsequently, apply in
parallel the isometries `W`"); arXiv:2103.13367, paragraph "State transformations with QC and
LOCC", where a protocol is followed by further operations in "a more general scheme with
multiple rounds of LOCC". -/
def IsPreparedWithMeasurementsAndCircuitInDepth (T : ℕ) (ψ : Cfg d N → ℂ) : Prop :=
  ∃ (T₁ T₂ : ℕ) (φ : Cfg d N → ℂ) (U : Matrix (Cfg d N) (Cfg d N) ℂ), T₁ + T₂ ≤ T ∧
    IsPreparedWithMeasurementsInDepth T₁ φ ∧ IsLocalCircuitOfDepth U T₂ ∧ ψ = U *ᵥ φ

theorem IsPreparedWithMeasurementsAndCircuitInDepth.mono {T T' : ℕ} {ψ : Cfg d N → ℂ}
    (h : IsPreparedWithMeasurementsAndCircuitInDepth T ψ) (hT : T ≤ T') :
    IsPreparedWithMeasurementsAndCircuitInDepth T' ψ := by
  obtain ⟨T₁, T₂, φ, U, hT', hφ, hU, rfl⟩ := h
  exact ⟨T₁, T₂, φ, U, hT'.trans hT, hφ, hU, rfl⟩

/-- A nonzero multiple of a vector prepared with measurements is prepared with measurements by the
same protocol. -/
theorem IsPreparedWithMeasurementsInDepth.smul {T : ℕ} {φ : Cfg d N → ℂ}
    (h : IsPreparedWithMeasurementsInDepth T φ) {c : ℂ} (hc : c ≠ 0) :
    IsPreparedWithMeasurementsInDepth T (c • φ) := by
  obtain ⟨P, hT, h0, hP⟩ := h
  refine ⟨P, hT, h0, fun m hm => ?_⟩
  obtain ⟨c', hc'⟩ := hP m hm
  exact ⟨c' * c⁻¹, by rw [hc', smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]⟩

/-- A nonzero multiple of a vector prepared with measurements and a circuit is prepared the same
way. -/
theorem IsPreparedWithMeasurementsAndCircuitInDepth.smul {T : ℕ} {ψ : Cfg d N → ℂ}
    (h : IsPreparedWithMeasurementsAndCircuitInDepth T ψ) {c : ℂ} (hc : c ≠ 0) :
    IsPreparedWithMeasurementsAndCircuitInDepth T (c • ψ) := by
  obtain ⟨T₁, T₂, φ, U, hT, hφ, hU, rfl⟩ := h
  exact ⟨T₁, T₂, c • φ, U, hT, hφ.smul hc, hU, by rw [mulVec_smul]⟩

end TwoStage

/-! ### The GHZ-type state as a sum of configurations -/

section Registers

variable {M r₁ b : ℕ} {ℓ : Fin M → ℕ} [NeZero d] (hN : ∑ k, ℓ k = N)
  (hr : ∀ k, r₁ + r₁ ≤ ℓ k)

/-- The configuration carrying `u` on every register `R_k` and `0` elsewhere. -/
noncomputable def registerCfg (u : Cfg d r₁) : Cfg d N :=
  Function.extend (fun q : Fin M × Fin r₁ => registerSite hN hr q.1 q.2) (fun q => u q.2) 0

theorem registerCfg_registerSite (u : Cfg d r₁) (k : Fin M) (i : Fin r₁) :
    registerCfg hN hr u (registerSite hN hr k i) = u i :=
  (show Function.Injective fun q : Fin M × Fin r₁ => registerSite hN hr q.1 q.2 from
    fun q q' h => Prod.ext ((registerSite_inj hN hr).1 h).1 ((registerSite_inj hN hr).1 h).2
    ).extend_apply _ _ (k, i)

theorem registerCfg_of_forall_ne (u : Cfg d r₁) {i : Fin N}
    (hi : ∀ k j, registerSite hN hr k j ≠ i) : registerCfg hN hr u i = 0 := by
  rw [registerCfg, Function.extend_apply' _ _ _ fun ⟨q, hq⟩ => hi q.1 q.2 hq]
  rfl

/-- The configuration of a pair window carrying `u` on its first `r₁` sites and `0` on the
others. -/
def windowInput (u : Cfg d r₁) : Cfg d (r₁ + r₁) := fun p =>
  if h : p.val < r₁ then u ⟨p.val, h⟩ else 0

theorem windowInput_injective : Function.Injective (windowInput (d := d) (r₁ := r₁)) :=
  fun u u' h => funext fun p => by
    have := congrFun h (Fin.castAdd r₁ p)
    simpa [windowInput] using this

theorem registerCfg_comp_pairSite (u : Cfg d r₁) (k : Fin M) :
    registerCfg hN hr u ∘ pairSite hN hr k = windowInput u := by
  funext p
  simp only [Function.comp_apply, windowInput]
  by_cases h : p.val < r₁
  · rw [dite_eq_left h, show pairSite hN hr k p = registerSite hN hr k ⟨p.val, h⟩ from
      congrArg _ (Fin.ext rfl), registerCfg_registerSite]
  · rw [dite_eq_right h, show pairSite hN hr k p = ancillaSite hN hr k ⟨p.val - r₁, by omega⟩
      from congrArg _ (Fin.ext (by simp; omega))]
    exact registerCfg_of_forall_ne hN hr u fun k' j' h' =>
      registerSite_ne_ancillaSite hN hr k' k j' _ h'

theorem registerCfg_of_forall_pairSite_ne (u : Cfg d r₁) {i : Fin N}
    (hi : ∀ k j, pairSite hN hr k j ≠ i) : registerCfg hN hr u i = 0 :=
  registerCfg_of_forall_ne hN hr u fun k j h => hi k (Fin.castAdd r₁ j) h

/-- **The GHZ-type state as a sum of configurations.** For labels `j` encoded injectively as
register configurations `dig₀ j`, the GHZ-type state of the amplitudes `αⱼ` is
`∑ⱼ αⱼ |dig₀ j, ⋯, dig₀ j⟩`, with every site outside the registers in `|0⟩`: the state
`|χ_M⟩ = ∑ⱼ αⱼ |j⟩^{⊗M}` of arXiv:2307.01696, paragraph "Long-range MPS using measurements". -/
theorem windowGHZState_extend [NeZero M] {dig₀ : Fin b → Cfg d r₁}
    (hdig₀ : Function.Injective dig₀) (α : Fin b → ℂ) :
    windowGHZState hN hr (Function.extend dig₀ α 0) =
      fun x => ∑ j, α j * if x = registerCfg hN hr (dig₀ j) then 1 else 0 := by
  classical
  funext x
  simp only [windowGHZState]
  by_cases hc : (∀ k, x ∘ registerSite hN hr k = x ∘ registerSite hN hr 0) ∧
      ∀ i, (∀ k j, registerSite hN hr k j ≠ i) → x i = 0
  · rw [ite_eq_left hc]
    have hx : x = registerCfg hN hr (x ∘ registerSite hN hr 0) := funext fun i => by
      by_cases hi : ∃ k p, registerSite hN hr k p = i
      · obtain ⟨k, p, rfl⟩ := hi
        rw [registerCfg_registerSite]
        exact congrFun (hc.1 k) p
      · push Not at hi
        rw [registerCfg_of_forall_ne hN hr _ hi, hc.2 i hi]
    have hiff : ∀ j, x = registerCfg hN hr (dig₀ j) ↔ x ∘ registerSite hN hr 0 = dig₀ j :=
      fun j => ⟨fun h => by
        rw [h]; funext p; simp only [Function.comp_apply, registerCfg_registerSite],
        fun h => by rw [hx, h]⟩
    simp only [hiff]
    by_cases hu : ∃ j, dig₀ j = x ∘ registerSite hN hr 0
    · obtain ⟨j, hj⟩ := hu
      rw [← hj, hdig₀.extend_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · simp
      · intro j' _ hj'
        rw [ite_eq_right fun h => hj' (hdig₀ h).symm, mul_zero]
    · rw [Function.extend_apply' _ _ _ hu]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right (fun h => hu ⟨j, h.symm⟩), mul_zero]
  · rw [ite_eq_right hc]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right ?_, mul_zero]
    rintro rfl
    refine hc ⟨fun k => funext fun p => ?_, fun i hi => registerCfg_of_forall_ne hN hr _ hi⟩
    simp only [Function.comp_apply, registerCfg_registerSite]

end Registers

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
  have hcirc : IsCircuitOn Set.univ (KW + CU * L) (blockLayerOp hN U * pairLayerOp hN hr W) :=
    (isCircuitOn_pairLayerOp hN hr (hKW W hWu)).mul
      (isCircuitOn_blockLayerOp hN (K := CU * L) fun k =>
        (hUpp k).mono (Nat.mul_le_mul_left CU (hL k)))
  refine ⟨CG * L, KW + CU * L, windowGHZState hN hr α', blockLayerOp hN U * pairLayerOp hN hr W,
    by nlinarith, hφ, hcirc.isLocalCircuitOfDepth, ?_⟩
  -- The circuit takes each configuration of the GHZ-type state to the state of its block.
  have hj : ∀ j, (blockLayerOp hN U * pairLayerOp hN hr W) *ᵥ
      Pi.single (registerCfg hN hr (dig₀ j)) 1 = fun s => blockIsometryState (A j) (ω j) hN s := by
    intro j
    obtain ⟨Wj, -, hWj⟩ := exists_pairUnitary hd (hdig.comp (flatCoord_injective (Dj := Dj) j))
      (ω j) (hω j)
    funext s
    rw [blockIsometryState_eq_mulVec hd hN hr (hdig.comp (flatCoord_injective (Dj := Dj) j))
      (A j) (ω j) (U := U) (fun k l r τ => hU k j l r τ) (W := Wj) hWj s,
      ← mulVec_mulVec, ← mulVec_mulVec]
    have key : pairLayerOp hN hr W *ᵥ Pi.single (registerCfg hN hr (dig₀ j)) 1 =
        pairLayerOp hN hr Wj *ᵥ productVector fun _ => Pi.single ⟨0, hd⟩ 1 := by
      funext y
      rw [pairLayerOp_mulVec_apply hd hN hr Wj y]
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
