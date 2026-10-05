/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Measurement.PreparedComposition
import TNLean.MPS.Preparation.GHZSeedCircuit
import TNLean.MPS.Preparation.SparseWindowGHZ
import TNLean.MPS.Preparation.SupportedTreePreparation
import TNLean.MPS.Preparation.UnequalTreePreparation

/-!
# Coherent block-state preparation by supported trees

The sparse GHZ seed, the simultaneous pair isometry, and the supported polar trees combine
in depth proportional to the tree height. Pair-product support is required only at the actual
ring size. The physical bond encodings end in a zero site, so their full block configurations
agree with the even-cutoff tree-root windows also when a block length is odd.

## References

* arXiv:2307.01696, eqs. (11), (16), and "Long-range MPS using measurements".
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators

namespace MPSPreparation

/-- A pair layer on the encoded GHZ seed leaves the interiors of the physical blocks at zero. -/
private theorem isZeroOn_pairLayerOp_windowGHZState {d D b M N s : ℕ}
    [NeZero d] [NeZero M] [NeZero N] {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (hr : ∀ k, s + s ≤ ℓ k) {dig : Fin D → Cfg d s} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d s} (hdig₀ : Function.Injective dig₀)
    (ω : Fin b → Fin D × Fin D → ℂ)
    (hω : ∀ j, ∑ p, star (ω j p) * ω j p = 1)
    {W : Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ}
    (hW : ∀ u j, W u (windowInput (dig₀ j)) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω j) 0 u)
    (α : Fin b → ℂ) :
    IsZeroOn {x | ∃ k y, s ≤ y.val ∧ y.val + s < ℓ k ∧ x = blockSite hN k y}
      (pairLayerOp hN hr (fun _ => W) *ᵥ
        windowGHZState hN hr (Function.extend dig₀ α 0)) := by
  classical
  have hseed : windowGHZState hN hr (Function.extend dig₀ α 0) =
      ∑ j, α j • Pi.single (registerCfg hN hr (dig₀ j)) 1 := by
    ext x
    rw [windowGHZState_extend hN hr hdig₀]
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  change pairLayerOp hN hr (fun _ => W) *ᵥ _ ∈ zeroOnSubmodule _
  rw [hseed, Matrix.mulVec_sum]
  apply Submodule.sum_mem
  intro j _
  rw [Matrix.mulVec_smul]
  apply Submodule.smul_mem
  obtain ⟨W₀, -, hW₀⟩ := exists_pairUnitary (NeZero.pos d) hdig (ω j) (hω j)
  rw [pairLayerOp_mulVec_registerCfg_eq hN hr dig (dig₀ j) (ω j) (fun u => hW u j) hW₀]
  exact isZeroOn_pairLayerOp_mulVec_productVector hN hr (fun _ => W₀)

/-- A coherent family of supported block states is prepared in depth `C(h+1)`.
The support condition concerns the actual number of blocks `M`, which permits the arbitrary
supported one-block pair needed for whole-ring exact preparation. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_sum_blockIsometryState
    (d s c : ℕ) [NeZero d] (hs : 2 ≤ s) :
    ∃ C : ℕ, ∀ {D b χ : ℕ} (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
      (e : Fin χ ↪ Fin (D * D)), Set.range (virtualPairEquiv D ∘ e) = (S : Set _) →
      (∀ m, s ≤ m → IsInjectiveOn (blockTensor A m) (S : Set _)) →
      ∀ (dig : Fin D → Cfg d s), Function.Injective dig →
      (∀ l, dig l ⟨s - 1, by omega⟩ = 0) →
      ∀ (dig₀ : Fin b → Cfg d s), Function.Injective dig₀ →
      ∀ (enc : Fin χ → Cfg d s), Function.Injective enc →
      ∀ (h : ℕ) {M N : ℕ} [NeZero M] [NeZero N]
        (ℓ : Fin M → ℕ) (hN : ∑ k, ℓ k = N),
        (∀ k, 2 ^ (h + 2) * s ≤ ℓ k) → (∀ k, ℓ k ≤ 2 ^ (h + 1) * c) →
        ∀ (ω : Fin b → Fin D × Fin D → ℂ),
        (∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) →
        (∀ j (x : Fin M → Fin D × Fin D), pairProductState (ω j) x ≠ 0 → ∀ k, x k ∈ S) →
        ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
        IsPreparedWithMeasurementRoundsInDepth (C * (h + 1))
          (fun x => ∑ j, α j * blockIsometryState A (ω j) hN x) := by
  classical
  have : NeZero s := ⟨by omega⟩
  obtain ⟨CG, hCG⟩ := exists_isPreparedWithMeasurementRoundsInDepth_windowGHZState (d := d) hs
  obtain ⟨K, hK⟩ := exists_isPairProduct (n := s + s) (NeZero.pos d) (by omega)
  obtain ⟨CT, hCT⟩ := exists_rounds_blockLayerOp_supportedPolarTree d s (c + 3)
  refine ⟨CG + K + CT + 2, fun {D b χ} A S e he hinj dig hdig hdig0 dig₀ hdig₀
    enc henc h {M N} _ _ ℓ hN hℓ₁ hℓ₂ ω hω hωS α hα => ?_⟩
  have hT : ∀ k, IsTreeLayout h s (ℓ k) (balancedWidths (2 ^ (h + 1)) (ℓ k)) :=
    fun k => isTreeLayout_balancedWidths (hℓ₁ k)
  have hℓ : ∀ k, 3 * s ≤ ℓ k := by
    intro k
    have hk := hℓ₁ k
    have hpow : 4 ≤ 2 ^ (h + 2) := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ (h + 2) := Nat.pow_le_pow_right two_pos (by omega)
    nlinarith
  have hr : ∀ k, s + s ≤ ℓ k := fun k => by have := hℓ k; omega
  set ι₀ : ∀ k, Fin χ → Cfg d (s + s) := fun k x =>
    blockInputCfg (NeZero.pos d) (ℓ k) dig (virtualPairEquiv D (e x)).1
      (virtualPairEquiv D (e x)).2 ∘ nodeWindow (hT k) 0 0 with hι₀def
  have hroot : ∀ k x, blockInputCfg (NeZero.pos d) (ℓ k) dig
      (virtualPairEquiv D (e x)).1 (virtualPairEquiv D (e x)).2 =
      placeCfg (fun p : Fin (2 ^ 0) => nodeWindow (hT k) 0 p) fun _ => ι₀ k x := by
    intro k x
    exact blockInputCfg_eq_placeCfg (hT k)
      (le_leafOffset_balancedWidths_add_one h (ℓ k)) hdig0 _ _
  have hι₀ : ∀ k, Function.Injective (ι₀ k) := by
    intro k x y hxy
    apply e.injective
    apply (virtualPairEquiv D).injective
    have hcfg := blockInputCfg_injective (NeZero.pos d) (hr k) hdig
      (l := (virtualPairEquiv D (e x)).1) (r := (virtualPairEquiv D (e x)).2)
      (l' := (virtualPairEquiv D (e y)).1) (r' := (virtualPairEquiv D (e y)).2)
      (by rw [hroot k x, hroot k y, hxy])
    exact Prod.ext hcfg.1 hcfg.2
  obtain ⟨U, Rs, hRs, himpl, -, hU⟩ := hCT A e (fun m hm => by rw [he]; exact hinj m hm)
    h ℓ hN (fun k => balancedWidths (2 ^ (h + 1)) (ℓ k)) hT
    (fun k p => leafLen_balancedWidths_le (hℓ₂ k) p) ι₀ enc hι₀ henc
  have hUS : ∀ k l r τ, (l, r) ∈ S →
      U k τ (blockInputCfg (NeZero.pos d) (ℓ k) dig l r) =
        polarIsoMatrix (blockTensor A (ℓ k)) ((decodeBlockEquiv d (ℓ k)).symm τ)
          (finProdFinEquiv (l, r)) := by
    intro k l r τ hp
    obtain ⟨x, hx⟩ : ∃ x, virtualPairEquiv D (e x) = (l, r) := by
      have hp' : (l, r) ∈ Set.range (virtualPairEquiv D ∘ e) := by rw [he]; exact hp
      simpa only [Set.mem_range, Function.comp_apply] using hp'
    have hu := hU k x τ
    rw [← hroot k x] at hu
    have hex : e x = finProdFinEquiv (l, r) := by
      apply (virtualPairEquiv D).injective
      simpa [virtualPairEquiv] using hx
    simpa only [hex, cfgPolarIso, virtualPairEquiv, Equiv.symm_apply_apply] using hu
  obtain ⟨W, hWu, hW⟩ := exists_pairFamilyUnitary hdig hdig₀ ω hω
  obtain ⟨Ls, hLs, -, hLsW⟩ := isCircuitOn_pairLayerOp hN hr fun _ => hK W hWu
  set seed := windowGHZState hN hr (Function.extend dig₀ α 0)
  have hpair : MeasurementRound.IsRoundsImplementationOn [TeleportHop.round Ls []
      TeleportHop.valid_nil] {seed} (pairLayerOp hN hr fun _ => W) := by
    have := (TeleportHop.isImplementationOn_round (d := d) Ls
      (TeleportHop.valid_nil (N := N))).isRoundsImplementationOn
    rw [TeleportHop.chainPerm_nil, Matrix.one_mul, ← hLsW] at this
    exact this.mono fun v _ => fun _ _ _ h => h.elim
  have hall := hpair.append himpl fun v hv => by
    rw [Set.mem_singleton_iff] at hv
    subst v
    refine (isZeroOn_pairLayerOp_windowGHZState hN hr hdig hdig₀ ω
      (fun j => by simpa using hω j j) hW α).mono ?_
    rintro x ⟨k, y, hy₁, hy₂, rfl⟩
    exact ⟨k, y, hy₁, by have := (hT k).le; simp only at hy₂; omega, rfl⟩
  have hseed : IsPreparedWithMeasurementRoundsInDepth CG seed := by
    apply hCG ℓ hN hr hℓ
    rw [sum_extend_zero hdig₀ α (fun _ a => star a * a) (by simp)]
    exact hα
  have hdepth : (([TeleportHop.round Ls [] TeleportHop.valid_nil] ++ Rs).map
      MeasurementRound.depth).sum ≤ K + 2 + CT * (h + 1) := by
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, TeleportHop.depth_round, hLs]
    omega
  have hprep := hseed.apply_implementation hall rfl hdepth
  have hj := fun j => blockLayerOp_pairLayerOp_mulVec_registerCfg hN hr hdig A S (ω j)
    (by simpa using hω j j) (hωS j) (dig₀ j) hUS (fun u => hW u j)
  rw [mulVec_windowGHZState_of_registerCfg hdig₀ hj α] at hprep
  exact hprep.mono (by nlinarith)

/-- Choose all physical encodings once from the dimensions and a support-injectivity cutoff.
The same constants apply to every number of labels at most `B`, so a canonical family and
the one-label exact whole-ring pair use the same tree scale. -/
theorem exists_supported_block_preparation_constants {d D : ℕ} (hd : 2 ≤ d)
    (A : MPSTensor d D) (S : Finset (Fin D × Fin D)) (B L : ℕ)
    (hinj : ∀ m, L ≤ m → IsInjectiveOn (blockTensor A m) (S : Set _)) :
    ∃ s C : ℕ, 2 ≤ s ∧ L ≤ s ∧ ∀ {b : ℕ}, b ≤ B →
      ∀ (h : ℕ) {M N : ℕ} [NeZero M] [NeZero N]
        (ℓ : Fin M → ℕ) (hN : ∑ k, ℓ k = N),
        (∀ k, 2 ^ (h + 2) * s ≤ ℓ k) → (∀ k, ℓ k ≤ 2 ^ (h + 1) * (8 * s)) →
        ∀ (ω : Fin b → Fin D × Fin D → ℂ),
        (∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) →
        (∀ j (x : Fin M → Fin D × Fin D), pairProductState (ω j) x ≠ 0 → ∀ k, x k ∈ S) →
        ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
        IsPreparedWithMeasurementRoundsInDepth (C * (h + 1))
          (fun x => ∑ j, α j * blockIsometryState A (ω j) hN x) := by
  classical
  have : NeZero d := ⟨by omega⟩
  set s := L + B + D * D + D + 2 with hsdef
  have hs : 2 ≤ s := by omega
  have hLs : L ≤ s := by omega
  have hpow : s < d ^ s := (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hd s)
  have hpow' : s - 1 < d ^ (s - 1) :=
    (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hd (s - 1))
  have hcard : S.card ≤ D * D := by simpa using (Finset.card_le_univ (s := S))
  let t : Fin S.card ≃ ↥S := (Fintype.equivFinOfCardEq (by simp)).symm
  let e : Fin S.card ↪ Fin (D * D) :=
    ⟨fun x => (virtualPairEquiv D).symm (t x).val, fun x y hxy =>
      t.injective (Subtype.ext ((virtualPairEquiv D).symm.injective hxy))⟩
  have he : Set.range (virtualPairEquiv D ∘ e) = (S : Set _) := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      change (virtualPairEquiv D) ((virtualPairEquiv D).symm (t x).val) ∈ S
      rw [Equiv.apply_symm_apply]
      exact (t x).property
    · intro hp
      refine ⟨t.symm ⟨p, hp⟩, ?_⟩
      change (virtualPairEquiv D) ((virtualPairEquiv D).symm (t (t.symm ⟨p, hp⟩)).val) = p
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  obtain ⟨enc⟩ : Nonempty (Fin S.card ↪ Cfg d s) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨dig'⟩ : Nonempty (Fin D ↪ Cfg d (s - 1)) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  let dig : Fin D → Cfg d s := fun l i =>
    if hi : i.val < s - 1 then dig' l ⟨i.val, hi⟩ else 0
  have hdig : Function.Injective dig := fun l l' heq => dig'.injective (funext fun i => by
    have := congrFun heq ⟨i.val, by omega⟩
    simpa [dig, show i.val < s - 1 from i.isLt] using this)
  have hdig0 : ∀ l, dig l ⟨s - 1, by omega⟩ = 0 := fun l => by simp [dig]
  obtain ⟨C, hC⟩ := exists_isPreparedWithMeasurementRoundsInDepth_sum_blockIsometryState
    d s (8 * s) hs
  refine ⟨s, C, hs, hLs, fun {b} hb => ?_⟩
  obtain ⟨dig₀⟩ : Nonempty (Fin b ↪ Cfg d s) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  exact hC A S e he (fun m hm => hinj m (hLs.trans hm)) dig hdig hdig0
    dig₀ dig₀.injective enc enc.injective

end MPSPreparation
