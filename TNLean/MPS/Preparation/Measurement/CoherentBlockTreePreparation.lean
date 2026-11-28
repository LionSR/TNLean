/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Model.Measurement
import TNLean.MPS.Preparation.Circuit.GHZSeedCircuit
import TNLean.MPS.Preparation.Circuit.SparseWindowGHZ
import TNLean.MPS.Preparation.Circuit.UnequalRegisterTreeState
import TNLean.MPS.Preparation.Circuit.UnequalTreePreparation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QICLean.Analysis.Real.PowerExponential
import TNLean.MPS.Preparation.Circuit.LogLogDepthBound
import TNLean.MPS.Preparation.Circuit.ShortChainPreparation
import TNLean.MPS.Preparation.Circuit.RemainderBlocks

/-!
# Coherent block-state preparation by supported trees

The sparse GHZ seed, the simultaneous pair isometry, and the supported polar trees combine
in depth proportional to the tree height. Pair-product support is required only at the actual
ring size. The physical bond encodings end in a zero site, so their full block configurations
agree with the even-cutoff tree-root windows also when a block length is odd.

## References

* arXiv:2307.01696, eqs. (11), (16), and "Long-range MPS using measurements".

## Double-logarithmic compilation of supported block approximations

An exponentially accurate coherent block approximation, together with eventual support
injectivity, yields measurement-assisted preparation in double-logarithmic depth at every
admissible length. The exact whole-ring branch uses a supported pair only at `M = 1`.
Small rings below the fixed support scale use bounded exact synthesis.

### References

* arXiv:2307.01696, "Tree-RG circuit with measurements", "Long-range MPS using measurements",
  and Supplemental Material, proof of Theorem 1.
-/

section

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
theorem exists_isMeasurementConversion_sum_blockIsometryState
    (d s c : ℕ) [NeZero d] (hs : 2 ≤ s) :
    ∃ C : ℕ, ∀ {D b χ : ℕ} (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
      (e : Fin χ ↪ Fin (D * D)), Set.range (virtualPairEquiv D ∘ e) = (S : Set _) →
      (∀ m, s ≤ m → IsInjectiveOn (Kraus.block A m) (S : Set _)) →
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
        ∃ v : Fin N → Fin d → ℂ, IsMeasurementConversion (Geometry.ring N) (C * (h + 1))
          (fun σ ↦ ∏ i, v i (σ i)) (fun x => ∑ j, α j * blockIsometryState A (ω j) hN x) := by
  classical
  have : NeZero s := ⟨by omega⟩
  obtain ⟨CG, hCG⟩ := exists_isMeasurementConversion_windowGHZState (d := d) hs
  have : NeZero (s + s) := ⟨by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, ∀ X : Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ,
      X ∈ unitary (Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) →
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (s + s))) K X :=
    ⟨_, fun X hX ↦ isGateProduct_pathGraph_unitaryGateCount hX⟩
  obtain ⟨CT, hCT⟩ := exists_rounds_blockLayerOp_supportedPolarTree d s (c + 3)
  refine ⟨CG + K + CT, fun {D b χ} A S e he hinj dig hdig hdig0 dig₀ hdig₀
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
  obtain ⟨U, R, hRf, hRd, himpl, -, hU⟩ := hCT A e (fun m hm => by rw [he]; exact hinj m hm)
    h ℓ hN (fun k => balancedWidths (2 ^ (h + 1)) (ℓ k)) hT
    (fun k p => leafLen_balancedWidths_le (hℓ₂ k) p) ι₀ enc hι₀ henc
  have hUS : ∀ k l r τ, (l, r) ∈ S →
      U k τ (blockInputCfg (NeZero.pos d) (ℓ k) dig l r) =
        polarIsoMatrix (Kraus.block A (ℓ k)) (τ)
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
    simpa only [hex, virtualPairEquiv, Equiv.symm_apply_apply] using hu
  obtain ⟨W, hWu, hW⟩ := exists_pairFamilyUnitary hdig hdig₀ ω hω
  obtain ⟨u, -, hud, huop⟩ := isUnitaryCircuitOn_pairLayerOp hN hr fun _ => hK W hWu
  set seed := windowGHZState hN hr (Function.extend dig₀ α 0)
  have hpair : u.toCircuit.IsImplementationOn KrausGate.ev {seed}
      (pairLayerOp hN hr fun _ => W) := by
    rw [← huop]
    exact u.isImplementationOn _
  have hall := hpair.comp himpl fun v hv => by
    rw [Set.mem_singleton_iff] at hv
    subst v
    refine (isZeroOn_pairLayerOp_windowGHZState hN hr hdig hdig₀ ω
      (fun j => by simpa using hω j j) hW α).mono ?_
    intro x hx
    obtain ⟨k, y, hy₁, hy₂, rfl⟩ := mem_treeCentralSites.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, y, hy₁, by have := (hT k).le; omega, rfl⟩
  obtain ⟨v, hseed⟩ := hCG ℓ hN hr hℓ (Function.extend dig₀ α 0) (by
    rw [sum_extend_zero hdig₀ α (fun _ a => star a * a) (by simp)]
    exact hα)
  have hdepth : (u.toCircuit.comp R).depth ≤ K + CT * (h + 1) :=
    (Circuit.depth_comp _ _).trans (Nat.add_le_add hud hRd)
  have hprep := hseed.trans (hall.isMeasurementConversion
    ((u.forall_isUnitary.mono fun _ hK ↦ Or.inl hK).comp _ hRf) hdepth hseed.ne_zero rfl)
  have hj := fun j => blockLayerOp_pairLayerOp_mulVec_registerCfg hN hr hdig A S (ω j)
    (by simpa using hω j j) (hωS j) (dig₀ j) hUS (fun u => hW u j)
  rw [mulVec_windowGHZState_of_registerCfg hdig₀ hj α] at hprep
  exact ⟨v, hprep.mono (by nlinarith)⟩

/-- Choose all physical encodings once from the dimensions and a support-injectivity cutoff.
The same constants apply to every number of labels at most `B`, so a canonical family and
the one-label exact whole-ring pair use the same tree scale. -/
theorem exists_supported_block_preparation_constants {d D : ℕ} (hd : 2 ≤ d)
    (A : MPSTensor d D) (S : Finset (Fin D × Fin D)) (B L : ℕ)
    (hinj : ∀ m, L ≤ m → IsInjectiveOn (Kraus.block A m) (S : Set _)) :
    ∃ s C : ℕ, 2 ≤ s ∧ L ≤ s ∧ ∀ {b : ℕ}, b ≤ B →
      ∀ (h : ℕ) {M N : ℕ} [NeZero M] [NeZero N]
        (ℓ : Fin M → ℕ) (hN : ∑ k, ℓ k = N),
        (∀ k, 2 ^ (h + 2) * s ≤ ℓ k) → (∀ k, ℓ k ≤ 2 ^ (h + 1) * (8 * s)) →
        ∀ (ω : Fin b → Fin D × Fin D → ℂ),
        (∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) →
        (∀ j (x : Fin M → Fin D × Fin D), pairProductState (ω j) x ≠ 0 → ∀ k, x k ∈ S) →
        ∀ α : Fin b → ℂ, ∑ j, star (α j) * α j = 1 →
        ∃ v : Fin N → Fin d → ℂ, IsMeasurementConversion (Geometry.ring N) (C * (h + 1))
          (fun σ ↦ ∏ i, v i (σ i)) (fun x => ∑ j, α j * blockIsometryState A (ω j) hN x) := by
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
  obtain ⟨C, hC⟩ := exists_isMeasurementConversion_sum_blockIsometryState
    d s (8 * s) hs
  refine ⟨s, C, hs, hLs, fun {b} hb => ?_⟩
  obtain ⟨dig₀⟩ : Nonempty (Fin b ↪ Cfg d s) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  exact hC A S e he (fun m hm => hinj m (hLs.trans hm)) dig hdig hdig0
    dig₀ dig₀.injective enc enc.injective

end MPSPreparation

end

section

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- Compile a coherent supported block approximation with error `K M exp(-r q)` to
all-length double-logarithmic measurement depth. Constants precede the length and accuracy;
the exact one-block hypothesis imposes no support condition at unused ring sizes. -/
theorem exists_log_log_preparation_of_supported_block_approximation
    {d D b : ℕ} (hd : 2 ≤ d) (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
    (L : ℕ) (hinj : ∀ m, L ≤ m → IsInjectiveOn (Kraus.block A m) (S : Set _))
    (ω : Fin b → Fin D × Fin D → ℂ)
    (hω : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0)
    (hωS : ∀ j {M : ℕ} (x : Fin M → Fin D × Fin D),
      pairProductState (ω j) x ≠ 0 → ∀ k, x k ∈ S)
    (target : ∀ N, MPVSpace (Fin d) N) (admissible : ℕ → Prop)
    (htarget : ∀ N, admissible N → ‖target N‖ = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (happrox : ∀ N [NeZero N], admissible N → ∃ α : Fin b → ℂ,
      (∑ j, star (α j) * α j = 1) ∧
      ∀ M [NeZero M] (ℓ : Fin M → ℕ) (hN : ∑ k, ℓ k = N) (q : ℕ),
        L ≤ q → (∀ k, q ≤ ℓ k) →
        ‖∑ j, α j • blockIsometryState A (ω j) hN‖ = 1 ∧
        1 - ‖⟪∑ j, α j • blockIsometryState A (ω j) hN, target N⟫_ℂ‖ ≤
          K * (M * Real.exp (-(r * q))))
    (hexact : ∀ N [NeZero N], admissible N → L ≤ N →
      ∀ hN : ∑ _ : Fin 1, N = N, ∃ ω₁ : Fin D × Fin D → ℂ,
        (∑ p, star (ω₁ p) * ω₁ p = 1) ∧
        (∀ x : Fin 1 → Fin D × Fin D, pairProductState ω₁ x ≠ 0 → ∀ k, x k ∈ S) ∧
        blockIsometryState A ω₁ hN = target N) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N → admissible N →
      ∃ (ψ : MPVSpace (Fin d) N) (T : ℕ), ‖ψ‖ = 1 ∧
        (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
        (∃ v : Fin N → Fin d → ℂ,
          IsMeasurementConversion (Geometry.ring N) T (fun σ ↦ ∏ i, v i (σ i)) (fun x => ψ x)) ∧
        1 - ‖⟪ψ, target N⟫_ℂ‖ ≤ ε := by
  classical
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨hd0.ne'⟩
  obtain ⟨s, C, hs, hLs, hC⟩ :=
    exists_supported_block_preparation_constants hd A S (b + 1) L hinj
  have hs0 : 0 < s := by omega
  obtain ⟨Ks, hKs⟩ := exists_isPreparedInDepth_of_norm_eq_one hd0 (4 * s)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a := 1 / r with ha
  set bq : ℝ := max (Real.log K) 0 / r + 4 * s + 1 with hb
  have ha0 : 0 < a := by positivity
  have hmax : 0 ≤ max (Real.log K) 0 / r := by positivity
  have hb0 : 0 ≤ bq := by positivity
  have hμ : 0 < Real.log (1 + Real.log 2) := Real.log_pos (by linarith)
  set c₀ := (C : ℝ) * ((1 + Real.logb 2 (a + bq + 1)) / Real.log (1 + Real.log 2) +
    1 / Real.log 2)
  have hc₀ : 0 ≤ c₀ := by
    have : 0 ≤ Real.logb 2 (a + bq + 1) := Real.logb_nonneg one_lt_two (by linarith)
    positivity
  refine ⟨c₀ + Ks / Real.log (1 + Real.log 2), fun ε hε hε1 N _ hN hvalid => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 ≤ Real.log (N / ε) := hl2.le.trans hlog
  have hLX : Real.log (1 + Real.log 2) ≤ Real.log (Real.log (N / ε) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hLX0 : 0 ≤ Real.log (Real.log (N / ε) + 1) := hμ.le.trans hLX
  -- Each depth bound below is `c₀ log(log(N/ε) + 1)` or a bounded depth.
  have hc : ∀ T : ℕ, ((T : ℝ) ≤ c₀ * Real.log (Real.log (N / ε) + 1) ∨ T ≤ Ks) →
      (T : ℝ) ≤ (c₀ + Ks / Real.log (1 + Real.log 2)) * Real.log (Real.log (N / ε) + 1) := by
    intro T hT
    have h1 : 0 ≤ c₀ * Real.log (Real.log (N / ε) + 1) := by positivity
    have h2 : (Ks : ℝ) ≤ Ks / Real.log (1 + Real.log 2) * Real.log (Real.log (N / ε) + 1) := by
      calc (Ks : ℝ) = Ks / Real.log (1 + Real.log 2) * Real.log (1 + Real.log 2) := by
            field_simp
        _ ≤ _ := by gcongr
    have h3 : 0 ≤ Ks / Real.log (1 + Real.log 2) * Real.log (Real.log (N / ε) + 1) := by
      positivity
    rw [add_mul]
    rcases hT with h | h
    · linarith
    · have : (T : ℝ) ≤ Ks := by exact_mod_cast h
      linarith
  have hself : 1 - ‖⟪target N, target N⟫_ℂ‖ ≤ ε := by
    rw [inner_self_eq_norm_sq_to_K, htarget N hvalid]
    norm_num [hε.le]
  set Q := a * Real.log (N / ε) + bq with hQ
  set q := ⌈Q⌉₊ with hqdef
  have hQq : Q ≤ q := Nat.le_ceil Q
  have hqQ : (q : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by positivity)
  have h4s : 4 * s ≤ q := by
    have : ((4 * s : ℕ) : ℝ) ≤ q := by
      push_cast
      have : (0 : ℝ) ≤ a * Real.log (N / ε) + max (Real.log K) 0 / r + 1 := by positivity
      linarith
    exact_mod_cast this
  by_cases hqN : q ≤ N
  · -- Long chains: `M - 1` blocks of length `q` and one of length `q' = q + N % q < 2q`.
    have hq0 : 0 < q := by omega
    obtain ⟨m, ℓ, hm, hsum, hℓq, hℓ2⟩ := exists_remainderBlocks hq0 hqN
    obtain ⟨α, hα, hαapprox⟩ := happrox N hvalid
    obtain ⟨hnorm, herr⟩ := hαapprox (m + 1) ℓ hsum q (by omega) hℓq
    obtain ⟨h, hh1, hh2⟩ := exists_two_pow_le hs0 h4s
    set ψ := ∑ j, α j • blockIsometryState A (ω j) hsum
    have hψ : (fun x => ψ x) = fun x => ∑ j, α j * blockIsometryState A (ω j) hsum x := by
      funext x
      simp only [ψ, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    refine ⟨ψ, C * (h + 1), hnorm, hc _ (Or.inl ?_), ?_, ?_⟩
    · refine natCast_mul_succ_le_mul_log ha0 hb0 hlog ?_
      have : (2 : ℝ) ^ h ≤ q := by
        have : 2 ^ h ≤ q := by
          calc 2 ^ h ≤ 2 ^ (h + 2) * s := by
                rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := h)]
            _ ≤ q := hh1
        exact_mod_cast this
      linarith
    · rw [hψ]
      exact hC (by omega) h ℓ hsum (fun k => hh1.trans (hℓq k))
        (fun k => (hℓ2 k).trans (by nlinarith)) ω hω (fun j x => hωS j x) α hα
    · refine herr.trans ?_
      -- `K M e^{-r q} ≤ ε` from `M ≤ N` and `r q ≥ log K + log(N/ε)`.
      have hMN : ((m + 1 : ℕ) : ℝ) ≤ N := by
        rw [← hm]; exact_mod_cast Nat.div_le_self N q
      have hN0 : (0 : ℝ) < N := by linarith
      have hrq : Real.log K + Real.log N - Real.log ε ≤ r * q := by
        have h1 : r * Q ≤ r * q := mul_le_mul_of_nonneg_left hQq hr.le
        have h2 : r * Q = Real.log (N / ε) + max (Real.log K) 0 + r * (4 * s + 1) := by
          simp only [Q, bq, a]; field_simp; ring
        rw [Real.log_div hN0.ne' hε.ne'] at h2
        have : 0 ≤ r * (4 * s + 1) := by positivity
        linarith [le_max_left (Real.log K) 0]
      calc K * (((m + 1 : ℕ) : ℝ) * Real.exp (-(r * q)))
          ≤ K * (N * Real.exp (-(r * q))) := by gcongr
        _ ≤ ε := mul_mul_exp_neg_le_of_log_le hK hN0 hε hrq
  · -- A whole-ring supported tree, even when the accuracy scale exceeds `N`.
    have hNQ : (N : ℝ) < Q := Nat.lt_ceil.mp (not_le.mp hqN)
    by_cases hN4 : 4 * s ≤ N
    · have hN1 : ∑ _ : Fin 1, N = N := by simp
      obtain ⟨ω₁, hω₁, hω₁S, heq⟩ := hexact N hvalid (by omega) hN1
      obtain ⟨h, hh1, hh2⟩ := exists_two_pow_le hs0 hN4
      refine ⟨target N, C * (h + 1), htarget N hvalid, hc _ (Or.inl ?_), ?_, hself⟩
      · refine natCast_mul_succ_le_mul_log ha0 hb0 hlog ?_
        have : (2 : ℝ) ^ h ≤ N := by
          have : 2 ^ h ≤ N := by
            calc 2 ^ h ≤ 2 ^ (h + 2) * s := by
                  rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := h)]
              _ ≤ N := hh1
          exact_mod_cast this
        linarith
      · have hp := hC (b := 1) (by omega) h (fun _ : Fin 1 => N) hN1 (fun _ => hh1)
          (fun _ => by nlinarith) (fun _ => ω₁)
          (fun j j' => by simpa [Subsingleton.elim j j'] using hω₁)
          (fun _ x => hω₁S x) (fun _ => 1) (by simp)
        simpa only [Fin.sum_univ_one, one_mul, heq] using hp
    · have hψ := htarget N hvalid
      refine ⟨target N, Ks, hψ, hc _ (Or.inr le_rfl),
        (hKs N hN (by omega) _ hψ).exists_isMeasurementConversion fun h' => ?_, hself⟩
      have : target N = 0 := by
        ext x; exact congrFun h' x
      rw [this, norm_zero] at hψ
      exact zero_ne_one hψ


end MPSPreparation

end
