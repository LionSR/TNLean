/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Gate.PartialIsometryDilation
import TNLean.MPS.Tensor.VaryingBond.IsometricChain
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.Circuit.Compile.WindowUniversality
import TNLean.MPS.Tensor.Overlap

/-!
# The staircase circuit of an isometric chain

Let `Q₀, …, Q_{n-1}` be an isometric open chain with bond space `ℂ^{D'}`, as produced by the
sequential factorization (`MPSPreparation.exists_isometric_chain_polarIsoMatrix`), and let the
bond levels be encoded injectively in the configurations of `r ≥ 2` sites. Then there is a
unitary `U` on the open chain of `n ≥ r` sites with
`⟨σ| U |0 ⋯ 0, enc(x)⟩ = (Q₀(σ₀) ⋯ Q_{n-1}(σ_{n-1}))_{0x}`, where the encoded input occupies
the last `r` sites. For every unitary `Z` acting on the last `r` sites, `U Z` is a product of
at most `max 1 (n - r)` gates, each acting on at most `r + 1` consecutive sites, and so is `U`
(`MPSPreparation.exists_staircase_isWindowProduct`). For `r ≥ 2`
it is therefore a product of at most `K₀ + (n - r) K₁` gates on neighbouring sites, with `K₀`,
`K₁ = 12 (d^{r+1})^5` depending only on `d` and `r` (`MPSPreparation.exists_staircase`).

The unitary is the staircase of arXiv:2307.01696, paragraph "The sequential-RG circuit" and
Fig. 1: the bond register moves one site to the left at each step, the unitary extending
`Q_p` acts on the `r` register sites and one fresh site in `|0⟩` and leaves the physical output
on the rightmost of them, and the last `r` isometries act on the final position of the
register. Each step acts on `r + 1` consecutive sites, so it is a product of a bounded number
of two-site gates (`QuantumCircuit.IsGateProduct.of_window`). The induction places the
staircase of the first `n` sites on every longer chain, so that the later steps are gates on
windows of that chain.

**Scope restriction (nonempty chain):** `exists_staircase_isWindowProduct` assumes `0 < n`
(the source's chains have `q ≥ 1` sites), because on the empty chain a product of gates is only
the identity, so `U Z` cannot be one for both `Z = 1` and `Z = -1`, the old statement there
having relied on global phases being circuits.

## References

* Malz, Styliaris, Wei, Cirac, *Preparation of matrix product states with log-depth
  quantum circuits*, arXiv:2307.01696, eq. (14), the paragraph "The sequential-RG circuit"
  and Fig. 1.
-/

open Matrix MPSTensor
open MPSChainTensor (eval eval_succ')
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

variable {d : ℕ}

/-! ### One step of the staircase -/

/-- Appending one site to an injective encoding of the bond levels is injective. -/
private theorem snoc_enc_injective {r D' : ℕ} {enc : Fin D' → Cfg d r}
    (henc : Function.Injective enc) :
    Function.Injective fun p : Fin D' × Fin d => (Fin.snoc (enc p.1) p.2 : Cfg d (r + 1)) := by
  rintro ⟨α, i⟩ ⟨α', i'⟩ h
  have h1 := congrFun h (Fin.last r)
  simp only [Fin.snoc_last] at h1
  have h2 : enc α = enc α' := funext fun j => by
    have := congrFun h j.castSucc
    simpa [Fin.snoc_castSucc] using this
  rw [henc h2, h1]

/-- The unitary extending one site of an isometric chain: on the `r + 1` sites of a window it
sends `|0, enc(x)⟩` to `∑_{α,i} Q(i)_{α x} |enc(α), i⟩` for every `x < b`. -/
theorem exists_step_unitary (hd : 0 < d) {r D' : ℕ} {enc : Fin D' → Cfg d r}
    (henc : Function.Injective enc) {b : ℕ} {Q : Fin d → Matrix (Fin D') (Fin D') ℂ}
    (hQ : IsIsometryOn b Q) :
    ∃ W ∈ unitary (Matrix (Cfg d (r + 1)) (Cfg d (r + 1)) ℂ), ∀ x : Fin D', x.val < b →
      ∀ u, W u (Fin.cons ⟨0, hd⟩ (enc x)) =
        Function.extend (fun p : Fin D' × Fin d => (Fin.snoc (enc p.1) p.2 : Cfg d (r + 1)))
          (fun p => Q p.2 p.1 x) 0 u := by
  classical
  set s : Fin D' × Fin d → Cfg d (r + 1) := fun p => Fin.snoc (enc p.1) p.2
  have hsi : Function.Injective s := snoc_enc_injective henc
  let κ := {x : Fin D' // x.val < b}
  let V : Matrix (Cfg d (r + 1)) κ ℂ :=
    Matrix.of fun u x => Function.extend s (fun p => Q p.2 p.1 x.1) 0 u
  have hV : V.IsIsometry := by
    ext x x'
    rw [mul_apply, one_apply]
    simp only [conjTranspose_apply, V, of_apply]
    rw [sum_extend_zero hsi (fun p => Q p.2 p.1 x.1)
      (fun u a => star a * Function.extend s (fun p => Q p.2 p.1 x'.1) 0 u) (by simp)]
    simp only [hsi.extend_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm, hQ x.1 x'.1 x.2 x'.2]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (Subtype.ext h1) h2
    · exact absurd (congrArg Subtype.val h2) h1
    · rfl
  let emb : κ ↪ Cfg d (r + 1) :=
    ⟨fun x => Fin.cons ⟨0, hd⟩ (enc x.1), fun x x' h => Subtype.ext (henc (by
      have := congrArg Fin.tail h
      simpa using this))⟩
  obtain ⟨W, hW, hWV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
  exact ⟨W, hW, fun x hx u => (hWV u ⟨x, hx⟩).trans (of_apply _ _ _)⟩

/-! ### The staircase -/

/-- The first `n` sites of a chain of `N` sites lie in the interval `[0, n)`. -/
private theorem map_castLEEmb_subset {n N : ℕ} (h : n ≤ N) :
    Finset.univ.map (Fin.castLEEmb h) ⊆ ManyBody.interval N 0 n := by
  intro p hp
  obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hp
  rw [ManyBody.mem_interval, Fin.castLEEmb_apply, Fin.val_castLE]
  exact ⟨Nat.zero_le _, u.isLt⟩

/-- An interval of a chain inside a larger interval. -/
private theorem interval_subset_interval {N a b a' b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b') :
    ManyBody.interval N a b ⊆ ManyBody.interval N a' b' := by
  intro p hp
  rw [ManyBody.mem_interval] at hp ⊢
  omega

/-- The staircase on a chain of `n` sites placed on the first `n` sites of every longer chain:
for every `N ≥ n` with `N > 0` and every unitary `Z` on the `N` sites supported on the last `r`
of the first `n` sites, the product of the placed staircase and `Z` is a product of at most
`max 1 (n - r)` gates on windows of `r + 1` consecutive sites. -/
private theorem exists_staircase_window (hd : 0 < d) {r D' : ℕ} (hD' : 0 < D')
    {enc : Fin D' → Cfg d r} (henc : Function.Injective enc) :
    ∀ n, r ≤ n → ∀ (b : Fin (n + 1) → ℕ) (Q : MPSChainTensor d D' n),
      b 0 = 1 → (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) →
      (∀ p, IsIsometryOn (b p.succ) (Q p)) →
      ∃ U : Matrix (Cfg d n) (Cfg d n) ℂ,
        (∀ N (hnN : n ≤ N), 0 < N → ∀ Z ∈ unitaryGroup (Cfg d N) ℂ,
          Z ∈ ManyBody.supportedOperators (fun _ : Fin N ↦ Fin d)
              (ManyBody.interval N (n - r) n) →
            IsGateProduct (Geometry.window N (r + 1)) (max 1 (n - r))
              (ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d) (Fin.castLEEmb hnN) U * Z)) ∧
        ∀ x : Fin D', x.val < b (Fin.last n) → ∀ σ,
          U σ (inputCfg hd n (enc x)) = eval Q σ ⟨0, hD'⟩ x := by
  classical
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro b Q hb0 hrow hiso
    let κ := {x : Fin D' // x.val < b (Fin.last r)}
    let V : Matrix (Cfg d r) κ ℂ := Matrix.of fun σ x => eval Q σ ⟨0, hD'⟩ x.1
    have hV : V.IsIsometry := by
      ext x x'
      have hsx : ∀ y : κ, IsSupportedBelow (b (Fin.last r)) (Pi.single y.1 (1 : ℂ)) :=
        fun y β hβ => by
          rw [Pi.single_apply, ite_eq_right]; rintro rfl; exact absurd y.2 (by omega)
      have h := sum_star_eval_mulVec_dotProduct b Q hrow hiso (Pi.single x.1 1)
        (Pi.single x'.1 1) (hsx x) (hsx x')
      have hs : ∀ σ, star (eval Q σ *ᵥ Pi.single x.1 1) ⬝ᵥ (eval Q σ *ᵥ Pi.single x'.1 1) =
          star (V σ x) * V σ x' := fun σ => by
        rw [dotProduct, Finset.sum_eq_single ⟨0, hD'⟩]
        · simp [V]
        · intro β _ hβ
          rw [isSupportedBelow_eval_mulVec b Q hrow _ (hsx x') σ β (by
            rw [hb0]; exact Nat.one_le_iff_ne_zero.mpr fun h => hβ (Fin.ext h)), mul_zero]
        · simp
      simp only [hs] at h
      have hr : star (Pi.single x.1 (1 : ℂ)) ⬝ᵥ Pi.single x'.1 1 = if x = x' then 1 else 0 := by
        rw [dotProduct, Finset.sum_eq_single x.1]
        · by_cases hxx : x = x'
          · subst hxx; simp
          · have : x.1 ≠ x'.1 := fun h => hxx (Subtype.ext h)
            simp [this, hxx]
        · intro β _ hβ; simp [Pi.single_apply, hβ]
        · simp
      rw [mul_apply, one_apply]
      simp only [conjTranspose_apply]
      rw [h, hr]
    let emb : κ ↪ Cfg d r := ⟨fun x => inputCfg hd r (enc x.1), fun x x' h => Subtype.ext
      (henc (by simpa [inputCfg_self] using h))⟩
    obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
    refine ⟨U, fun N hrN hN0 Z hZu hZS => ?_,
      fun x hx σ => (hUV σ ⟨x, hx⟩).trans (of_apply _ _ _)⟩
    -- the placed unitary and `Z` form one gate on the window of the first `r + 1` sites
    refine (IsGateProduct.window_of_mem_supportedOperators (m := r + 1) (⟨0, hN0⟩ : Fin N)
      (mul_mem (ManyBody.placeAlong_mem_unitaryGroup (X := fun _ : Fin N ↦ Fin d)
        (Fin.castLEEmb hrN) hU) hZu) (mul_mem ?_ ?_)).mono (le_max_left _ _)
    · exact ManyBody.supportedOperators_mono ((map_castLEEmb_subset hrN).trans
        (interval_subset_interval (show 0 ≤ 0 from le_rfl) (show r ≤ 0 + (r + 1) by omega)))
        (ManyBody.placeAlong_mem_supportedOperators (X := fun _ : Fin N ↦ Fin d)
          (Fin.castLEEmb hrN) U)
    · exact ManyBody.supportedOperators_mono
        (interval_subset_interval (show 0 ≤ r - r by omega) (show r ≤ 0 + (r + 1) by omega))
        hZS
  | succ n hn ih =>
    intro b Q hb0 hrow hiso
    -- the chain without its last site
    obtain ⟨U', hU', hU'Q⟩ := ih (fun k => b k.castSucc) (fun p => Q p.castSucc) hb0
      (fun p i => hrow p.castSucc i) (fun p => by
        have h := hiso p.castSucc
        rw [Fin.succ_castSucc] at h
        exact h)
    -- the unitary of the last step
    obtain ⟨W, hWu, hW⟩ := exists_step_unitary hd henc (hiso (Fin.last n))
    set win : Fin (r + 1) → Fin (n + 1) := fun j => ⟨n - r + j.val, by omega⟩ with hwin
    have hwini : Function.Injective win := fun j j' h => by
      simp only [hwin, Fin.mk.injEq] at h; exact Fin.ext (by omega)
    set c : Fin n ↪ Fin (n + 1) := Fin.castLEEmb (Nat.le_succ n) with hc
    set w : Fin (r + 1) ↪ Fin (n + 1) := ⟨win, hwini⟩ with hw
    have hwcoe : ⇑w = win := rfl
    refine ⟨ManyBody.placeAlong (X := fun _ : Fin (n + 1) ↦ Fin d) c U' *
      ManyBody.placeAlong (X := fun _ : Fin (n + 1) ↦ Fin d) w W, ?_, ?_⟩
    · intro N hnN hN0 Z hZu hZS
      have hnN' : n ≤ N := by omega
      set c' : Fin (n + 1) ↪ Fin N := Fin.castLEEmb hnN with hc'
      -- the placed chain without its last site
      have hU'1 := hU' N hnN' hN0 1 (one_mem _) (one_mem _)
      rw [mul_one] at hU'1
      have hcomp : ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d) c'
          (ManyBody.placeAlong (X := fun _ : Fin (n + 1) ↦ Fin d) c U') =
          ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d) (Fin.castLEEmb hnN') U' :=
        (ManyBody.placeAlong_placeAlong (X := fun _ : Fin N ↦ Fin d) c' c U').trans rfl
      -- the placed last step
      obtain ⟨Wp, hWp⟩ : ∃ Wp, Wp = ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d) c'
          (ManyBody.placeAlong (X := fun _ : Fin (n + 1) ↦ Fin d) w W) := ⟨_, rfl⟩
      have hWpu : Wp ∈ unitaryGroup (Cfg d N) ℂ := by
        rw [hWp]
        exact ManyBody.placeAlong_mem_unitaryGroup (X := fun _ : Fin N ↦ Fin d) c'
          (ManyBody.placeAlong_mem_unitaryGroup (X := fun _ : Fin (n + 1) ↦ Fin d) w hWu)
      have hWpS : Wp ∈ ManyBody.supportedOperators (fun _ : Fin N ↦ Fin d)
          (ManyBody.interval N (n - r) (n + 1)) := by
        rw [hWp]
        refine ManyBody.supportedOperators_mono ?_
          (ManyBody.placeAlong_mem_supportedOperators_map (X := fun _ : Fin N ↦ Fin d) c'
            (ManyBody.placeAlong_mem_supportedOperators (X := fun _ : Fin (n + 1) ↦ Fin d) w W))
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
        obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hq
        rw [ManyBody.mem_interval, hc', Fin.castLEEmb_apply, Fin.val_castLE, hwcoe]
        simp only [hwin]
        omega
      have hsplit : ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d) c'
          (ManyBody.placeAlong (X := fun _ : Fin (n + 1) ↦ Fin d) c U' *
            ManyBody.placeAlong (X := fun _ : Fin (n + 1) ↦ Fin d) w W) * Z =
          ManyBody.placeAlong (X := fun _ : Fin N ↦ Fin d) (Fin.castLEEmb hnN') U' * (Wp * Z) := by
        rw [ManyBody.placeAlong_mul, hcomp, ← hWp, mul_assoc]
      rw [hsplit]
      by_cases hnr : n = r
      · -- the whole product is one gate on the window of the first `r + 1` sites
        refine (IsGateProduct.window_of_mem_supportedOperators (m := r + 1) (⟨0, hN0⟩ : Fin N)
          (mul_mem hU'1.mem_unitaryGroup (mul_mem hWpu hZu))
          (mul_mem ?_ (mul_mem ?_ ?_))).mono (le_max_left _ _)
        · exact ManyBody.supportedOperators_mono ((map_castLEEmb_subset hnN').trans
            (interval_subset_interval (show 0 ≤ 0 from le_rfl) (show n ≤ 0 + (r + 1) by omega)))
            (ManyBody.placeAlong_mem_supportedOperators (X := fun _ : Fin N ↦ Fin d)
              (Fin.castLEEmb hnN') U')
        · exact ManyBody.supportedOperators_mono
            (interval_subset_interval (show 0 ≤ n - r by omega)
              (show n + 1 ≤ 0 + (r + 1) by omega)) hWpS
        · exact ManyBody.supportedOperators_mono
            (interval_subset_interval (show 0 ≤ n + 1 - r by omega)
              (show n + 1 ≤ 0 + (r + 1) by omega)) hZS
      -- the last step and `Z` form one gate on the window at `n - r`
      have hWZ := IsGateProduct.window_of_mem_supportedOperators (m := r + 1)
        (⟨n - r, by omega⟩ : Fin N) (mul_mem hWpu hZu)
        (mul_mem (ManyBody.supportedOperators_mono
          (interval_subset_interval (show n - r ≤ n - r from le_rfl)
            (show n + 1 ≤ n - r + (r + 1) by omega)) hWpS)
          (ManyBody.supportedOperators_mono
            (interval_subset_interval (show n - r ≤ n + 1 - r by omega)
              (show n + 1 ≤ n - r + (r + 1) by omega)) hZS))
      exact (hU'1.mul hWZ).mono (by omega)
    · intro x hx σ
      set y := inputCfg hd (n + 1) (enc x) with hy
      have hyw : y ∘ win = Fin.cons ⟨0, hd⟩ (enc x) := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · rw [Fin.cons_zero, Function.comp_apply, hy]
          unfold inputCfg
          split_ifs with h
          · exfalso; simp [hwin] at h; omega
          · rfl
        · rw [Fin.cons_succ, Function.comp_apply, hy]
          unfold inputCfg
          split_ifs with h
          · congr 1; ext; simp [hwin]; omega
          · exfalso; simp [hwin] at h; omega
      rw [ManyBody.mul_placeAlong_apply, hwcoe, hyw]
      simp_rw [hW x hx]
      rw [sum_extend_zero (snoc_enc_injective henc) _ _ (fun u => mul_zero _)]
      -- evaluate the first factor on the extended configurations
      have hlast : Fin.last n = win (Fin.last r) := by ext; simp [hwin]; omega
      have hcne : ∀ u : Fin n, c u ≠ Fin.last n := fun u hu => by
        have h := congrArg Fin.val hu
        rw [hc, Fin.castLEEmb_apply, Fin.val_castLE, Fin.val_last] at h
        exact absurd h (Nat.ne_of_lt u.isLt)
      have hext : ∀ (α : Fin D') (i : Fin d),
          ManyBody.placeAlong (X := fun _ : Fin (n + 1) ↦ Fin d) c U' σ
            (Function.extend win (Fin.snoc (enc α) i : Cfg d (r + 1)) y) =
          if σ (Fin.last n) = i then U' (fun u ↦ σ (c u)) (inputCfg hd n (enc α)) else 0 := by
        intro α i
        set z := Function.extend win (Fin.snoc (enc α) i : Cfg d (r + 1)) y with hz
        have hzl : z (Fin.last n) = i := by
          rw [hz, hlast, hwini.extend_apply, Fin.snoc_last]
        have hzc : (fun u ↦ z (c u)) = inputCfg hd n (enc α) := by
          funext k
          change z k.castSucc = _
          simp only [hz]
          by_cases hk : n - r ≤ k.val
          · have hkw : k.castSucc = win (⟨k.val - (n - r), by omega⟩ : Fin r).castSucc := by
              ext; simp [hwin]; omega
            rw [hkw, hwini.extend_apply, Fin.snoc_castSucc, inputCfg, dite_eq_left hk]
          · rw [Function.extend_apply' _ _ _ (by
              rintro ⟨j, hj⟩
              have := congrArg Fin.val hj
              simp [hwin] at this; omega), hy, inputCfg, inputCfg, dite_eq_right (by simp; omega),
              dite_eq_right hk]
        have hag : (∀ v, (∀ u, c u ≠ v) → σ v = z v) ↔ σ (Fin.last n) = i := by
          rw [← hzl]
          constructor
          · intro h; exact h _ hcne
          · intro h k hk
            have : k = Fin.last n := by
              by_contra hne
              exact hk (k.castPred hne) (Fin.castSucc_castPred k hne)
            rw [this]; exact h
        rw [ManyBody.placeAlong_apply, hzc]
        by_cases h : σ (Fin.last n) = i
        · rw [ite_eq_left (hag.mpr h), ite_eq_left h]
        · rw [ite_eq_right (fun h' => h (hag.mp h')), ite_eq_right h]
      simp only [hext, ite_mul, zero_mul]
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [eval_succ', mul_apply]
      refine Finset.sum_congr rfl fun α _ => ?_
      by_cases hα : α.val < b (Fin.last n).castSucc
      · rw [hU'Q α (by simpa using hα)]; rfl
      · rw [hrow (Fin.last n) (σ (Fin.last n)) α x (by omega), mul_zero, mul_zero]

/-- **The staircase circuit of an isometric chain, with gates on `r + 1` consecutive sites.**
Let `enc` encode the bond levels `Fin D'` injectively in the configurations of `r` sites. For
every `n ≥ r` with `n > 0` and every chain `Q₀, …, Q_{n-1}` with bonds `b₀ = 1, b₁, …, b_n`,
every site vanishing on the rows beyond its left bond and isometric on its right bond, there is
a unitary `U` on `n` sites with `⟨σ| U |0 ⋯ 0, enc(x)⟩ = (Q₀(σ₀) ⋯ Q_{n-1}(σ_{n-1}))_{0x}` for
every `x < b_n`, such that for every unitary `Z` acting on the last `r` sites, `U Z` is a product
of at most `max 1 (n - r)` gates each acting on at most `r + 1` consecutive sites. The first
gate applied extends `Q_{n-1}` and absorbs `Z`, each later one extends the next site to the
left, and the unitary on the first `r` sites extending the remaining chain is absorbed into the
last one.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1: the isometries `V_i` of
eq. (14) applied in sequence, each acting on the bond register and one site; the successive
isometries of arXiv:quant-ph/0501096, eq. `induction`. -/
theorem exists_staircase_isWindowProduct (hd : 0 < d) {r D' : ℕ} (hD' : 0 < D')
    {enc : Fin D' → Cfg d r} (henc : Function.Injective enc) :
    ∀ n, r ≤ n → 0 < n → ∀ (b : Fin (n + 1) → ℕ) (Q : MPSChainTensor d D' n),
      b 0 = 1 → (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) →
      (∀ p, IsIsometryOn (b p.succ) (Q p)) →
      ∃ U : Matrix (Cfg d n) (Cfg d n) ℂ,
        (∀ Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ),
          Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (ManyBody.interval n (n - r) n) →
            IsGateProduct (Geometry.window n (r + 1)) (max 1 (n - r)) (U * Z)) ∧
        ∀ x : Fin D', x.val < b (Fin.last n) → ∀ σ,
          U σ (inputCfg hd n (enc x)) = eval Q σ ⟨0, hD'⟩ x := by
  intro n hn hn0 b Q hb0 hrow hiso
  obtain ⟨U, hU, hUQ⟩ := exists_staircase_window hd hD' henc n hn b Q hb0 hrow hiso
  refine ⟨U, fun Z hZu hZS => ?_, hUQ⟩
  have hrefl : ManyBody.placeAlong (X := fun _ : Fin n ↦ Fin d) (Fin.castLEEmb (le_refl n)) U =
      U := by
    rw [show Fin.castLEEmb (le_refl n) = Function.Embedding.refl (Fin n) from
      Function.Embedding.ext fun _ => rfl]
    exact ManyBody.placeAlong_refl U
  have h := hU n (le_refl n) hn0 Z hZu hZS
  rwa [hrefl] at h

/-- On the open chain of `n ≥ 2` sites with a one-dimensional space at every site, every unitary
is one gate on neighbouring sites. -/
private theorem isGateProduct_one_of_le_one (hd : d ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    {U : Matrix (Cfg d n) (Cfg d n) ℂ} (hU : U ∈ unitaryGroup (Cfg d n) ℂ) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) 1 U := by
  have hsub : ∀ a b : Fin d, a = b := fun a b => Fin.ext (by
    have := a.isLt
    have := b.isLt
    omega)
  have hpair : (⟨1, by omega⟩ : Fin n).val = (⟨0, by omega⟩ : Fin n).val + 1 := rfl
  refine IsGateProduct.of_mem_supportedOperators (b := Geometry.pathCell hpair) hU
    (ManyBody.mem_supportedOperators_iff.mpr
      ⟨fun σ τ ⟨v, _, hne⟩ => absurd (hsub _ _) hne, fun σ τ σ' τ' _ _ _ _ => ?_⟩)
  rw [show σ = σ' from funext fun v => hsub _ _, show τ = τ' from funext fun v => hsub _ _]

/-- **The staircase circuit of an isometric chain.** Let `r ≥ 2`, and let `enc` encode the bond
levels `Fin D'` injectively in the configurations of `r` sites. There are `K₀`, `K₁` such
that for every `n ≥ r` and every chain `Q₀, …, Q_{n-1}` with bonds `b₀ = 1, b₁, …, b_n`, every
site vanishing on the rows beyond its left bond and isometric on its right bond, there is a
unitary `U` on `n` sites, a product of at most `K₀ + (n - r) K₁` gates on neighbouring sites,
with `⟨σ| U |0 ⋯ 0, enc(x)⟩ = (Q₀(σ₀) ⋯ Q_{n-1}(σ_{n-1}))_{0x}` for every `x < b_n`.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1: the isometries `V_i` of
eq. (14) applied in sequence, each acting on the bond register and one site. -/
theorem exists_staircase (hd : 0 < d) {r D' : ℕ} (hr : 2 ≤ r) (hD' : 0 < D')
    {enc : Fin D' → Cfg d r} (henc : Function.Injective enc) :
    ∃ K₀ K₁ : ℕ, ∀ n, r ≤ n → ∀ (b : Fin (n + 1) → ℕ) (Q : MPSChainTensor d D' n),
      b 0 = 1 → (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) →
      (∀ p, IsIsometryOn (b p.succ) (Q p)) →
      ∃ U : Matrix (Cfg d n) (Cfg d n) ℂ,
        IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (K₀ + (n - r) * K₁) U ∧
        ∀ x : Fin D', x.val < b (Fin.last n) → ∀ σ,
          U σ (inputCfg hd n (enc x)) = eval Q σ ⟨0, hD'⟩ x := by
  refine ⟨12 * (d ^ (r + 1)) ^ 5, 12 * (d ^ (r + 1)) ^ 5, fun n hn b Q hb0 hrow hiso => ?_⟩
  obtain ⟨U, hU, hUQ⟩ :=
    exists_staircase_isWindowProduct hd hD' henc n hn (by omega) b Q hb0 hrow hiso
  have hU1 : IsGateProduct (Geometry.window n (r + 1)) (max 1 (n - r)) U := by
    have h := hU 1 (one_mem _) (one_mem _)
    rwa [mul_one] at h
  refine ⟨U, ?_, hUQ⟩
  have hpath : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n))
      (12 * (d ^ (r + 1)) ^ 5 * max 1 (n - r)) U := by
    rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · exact (isGateProduct_one_of_le_one (by omega) (by omega) hU1.mem_unitaryGroup).mono
        (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (pow_pos hd _) _))
          (lt_max_of_lt_left one_pos)))
    · have h := hU1.of_window (α := Fin d) (by rw [Fintype.card_fin]; exact hd2) (by omega)
      rwa [Fintype.card_fin] at h
  refine hpath.mono ?_
  calc 12 * (d ^ (r + 1)) ^ 5 * max 1 (n - r) ≤ 12 * (d ^ (r + 1)) ^ 5 * (1 + (n - r)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 12 * (d ^ (r + 1)) ^ 5 + (n - r) * (12 * (d ^ (r + 1)) ^ 5) := by ring

end MPSPreparation
