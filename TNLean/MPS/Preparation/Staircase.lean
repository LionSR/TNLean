/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometryUnitaryExtension
import TNLean.MPS.Preparation.IsometricChain
import TNLean.MPS.Preparation.UnitaryGates

/-!
# The staircase circuit of an isometric chain

Let `Q₀, …, Q_{n-1}` be an isometric open chain with bond space `ℂ^{D'}`, as produced by the
sequential factorization (`MPSPreparation.exists_isometric_chain_polarIsoMatrix`), and let the
bond levels be encoded injectively in the configurations of `r ≥ 2` sites. Then there is a
unitary `U` on the open chain of `n ≥ r` sites with
`⟨σ| U |0 ⋯ 0, enc(x)⟩ = (Q₀(σ₀) ⋯ Q_{n-1}(σ_{n-1}))_{0x}`, where the encoded input occupies
the last `r` sites, and `U` is a product of at most `K₀ + (n - r) K₁` gates on neighbouring
sites, with `K₀`, `K₁` depending only on `d` and `r` (`MPSPreparation.exists_staircase`).

The unitary is the staircase of arXiv:2307.01696, paragraph "The sequential-RG circuit" and
Fig. 1: the bond register moves one site to the left at each step, the unitary extending
`Q_p` acts on the `r` register sites and one fresh site in `|0⟩` and leaves the physical output
on the rightmost of them, and the last `r` isometries act on the final position of the
register. Each step acts on `r + 1` sites, so it is a product of a bounded number of two-site
gates (`MPSPreparation.exists_isPairProduct`).
-/

open Matrix MPSTensor
open MPSChainTensor (eval eval_succ')
open scoped BigOperators

namespace MPSPreparation

variable {d : ℕ}

/-! ### Configurations with the input on the last sites -/

/-- The configuration of `n` sites carrying `w` on the last `r` sites and `0` elsewhere. -/
def inputCfg (hd : 0 < d) {r : ℕ} (n : ℕ) (w : Cfg d r) : Cfg d n :=
  fun i => if h : n - r ≤ i.val then w ⟨i.val - (n - r), by omega⟩ else ⟨0, hd⟩

theorem inputCfg_self (hd : 0 < d) {r : ℕ} (w : Cfg d r) : inputCfg hd r w = w := by
  funext i
  simp only [inputCfg, Nat.sub_self, zero_le, dite_true, Nat.sub_zero]

theorem inputCfg_injective (hd : 0 < d) {r n : ℕ} (hr : r ≤ n) :
    Function.Injective (inputCfg (d := d) hd (r := r) n) := by
  intro w w' h
  funext j
  have := congrFun h ⟨n - r + j.val, by omega⟩
  simp only [inputCfg, show n - r ≤ n - r + j.val by omega, dite_true] at this
  convert this using 2 <;> ext <;> simp

/-! ### Sums over extensions by zero -/

theorem sum_extend_zero {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] {s : α → β}
    (hs : Function.Injective s) (f : α → ℂ) (H : β → ℂ → ℂ) (hH : ∀ u, H u 0 = 0) :
    ∑ u, H u (Function.extend s f 0 u) = ∑ p, H (s p) (f p) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image s))]
  · rw [Finset.sum_image fun p _ p' _ h => hs h]
    exact Finset.sum_congr rfl fun p _ => by rw [hs.extend_apply]
  · intro u _ hu
    have : ¬∃ p, s p = u := by simpa using hu
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, hH]

theorem eq_extend_of_agreeOff {m n : ℕ} {e : Fin m → Fin n} (he : Function.Injective e)
    {y z : Cfg d n} (h : AgreeOff e y z) : z = Function.extend e (z ∘ e) y := by
  funext i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [he.extend_apply]; rfl
  · rw [Function.extend_apply' _ _ _ hi]
    exact (h i fun j hj => hi ⟨j, hj⟩).symm

/-- The matrix elements of `Y (X ⊗ 1)`, as a sum over the configurations of the placed sites. -/
theorem mul_embedOp_apply {m n : ℕ} {e : Fin m → Fin n} (he : Function.Injective e)
    (Y : Matrix (Cfg d n) (Cfg d n) ℂ) (X : Matrix (Cfg d m) (Cfg d m) ℂ) (x y : Cfg d n) :
    (Y * embedOp e X) x y = ∑ u, Y x (Function.extend e u y) * X u (y ∘ e) := by
  rw [mul_apply, ← sum_agreeOff he y fun u => Y x (Function.extend e u y) * X u (y ∘ e)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [embedOp_apply]
  by_cases h : AgreeOff e y z
  · rw [ite_eq_left h.symm, ite_eq_left h, ← eq_extend_of_agreeOff he h]
  · rw [ite_eq_right fun h' => h h'.symm, ite_eq_right h, mul_zero]

/-! ### One step of the staircase -/

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
  set s : Fin D' × Fin d → Cfg d (r + 1) := fun p => Fin.snoc (enc p.1) p.2 with hs
  have hsi : Function.Injective s := by
    rintro ⟨α, i⟩ ⟨α', i'⟩ h
    have h1 := congrFun h (Fin.last r)
    simp only [hs, Fin.snoc_last] at h1
    have h2 : enc α = enc α' := funext fun j => by
      have := congrFun h j.castSucc
      simpa [hs, Fin.snoc_castSucc] using this
    rw [henc h2, h1]
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
      ∃ U : Matrix (Cfg d n) (Cfg d n) ℂ, IsPairProduct d n (K₀ + (n - r) * K₁) U ∧
        ∀ x : Fin D', x.val < b (Fin.last n) → ∀ σ,
          U σ (inputCfg hd n (enc x)) = eval Q σ ⟨0, hD'⟩ x := by
  classical
  obtain ⟨K₀, hK₀⟩ := exists_isPairProduct (n := r) hd (by omega)
  obtain ⟨K₁, hK₁⟩ := exists_isPairProduct (n := r + 1) hd (by omega)
  refine ⟨K₀, K₁, fun n hn => ?_⟩
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
        · simp [V, mulVec_single_one]
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
            simp [Pi.single_apply, this, hxx]
        · intro β _ hβ; simp [Pi.single_apply, hβ]
        · simp
      rw [mul_apply, one_apply]
      simp only [conjTranspose_apply]
      rw [h, hr]
    let emb : κ ↪ Cfg d r := ⟨fun x => inputCfg hd r (enc x.1), fun x x' h => Subtype.ext
      (henc (by simpa [inputCfg_self] using h))⟩
    obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
    exact ⟨U, by simpa using hK₀ U hU, fun x hx σ => (hUV σ ⟨x, hx⟩).trans (of_apply _ _ _)⟩
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
    have hcs : Function.Injective (Fin.castSucc : Fin n → Fin (n + 1)) := Fin.castSucc_injective n
    refine ⟨embedOp Fin.castSucc U' * embedOp win W, ?_, ?_⟩
    · have h1 := hU'.embedOp (a := 0) hcs (fun i => by simp)
      have h2 := (hK₁ W hWu).embedOp (a := n - r) hwini (fun i => rfl)
      refine (h1.mul h2).mono (le_of_eq ?_)
      rw [show n + 1 - r = (n - r) + 1 by omega]
      ring
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
      rw [mul_embedOp_apply hwini, hyw]
      simp_rw [hW x hx]
      rw [sum_extend_zero (fun p q h => by
          obtain ⟨α, i⟩ := p; obtain ⟨α', i'⟩ := q
          have h1 := congrFun h (Fin.last r)
          simp only [Fin.snoc_last] at h1
          have h2 : enc α = enc α' := funext fun j => by
            have := congrFun h j.castSucc
            simpa [Fin.snoc_castSucc] using this
          rw [henc h2, h1]) _ _ (fun u => mul_zero _)]
      -- evaluate the first factor on the extended configurations
      have hlast : Fin.last n = win (Fin.last r) := by ext; simp [hwin]; omega
      have hext : ∀ (α : Fin D') (i : Fin d),
          (embedOp Fin.castSucc U') σ
            (Function.extend win (Fin.snoc (enc α) i : Cfg d (r + 1)) y) =
          if σ (Fin.last n) = i then U' (σ ∘ Fin.castSucc) (inputCfg hd n (enc α)) else 0 := by
        intro α i
        set z := Function.extend win (Fin.snoc (enc α) i : Cfg d (r + 1)) y with hz
        have hzl : z (Fin.last n) = i := by
          rw [hz, hlast, hwini.extend_apply, Fin.snoc_last]
        have hzc : z ∘ Fin.castSucc = inputCfg hd n (enc α) := by
          funext k
          simp only [Function.comp_apply, hz]
          by_cases hk : n - r ≤ k.val
          · have hkw : k.castSucc = win (⟨k.val - (n - r), by omega⟩ : Fin r).castSucc := by
              ext; simp [hwin]; omega
            rw [hkw, hwini.extend_apply, Fin.snoc_castSucc, inputCfg, dite_eq_left hk]
          · rw [Function.extend_apply' _ _ _ (by
              rintro ⟨j, hj⟩
              have := congrArg Fin.val hj
              simp [hwin] at this; omega), hy, inputCfg, inputCfg, dite_eq_right (by simp; omega),
              dite_eq_right hk]
        have hag : AgreeOff Fin.castSucc σ z ↔ σ (Fin.last n) = i := by
          rw [← hzl]
          constructor
          · intro h; exact h _ fun j hj => Fin.castSucc_ne_last j hj
          · intro h k hk
            have : k = Fin.last n := by
              by_contra hne
              exact hk (k.castPred hne) (Fin.castSucc_castPred k hne)
            rw [this]; exact h
        rw [embedOp_apply, hzc]
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

end MPSPreparation
