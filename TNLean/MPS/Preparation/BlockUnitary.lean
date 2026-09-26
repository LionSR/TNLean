/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.Staircase

/-!
# The unitary of one block as a circuit of depth `O(q)`

In the preparation of arXiv:2307.01696 the `q` sites of a block carry, before the block unitary
is applied, the left index `l` on the first `r₁` sites, the right index `r` on the last `r₁`
sites, and `|0⟩` in between (eq. (10) and Fig. 1, with `D ≤ d^{r₁}`). The staircase circuit
(`MPSPreparation.exists_staircase`) needs the pair `(l, r)` on the last `2 r₁` sites; SWAP gates
move the first `r₁` sites next to the last ones: "the inputs of the unitary ... are separated
by `O(q)` sites, which requires one to implement SWAP gates" (paragraph "The sequential-RG
circuit").

The result (`MPSPreparation.exists_blockUnitary`) is a unitary `U` on `q ≥ 3 r₁` sites with
`⟨σ| U |l, 0 ⋯ 0, r⟩ = (Q₀(σ₀) ⋯ Q_{q-1}(σ_{q-1}))_{0,(l,r)}` for an isometric chain `Q`
whose last bond is `D²`, and `U` is a product of at most `C q` gates on neighbouring sites
with `C` depending only on `d`, `D` and `r₁`.
-/

open Matrix MPSTensor
open MPSChainTensor (eval)
open scoped BigOperators

namespace MPSPreparation

variable {d D : ℕ}

/-! ### Two registers side by side -/

/-- The configuration of `r₁ + r₁` sites carrying `dig a` on the first `r₁` sites and `dig b`
on the last `r₁`. -/
def twoCfg {r₁ : ℕ} (dig : Fin D → Cfg d r₁) (a b : Fin D) : Cfg d (r₁ + r₁) :=
  fun k => if h : k.val < r₁ then dig a ⟨k.val, h⟩ else dig b ⟨k.val - r₁, by omega⟩

theorem twoCfg_injective {r₁ : ℕ} {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    {a b a' b' : Fin D} (h : twoCfg dig a b = twoCfg dig a' b') : a = a' ∧ b = b' := by
  constructor
  · refine hdig (funext fun j => ?_)
    have := congrFun h ⟨j.val, by omega⟩
    simpa [twoCfg, j.isLt] using this
  · refine hdig (funext fun j => ?_)
    have := congrFun h ⟨r₁ + j.val, by omega⟩
    simp only [twoCfg, show ¬(r₁ + j.val < r₁) by omega, dite_false] at this
    convert this using 2 <;> ext <;> simp

/-- The configuration of a block of `q` sites before its unitary: `dig l` on the first `r₁`
sites, `dig r` on the last `r₁` sites and `0` elsewhere.

arXiv:2307.01696, eq. (10) and Fig. 1 (the legs `L_k`, `C_k`, `R_k` of a block, the central
sites `C_k` in `|0⟩`). -/
def blockInputCfg (hd : 0 < d) {r₁ : ℕ} (q : ℕ) (dig : Fin D → Cfg d r₁) (l r : Fin D) :
    Cfg d q :=
  fun p => if h : p.val < r₁ then dig l ⟨p.val, h⟩
    else if h' : q - r₁ ≤ p.val then dig r ⟨p.val - (q - r₁), by omega⟩ else ⟨0, hd⟩

theorem blockInputCfg_injective (hd : 0 < d) {r₁ q : ℕ} (hq : r₁ + r₁ ≤ q)
    {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig) {l r l' r' : Fin D}
    (h : blockInputCfg hd q dig l r = blockInputCfg hd q dig l' r') : l = l' ∧ r = r' := by
  constructor
  · refine hdig (funext fun j => ?_)
    have := congrFun h ⟨j.val, by omega⟩
    simpa [blockInputCfg, j.isLt] using this
  · refine hdig (funext fun j => ?_)
    have := congrFun h ⟨q - r₁ + j.val, by omega⟩
    simp only [blockInputCfg, show ¬(q - r₁ + j.val < r₁) by omega,
      show q - r₁ ≤ q - r₁ + j.val by omega, dite_false, dite_true] at this
    convert this using 2 <;> ext <;> simp

/-! ### Permutations of sites -/

theorem permOp_mul {n : ℕ} (τ₁ τ₂ : Equiv.Perm (Fin n)) :
    permOp (d := d) (τ₁ * τ₂) = permOp τ₁ * permOp τ₂ := by
  ext x y
  simp only [permOp, of_apply, mul_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (x ∘ τ₁)]
  simp only [Finset.mem_univ, ite_true, Equiv.Perm.coe_mul]
  rfl

@[simp] theorem permOp_one {n : ℕ} : permOp (d := d) (1 : Equiv.Perm (Fin n)) = 1 := by
  ext x y
  simp only [permOp, of_apply, Equiv.Perm.coe_one, Function.comp_id, one_apply, eq_comm]

/-- A SWAP of two sites of the open chain of `n` sites is a product of at most `2n` gates on
neighbouring sites. -/
theorem isPairProduct_permOp_swap {n : ℕ} (i i' : Fin n) :
    IsPairProduct d n (2 * n) (permOp (Equiv.swap i i')) := by
  by_cases h : i = i'
  · rw [h, Equiv.swap_self, Equiv.refl_eq_one, permOp_one]
    exact IsPairProduct.one _
  · rw [permOp_swap_eq_embedOp h]
    exact isPairProduct_embedOp_pairSites h (permOp_mem_unitary _)

/-- The permutation exchanging the sites `i` and `a + i` for every `i < j`. -/
def routePerm (n a : ℕ) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | j + 1 => routePerm n a j *
      if h : a + j < n then Equiv.swap ⟨j, by omega⟩ ⟨a + j, h⟩ else 1

theorem routePerm_apply {n a : ℕ} :
    ∀ j, j ≤ a → a + j ≤ n → ∀ p : Fin n, (routePerm n a j p).val =
      if p.val < j then a + p.val else if a ≤ p.val ∧ p.val < a + j then p.val - a else p.val
  | 0, _, _, p => by simp [routePerm]
  | j + 1, hja, hjn, p => by
    have ih := routePerm_apply j (by omega) (by omega)
    rw [routePerm, dif_pos (by omega), Equiv.Perm.coe_mul, Function.comp_apply]
    by_cases hp1 : p.val = j
    · have : p = ⟨j, by omega⟩ := Fin.ext hp1
      rw [this, Equiv.swap_apply_left, ih]
      simp only
      split_ifs <;> omega
    by_cases hp2 : p.val = a + j
    · have : p = ⟨a + j, by omega⟩ := Fin.ext hp2
      rw [this, Equiv.swap_apply_right, ih]
      simp only
      split_ifs <;> omega
    rw [Equiv.swap_apply_of_ne_of_ne (fun h => hp1 (congrArg Fin.val h))
      (fun h => hp2 (congrArg Fin.val h)), ih]
    split_ifs <;> omega

theorem isPairProduct_permOp_routePerm (n a : ℕ) :
    ∀ j, IsPairProduct d n (j * (2 * n)) (permOp (routePerm n a j))
  | 0 => by simpa [routePerm] using IsPairProduct.one (d := d) (n := n) 0
  | j + 1 => by
    rw [routePerm, permOp_mul, Nat.succ_mul]
    refine (isPairProduct_permOp_routePerm n a j).mul ?_
    split_ifs with h
    · exact isPairProduct_permOp_swap _ _
    · simpa using IsPairProduct.one (d := d) (n := n) (2 * n)

/-- Moving the left register next to the right one: the configuration `|0 ⋯ 0, l, r⟩`, read
through the routing permutation, is `|l, 0 ⋯ 0, r⟩`. -/
theorem inputCfg_comp_routePerm (hd : 0 < d) {r₁ q : ℕ} (hq : 3 * r₁ ≤ q)
    (dig : Fin D → Cfg d r₁) (l r : Fin D) :
    inputCfg hd q (twoCfg dig l r) ∘ routePerm q (q - (r₁ + r₁)) r₁ =
      blockInputCfg hd q dig l r := by
  funext p
  have hτ := routePerm_apply (n := q) (a := q - (r₁ + r₁)) r₁ (by omega) (by omega) p
  simp only [Function.comp_apply, inputCfg, blockInputCfg, twoCfg]
  set t := routePerm q (q - (r₁ + r₁)) r₁ p with ht
  by_cases h1 : p.val < r₁
  · rw [if_pos h1] at hτ
    rw [dif_pos (by omega), dif_pos (by omega), dif_pos h1]
    congr 1; ext; simp; omega
  by_cases h2 : q - (r₁ + r₁) ≤ p.val ∧ p.val < q - (r₁ + r₁) + r₁
  · rw [if_neg h1, if_pos h2] at hτ
    rw [dif_neg (by omega), dif_neg h1, dif_neg (by omega)]
  · rw [if_neg h1, if_neg h2] at hτ
    by_cases h3 : q - r₁ ≤ p.val
    · rw [dif_pos (by omega), dif_neg (by omega), dif_neg h1, dif_pos h3]
      congr 1; ext; simp; omega
    · rw [dif_neg (by omega), dif_neg h1, dif_neg h3]

/-! ### The block unitary -/

/-- **The unitary of a block.** Let `D ≤ d^{r₁}` through an injective `dig`, `r₁ ≥ 1`. There is
`C` such that for every `q ≥ 3 r₁` and every isometric chain `Q₀, …, Q_{q-1}` with bonds
`b₀ = 1`, `b_q = D²` (as produced by the sequential factorization), there is a unitary `U` on
`q` sites, a product of at most `C q` gates on neighbouring sites, with
`⟨σ| U |l, 0 ⋯ 0, r⟩ = (Q₀(σ₀) ⋯ Q_{q-1}(σ_{q-1}))_{0,(l,r)}`.

arXiv:2307.01696, paragraph "The sequential-RG circuit": each block unitary is a staircase of
the isometries of eq. (14), with SWAP gates bringing its two inputs together, of depth `O(q)`. -/
theorem exists_blockUnitary (hd : 0 < d) {r₁ : ℕ} (hr₁ : 1 ≤ r₁) {dig : Fin D → Cfg d r₁}
    (hdig : Function.Injective dig) (hD : 0 < D) :
    ∃ C : ℕ, ∀ q, 3 * r₁ ≤ q → ∀ (b : Fin (q + 1) → ℕ) (Q : MPSChainTensor d (D * D) q),
      b 0 = 1 → b (Fin.last q) = D * D →
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) →
      (∀ p, IsIsometryOn (b p.succ) (Q p)) →
      ∃ U : Matrix (Cfg d q) (Cfg d q) ℂ, IsPairProduct d q (C * q) U ∧
        ∀ l r σ, U σ (blockInputCfg hd q dig l r) =
          eval Q σ ⟨0, Nat.mul_pos hD hD⟩ (finProdFinEquiv (l, r)) := by
  classical
  set enc : Fin (D * D) → Cfg d (r₁ + r₁) := fun x =>
    twoCfg dig (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 with henc
  have hencinj : Function.Injective enc := fun x x' h => by
    obtain ⟨h1, h2⟩ := twoCfg_injective hdig h
    exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)
  obtain ⟨K₀, K₁, hK⟩ := exists_staircase hd (r := r₁ + r₁) (by omega) (Nat.mul_pos hD hD)
    hencinj
  refine ⟨K₀ + K₁ + 2 * r₁, fun q hq b Q hb0 hbq hrow hiso => ?_⟩
  obtain ⟨U, hU, hUQ⟩ := hK q (by omega) b Q hb0 hrow hiso
  set τ := routePerm q (q - (r₁ + r₁)) r₁
  refine ⟨U * permOp τ, ?_, fun l r σ => ?_⟩
  · refine (hU.mul (isPairProduct_permOp_routePerm q _ r₁)).mono ?_
    have h1 : (q - (r₁ + r₁)) * K₁ ≤ q * K₁ := Nat.mul_le_mul_right _ (by omega)
    have h2 : K₀ ≤ q * K₀ := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  · have hin := inputCfg_comp_routePerm hd hq dig l r
    rw [mul_apply, Finset.sum_eq_single (inputCfg hd q (twoCfg dig l r))]
    · rw [permOp, of_apply, if_pos hin.symm, mul_one, show twoCfg dig l r =
        enc (finProdFinEquiv (l, r)) by simp [henc]]
      exact hUQ _ (by rw [hbq]; exact (finProdFinEquiv (l, r)).isLt) σ
    · intro z _ hz
      rw [permOp, of_apply, if_neg, mul_zero]
      intro h
      apply hz
      funext p
      have := congrFun (h.symm.trans hin.symm) (τ.symm p)
      simpa using this
    · simp

end MPSPreparation
