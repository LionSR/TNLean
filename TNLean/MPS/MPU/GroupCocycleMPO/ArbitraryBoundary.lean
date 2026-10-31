/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.GroupCocycleMPO

/-!
# Group matrix product operators from a three-cocycle: the arbitrary-boundary operators

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), subsubsection
"Arbitrary boundary condition case", `Papers/2203.12563/REsubmission.tex` lines 2003–2096: for a
finite group `G` and a three-cocycle `ω`, every site carries the space `ℂ[G] ⊗ ℂ[G]` of two half
sites `[i]_l`, `[i]_r`, and the block `T_g` of bond dimension `|G|` has the nonzero entries
`ω(g, l, l⁻¹ k)` at the bond labels `k` (left) and `l` (right), the input `(k, l)` and the output
`(g k, g l)` (lines 2005–2024). The periodic operator `O_e` of the identity block is the
projector `⨂_i 𝒫^{[i]_r,[i+1]_l}`, `𝒫 = ∑_g |g,g⟩⟨g,g|` (lines 2073–2092), and "these MPOs
satisfy `O_g O_h = O_{gh}` and `O_g† = O_{g⁻¹}`, so they form a representation of `G` on the
subspace `O_e (ℂ[G] ⊗ ℂ[G])^{⊗ n}`" (line 2096). The periodic operators `U_g` of
`MPOTensor.GroupCocycle.tensor` are obtained from `O_g` by the isometry
`Γ : |g,g⟩_{[i]_r,[i+1]_l} ↦ |g⟩_i` of lines 2200–2203.

**Formalized here.** The arbitrary-boundary tensor `T_g` (`boundaryTensor`), and, on every
nonempty periodic chain, the factorization `O_g = Γ† U_g Γ` through the embedding
`Γ† : |t⟩ ↦ ⨂_i |t_i, t_{i+1}⟩` (`halfSiteEmbedding`), with `Γ Γ† = 1`. From it: `O_e = Γ† Γ` is
an orthogonal projector whose range is the subspace where the right half of every site agrees with
the left half of the next (`⨂_i 𝒫`), `O_g O_h = O_{gh}` (as operators on the whole space, so in
particular on the range of `O_e`), `O_g† = O_{g⁻¹}` for unit-modulus `ω`, and
`U_g = Γ O_g Γ†`, the periodic representation of lines 2200–2205 with the single shift per site of
`MPOTensor.GroupCocycle.tensor` (see `docs/paper-gaps/glm23_pbc_group_mpo_single_shift.tex`).

## Main definitions

* `MPOTensor.GroupCocycle.boundaryTensor`: the arbitrary-boundary tensor `T_g`.
* `MPOTensor.GroupCocycle.halfSiteConfig`: the configuration `i ↦ (t_i, t_{i+1})` of half sites.
* `MPOTensor.GroupCocycle.halfSiteEmbedding`: the embedding `Γ†`.

## Main results

* `MPOTensor.GroupCocycle.mpo_boundaryTensor`: `O_g = Γ† U_g Γ`.
* `MPOTensor.GroupCocycle.mpo_boundaryTensor_one_apply`: `O_e = ⨂_i 𝒫^{[i]_r,[i+1]_l}`.
* `MPOTensor.GroupCocycle.mpo_boundaryTensor_one_mul_self`,
  `MPOTensor.GroupCocycle.isHermitian_mpo_boundaryTensor_one`: `O_e` is an orthogonal projector.
* `MPOTensor.GroupCocycle.mpo_boundaryTensor_mul`: `O_g O_h = O_{gh}`.
* `MPOTensor.GroupCocycle.mpo_boundaryTensor_conjTranspose`: `O_g† = O_{g⁻¹}`.
* `MPOTensor.GroupCocycle.mpo_tensor_eq_halfSiteEmbedding`: `U_g = Γ O_g Γ†`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
-/

noncomputable section

open scoped BigOperators Matrix

namespace MPOTensor.GroupCocycle

open TNLean.Algebra

variable {G : Type} [Group G] {n : ℕ} (e : G ≃ Fin n)

/-! ### The tensor -/

/-- **The arbitrary-boundary tensor `T_g`**: the physical index of a site is the pair `(k, l)` of
its two half sites, encoded in `Fin (n * n)`; the entry at the bond labels `k`, `l` is
`ω(g, l, l⁻¹ k)` when the input is `(k, l)` and the output is `(g k, g l)`, and zero otherwise.
The first physical index is the output row, the second the input column.

Source: arXiv:2203.12563, lines 2005–2024. -/
def boundaryTensor (ω : ScalarThreeCochain G) (g : G) : MPOTensor (n * n) n :=
  fun i j ↦ Matrix.of fun k l ↦
    if j = finProdFinEquiv (k, l) ∧ i = finProdFinEquiv (siteShift e g k, siteShift e g l) then
      (ω g (e.symm l) ((e.symm l)⁻¹ * e.symm k) : ℂ)
    else 0

theorem boundaryTensor_apply (ω : ScalarThreeCochain G) (g : G) (i j : Fin (n * n))
    (k l : Fin n) :
    boundaryTensor e ω g i j k l =
      if j = finProdFinEquiv (k, l) ∧ i = finProdFinEquiv (siteShift e g k, siteShift e g l) then
        (ω g (e.symm l) ((e.symm l)⁻¹ * e.symm k) : ℂ)
      else 0 := rfl

/-! ### The embedding of periodic configurations into pairs of half sites -/

variable {N : ℕ} [NeZero N]

/-- The configuration of half sites `i ↦ (t_i, t_{i+1})`: the right half of site `i` and the left
half of site `i + 1` both carry the label `t_{i+1}`. -/
def halfSiteConfig (t : Fin N → Fin n) : Fin N → Fin (n * n) :=
  fun i ↦ finProdFinEquiv (t i, t (i + 1))

theorem halfSiteConfig_injective : Function.Injective (halfSiteConfig (N := N) (n := n)) := by
  intro t t' h
  funext i
  simpa [halfSiteConfig] using congrArg (fun s ↦ (finProdFinEquiv.symm (s i)).1) h

/-- A configuration of half sites is a pair configuration exactly when the right half of every
site agrees with the left half of the next: the support of `⨂_i 𝒫^{[i]_r,[i+1]_l}`
(arXiv:2203.12563, lines 2073–2092). -/
theorem exists_eq_halfSiteConfig_iff (s : Fin N → Fin (n * n)) :
    (∃ t, s = halfSiteConfig t) ↔
      ∀ i, (finProdFinEquiv.symm (s i)).2 = (finProdFinEquiv.symm (s (i + 1))).1 := by
  constructor
  · rintro ⟨t, rfl⟩ i
    simp [halfSiteConfig]
  · intro h
    refine ⟨fun i ↦ (finProdFinEquiv.symm (s i)).1, funext fun i ↦ ?_⟩
    rw [halfSiteConfig, ← h i, Prod.mk.eta, Equiv.apply_symm_apply]

variable (n N) in
/-- **The embedding `Γ†`**: the matrix sending the basis vector of a periodic configuration `t`
of `ℂ[G]^{⊗ N}` to the basis vector of the configuration of half sites `i ↦ (t_i, t_{i+1})`. It is
the adjoint of the isometry `Γ : |g,g⟩_{[i]_r,[i+1]_l} ↦ |g⟩_i` of arXiv:2203.12563,
lines 2200–2203. -/
def halfSiteEmbedding : Matrix (Fin N → Fin (n * n)) (Fin N → Fin n) ℂ :=
  Matrix.of fun s t ↦ if s = halfSiteConfig t then 1 else 0

theorem halfSiteEmbedding_apply (s : Fin N → Fin (n * n)) (t : Fin N → Fin n) :
    halfSiteEmbedding n N s t = if s = halfSiteConfig t then 1 else 0 := rfl

theorem conjTranspose_halfSiteEmbedding_apply (t : Fin N → Fin n) (s : Fin N → Fin (n * n)) :
    (halfSiteEmbedding n N)ᴴ t s = if s = halfSiteConfig t then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, halfSiteEmbedding_apply]
  split_ifs <;> simp

/-- **`Γ` is an isometry onto its range**: `Γ Γ† = 1`. -/
theorem conjTranspose_halfSiteEmbedding_mul :
    (halfSiteEmbedding n N)ᴴ * halfSiteEmbedding n N = 1 := by
  ext t t'
  simp only [Matrix.mul_apply, conjTranspose_halfSiteEmbedding_apply, halfSiteEmbedding_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    halfSiteConfig_injective.eq_iff, Matrix.one_apply]

/-- The entries of `Γ† Γ`: the diagonal projector onto the pair configurations. -/
theorem halfSiteEmbedding_mul_conjTranspose_apply (s s' : Fin N → Fin (n * n)) :
    (halfSiteEmbedding n N * (halfSiteEmbedding n N)ᴴ) s s' =
      if s = s' ∧ ∃ t, s' = halfSiteConfig t then 1 else 0 := by
  simp only [Matrix.mul_apply, conjTranspose_halfSiteEmbedding_apply, halfSiteEmbedding_apply,
    mul_ite, mul_one, mul_zero]
  by_cases h : ∃ t, s' = halfSiteConfig t
  · obtain ⟨t, rfl⟩ := h
    rw [Fintype.sum_eq_single t fun t' ht' ↦ by
      rw [ite_eq_right fun h ↦ ht' (halfSiteConfig_injective h).symm]]
    simp
  · rw [Finset.sum_eq_zero fun t _ ↦ by rw [ite_eq_right fun h' ↦ h ⟨t, h'⟩]]
    simp [h]

/-! ### The periodic operators -/

/-- **`O_g = Γ† U_g Γ`**: the periodic operator of the arbitrary-boundary tensor `T_g` is the
periodic operator `U_g` of `MPOTensor.GroupCocycle.tensor`, carried to the pair configurations
by `Γ†` and vanishing on their complement.

Source: arXiv:2203.12563, lines 2094 (`O_g` as a product of local gates and the projectors
`𝒫^{[i]_r,[i+1]_l}`) and 2200–2203 (the passage from `O_g` to `U_g` by `Γ`). The closed bond
configuration of `T_g` is forced by the input: the bond to the left of site `i` is the left half
of its input, which equals the right half of the input of site `i - 1`. -/
theorem mpo_boundaryTensor (ω : ScalarThreeCochain G) (g : G) :
    mpo (boundaryTensor e ω g) N =
      halfSiteEmbedding n N * mpo (tensor e ω g) N * (halfSiteEmbedding n N)ᴴ := by
  have key : ∀ (s t : Fin N → Fin (n * n)) (b : Fin N → Fin n),
      ∏ i, boundaryTensor e ω g (s i) (t i) (b i) (b (i + 1)) =
        if t = halfSiteConfig b ∧ s = halfSiteConfig (shift e g N b) then
          ∏ i, (ω g (e.symm (b (i + 1))) ((e.symm (b (i + 1)))⁻¹ * e.symm (b i)) : ℂ)
        else 0 := fun s t b ↦ by
    by_cases h : t = halfSiteConfig b ∧ s = halfSiteConfig (shift e g N b)
    · rw [ite_eq_left h]
      exact Finset.prod_congr rfl fun i _ ↦ by
        rw [boundaryTensor_apply]
        exact ite_eq_left ⟨congrFun h.1 i, congrFun h.2 i⟩
    · rw [ite_eq_right h]
      have : ∃ i, ¬ (t i = halfSiteConfig b i ∧ s i = halfSiteConfig (shift e g N b) i) := by
        by_contra hc
        push Not at hc
        exact h ⟨funext fun i ↦ (hc i).1, funext fun i ↦ (hc i).2⟩
      obtain ⟨i, hi⟩ := this
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [boundaryTensor_apply]
      exact ite_eq_right hi
  ext s t
  rw [mpo_apply_eq_sum_cyclic]
  simp only [key, Matrix.mul_apply, conjTranspose_halfSiteEmbedding_apply, halfSiteEmbedding_apply,
    mpo_tensor_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Fintype.sum_eq_single (shift e g N b) fun a ha ↦ by rw [ite_eq_right ha]]
  by_cases ht : t = halfSiteConfig b <;> by_cases hs : s = halfSiteConfig (shift e g N b) <;>
    simp [ht, hs]

/-- **The identity operator is `⨂_i 𝒫^{[i]_r,[i+1]_l}`** for a normalized cocycle: `O_e` is the
diagonal projector onto the configurations of half sites in which the right half of every site
agrees with the left half of the next.

Source: arXiv:2203.12563, lines 2073–2092. -/
theorem mpo_boundaryTensor_one_apply {ω : ScalarThreeCochain G}
    (hn : ScalarThreeCochain.IsNormalized ω) (s t : Fin N → Fin (n * n)) :
    mpo (boundaryTensor e ω 1) N s t =
      if s = t ∧ ∀ i, (finProdFinEquiv.symm (t i)).2 = (finProdFinEquiv.symm (t (i + 1))).1 then
        1
      else 0 := by
  rw [mpo_boundaryTensor, mpo_tensor_one e hn, Matrix.mul_one,
    halfSiteEmbedding_mul_conjTranspose_apply]
  simp only [exists_eq_halfSiteConfig_iff]

/-- `O_e = Γ† Γ` for a normalized cocycle. -/
theorem mpo_boundaryTensor_one {ω : ScalarThreeCochain G}
    (hn : ScalarThreeCochain.IsNormalized ω) :
    mpo (boundaryTensor e ω 1) N = halfSiteEmbedding n N * (halfSiteEmbedding n N)ᴴ := by
  rw [mpo_boundaryTensor, mpo_tensor_one e hn, Matrix.mul_one]

/-- **`O_e` is a projector** (arXiv:2203.12563, line 2073: "the PBC MPO corresponding to the
trivial element `e` is a projector"). -/
theorem mpo_boundaryTensor_one_mul_self {ω : ScalarThreeCochain G}
    (hn : ScalarThreeCochain.IsNormalized ω) :
    mpo (boundaryTensor e ω 1) N * mpo (boundaryTensor e ω 1) N =
      mpo (boundaryTensor e ω 1) N := by
  rw [mpo_boundaryTensor_one e hn, Matrix.mul_assoc, ← Matrix.mul_assoc (halfSiteEmbedding n N)ᴴ,
    conjTranspose_halfSiteEmbedding_mul, Matrix.one_mul]

/-- **`O_e` is an orthogonal projector**: it is Hermitian (arXiv:2203.12563, lines 2073–2092,
where `𝒫 = ∑_g |g,g⟩⟨g,g|`). -/
theorem isHermitian_mpo_boundaryTensor_one {ω : ScalarThreeCochain G}
    (hn : ScalarThreeCochain.IsNormalized ω) :
    (mpo (boundaryTensor e ω 1) N).IsHermitian := by
  rw [mpo_boundaryTensor_one e hn, Matrix.IsHermitian, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- **Multiplication law** `O_g O_h = O_{gh}` on every nonempty periodic chain. It holds on the
whole space, so in particular on the range of `O_e`, where the source states it.

Source: arXiv:2203.12563, line 2096. -/
theorem mpo_boundaryTensor_mul {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h : G) :
    mpo (boundaryTensor e ω g) N * mpo (boundaryTensor e ω h) N =
      mpo (boundaryTensor e ω (g * h)) N := by
  simp only [mpo_boundaryTensor, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (halfSiteEmbedding n N)ᴴ, conjTranspose_halfSiteEmbedding_mul,
    Matrix.one_mul, ← Matrix.mul_assoc (mpo (tensor e ω g) N), mpo_tensor_mul e hω]

/-- **Adjoint law** `O_g† = O_{g⁻¹}` on every nonempty periodic chain, for a normalized
three-cocycle with unit-modulus values.

Source: arXiv:2203.12563, line 2096. -/
theorem mpo_boundaryTensor_conjTranspose {ω : ScalarThreeCochain G}
    (hc : ScalarThreeCochain.IsCocycle ω) (hn : ScalarThreeCochain.IsNormalized ω)
    (hω : ∀ a b c, ‖(ω a b c : ℂ)‖ = 1) (g : G) :
    (mpo (boundaryTensor e ω g) N)ᴴ = mpo (boundaryTensor e ω g⁻¹) N := by
  rw [mpo_boundaryTensor, mpo_boundaryTensor, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, mpo_tensor_conjTranspose e hc hn hω, Matrix.mul_assoc]

/-- **`U_g = Γ O_g Γ†`**: the periodic operators of `MPOTensor.GroupCocycle.tensor` are the
arbitrary-boundary operators restricted to the range of `O_e` and carried back by the isometry
`Γ`.

Source: arXiv:2203.12563, lines 2200–2205, with one shift `L_g` per site as in
`docs/paper-gaps/glm23_pbc_group_mpo_single_shift.tex`. -/
theorem mpo_tensor_eq_halfSiteEmbedding (ω : ScalarThreeCochain G) (g : G) :
    mpo (tensor e ω g) N =
      (halfSiteEmbedding n N)ᴴ * mpo (boundaryTensor e ω g) N * halfSiteEmbedding n N := by
  rw [mpo_boundaryTensor, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    conjTranspose_halfSiteEmbedding_mul, Matrix.one_mul, Matrix.mul_assoc,
    conjTranspose_halfSiteEmbedding_mul, Matrix.mul_one]

end MPOTensor.GroupCocycle
