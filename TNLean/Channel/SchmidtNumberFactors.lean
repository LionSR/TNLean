/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.SchmidtNumber

/-!
# General bipartite reduction forward step

`SchmidtNumber.lean` establishes the forward step of Wolf's reduction criterion —
that a bipartite state of Schmidt number at most `n` satisfies `(T ⊗ id)(ρ) ≥ 0`
for every `n`-positive map `T` — on the **square** system `ℂ^D ⊗ ℂ^D`.  This file
lifts that result to a general bipartite system `ℂ^d ⊗ ℂ^{d'}` with the first factor
`d` equal to the map's dimension and **no relation imposed** between the two tensor
factors (Wolf §3.2, eq. (3.18) step 1, Prop 3.4 only-if).

The lift uses two zero-padding directions to reach the square system the square
result needs.  When the second factor is the smaller, `d' ≤ d`, the second factor is
padded up to `d` by zeros and the square result is restricted back to the `d × d'`
corner.  When the second factor is the larger, `d ≤ d'`, the first factor is padded up
to `d'` by zeros and the map `T` is extended to the larger square `M_{d'}` by the
corner sandwich `cornerPad ∘ T ∘ cornerCompress`, which stays `n`-positive; the square
result then applies and is again restricted to the corner.  Both paddings preserve the
Schmidt rank, because bordering the coefficient matrix by zero rows or columns cannot
raise its rank.

## Main results

* `Matrix.tensorMapId_posSemidef_of_hasSchmidtRankLE'` and
  `Matrix.HasSchmidtNumberLE.tensorMapId_posSemidef'`: the only-if direction for second
  factor `d' ≤ d`, by padding the second factor up to `d` with zeros and restricting
  back to the `d × d'` corner.
* `Matrix.isNPositiveMap_cornerExtendMap`: the corner sandwich `cornerExtendMap` of an
  `n`-positive map `M_d → M_d` to a larger square `M_{d'} → M_{d'}` is again
  `n`-positive.
* `Matrix.tensorMapId_posSemidef_of_hasSchmidtRankLE''` and
  `Matrix.HasSchmidtNumberLE.tensorMapId_posSemidef''`: the only-if direction for second
  factor `d ≤ d'`, by padding the first factor up to `d'` with zeros, extending `T` by
  the corner sandwich, and restricting back to the `d × d'` corner.
* `Matrix.tensorMapId_posSemidef_of_hasSchmidtRankLE_general` and
  `Matrix.HasSchmidtNumberLE.tensorMapId_posSemidef_general`: the **general bipartite
  forward step** of Wolf Prop 3.4 (only if), with no relation imposed between the two
  tensor factors, combining the two padding directions.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Section 3.2, the *Detecting entanglement* paragraph and Example 3.1,
  equation (3.18)][Wolf2012QChannels]
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

variable {d d' D : ℕ}

/-! ## Padding the second factor to a square system

The square forward step of `SchmidtNumber.lean` fixes both tensor factors to the
map's dimension `d`.  To reach Wolf's general bipartite system `ℂ^d ⊗ ℂ^{d'}` we
pad the second factor up to `d` by zeros (valid when `d' ≤ d`), apply the square
result, and restrict back to the `d × d'` corner with `Matrix.PosSemidef.submatrix`.
The padding is the standard zero-border dilation; it preserves Schmidt rank because
appending zero columns to the coefficient matrix cannot raise its rank. -/

/-- **Pad the second tensor factor of a bipartite vector by zeros.**  A vector on
`Fin d × Fin d'` is extended to `Fin d × Fin d` (used with `d' ≤ d`) by setting the
new coordinates `d' ≤ j < d` to zero, keeping the `d × d'` block.  Its coefficient
matrix is the original coefficient matrix bordered by zero columns. -/
def padSecondFactor (ψ : Fin d × Fin d' → ℂ) : Fin d × Fin d → ℂ :=
  fun p => if hp : (p.2 : ℕ) < d' then ψ (p.1, ⟨(p.2 : ℕ), hp⟩) else 0

/-- The corner-index embedding `Fin d × Fin d' ↪ Fin d × Fin d` that fixes the
first factor and includes the second factor as the initial `d'` coordinates. -/
def cornerEmbed (h : d' ≤ d) : Fin d × Fin d' → Fin d × Fin d :=
  fun p => (p.1, Fin.castLE h p.2)

@[simp]
theorem padSecondFactor_cornerEmbed (h : d' ≤ d) (ψ : Fin d × Fin d' → ℂ)
    (p : Fin d × Fin d') : padSecondFactor (ψ) (cornerEmbed h p) = ψ p := by
  cases p with
  | mk i j =>
    have hj : ((Fin.castLE h j : Fin d) : ℕ) < d' := by simp [Fin.castLE]
    have hidx : (⟨((Fin.castLE h j : Fin d) : ℕ), hj⟩ : Fin d') = j := Fin.ext rfl
    simp only [cornerEmbed, padSecondFactor, hj, dif_pos, hidx]

/-- Padding the second factor by zeros preserves the Schmidt-rank bound: the
padded coefficient matrix is the original coefficient matrix right-multiplied by a
zero-bordered inclusion, so its rank cannot exceed that of the original. -/
theorem hasSchmidtRankLE_padSecondFactor {n : ℕ}
    {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    HasSchmidtRankLE n (padSecondFactor ψ) := by
  classical
  -- The padded coefficient matrix factors as `schmidtCoeffMatrix ψ * E`, with `E`
  -- the zero-bordered inclusion `Fin d' → Fin d`.
  set M : Matrix (Fin d) (Fin d') ℂ := schmidtCoeffMatrix ψ with hM
  set E : Matrix (Fin d') (Fin d) ℂ :=
    fun k j => if hj : (j : ℕ) < d' then (if k = ⟨(j : ℕ), hj⟩ then 1 else 0) else 0
    with hE
  have hfactor : schmidtCoeffMatrix (padSecondFactor ψ) = M * E := by
    ext i j
    simp only [schmidtCoeffMatrix_apply, padSecondFactor, Matrix.mul_apply, hM, hE]
    by_cases hj : (j : ℕ) < d'
    · simp only [hj, dif_pos]
      rw [Finset.sum_eq_single (⟨(j : ℕ), hj⟩ : Fin d')]
      · simp
      · intro b _ hb
        simp [if_neg hb]
      · intro hb; exact absurd (Finset.mem_univ _) hb
    · simp only [hj, dif_neg, not_false_iff]
      symm
      apply Finset.sum_eq_zero
      intro k _
      simp
  have hrank : (schmidtCoeffMatrix (padSecondFactor ψ)).rank ≤ n := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_left M E).trans hψ
  simpa [HasSchmidtRankLE, schmidtRank] using hrank

/-- The ampliation on the padded square system restricts on the `d × d'` corner to
the ampliation of the original state: `tensorMapId T ρ` is the corner submatrix of
the ampliation of the zero-padded state, because `tensorMapId` carries the second
factor through untouched and the padded second-factor coordinates lie inside the
corner. -/
theorem tensorMapId_padSecondFactor_submatrix (h : d' ≤ d)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    {ι : Type} [Fintype ι] (ψ : ι → (Fin d × Fin d' → ℂ)) :
    tensorMapId T (∑ i, vecMulVec (ψ i) (star (ψ i)))
      = (tensorMapId T
          (∑ i, vecMulVec (padSecondFactor (ψ i)) (star (padSecondFactor (ψ i))))).submatrix
        (cornerEmbed h) (cornerEmbed h) := by
  classical
  -- The padded summand restricted to the corner is the original summand.
  have hsum :
      (∑ i, vecMulVec (ψ i) (star (ψ i)))
        = (∑ i, vecMulVec (padSecondFactor (ψ i))
            (star (padSecondFactor (ψ i)))).submatrix (cornerEmbed h) (cornerEmbed h) := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply,
      padSecondFactor_cornerEmbed]
  -- The ampliation commutes with the corner restriction of the second factor.
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  simp only [Matrix.submatrix_apply, cornerEmbed, tensorMapId_apply]
  -- The relevant second-factor slice agrees on the corner.
  have hslice :
      bipartiteSlice (∑ i, vecMulVec (ψ i) (star (ψ i))) i₂ j₂
        = bipartiteSlice (∑ i, vecMulVec (padSecondFactor (ψ i))
            (star (padSecondFactor (ψ i)))) (Fin.castLE h i₂) (Fin.castLE h j₂) := by
    ext a b
    simp only [bipartiteSlice]
    have := congrFun (congrFun hsum (a, i₂)) (b, j₂)
    simpa [cornerEmbed, Matrix.submatrix_apply] using this
  rw [hslice]

/-- **Positive maps and entanglement, only-if direction, pure-state step, differing
factors** (Wolf §3.2, Prop 3.4).  For a pure state `|ψ⟩⟨ψ|` on `ℂ^d ⊗ ℂ^{d'}` with
ψ of Schmidt rank at most `n`, the first factor `d` equal to the dimension of the
`n`-positive map `T`, and the second factor `d' ≤ d`, the ampliation
`(T ⊗ id)(|ψ⟩⟨ψ|)` is positive semidefinite.

The vector is padded to the square system `ℂ^d ⊗ ℂ^d` by zero columns, which keeps
the Schmidt rank at most `n`; the square pure-state step makes the padded ampliation
positive semidefinite; and the original ampliation is the `d × d'` corner submatrix
of the padded one, hence positive semidefinite.

**Scope restriction (d' ≤ d):** the second factor is padded up to the first factor
`d`, which requires `d' ≤ d`; the complementary case `d' > d` (extending `T` to the
larger square) is documented in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem tensorMapId_posSemidef_of_hasSchmidtRankLE' [NeZero d] {n : ℕ} (h : d' ≤ d)
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T) {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    (tensorMapId T (vecMulVec ψ (star ψ))).PosSemidef := by
  classical
  -- Pad to the square system and restrict back to the corner.
  have hsq :
      (tensorMapId T (vecMulVec (padSecondFactor ψ)
        (star (padSecondFactor ψ)))).PosSemidef :=
    tensorMapId_posSemidef_of_hasSchmidtRankLE hTpos (hasSchmidtRankLE_padSecondFactor hψ)
  have hcorner :
      tensorMapId T (vecMulVec ψ (star ψ))
        = (tensorMapId T (vecMulVec (padSecondFactor ψ)
            (star (padSecondFactor ψ)))).submatrix (cornerEmbed h) (cornerEmbed h) := by
    have := tensorMapId_padSecondFactor_submatrix (ι := PUnit) h T (fun _ => ψ)
    simpa using this
  rw [hcorner]
  exact hsq.submatrix (cornerEmbed h)

/-- **Positive maps and entanglement, only-if direction, differing factors**
(Wolf §3.2, Prop 3.4).  A bipartite state on `ℂ^d ⊗ ℂ^{d'}` of Schmidt number at
most `n`, with first factor `d` equal to the dimension of the `n`-positive map `T`
and second factor `d' ≤ d`, satisfies `(T ⊗ id)(ρ) ≥ 0`.

The state is padded to the square system `ℂ^d ⊗ ℂ^d` by zero columns on each pure
summand, which preserves the Schmidt-number bound; the square forward step makes the
padded ampliation positive semidefinite; and the original ampliation is its `d × d'`
corner submatrix.

**Scope restriction (d' ≤ d):** inherited from the pure-state step; the
complementary case `d' > d` is documented in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem HasSchmidtNumberLE.tensorMapId_posSemidef' [NeZero d] {n : ℕ} (h : d' ≤ d)
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    (tensorMapId T ρ).PosSemidef := by
  classical
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
  -- Pad each pure summand and restrict the padded square ampliation to the corner.
  have hsq :
      (tensorMapId T
        (∑ i, vecMulVec (padSecondFactor (ψ i))
          (star (padSecondFactor (ψ i))))).PosSemidef := by
    rw [tensorMapId_sum]
    exact posSemidef_sum Finset.univ fun i _ =>
      tensorMapId_posSemidef_of_hasSchmidtRankLE hTpos
        (hasSchmidtRankLE_padSecondFactor (hψ i))
  rw [tensorMapId_padSecondFactor_submatrix h T ψ]
  exact hsq.submatrix (cornerEmbed h)

/-! ## Padding the first factor and extending the map

When the second factor exceeds the first, `d < d'`, the roles reverse: we pad the
*first* factor up to `d'` by zeros to reach the square system `ℂ^{d'} ⊗ ℂ^{d'}`, and
extend the map `T` to the larger square by the corner-compression sandwich
`ι ∘ T ∘ π`, where `π` compresses to the `d × d` principal corner and `ι` pads with
zeros.  The extended map is again `n`-positive, the square forward step applies, and
the original ampliation is the principal-corner submatrix of the padded one. -/

/-- **A matrix supported on the corner of an injection, positive semidefinite on that
corner, is positive semidefinite.**  If `M` vanishes whenever a row or column index
lies outside the range of an injective `g`, and the corner submatrix `M.submatrix g g`
is positive semidefinite, then `M` is positive semidefinite: writing the corner as a
sum of rank-one projectors and extending each coefficient vector by zero off the range
of `g` realizes `M` itself as a sum of rank-one projectors. -/
theorem posSemidef_of_submatrix_corner {α β : Type*} [Finite α] [Finite β]
    {g : α → β} (hg : Function.Injective g) {M : Matrix β β ℂ}
    (hsupp : ∀ i j, ((∀ a, g a ≠ i) ∨ ∀ a, g a ≠ j) → M i j = 0)
    (hpsd : (M.submatrix g g).PosSemidef) : M.PosSemidef := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  obtain ⟨m, u, hu⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hpsd
  -- Extend each corner coefficient vector by zero off the range of `g`.
  set uExt : Fin m → (β → ℂ) :=
    fun k b => if hb : ∃ a, g a = b then u k hb.choose else 0 with huExt
  have huExtg : ∀ (k : Fin m) (a : α), uExt k (g a) = u k a := by
    intro k a
    have hex : ∃ a', g a' = g a := ⟨a, rfl⟩
    simp only [huExt, hex, dif_pos]
    rw [hg hex.choose_spec]
  have huExtoff : ∀ (k : Fin m) (b : β), (∀ a, g a ≠ b) → uExt k b = 0 := by
    intro k b hb
    have : ¬ ∃ a, g a = b := fun ⟨a, ha⟩ => hb a ha
    simp [huExt, this]
  refine posSemidef_iff_eq_sum_vecMulVec.mpr ⟨m, uExt, ?_⟩
  ext i j
  simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply]
  by_cases hi : ∃ a, g a = i
  · by_cases hj : ∃ a, g a = j
    · obtain ⟨a, rfl⟩ := hi
      obtain ⟨b, rfl⟩ := hj
      have hMij : M (g a) (g b) = (M.submatrix g g) a b := by
        simp [Matrix.submatrix_apply]
      rw [hMij, hu]
      simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, huExtg]
    · simp only [not_exists] at hj
      rw [hsupp i j (Or.inr hj)]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [huExtoff k j hj, star_zero, mul_zero]
  · simp only [not_exists] at hi
    rw [hsupp i j (Or.inl hi)]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [huExtoff k i hi, zero_mul]

/-- **Pad the first tensor factor of a bipartite vector by zeros.**  A vector on
`Fin d × Fin d'` is extended to `Fin d' × Fin d'` (used with `d ≤ d'`) by setting the
new first-factor coordinates `d ≤ i < d'` to zero, keeping the `d × d'` block.  Its
coefficient matrix is the original coefficient matrix bordered by zero rows. -/
def padFirstFactor (ψ : Fin d × Fin d' → ℂ) : Fin d' × Fin d' → ℂ :=
  fun p => if hp : (p.1 : ℕ) < d then ψ (⟨(p.1 : ℕ), hp⟩, p.2) else 0

/-- The corner-index embedding `Fin d × Fin d' ↪ Fin d' × Fin d'` that includes the
first factor as the initial `d` coordinates and fixes the second factor. -/
def cornerEmbedFirst (h : d ≤ d') : Fin d × Fin d' → Fin d' × Fin d' :=
  fun p => (Fin.castLE h p.1, p.2)

theorem cornerEmbedFirst_injective (h : d ≤ d') :
    Function.Injective (cornerEmbedFirst h : Fin d × Fin d' → Fin d' × Fin d') := by
  intro p q hpq
  simp only [cornerEmbedFirst, Prod.mk.injEq] at hpq
  exact Prod.ext (Fin.castLE_injective h hpq.1) hpq.2

@[simp]
theorem padFirstFactor_cornerEmbedFirst (h : d ≤ d') (ψ : Fin d × Fin d' → ℂ)
    (p : Fin d × Fin d') : padFirstFactor (ψ) (cornerEmbedFirst h p) = ψ p := by
  cases p with
  | mk i j =>
    have hi : ((Fin.castLE h i : Fin d') : ℕ) < d := by simp [Fin.castLE]
    have hidx : (⟨((Fin.castLE h i : Fin d') : ℕ), hi⟩ : Fin d) = i := Fin.ext rfl
    simp only [cornerEmbedFirst, padFirstFactor, hi, dif_pos, hidx]

/-- Padding the first factor by zeros preserves the Schmidt-rank bound: the padded
coefficient matrix is the original coefficient matrix left-multiplied by a
zero-bordered inclusion, so its rank cannot exceed that of the original. -/
theorem hasSchmidtRankLE_padFirstFactor {n : ℕ}
    {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    HasSchmidtRankLE n (padFirstFactor ψ) := by
  classical
  -- The padded coefficient matrix factors as `F * schmidtCoeffMatrix ψ`, with `F`
  -- the zero-bordered inclusion `Fin d' → Fin d`.
  set M : Matrix (Fin d) (Fin d') ℂ := schmidtCoeffMatrix ψ with hM
  set F : Matrix (Fin d') (Fin d) ℂ :=
    fun i k => if hi : (i : ℕ) < d then (if k = ⟨(i : ℕ), hi⟩ then 1 else 0) else 0
    with hF
  have hfactor : schmidtCoeffMatrix (padFirstFactor ψ) = F * M := by
    ext i j
    simp only [schmidtCoeffMatrix_apply, padFirstFactor, Matrix.mul_apply, hM, hF]
    by_cases hi : (i : ℕ) < d
    · simp only [hi, dif_pos]
      rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin d)]
      · simp
      · intro b _ hb
        simp [if_neg hb]
      · intro hb; exact absurd (Finset.mem_univ _) hb
    · simp only [hi, dif_neg, not_false_iff]
      symm
      apply Finset.sum_eq_zero
      intro k _
      simp
  have hrank : (schmidtCoeffMatrix (padFirstFactor ψ)).rank ≤ n := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_right F M).trans hψ
  simpa [HasSchmidtRankLE, schmidtRank] using hrank

/-- **Compress a matrix to its `d × d` principal corner** (`d ≤ d'`), as a linear map
`M_{d'} → M_d`.  This is the submatrix along the corner inclusion `Fin.castLE`. -/
noncomputable def cornerCompress (h : d ≤ d') :
    Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := X.submatrix (Fin.castLE h) (Fin.castLE h)
  map_add' X Y := by ext; simp
  map_smul' c X := by ext; simp

/-- **Pad a `d × d` matrix to the `d × d` principal corner of `M_{d'}`** (`d ≤ d'`),
as a linear map `M_d → M_{d'}`: entries inside the corner are kept, all others are
zero. -/
noncomputable def cornerPad (_h : d ≤ d') :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ where
  toFun Z := Matrix.of fun a b =>
    if ha : (a : ℕ) < d then (if hb : (b : ℕ) < d then Z ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0
  map_add' X Y := by
    ext a b
    by_cases ha : (a : ℕ) < d <;> by_cases hb : (b : ℕ) < d <;>
      simp [ha, hb, Matrix.of_apply]
  map_smul' c X := by
    ext a b
    by_cases ha : (a : ℕ) < d <;> by_cases hb : (b : ℕ) < d <;>
      simp [ha, hb, Matrix.of_apply]

/-- **Extend a square map to a larger square by corner sandwich** (`d ≤ d'`).  The map
`cornerExtendMap h T : M_{d'} → M_{d'}` first compresses its argument to the `d × d`
principal corner, applies `T`, and pads the result back with zeros.  It coincides with
`cornerPad ∘ T ∘ cornerCompress`. -/
noncomputable def cornerExtendMap (h : d ≤ d')
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ :=
  (cornerPad h).comp (T.comp (cornerCompress h))

theorem cornerExtendMap_apply (h : d ≤ d')
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (Z : Matrix (Fin d') (Fin d') ℂ) (a b : Fin d') :
    cornerExtendMap h T Z a b =
      if ha : (a : ℕ) < d then
        (if hb : (b : ℕ) < d then
          T (Z.submatrix (Fin.castLE h) (Fin.castLE h)) ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0 :=
  rfl

/-- **The corner extension preserves `n`-positivity** (the crux of the `d < d'` step).
If `T` is `n`-positive then so is `cornerExtendMap h T`.  Given a positive
semidefinite ampliated input on `ℂ^{d'} ⊗ ℂ^n`, the extended map's output is supported
on the `d × d` principal corner of the first factor, where it equals the ampliation of
`T` on the corner-compressed input — a principal submatrix of the input, hence positive
semidefinite, made positive semidefinite by the `n`-positivity of `T`.  A matrix
supported on the corner with that corner positive semidefinite is itself positive
semidefinite. -/
theorem isNPositiveMap_cornerExtendMap (h : d ≤ d') {n : ℕ}
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsNPositiveMap n T) : IsNPositiveMap n (cornerExtendMap h T) := by
  classical
  intro X hX
  -- The first-factor corner inclusion at the ampliated level.
  set g : Fin d × Fin n → Fin d' × Fin n :=
    fun p => (Fin.castLE h p.1, p.2) with hg
  have hginj : Function.Injective g := by
    intro p q hpq
    simp only [hg, Prod.mk.injEq] at hpq
    exact Prod.ext (Fin.castLE_injective h hpq.1) hpq.2
  set Y : Matrix (Fin d' × Fin n) (Fin d' × Fin n) ℂ :=
    Matrix.of fun ip jq =>
      (cornerExtendMap h T (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1 with hY
  -- `Y` is supported on the corner image of `g`: outside the corner the extension is 0.
  have hsupp : ∀ ip jq,
      ((∀ a, g a ≠ ip) ∨ ∀ a, g a ≠ jq) → Y ip jq = 0 := by
    intro ip jq hor
    simp only [hY, Matrix.of_apply, cornerExtendMap_apply]
    -- If `ip.1 ≥ d` or `jq.1 ≥ d`, the corner padding outputs zero.
    rcases hor with hi | hj
    · have hip1 : ¬ (ip.1 : ℕ) < d := by
        intro hlt
        exact hi (⟨ip.1, hlt⟩, ip.2)
          (Prod.ext (Fin.ext (by simp [g, Fin.castLE])) rfl)
      simp [hip1]
    · have hjq1 : ¬ (jq.1 : ℕ) < d := by
        intro hlt
        exact hj (⟨jq.1, hlt⟩, jq.2)
          (Prod.ext (Fin.ext (by simp [g, Fin.castLE])) rfl)
      by_cases hip1 : (ip.1 : ℕ) < d
      · simp [hip1, hjq1]
      · simp [hip1]
  -- The corner submatrix of `Y` is the `n`-ampliation of `T` on the compressed input.
  set X' : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ := X.submatrix g g with hX'
  have hcorner : Y.submatrix g g =
      Matrix.of fun (ip : Fin d × Fin n) (jq : Fin d × Fin n) =>
        (T (Matrix.of fun i j => X' (i, ip.2) (j, jq.2))) ip.1 jq.1 := by
    ext ip jq
    have hi : ((Fin.castLE h ip.1 : Fin d') : ℕ) < d := by simp [Fin.castLE]
    have hj : ((Fin.castLE h jq.1 : Fin d') : ℕ) < d := by simp [Fin.castLE]
    have hidx_i : (⟨((Fin.castLE h ip.1 : Fin d') : ℕ), hi⟩ : Fin d) = ip.1 := Fin.ext rfl
    have hidx_j : (⟨((Fin.castLE h jq.1 : Fin d') : ℕ), hj⟩ : Fin d) = jq.1 := Fin.ext rfl
    -- The compressed padded slice equals the `X'` slice.
    have harg :
        (Matrix.of fun i j => X (i, ip.2) (j, jq.2)).submatrix
            (Fin.castLE h) (Fin.castLE h)
          = Matrix.of fun i j => X' (i, ip.2) (j, jq.2) := by
      ext a b
      simp only [Matrix.submatrix_apply, hX', Matrix.of_apply, hg]
    simp only [Matrix.submatrix_apply, hY, Matrix.of_apply, cornerExtendMap_apply, hg,
      hi, dif_pos, hj, hidx_i, hidx_j]
    rw [harg]
  -- That corner is positive semidefinite by `n`-positivity of `T` on a PSD input.
  have hX'psd : X'.PosSemidef := hX.submatrix g
  have hcornerpsd : (Y.submatrix g g).PosSemidef := by
    rw [hcorner]; exact hT X' hX'psd
  -- Assemble.
  exact posSemidef_of_submatrix_corner hginj hsupp hcornerpsd

/-- The padded square ampliation restricts on the `d × d'` corner of the first factor
to the original ampliation: `tensorMapId T ρ` (on `Fin d × Fin d'`) is the principal
submatrix of `tensorMapId (cornerExtendMap h T) ρ'` (on `Fin d' × Fin d'`), where `ρ'`
is the first-factor zero-padding of `ρ`.  The extended map outputs zero off the corner
and reproduces `T` on it, and the padded state agrees with the original on the corner. -/
theorem tensorMapId_padFirstFactor_submatrix (h : d ≤ d')
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    {ι : Type} [Fintype ι] (ψ : ι → (Fin d × Fin d' → ℂ)) :
    tensorMapId T (∑ i, vecMulVec (ψ i) (star (ψ i)))
      = (tensorMapId (cornerExtendMap h T)
          (∑ i, vecMulVec (padFirstFactor (ψ i))
            (star (padFirstFactor (ψ i))))).submatrix
              (cornerEmbedFirst h) (cornerEmbedFirst h) := by
  classical
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  simp only [Matrix.submatrix_apply, cornerEmbedFirst, tensorMapId_apply,
    cornerExtendMap_apply]
  have hi : ((Fin.castLE h i₁ : Fin d') : ℕ) < d := by simp [Fin.castLE]
  have hj : ((Fin.castLE h j₁ : Fin d') : ℕ) < d := by simp [Fin.castLE]
  have hidx_i : (⟨((Fin.castLE h i₁ : Fin d') : ℕ), hi⟩ : Fin d) = i₁ := Fin.ext rfl
  have hidx_j : (⟨((Fin.castLE h j₁ : Fin d') : ℕ), hj⟩ : Fin d) = j₁ := Fin.ext rfl
  -- The compressed padded slice equals the original slice.
  have hslice :
      (bipartiteSlice (∑ i, vecMulVec (padFirstFactor (ψ i))
          (star (padFirstFactor (ψ i)))) i₂ j₂).submatrix (Fin.castLE h) (Fin.castLE h)
        = bipartiteSlice (∑ i, vecMulVec (ψ i) (star (ψ i))) i₂ j₂ := by
    ext a b
    simp only [Matrix.submatrix_apply, bipartiteSlice, Matrix.sum_apply, vecMulVec_apply,
      Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have ha : padFirstFactor (ψ k) (Fin.castLE h a, i₂) = ψ k (a, i₂) :=
      padFirstFactor_cornerEmbedFirst h (ψ k) (a, i₂)
    have hb : padFirstFactor (ψ k) (Fin.castLE h b, j₂) = ψ k (b, j₂) :=
      padFirstFactor_cornerEmbedFirst h (ψ k) (b, j₂)
    rw [ha, hb]
  simp only [hi, dif_pos, hj, hslice, hidx_i, hidx_j]

/-- **Positive maps and entanglement, only-if direction, pure-state step, second
factor larger** (Wolf §3.2, Prop 3.4).  For a pure state `|ψ⟩⟨ψ|` on
`ℂ^d ⊗ ℂ^{d'}` with ψ of Schmidt rank at most `n`, the first factor `d` equal to the
dimension of the `n`-positive map `T`, and `d ≤ d'`, the ampliation
`(T ⊗ id)(|ψ⟩⟨ψ|)` is positive semidefinite.

The vector is padded on the first factor to the square system `ℂ^{d'} ⊗ ℂ^{d'}`, which
keeps the Schmidt rank at most `n`; the map `T` is extended to that square by the
corner sandwich, which stays `n`-positive; the square pure-state step makes the padded
ampliation positive semidefinite; and the original ampliation is its `d × d'`
principal-corner submatrix.

**Scope restriction (d ≤ d'):** the first factor is padded up to the second factor
`d'`; the complementary case `d' ≤ d` is `tensorMapId_posSemidef_of_hasSchmidtRankLE'`.
Both are combined without restriction in
`tensorMapId_posSemidef_of_hasSchmidtRankLE_general`. -/
theorem tensorMapId_posSemidef_of_hasSchmidtRankLE'' [NeZero d'] {n : ℕ} (h : d ≤ d')
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T) {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    (tensorMapId T (vecMulVec ψ (star ψ))).PosSemidef := by
  classical
  -- Pad the first factor to the square system and restrict back to the corner.
  have hsq :
      (tensorMapId (cornerExtendMap h T) (vecMulVec (padFirstFactor ψ)
        (star (padFirstFactor ψ)))).PosSemidef :=
    tensorMapId_posSemidef_of_hasSchmidtRankLE (isNPositiveMap_cornerExtendMap h hTpos)
      (hasSchmidtRankLE_padFirstFactor hψ)
  have hcorner :
      tensorMapId T (vecMulVec ψ (star ψ))
        = (tensorMapId (cornerExtendMap h T) (vecMulVec (padFirstFactor ψ)
            (star (padFirstFactor ψ)))).submatrix (cornerEmbedFirst h) (cornerEmbedFirst h) := by
    have := tensorMapId_padFirstFactor_submatrix (ι := PUnit) h T (fun _ => ψ)
    simpa using this
  rw [hcorner]
  exact hsq.submatrix (cornerEmbedFirst h)

/-- **Positive maps and entanglement, only-if direction, second factor larger**
(Wolf §3.2, Prop 3.4).  A bipartite state on `ℂ^d ⊗ ℂ^{d'}` of Schmidt number at
most `n`, with first factor `d` equal to the dimension of the `n`-positive map `T`
and `d ≤ d'`, satisfies `(T ⊗ id)(ρ) ≥ 0`.

Each pure summand is padded on the first factor to the square system `ℂ^{d'} ⊗ ℂ^{d'}`,
which preserves the Schmidt-number bound; the corner extension of `T` stays
`n`-positive; the square forward step makes the padded ampliation positive
semidefinite; and the original ampliation is its `d × d'` principal-corner submatrix.

**Scope restriction (d ≤ d'):** inherited from the pure-state step; the complementary
case `d' ≤ d` is `HasSchmidtNumberLE.tensorMapId_posSemidef'`.  Both are combined
without restriction in `HasSchmidtNumberLE.tensorMapId_posSemidef_general`. -/
theorem HasSchmidtNumberLE.tensorMapId_posSemidef'' [NeZero d'] {n : ℕ} (h : d ≤ d')
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    (tensorMapId T ρ).PosSemidef := by
  classical
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
  -- Pad each pure summand on the first factor and restrict to the corner.
  have hsq :
      (tensorMapId (cornerExtendMap h T)
        (∑ i, vecMulVec (padFirstFactor (ψ i))
          (star (padFirstFactor (ψ i))))).PosSemidef := by
    rw [tensorMapId_sum]
    exact posSemidef_sum Finset.univ fun i _ =>
      tensorMapId_posSemidef_of_hasSchmidtRankLE (isNPositiveMap_cornerExtendMap h hTpos)
        (hasSchmidtRankLE_padFirstFactor (hψ i))
  rw [tensorMapId_padFirstFactor_submatrix h T ψ]
  exact hsq.submatrix (cornerEmbedFirst h)

/-! ## The general bipartite forward step

Combining the two padding directions removes every restriction relating the two
tensor factors.  For a pure state or a state of bounded Schmidt number on a general
bipartite system `ℂ^d ⊗ ℂ^{d'}` with first factor `d` equal to the map's dimension,
the ampliation `(T ⊗ id)` of any `n`-positive map is positive semidefinite. -/

/-- **Positive maps and entanglement, only-if direction, pure-state step, general
bipartite second factor** (Wolf §3.2, Prop 3.4, eq. (3.18) step 1).  For a pure state
`|ψ⟩⟨ψ|` on a general bipartite system `ℂ^d ⊗ ℂ^{d'}` with ψ of Schmidt rank at most
`n` and first factor `d` equal to the dimension of the `n`-positive map `T`, the
ampliation `(T ⊗ id)(|ψ⟩⟨ψ|)` is positive semidefinite, with no relation imposed
between the two tensor factors.

The two padding directions cover the full range: when the second factor is the smaller,
`d' ≤ d`, the second factor is padded up to `d`; when it is the larger, `d ≤ d'`, the
first factor is padded up to `d'` and `T` is extended to the larger square. -/
theorem tensorMapId_posSemidef_of_hasSchmidtRankLE_general [NeZero d] [NeZero d'] {n : ℕ}
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T) {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    (tensorMapId T (vecMulVec ψ (star ψ))).PosSemidef := by
  rcases le_or_gt d' d with h | h
  · exact tensorMapId_posSemidef_of_hasSchmidtRankLE' h hTpos hψ
  · exact tensorMapId_posSemidef_of_hasSchmidtRankLE'' h.le hTpos hψ

/-- **Positive maps and entanglement, only-if direction, general bipartite second
factor** (Wolf §3.2, Prop 3.4, eq. (3.18) step 1).  A bipartite state on a general
system `ℂ^d ⊗ ℂ^{d'}` of Schmidt number at most `n`, with first factor `d` equal to the
dimension of the `n`-positive map `T`, satisfies `(T ⊗ id)(ρ) ≥ 0`, with no relation
imposed between the two tensor factors.

This is the faithful bipartite forward step of Wolf eq. (3.18): the two padding
directions of the pure-state step (`d' ≤ d` padding the second factor, `d ≤ d'` padding
the first factor and extending `T`) jointly cover all `d'`, and the ampliation is
linear over the finite pure-state decomposition. -/
theorem HasSchmidtNumberLE.tensorMapId_posSemidef_general [NeZero d] [NeZero d'] {n : ℕ}
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    (tensorMapId T ρ).PosSemidef := by
  rcases le_or_gt d' d with h | h
  · exact hρ.tensorMapId_posSemidef' h hTpos
  · exact hρ.tensorMapId_posSemidef'' h.le hTpos

end Matrix
