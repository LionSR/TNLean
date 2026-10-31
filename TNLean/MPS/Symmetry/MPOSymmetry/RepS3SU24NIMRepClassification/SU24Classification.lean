/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.RepS3SU24NIMRepClassification.RepS3Classification

/-!
# Classification of the dual nonnegative integer representations of `su(2)₄`

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section `sec:examples`,
`Papers/2203.12563/REsubmission.tex` lines 1890–1931: "there are only two different phases" of
matrix product states symmetric under the `su(2)₄` matrix product operator algebra, the regular
one with five blocks and `𝓜_TY` with four. The source takes completeness of this list from the
classification of module categories, which it cites. Every label of `su(2)₄` is self-dual, so
the duality of lines 564–565 reads `M_a = M_aᵀ`.

**Formalized here.** On any finite set of blocks, every block of a dual representation of
`su(2)₄` with trivial unit lies in a direct summand isomorphic to the regular phase or to
`𝓜_TY`, and an indecomposable representation is one of them.

The integer labels `0, 1, 2` of `su(2)₄` represent `Rep(S₃)`, so the local configurations of
`TNLean.MPS.Symmetry.MPOSymmetry.RepS3SU24NIMRepClassification.RepS3Classification` apply. The
relations `1/2 × 1/2 = 0 + 1` and `1/2 × 2 = 3/2` then determine the action of `1/2` around each
of these configurations: a `ℤ₁` or `ℤ₃` configuration closes into `𝓜_TY`, and an `S₃` or `ℤ₂`
configuration into the regular phase.

**Scope restriction (printed list):** the input is the nonnegative integer representation of a
module category, not the module category itself; the lists are identified at the level of the
multiplicities. Documented in `docs/paper-gaps/glm23_reps3_su24_module_list.tex`.

## Main results

* `MPOTensor.exists_isNIMRepSummand_su24`: every block of a dual representation of `su(2)₄` with
  trivial unit lies in a summand isomorphic to the regular phase or to `𝓜_TY`.
* `MPOTensor.exists_equiv_of_isIndecomposable_su24`: the indecomposable ones are exactly these
  two.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

namespace MPOTensor

variable {ι κ κ' : Type*}

/-! ### `su(2)₄` -/

section SU24

variable [Fintype κ] [DecidableEq κ] {M : Fin 5 → κ → κ → ℕ}

omit [DecidableEq κ] in
/-- The integer labels of a representation of `su(2)₄` represent `Rep(S₃)` (arXiv:2203.12563,
line 1934). -/
private theorem isNIMRep_repS3_comp (hM : IsNIMRep su24Fusion M) :
    IsNIMRep repS3Fusion fun a => M (repS3ToSU24 a) := by
  intro a b x y
  change ∑ c, repS3Fusion a b c * M (repS3ToSU24 c) x y =
    ∑ z, M (repS3ToSU24 b) x z * M (repS3ToSU24 a) z y
  rw [← hM (repS3ToSU24 a) (repS3ToSU24 b) x y]
  have ha : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases ha a with rfl | rfl | rfl <;> rcases ha b with rfl | rfl | rfl <;>
    simp [Fin.sum_univ_five, Fin.sum_univ_three, su24Fusion, repS3Fusion, repS3ToSU24,
      Matrix.one_apply]

/-- The local facts behind the classification for `su(2)₄`, with `Q = M_{1/2}` and
`T = M_1`: the `Rep(S₃)` facts of the integer labels, and the relations
`1/2 × 1/2 = 0 + 1` and `1/2 × 2 = 2 × 1/2 = 3/2` (arXiv:2203.12563, lines 1891–1904). -/
private structure SU24Local (M : Fin 5 → κ → κ → ℕ) (σ : κ → κ) : Prop where
  unit : ∀ x y, M 0 x y = if x = y then 1 else 0
  perm : ∀ x y, M 4 x y = if y = σ x then 1 else 0
  invol : ∀ x, σ (σ x) = x
  T_σ : ∀ x y, M 2 (σ x) y = M 2 x y
  T_symm : ∀ x y, M 2 x y = M 2 y x
  T_row : ∀ x, ∑ z, M 2 x z * M 2 x z = 1 + M 2 x x + if σ x = x then 1 else 0
  T_off : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, M 2 x z * M 2 z y = M 2 x y
  Q_symm : ∀ x y, M 1 x y = M 1 y x
  Q_row : ∀ x, ∑ z, M 1 x z * M 1 x z = 1 + M 2 x x
  Q_off : ∀ x y, x ≠ y → ∑ z, M 1 x z * M 1 z y = M 2 x y
  three : ∀ x y, M 3 x y = M 1 x (σ y)
  Q_σ : ∀ x y, M 1 (σ x) y = M 1 x (σ y)

private theorem su24_exists_local (hM : IsNIMRep su24Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) :
    ∃ σ, SU24Local M σ := by
  obtain ⟨σ, hσ, hσσ, hTσ, hT, hrow, hoff⟩ := repS3_exists_local (isNIMRep_repS3_comp hM)
    (fun x y => hunit x y) (fun a x y => hdual (repS3ToSU24 a) x y)
  have hQ : ∀ x y, M 1 x y = M 1 y x := fun x y => (hdual 1 y x).symm
  have h11 : ∀ x y, ∑ z, M 1 x z * M 1 z y = (if x = y then 1 else 0) + M 2 x y := fun x y => by
    have h := hM 1 1 x y
    simp only [su24Fusion, Fin.sum_univ_five, hunit] at h
    simpa using h.symm
  have h3a : ∀ x y, M 3 x y = ∑ z, M 4 x z * M 1 z y := fun x y => by
    have h := hM 1 4 x y
    simp only [su24Fusion, Fin.sum_univ_five] at h
    simpa using h
  have h3b : ∀ x y, M 3 x y = ∑ z, M 1 x z * M 4 z y := fun x y => by
    have h := hM 4 1 x y
    simp only [su24Fusion, Fin.sum_univ_five] at h
    simpa using h
  have hσ' : ∀ x y, M 4 x y = if y = σ x then 1 else 0 := hσ
  have hthree : ∀ x y, M 3 x y = M 1 x (σ y) := fun x y => by
    rw [h3b, Fintype.sum_eq_single (σ y) fun z hz => by
      have : ¬ y = σ z := fun h => hz (by rw [h, hσσ])
      simp [hσ', this], hσ', hσσ]
    simp
  refine ⟨σ, hunit, hσ', hσσ, hTσ, hT, hrow, hoff, hQ, fun x => ?_, fun x y hxy => ?_, hthree,
    fun x y => ?_⟩
  · have h := h11 x x
    simp only [↓reduceIte] at h
    rw [← h]
    exact Finset.sum_congr rfl fun z _ => by rw [hQ z x]
  · simpa [hxy] using h11 x y
  · rw [← hthree, h3a, Fintype.sum_eq_single (σ x) fun z hz => by
      simp [hσ', hz], hσ']
    simp

/-- The label `2` of `su(2)₄` acts on the labels by the reflection `j ↦ 4 - j`. -/
private def su24Reflect : Fin 5 → Fin 5 := ![4, 3, 2, 1, 0]

private theorem su24Fusion_four_apply (i j : Fin 5) :
    su24Fusion 4 i j = if j = su24Reflect i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem su24Fusion_three_apply (i j : Fin 5) :
    su24Fusion 3 i j = su24Fusion 1 i (su24Reflect j) := by
  fin_cases i <;> fin_cases j <;> simp [su24Fusion, su24Reflect]

namespace SU24Local

variable {σ : κ → κ} (L : SU24Local M σ)
include L

/-- If `σ` moves the block `x`, the row of label `2` at `x` either has diagonal entry one and
vanishes away from `x` and `σ x`, or has diagonal entry zero and is the unit vector at a
`σ`-fixed block `w`, whose own row has diagonal entry one and vanishes away from `x`, `σ x`,
and `w`. -/
theorem of_ne {x : κ} (hx : σ x ≠ x) :
    (M 2 x x = 1 ∧ ∀ z, z ≠ x → z ≠ σ x → M 2 x z = 0) ∨
    (M 2 x x = 0 ∧ ∃ w, w ≠ x ∧ w ≠ σ x ∧ σ w = w ∧ M 2 x w = 1 ∧ M 2 w w = 1 ∧
      (∀ z, z ≠ w → M 2 x z = 0) ∧ ∀ z, z ≠ x → z ≠ σ x → z ≠ w → M 2 w z = 0) :=
  repS3_of_ne L.T_symm L.T_σ L.T_row L.T_off hx

/-- If `σ` fixes the block `x`, the row of label `2` at `x` has diagonal entry two and no other
entries, or diagonal entry one and a nonzero entry at a block moved by `σ`, or diagonal entry
zero and unit entries at two further `σ`-fixed blocks `w` and `v` joined to each other, with
the three rows vanishing elsewhere. -/
theorem of_eq {x : κ} (hx : σ x = x) :
    (M 2 x x = 2 ∧ ∀ z, z ≠ x → M 2 x z = 0) ∨
    (M 2 x x = 1 ∧ ∃ w, σ w ≠ w ∧ M 2 x w ≠ 0) ∨
    (M 2 x x = 0 ∧ ∃ w v, w ≠ x ∧ v ≠ x ∧ w ≠ v ∧ σ w = w ∧ σ v = v ∧ M 2 x w = 1 ∧
      M 2 x v = 1 ∧ M 2 w v = 1 ∧ M 2 w w = 0 ∧ M 2 v v = 0 ∧
      ∀ z, z ≠ x → z ≠ w → z ≠ v → M 2 x z = 0 ∧ M 2 w z = 0 ∧ M 2 v z = 0) :=
  repS3_of_eq L.T_symm L.invol L.T_σ L.T_row L.T_off hx

/-- Every diagonal entry of the action matrix of label `2` is at most two. -/
theorem T_le_two (x : κ) : M 2 x x ≤ 2 := by
  by_cases hx : σ x = x
  · rcases L.of_eq hx with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · rcases L.of_ne hx with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- The diagonal of the action matrix of label `2` is invariant under the involution `σ`. -/
theorem T_σσ (x : κ) : M 2 (σ x) (σ x) = M 2 x x := by
  rw [L.T_σ, L.T_symm, L.T_σ]

/-- Assembling a summand of a representation of `su(2)₄` from the actions of `1/2` and `1` on a
family of blocks closed under them and under the involution `σ` of `2`. -/
theorem isNIMRepSummand {k : ℕ} {M' : Fin 5 → Matrix (Fin k) (Fin k) ℕ} (hM'0 : M' 0 = 1)
    {π : Fin k → Fin k} (hM'4 : ∀ i j, M' 4 i j = if j = π i then 1 else 0)
    (hM'3 : ∀ i j, M' 3 i j = M' 1 i (π j)) {f : Fin k → κ} (hf : Function.Injective f)
    (hfσ : ∀ i, σ (f i) = f (π i))
    (hc1 : ∀ i z, z ∉ Set.range f → M 1 (f i) z = 0)
    (hc2 : ∀ i z, z ∉ Set.range f → M 2 (f i) z = 0)
    (he1 : ∀ i j, M 1 (f i) (f j) = M' 1 i j) (he2 : ∀ i j, M 2 (f i) (f j) = M' 2 i j) :
    IsNIMRepSummand M M' f := by
  have ha : ∀ a : Fin 5, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by decide
  refine ⟨hf, fun a i z hz => ?_, fun a i j => ?_⟩
  · have hne : ∀ l, f l ≠ z := fun l h => hz ⟨l, h⟩
    rcases ha a with rfl | rfl | rfl | rfl | rfl
    · simp [L.unit, hne i]
    · exact hc1 i z hz
    · exact hc2 i z hz
    · rw [L.three]
      refine hc1 i _ fun ⟨j, hj⟩ => hz ⟨π j, ?_⟩
      rw [← hfσ, hj, L.invol]
    · simp [L.perm, hfσ, Ne.symm (hne (π i))]
  · rcases ha a with rfl | rfl | rfl | rfl | rfl
    · rw [L.unit, hM'0]
      by_cases h : i = j
      · subst h
        simp
      · simp only [hf.ne h, ↓reduceIte, Matrix.one_apply_ne h]
    · exact he1 i j
    · exact he2 i j
    · rw [L.three, hfσ, he1, hM'3]
    · simp [L.perm, hfσ, hM'4, hf.eq_iff]

/-- **The module `𝓜_TY` around a `ℤ₃` block** (arXiv:2203.12563, lines 1911–1927): a block fixed
by `2` with `M_1` vanishing on its diagonal lies in a summand isomorphic to `𝓜_TY`. -/
theorem summand_of_fixed_zero {x : κ} (hx : σ x = x) (h0 : M 2 x x = 0) :
    ∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ x ∈ Set.range f := by
  rcases L.of_eq hx with ⟨h2, -⟩ | ⟨h1, -⟩ |
      ⟨-, w, v, hwx, hvx, hwv, hwfix, hvfix, hxw, hxv, hTwv, hww, hvv, hzero⟩
  · omega
  · omega
  obtain ⟨s, hxs, hx0⟩ := exists_eq_one_of_sum_mul_self_eq_one (f := M 1 x)
    (by rw [L.Q_row, h0])
  have hQ1 : ∀ y, y ≠ x → M 1 s y = M 2 x y := fun y hy => by
    have h := L.Q_off x y (Ne.symm hy)
    rwa [Fintype.sum_eq_single s fun z hz => by rw [hx0 z hz, zero_mul], hxs, one_mul] at h
  have hsx : M 1 s x = 1 := by rw [L.Q_symm]; exact hxs
  have hsw : M 1 s w = 1 := (hQ1 w hwx).trans hxw
  have hsv : M 1 s v = 1 := (hQ1 v hvx).trans hxv
  have h3 := sum_three_le (f := fun z => M 1 s z * M 1 s z) (Ne.symm hwx) (Ne.symm hvx) hwv
  simp only [hsx, hsw, hsv, L.Q_row] at h3
  have hss : M 2 s s = 2 := by have := L.T_le_two s; omega
  have hsfix : σ s = s := by
    by_contra h
    rcases L.of_ne h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hs0 : ∀ z, z ≠ s → M 2 s z = 0 := by
    rcases L.of_eq hsfix with ⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h
    · omega
    · omega
  have hsQ0 : ∀ z, z ≠ x → z ≠ w → z ≠ v → M 1 s z = 0 := fun z h1 h2 h3' =>
    mul_self_eq_zero.mp (eq_zero_of_sum_le_three (f := fun z => M 1 s z * M 1 s z)
      (Ne.symm hwx) (Ne.symm hvx) hwv (by simp only [hsx, hsw, hsv, L.Q_row, hss]; omega)
      h1 h2 h3')
  have hsx' : s ≠ x := fun h => by rw [h] at hss; omega
  have hsw' : s ≠ w := fun h => by rw [h] at hss; omega
  have hsv' : s ≠ v := fun h => by rw [h] at hss; omega
  have hrowQ : ∀ y, σ y = y → M 2 y y = 0 → M 1 y s = 1 → ∀ z, z ≠ s → M 1 y z = 0 :=
    fun y _ hyy hys => by
      obtain ⟨t, hyt, hy0⟩ := exists_eq_one_of_sum_mul_self_eq_one (f := M 1 y)
        (by rw [L.Q_row, hyy])
      have hts : t = s := by
        by_contra h
        rw [hy0 s (Ne.symm h)] at hys
        exact zero_ne_one hys
      rw [← hts]
      exact hy0
  have hw0 := hrowQ w hwfix hww (by rw [L.Q_symm]; exact hsw)
  have hv0 := hrowQ v hvfix hvv (by rw [L.Q_symm]; exact hsv)
  have hQx := eq_ite_of_forall (g := M 1 x) (P := fun z => z = s)
    (fun z hz => hz ▸ hxs) hx0
  have hQw := eq_ite_of_forall (g := M 1 w) (P := fun z => z = s)
    (fun z hz => hz ▸ (by rw [L.Q_symm]; exact hsw)) hw0
  have hQv := eq_ite_of_forall (g := M 1 v) (P := fun z => z = s)
    (fun z hz => hz ▸ (by rw [L.Q_symm]; exact hsv)) hv0
  have hQs := eq_ite_of_forall (g := M 1 s) (P := fun z => z = x ∨ z = w ∨ z = v)
    (fun z hz => by rcases hz with rfl | rfl | rfl <;> assumption)
    (fun z hz => by push Not at hz; exact hsQ0 z hz.1 hz.2.1 hz.2.2)
  have hTwx : M 2 w x = 1 := by rw [L.T_symm]; exact hxw
  have hTvx : M 2 v x = 1 := by rw [L.T_symm]; exact hxv
  have hTvw : M 2 v w = 1 := by rw [L.T_symm]; exact hTwv
  have hTx := eq_ite_of_forall (g := M 2 x) (P := fun z => z = w ∨ z = v)
    (fun z hz => by rcases hz with rfl | rfl <;> assumption)
    (fun z hz => by
      push Not at hz
      by_cases hzx : z = x
      · rw [hzx]; exact h0
      · exact (hzero z hzx hz.1 hz.2).1)
  have hTw := eq_ite_of_forall (g := M 2 w) (P := fun z => z = x ∨ z = v)
    (fun z hz => by rcases hz with rfl | rfl <;> assumption)
    (fun z hz => by
      push Not at hz
      by_cases hzw : z = w
      · rw [hzw]; exact hww
      · exact (hzero z hz.1 hzw hz.2).2.1)
  have hTv := eq_ite_of_forall (g := M 2 v) (P := fun z => z = x ∨ z = w)
    (fun z hz => by rcases hz with rfl | rfl <;> assumption)
    (fun z hz => by
      push Not at hz
      by_cases hzv : z = v
      · rw [hzv]; exact hvv
      · exact (hzero z hz.1 hz.2 hzv).2.2)
  refine ⟨![x, w, v, s], L.isNIMRepSummand (π := id) rfl
    (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
    (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
    (injective_vecCons_four (Ne.symm hwx) (Ne.symm hvx) (Ne.symm hsx') hwv (Ne.symm hsw')
      (Ne.symm hsv'))
    (fun i => by fin_cases i <;> simp [hx, hwfix, hvfix, hsfix]) (fun i z hz => ?_)
    (fun i z hz => ?_) (fun i j => ?_) (fun i j => ?_), 0, rfl⟩
  · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
    have hz1 : z ≠ w := by simpa using ne_of_notMem_range hz 1
    have hz2 : z ≠ v := by simpa using ne_of_notMem_range hz 2
    have hz3 : z ≠ s := by simpa using ne_of_notMem_range hz 3
    fin_cases i <;> simp [hQx, hQw, hQv, hQs, hz0, hz1, hz2, hz3]
  · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
    have hz1 : z ≠ w := by simpa using ne_of_notMem_range hz 1
    have hz2 : z ≠ v := by simpa using ne_of_notMem_range hz 2
    have hz3 : z ≠ s := by simpa using ne_of_notMem_range hz 3
    fin_cases i <;> simp [hTx, hTw, hTv, hs0 z hz3, hz0, hz1, hz2]
  · fin_cases i <;> fin_cases j <;>
      simp [su24TY, hQx, hQw, hQv, hQs, hwx, hvx, hwv, hsx', hsw', hsv', Ne.symm hwx,
        Ne.symm hvx, Ne.symm hwv, Ne.symm hsx', Ne.symm hsw', Ne.symm hsv']
  · fin_cases i <;> fin_cases j <;>
      simp [su24TY, hTx, hTw, hTv, hss, hs0, hwx, hvx, hwv, hsx', hsw', hsv', Ne.symm hwx,
        Ne.symm hvx, Ne.symm hwv, Ne.symm hsx', Ne.symm hsw', Ne.symm hsv']

/-- **The module `𝓜_TY` around a `ℤ₁` block** (arXiv:2203.12563, lines 1911–1927): a block with
`M_1` equal to `2` on its diagonal lies in a summand isomorphic to `𝓜_TY`. Each neighbour `u` of
the block `s` under `1/2` has `s` as its only neighbour, so `u` is fixed by `2` with `M_1`
vanishing on its diagonal. -/
theorem summand_of_two {s : κ} (h2 : M 2 s s = 2) :
    ∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ s ∈ Set.range f := by
  have hsfix : σ s = s := by
    by_contra h
    rcases L.of_ne h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hs0 : ∀ z, z ≠ s → M 2 s z = 0 := by
    rcases L.of_eq hsfix with ⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h
    · omega
    · omega
  have hrow := L.Q_row s
  rw [h2] at hrow
  -- every neighbour of `s` has `s` as its only neighbour
  have hnb : ∀ u, M 1 s u ≠ 0 → ∀ v, v ≠ s → M 1 u v = 0 := fun u hu v hv => by
    have h := L.Q_off s v (Ne.symm hv)
    rw [hs0 v hv] at h
    have hle := Finset.single_le_sum (fun z _ => Nat.zero_le (M 1 s z * M 1 z v))
      (Finset.mem_univ u)
    rw [h] at hle
    exact (mul_eq_zero.mp (by omega)).resolve_left hu
  -- a neighbour with a single neighbour has `M_1` vanishing on its diagonal
  have hlone : ∀ u, M 1 s u ≠ 0 → u ≠ s ∧ M 2 u u = 0 := fun u hu => by
    have hrowu := L.Q_row u
    rw [Fintype.sum_eq_single s fun z hz => by rw [hnb u hu z hz, zero_mul]] at hrowu
    have hle := L.T_le_two u
    have hus : M 1 u s ≠ 0 := by rwa [L.Q_symm]
    refine ⟨fun h => ?_, ?_⟩
    · rw [h] at hu
      have h' := hrow
      rw [Fintype.sum_eq_single s fun z hz => by rw [hnb s hu z hz, zero_mul]] at h'
      exact mul_self_ne_two_three.2 (by omega)
    · rcases Nat.lt_or_ge (M 1 u s) 2 with h' | h'
      · interval_cases (M 1 u s) <;> omega
      · nlinarith
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun z => M 1 s z * M 1 s z) (by omega)
  have hsu : M 1 s u ≠ 0 := fun h => hu (by simp [h])
  obtain ⟨hus, huu⟩ := hlone u hsu
  have hufix : σ u = u := by
    by_contra hne
    rcases L.of_ne hne with ⟨h1, -⟩ | ⟨-, w, hwu, -, -, huw, hww, -, -⟩
    · omega
    have h := L.Q_off u w (Ne.symm hwu)
    rw [Fintype.sum_eq_single s fun z hz => by rw [hnb u hsu z hz, zero_mul], huw] at h
    have hsw : M 1 s w ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
    have := (hlone w hsw).2
    omega
  obtain ⟨f, hf, i, hi⟩ := L.summand_of_fixed_zero hufix huu
  exact ⟨f, hf, hf.mem_range (a := 1) (u := i) (by rw [hi, L.Q_symm]; exact hsu)⟩

/-- **The regular `su(2)₄` phase around a corner of an `S₃` block** (arXiv:2203.12563,
line 1909): a block moved by `2` with `M_1` vanishing on its diagonal lies in a summand
isomorphic to the regular representation. With `a ↦ 0`, the neighbour `p` of `a` under `1/2`
is `1/2`, the middle block `w` of the `S₃` summand is `1`, `σ p` is `3/2` and `σ a` is `2`. -/
theorem summand_of_corner {a : κ} (ha : σ a ≠ a) (h0 : M 2 a a = 0) :
    ∃ f : Fin 5 → κ, IsNIMRepSummand M su24Fusion f ∧ a ∈ Set.range f := by
  rcases L.of_ne ha with ⟨h1, -⟩ | ⟨-, w, hwa, hwb, hwfix, haw, hww, ha0, hw0⟩
  · omega
  have hab : a ≠ σ a := fun h => ha h.symm
  obtain ⟨p, hap, ha0Q⟩ := exists_eq_one_of_sum_mul_self_eq_one (f := M 1 a)
    (by rw [L.Q_row, h0])
  have hpv : ∀ v, v ≠ a → M 1 p v = M 2 a v := fun v hv => by
    have h := L.Q_off a v (Ne.symm hv)
    rwa [Fintype.sum_eq_single p fun z hz => by rw [ha0Q z hz, zero_mul], hap, one_mul] at h
  have hpw : M 1 p w = 1 := (hpv w hwa).trans haw
  have hpa : M 1 p a = 1 := by rw [L.Q_symm]; exact hap
  have hp0 : ∀ v, v ≠ a → v ≠ w → M 1 p v = 0 := fun v hva hvw =>
    (hpv v hva).trans (ha0 v hvw)
  have hpfix : σ p ≠ p := fun h => by
    have h' := L.Q_σ p a
    rw [h, hpa] at h'
    rw [hp0 (σ a) (Ne.symm hab) (Ne.symm hwb)] at h'
    exact zero_ne_one h'.symm
  have hpa' : p ≠ a := fun h => by
    rw [h] at hpw
    rw [ha0Q w (fun h' => hwa (h'.trans h))] at hpw
    exact zero_ne_one hpw
  have hpw' : p ≠ w := fun h => hpfix (by rw [h, hwfix])
  have hpp : M 2 p p = 1 := by
    have h := L.Q_row p
    rw [← Finset.sum_subset (Finset.subset_univ {a, w}) fun z _ hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        rw [hp0 z hz.1 hz.2, zero_mul],
      Finset.sum_pair (Ne.symm hwa), hpa, hpw] at h
    omega
  rcases L.of_ne hpfix with ⟨-, hpT0⟩ | ⟨h0', -⟩
  swap
  · omega
  have hbb : M 2 (σ a) (σ a) = 0 := by rw [L.T_σσ, h0]
  have hp'p' : M 2 (σ p) (σ p) = 1 := by rw [L.T_σσ, hpp]
  have hpb : p ≠ σ a := fun h => by rw [h, hbb] at hpp; exact zero_ne_one hpp
  have hp'a : σ p ≠ a := fun h => by rw [h, h0] at hp'p'; exact zero_ne_one hp'p'
  have hp'b : σ p ≠ σ a := fun h => by rw [h, hbb] at hp'p'; exact zero_ne_one hp'p'
  have hwp' : w ≠ σ p := fun h => hpw' (by rw [← L.invol p, ← h, hwfix])
  have hpp' : p ≠ σ p := fun h => hpfix h.symm
  -- the rows of `M_{1/2}`
  have hQa := eq_ite_of_forall (g := M 1 a) (P := fun z => z = p) (fun z hz => hz ▸ hap) ha0Q
  have hQp := eq_ite_of_forall (g := M 1 p) (P := fun z => z = a ∨ z = w)
    (fun z hz => by rcases hz with rfl | rfl <;> assumption)
    (fun z hz => by push Not at hz; exact hp0 z hz.1 hz.2)
  have hQp' : ∀ z, M 1 (σ p) z = if z = σ a ∨ z = w then 1 else 0 := fun z => by
    rw [L.Q_σ, hQp]
    have e1 : (σ z = a) ↔ (z = σ a) := ⟨fun h => by rw [← h, L.invol], fun h => by
      rw [h, L.invol]⟩
    have e2 : (σ z = w) ↔ (z = w) := ⟨fun h => by rw [← L.invol z, h, hwfix], fun h => by
      rw [h, hwfix]⟩
    simp only [e1, e2]
  have hQb : ∀ z, M 1 (σ a) z = if z = σ p then 1 else 0 := fun z => by
    rw [L.Q_σ, hQa]
    have e : (σ z = p) ↔ (z = σ p) := ⟨fun h => by rw [← h, L.invol], fun h => by
      rw [h, L.invol]⟩
    simp only [e]
  have hQw : ∀ z, M 1 w z = if z = p ∨ z = σ p then 1 else 0 := by
    have hwp : M 1 w p = 1 := by rw [L.Q_symm]; exact hpw
    have hwp2 : M 1 w (σ p) = 1 := by rw [L.Q_symm, hQp']; simp
    refine eq_ite_of_forall (fun z hz => by rcases hz with rfl | rfl <;> assumption)
      fun z hz => ?_
    push Not at hz
    have h := L.Q_row w
    rw [hww] at h
    exact mul_self_eq_zero.mp (eq_zero_of_sum_le_pair (f := fun z => M 1 w z * M 1 w z) hpp'
      (by simp only [hwp, hwp2, h]; omega) hz.1 hz.2)
  -- the rows of `M_1`
  have hTa := eq_ite_of_forall (g := M 2 a) (P := fun z => z = w) (fun z hz => hz ▸ haw) ha0
  have hTb : ∀ z, M 2 (σ a) z = if z = w then 1 else 0 := fun z => by rw [L.T_σ, hTa]
  have hTw : ∀ z, M 2 w z = if z = a ∨ z = w ∨ z = σ a then 1 else 0 :=
    eq_ite_of_forall
      (fun z hz => by
        rcases hz with rfl | rfl | rfl
        · rw [L.T_symm]; exact haw
        · exact hww
        · rw [L.T_symm, hTb]; simp)
      (fun z hz => by push Not at hz; exact hw0 z hz.1 hz.2.2 hz.2.1)
  have hTp : ∀ z, M 2 p z = if z = p ∨ z = σ p then 1 else 0 :=
    eq_ite_of_forall
      (fun z hz => by
        rcases hz with rfl | rfl
        · exact hpp
        · rw [L.T_symm, L.T_σ, hpp])
      (fun z hz => by push Not at hz; exact hpT0 z hz.1 hz.2)
  have hTp' : ∀ z, M 2 (σ p) z = if z = p ∨ z = σ p then 1 else 0 := fun z => by
    rw [L.T_σ, hTp]
  refine ⟨![a, p, w, σ p, σ a], L.isNIMRepSummand (π := su24Reflect) rfl
    su24Fusion_four_apply su24Fusion_three_apply
    (injective_vecCons_five (Ne.symm hpa') (Ne.symm hwa) (Ne.symm hp'a) hab hpw' hpp' hpb hwp'
      hwb hp'b)
    (fun i => by fin_cases i <;> simp [su24Reflect, hwfix, L.invol]) (fun i z hz => ?_)
    (fun i z hz => ?_) (fun i j => ?_) (fun i j => ?_), 0, rfl⟩
  · have hz0 : z ≠ a := by simpa using ne_of_notMem_range hz 0
    have hz1 : z ≠ p := by simpa using ne_of_notMem_range hz 1
    have hz2 : z ≠ w := by simpa using ne_of_notMem_range hz 2
    have hz3 : z ≠ σ p := by simpa using ne_of_notMem_range hz 3
    have hz4 : z ≠ σ a := by simpa using ne_of_notMem_range hz 4
    fin_cases i <;> simp [hQa, hQp, hQw, hQp', hQb, hz0, hz1, hz2, hz3, hz4]
  · have hz0 : z ≠ a := by simpa using ne_of_notMem_range hz 0
    have hz1 : z ≠ p := by simpa using ne_of_notMem_range hz 1
    have hz2 : z ≠ w := by simpa using ne_of_notMem_range hz 2
    have hz3 : z ≠ σ p := by simpa using ne_of_notMem_range hz 3
    have hz4 : z ≠ σ a := by simpa using ne_of_notMem_range hz 4
    fin_cases i <;> simp [hTa, hTp, hTw, hTp', hTb, hz0, hz1, hz2, hz3, hz4]
  · fin_cases i <;> fin_cases j <;>
      simp [su24Fusion, hQa, hQp, hQw, hQp', hQb, hpa', hwa, hp'a, hab, hpw', hpp', hpb, hwp',
        hwb, hp'b, Ne.symm hpa', Ne.symm hwa, Ne.symm hp'a, Ne.symm hab, Ne.symm hpw',
        Ne.symm hpp', Ne.symm hpb, Ne.symm hwp', Ne.symm hwb, Ne.symm hp'b]
  · fin_cases i <;> fin_cases j <;>
      simp [su24Fusion, hTa, hTp, hTw, hTp', hTb, hpa', hwa, hp'a, hab, hpw', hpp', hpb, hwp',
        hwb, hp'b, Ne.symm hpa', Ne.symm hwa, Ne.symm hp'a, Ne.symm hab, Ne.symm hpw',
        Ne.symm hpp', Ne.symm hpb, Ne.symm hwp', Ne.symm hwb, Ne.symm hp'b]

/-- A block fixed by the involution `σ` of `2` lies in a summand isomorphic to the regular
representation or to `𝓜_TY`. If `M_1` is `1` on its diagonal, the block is the middle block `1`
of a regular summand built around a corner. -/
theorem summand_of_fixed {x : κ} (hx : σ x = x) :
    (∃ f : Fin 5 → κ, IsNIMRepSummand M su24Fusion f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ x ∈ Set.range f) := by
  rcases L.of_eq hx with ⟨h2, -⟩ | ⟨-, w, hw, hxw⟩ | ⟨h0, -⟩
  · exact Or.inr (L.summand_of_two h2)
  · have hwx : M 2 w x ≠ 0 := by rwa [L.T_symm]
    rcases L.of_ne hw with ⟨-, hw0⟩ | ⟨h0, -⟩
    · have hxw' : x ≠ w := fun h => hw (by rw [← h]; exact hx)
      have hxσ : x ≠ σ w := fun h => by
        rw [h, L.invol] at hx
        exact hw hx.symm
      exact absurd (hw0 x hxw' hxσ) hwx
    · obtain ⟨f, hf, i, rfl⟩ := L.summand_of_corner hw h0
      exact Or.inl ⟨f, hf, hf.mem_range hwx⟩
  · exact Or.inr (L.summand_of_fixed_zero hx h0)

/-- Every block lies in a summand isomorphic to the regular representation or to `𝓜_TY`. A block
`x` moved by `σ` with `M_1` equal to `1` on its diagonal (the block `1/2` or `3/2` of a regular
summand) has a neighbour under `1/2` fixed by `σ`: by `1/2 × 1/2 = 0 + 1`,
`∑_z (M_{1/2})_{xz} (M_{1/2})_{x,σz} = (M_1)_{x,σx} = 1`, and a neighbour `z ≠ σz` would
contribute the two terms at `z` and `σz`. -/
theorem summand (x : κ) :
    (∃ f : Fin 5 → κ, IsNIMRepSummand M su24Fusion f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ x ∈ Set.range f) := by
  by_cases hx : σ x = x
  · exact L.summand_of_fixed hx
  rcases L.of_ne hx with ⟨h1, -⟩ | ⟨h0, -⟩
  swap
  · exact Or.inl (L.summand_of_corner hx h0)
  have hsum : ∑ z, M 1 x z * M 1 x (σ z) = 1 := by
    have h := L.Q_off x (σ x) fun h => hx h.symm
    rw [L.T_symm, L.T_σ, h1] at h
    rw [← h]
    exact Finset.sum_congr rfl fun z _ =>
      congrArg (M 1 x z * ·) ((L.Q_symm x (σ z)).trans (L.Q_σ z x))
  obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun z => M 1 x z * M 1 x (σ z)) (by omega)
  have hzx : M 1 z x ≠ 0 := by
    rw [L.Q_symm]
    exact fun h => hz (by simp [h])
  by_cases hzf : σ z = z
  · rcases L.summand_of_fixed hzf with ⟨f, hf, i, rfl⟩ | ⟨f, hf, i, rfl⟩
    · exact Or.inl ⟨f, hf, hf.mem_range hzx⟩
    · exact Or.inr ⟨f, hf, hf.mem_range hzx⟩
  · have h := sum_pair_le (f := fun z => M 1 x z * M 1 x (σ z)) (Ne.symm hzf)
    simp only [L.invol, hsum] at h
    have hz' : M 1 x z * M 1 x (σ z) ≠ 0 := hz
    rw [mul_comm (M 1 x (σ z))] at h
    omega

end SU24Local

/-- **Classification of the dual representations of `su(2)₄`** (arXiv:2203.12563,
lines 1906–1925: "there are only two different phases associated to this MPO algebra"). In a
nonnegative integer representation of `su(2)₄` on any finite set of blocks, with the unit acting
trivially and every label acting by a symmetric matrix (the duality of a module category, all
labels being self-dual), every block lies in a direct summand isomorphic to the regular phase
(five blocks) or to the phase `𝓜_TY` (four blocks). -/
theorem exists_isNIMRepSummand_su24 (hM : IsNIMRep su24Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) (x : κ) :
    (∃ f : Fin 5 → κ, IsNIMRepSummand M su24Fusion f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 4 → κ, IsNIMRepSummand M su24TY f ∧ x ∈ Set.range f) := by
  obtain ⟨σ, L⟩ := su24_exists_local hM hunit hdual
  exact L.summand x

/-- **The indecomposable dual representations of `su(2)₄` are the two printed phases**
(arXiv:2203.12563, lines 1906–1925). A nonempty dual representation with trivial unit on which
`1/2` acts indecomposably is, up to relabelling the blocks, the regular phase or `𝓜_TY`. -/
theorem exists_equiv_of_isIndecomposable_su24 [Nonempty κ] (hM : IsNIMRep su24Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id)
    (hind : Matrix.IsIndecomposable (M 1)) :
    (∃ e : κ ≃ Fin 5, ∀ a x y, M a x y = su24Fusion a (e x) (e y)) ∨
    (∃ e : κ ≃ Fin 4, ∀ a x y, M a x y = su24TY a (e x) (e y)) := by
  obtain ⟨x⟩ := ‹Nonempty κ›
  rcases exists_isNIMRepSummand_su24 hM hunit hdual x with ⟨f, hf, -⟩ | ⟨f, hf, -⟩
  · exact Or.inl (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))
  · exact Or.inr (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))

end SU24

end MPOTensor
