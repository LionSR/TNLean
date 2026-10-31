/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.RepS3SU24NIMRepClassification.Basic

/-!
# Classification of the dual nonnegative integer representations of `Rep(S₃)`

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), Section `sec:examples`,
`Papers/2203.12563/REsubmission.tex` lines 1933–1989: every phase of matrix product states
symmetric under the `Rep(S₃)` matrix product operator algebra is labelled by a subgroup `ℤ₁`,
`ℤ₂`, `ℤ₃` or `S₃`, with the four printed actions on the blocks. The source takes completeness
of this list from the classification of module categories, which it cites. Every label of
`Rep(S₃)` is self-dual, so the duality of lines 564–565 reads `M_a = M_aᵀ`.

**Formalized here.** On any finite set of blocks, every block of a dual representation of
`Rep(S₃)` with trivial unit lies in a direct summand isomorphic to one of the printed actions,
and an indecomposable representation is one of them. The two-block representation `M_ψ = 1`,
`M_π = [[0, 1], [2, 1]]` satisfies the representation identity but not the duality, so the
duality hypothesis cannot be dropped.

The proof is local. Since `M_ψ² = 1` and `M_ψ` is a symmetric natural matrix, it is the
permutation matrix of an involution `σ`. Writing `T = M_π`, the relations `T = M_ψ T` and
`T² = 1 + T + M_ψ` give, on the diagonal, `∑_z T_{xz}² = 1 + T_{xx} + [σx = x]`. A block moved
by `σ` lies in a `ℤ₂` summand (`T_{xx} = 1`) or is a corner of an `S₃` summand
(`T_{xx} = 0`); a block fixed by `σ` lies in a `ℤ₁` summand (`T_{xx} = 2`), is the middle
block of an `S₃` summand, or lies in a `ℤ₃` summand.

**Scope restriction (printed list):** the input is the nonnegative integer representation of a
module category, not the module category itself; the lists are identified at the level of the
multiplicities. Documented in `docs/paper-gaps/glm23_reps3_su24_module_list.tex`.

## Main definitions

* `MPOTensor.repS3NonDual`: a two-block representation that is not dual.

## Main results

* `MPOTensor.exists_isNIMRepSummand_repS3`: every block of a dual representation of `Rep(S₃)`
  with trivial unit lies in a summand isomorphic to the `ℤ₁`, `ℤ₂`, `ℤ₃` or `S₃` phase.
* `MPOTensor.exists_equiv_of_isIndecomposable_repS3`: the indecomposable ones are exactly these
  four.
* `MPOTensor.isNIMRep_repS3NonDual`, `MPOTensor.not_isTransposeDual_repS3NonDual`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

namespace MPOTensor

variable {ι κ κ' : Type*}

/-! ### The local structure of a dual representation of `Rep(S₃)` -/

section RepS3Local

variable [Fintype κ] [DecidableEq κ] {T : κ → κ → ℕ} {σ : κ → κ}

/-- **A block moved by `ψ`.** For a symmetric `T` with `T (σ x) = T x` and the diagonal
relation `∑_z T_{xz}² = 1 + T_{xx} + [σx = x]`, a block `x` with `σx ≠ x` either lies with `σx`
in a `ℤ₂` summand, or has a unique neighbour `w`, fixed by `σ`, with `T_{ww} = 1` and no
neighbours besides `x`, `σx`, `w` (the `S₃` summand). -/
theorem repS3_of_ne
    (hT : ∀ x y, T x y = T y x) (hTσ : ∀ x y, T (σ x) y = T x y)
    (hrow : ∀ x, ∑ z, T x z * T x z = 1 + T x x + if σ x = x then 1 else 0)
    (hoff : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, T x z * T z y = T x y)
    {x : κ} (hx : σ x ≠ x) :
    (T x x = 1 ∧ ∀ z, z ≠ x → z ≠ σ x → T x z = 0) ∨
    (T x x = 0 ∧ ∃ w, w ≠ x ∧ w ≠ σ x ∧ σ w = w ∧ T x w = 1 ∧ T w w = 1 ∧
      (∀ z, z ≠ w → T x z = 0) ∧ ∀ z, z ≠ x → z ≠ σ x → z ≠ w → T w z = 0) := by
  have hxy : x ≠ σ x := fun h => hx h.symm
  have hTxy : T x (σ x) = T x x := by rw [hT, hTσ]
  have hr := hrow x
  simp only [hx, ↓reduceIte, add_zero] at hr
  have h2 := sum_pair_le (f := fun z => T x z * T x z) hxy
  simp only [hTxy, hr] at h2
  have hle : T x x ≤ 1 := by nlinarith
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · right
    refine ⟨h0, ?_⟩
    rw [h0] at hr
    obtain ⟨w, hw1, hw0⟩ := exists_eq_one_of_sum_mul_self_eq_one (f := T x) (by simpa using hr)
    have hwx : w ≠ x := by
      rintro rfl
      omega
    have hwy : w ≠ σ x := by
      rintro rfl
      omega
    have hTwx : T w x = 1 := by rw [hT]; exact hw1
    have hTwy : T w (σ x) = 1 := by rw [hT, hTσ]; exact hw1
    have hrw := hrow w
    have h3 := sum_three_le (f := fun z => T w z * T w z) hxy (Ne.symm hwx) (Ne.symm hwy)
    simp only [hTwx, hTwy, hrw] at h3
    have hwfix : σ w = w := by
      by_contra hne
      simp only [hne, ↓reduceIte] at h3
      nlinarith
    simp only [hwfix, ↓reduceIte] at hrw h3
    have hww : T w w = 1 := by
      have h := hoff x w (Ne.symm hwx) hwy
      rw [Fintype.sum_eq_single w fun z hz => by rw [hw0 z hz, zero_mul], hw1, one_mul] at h
      exact h
    refine ⟨w, hwx, hwy, hwfix, hw1, hww, hw0, fun z hzx hzy hzw => ?_⟩
    have h := eq_zero_of_sum_le_three (f := fun z => T w z * T w z) hxy (Ne.symm hwx)
      (Ne.symm hwy) (by simp only [hTwx, hTwy, hww, hrw]; omega) hzx hzy hzw
    exact mul_self_eq_zero.mp h
  · left
    refine ⟨h1, fun z hzx hzy => ?_⟩
    have h := eq_zero_of_sum_le_pair (f := fun z => T x z * T x z) hxy
      (by simp only [hTxy, hr, h1]; omega) hzx hzy
    exact mul_self_eq_zero.mp h

/-- **A block fixed by `ψ`.** With the hypotheses of `repS3_of_ne`, a block `x` with `σx = x`
lies in a `ℤ₁` summand (`T_{xx} = 2`), or is a neighbour of a block moved by `σ` with
`T_{xx} = 1` (the middle of an `S₃` summand), or lies with two neighbours `w`, `v`, both fixed by
`σ`, in a `ℤ₃` summand. -/
theorem repS3_of_eq
    (hT : ∀ x y, T x y = T y x) (hσσ : ∀ x, σ (σ x) = x) (hTσ : ∀ x y, T (σ x) y = T x y)
    (hrow : ∀ x, ∑ z, T x z * T x z = 1 + T x x + if σ x = x then 1 else 0)
    (hoff : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, T x z * T z y = T x y)
    {x : κ} (hx : σ x = x) :
    (T x x = 2 ∧ ∀ z, z ≠ x → T x z = 0) ∨
    (T x x = 1 ∧ ∃ w, σ w ≠ w ∧ T x w ≠ 0) ∨
    (T x x = 0 ∧ ∃ w v, w ≠ x ∧ v ≠ x ∧ w ≠ v ∧ σ w = w ∧ σ v = v ∧ T x w = 1 ∧ T x v = 1 ∧
      T w v = 1 ∧ T w w = 0 ∧ T v v = 0 ∧
      ∀ z, z ≠ x → z ≠ w → z ≠ v → T x z = 0 ∧ T w z = 0 ∧ T v z = 0) := by
  have hr := hrow x
  simp only [hx, ↓reduceIte] at hr
  have hsq := Finset.single_le_sum (fun z _ => Nat.zero_le (T x z * T x z)) (Finset.mem_univ x)
  rw [hr] at hsq
  have hle : T x x ≤ 2 := by nlinarith
  by_cases h2 : T x x = 2
  · left
    refine ⟨h2, fun z hzx => mul_self_eq_zero.mp ?_⟩
    have h := Finset.add_le_sum (fun z _ => Nat.zero_le (T x z * T x z)) (Finset.mem_univ x)
      (Finset.mem_univ z) (Ne.symm hzx)
    rw [hr, h2] at h
    omega
  have hle1 : T x x ≤ 1 := by omega
  have htt : T x x * T x x = T x x := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h | h <;> rw [h]
  -- a neighbour of `x` other than `x`
  have hex : ∃ w, w ≠ x ∧ T x w ≠ 0 := by
    by_contra hne
    push Not at hne
    have h := Fintype.sum_eq_single (f := fun z => T x z * T x z) x
      fun z hz => by rw [hne z hz, zero_mul]
    rw [hr, htt] at h
    omega
  by_cases hmov : ∃ w, w ≠ x ∧ σ w ≠ w ∧ T x w ≠ 0
  · right; left
    obtain ⟨w, hwx, hw, hxw⟩ := hmov
    refine ⟨?_, w, hw, hxw⟩
    have hwx' : T w x ≠ 0 := by rwa [hT]
    rcases repS3_of_ne hT hTσ hrow hoff hw with ⟨-, h0⟩ | ⟨-, u, hux, -, -, -, huu, hw0, -⟩
    · refine absurd (h0 x (Ne.symm hwx) fun h => hwx ?_) hwx'
      rw [← hσσ w, ← h, hx]
    · have hux' : u = x := by
        by_contra hne
        exact hwx' (hw0 x (Ne.symm hne))
      rw [← hux']
      exact huu
  · right; right
    push Not at hmov
    obtain ⟨w, hwx, hxw⟩ := hex
    have hwfix : σ w = w := by
      by_contra h
      exact hxw (hmov w hwx h)
    have h2' := Finset.add_le_sum (fun z _ => Nat.zero_le (T x z * T x z)) (Finset.mem_univ x)
      (Finset.mem_univ w) (Ne.symm hwx)
    simp only [hr, htt] at h2'
    have hxw1 : T x w = 1 := by
      rcases Nat.lt_or_ge (T x w) 2 with h | h
      · omega
      · nlinarith
    -- a second neighbour
    have hex' : ∃ v, v ≠ x ∧ v ≠ w ∧ T x v ≠ 0 := by
      by_contra hne
      push Not at hne
      have h := Finset.sum_subset (Finset.subset_univ {x, w})
        (f := fun z => T x z * T x z) fun z _ hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
          rw [hne z hz.1 hz.2, zero_mul]
      rw [Finset.sum_pair (Ne.symm hwx), hr, htt, hxw1] at h
      omega
    obtain ⟨v, hvx, hvw, hxv⟩ := hex'
    have hvfix : σ v = v := by
      by_contra h
      exact hxv (hmov v hvx h)
    have h3 := sum_three_le (f := fun z => T x z * T x z) (Ne.symm hwx) (Ne.symm hvx)
      (Ne.symm hvw)
    simp only [hr, htt, hxw1] at h3
    have hxv1 : T x v = 1 := by
      rcases Nat.lt_or_ge (T x v) 2 with h | h
      · omega
      · nlinarith
    have hx0 : ∀ z, z ≠ x → z ≠ w → z ≠ v → T x z = 0 := fun z hzx hzw hzv =>
      mul_self_eq_zero.mp (eq_zero_of_sum_le_three (f := fun z => T x z * T x z)
        (Ne.symm hwx) (Ne.symm hvx) (Ne.symm hvw)
        (by simp only [hr, htt, hxw1, hxv1]; omega) hzx hzw hzv)
    -- the off-diagonal relations at `(x, w)` and `(w, v)`
    have hxw' := hoff x w (Ne.symm hwx) (by rw [hx]; exact hwx)
    rw [← Finset.sum_subset (Finset.subset_univ {x, w, v}) fun z _ hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        rw [hx0 z hz.1 hz.2.1 hz.2.2, zero_mul],
      Finset.sum_insert (by simp [Ne.symm hwx, Ne.symm hvx]), Finset.sum_pair (Ne.symm hvw),
      hxw1, hxv1] at hxw'
    have hwv' := hoff w v (Ne.symm hvw) (by rw [hwfix]; exact hvw)
    have hwv3 := sum_three_le (f := fun z => T w z * T z v) (Ne.symm hwx) (Ne.symm hvx)
      (Ne.symm hvw)
    rw [hwv'] at hwv3
    have hTwx : T w x = 1 := by rw [hT]; exact hxw1
    have hTvw : T v w = T w v := hT v w
    simp only [hTwx, hxv1] at hwv3
    have hwv1 : 1 ≤ T w v := by omega
    have hdiag : T w w + T v v = 0 := by nlinarith
    have hww : T w w = 0 := by omega
    have hvv : T v v = 0 := by omega
    rw [hww, hTvw] at hxw'
    have hxx : T x x = 0 := by omega
    have hwv : T w v = 1 := by omega
    refine ⟨hxx, w, v, hwx, hvx, hvw.symm, hwfix, hvfix, hxw1, hxv1, hwv, hww, hvv,
      fun z hzx hzw hzv => ⟨hx0 z hzx hzw hzv, ?_, ?_⟩⟩
    · have hrw := hrow w
      simp only [hwfix, hww, ↓reduceIte] at hrw
      exact mul_self_eq_zero.mp (eq_zero_of_sum_le_three (f := fun z => T w z * T w z)
        (Ne.symm hwx) (Ne.symm hvx) (Ne.symm hvw)
        (by simp only [hrw, hTwx, hww, hwv]; omega) hzx hzw hzv)
    · have hrv := hrow v
      simp only [hvfix, hvv, ↓reduceIte] at hrv
      have hTvx : T v x = 1 := by rw [hT]; exact hxv1
      exact mul_self_eq_zero.mp (eq_zero_of_sum_le_three (f := fun z => T v z * T v z)
        (Ne.symm hwx) (Ne.symm hvx) (Ne.symm hvw)
        (by simp only [hrv, hTvx, hTvw, hwv, hvv]; omega) hzx hzw hzv)

end RepS3Local

/-! ### `Rep(S₃)` -/

section RepS3

variable [Fintype κ] [DecidableEq κ] {M : Fin 3 → κ → κ → ℕ}

/-- The relations `ψ × ψ = 1`, `π × ψ = π` and `π × π = 1 + π + ψ` on the blocks
(arXiv:2203.12563, line 1934, through the relation of lines 564–565). -/
private theorem repS3_relations (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (x y : κ) :
    (∑ z, M 2 x z * M 2 z y = if x = y then 1 else 0) ∧
    (∑ z, M 2 x z * M 1 z y = M 1 x y) ∧
    (∑ z, M 1 x z * M 1 z y = (if x = y then 1 else 0) + M 1 x y + M 2 x y) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := hM 2 2 x y
    simp only [repS3Fusion, Fin.sum_univ_three, hunit] at h
    simpa using h.symm
  · have h := hM 1 2 x y
    simp only [repS3Fusion, Fin.sum_univ_three] at h
    simpa using h.symm
  · have h := hM 1 1 x y
    simp only [repS3Fusion, Fin.sum_univ_three, hunit] at h
    simpa [add_assoc] using h.symm

/-- **`ψ` acts by an involution of the blocks.** For a dual representation of `Rep(S₃)` with
trivial unit, `M_ψ` is the permutation matrix of an involution `σ` with `M_π (σx) = M_π x`. -/
private theorem repS3_exists_involution (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) :
    ∃ σ : κ → κ, (∀ x y, M 2 x y = if y = σ x then 1 else 0) ∧ (∀ x, σ (σ x) = x) ∧
      ∀ x y, M 1 (σ x) y = M 1 x y := by
  have hrow : ∀ x, ∃ w, M 2 x w = 1 ∧ ∀ u, u ≠ w → M 2 x u = 0 := fun x => by
    refine exists_eq_one_of_sum_mul_self_eq_one ?_
    have h := (repS3_relations hM hunit x x).1
    simp only [↓reduceIte] at h
    rw [← h]
    exact Finset.sum_congr rfl fun z _ => by rw [← hdual 2 z x]; rfl
  choose σ hσ1 hσ0 using hrow
  have hσ : ∀ x y, M 2 x y = if y = σ x then 1 else 0 := fun x y => by
    by_cases h : y = σ x
    · simp only [h, ↓reduceIte, hσ1]
    · simp only [h, ↓reduceIte, hσ0 x y h]
  refine ⟨σ, hσ, fun x => ?_, fun x y => ?_⟩
  · have h : M 2 (σ x) x = 1 := by rw [← hdual 2 x (σ x)]; exact hσ1 x
    rw [hσ] at h
    by_contra hne
    simp [Ne.symm hne] at h
  · have h := (repS3_relations hM hunit x y).2.1
    rw [Fintype.sum_eq_single (σ x) fun z hz => by rw [hσ0 x z hz, zero_mul], hσ1, one_mul] at h
    exact h

omit [Fintype κ] in
/-- Assembling a summand of a representation of `Rep(S₃)` from the action of `π` on a family
of blocks closed under `π` and under the involution `σ` of `ψ`. -/
private theorem isNIMRepSummand_repS3_of {k : ℕ} {M' : Fin 3 → Matrix (Fin k) (Fin k) ℕ}
    (hM'0 : M' 0 = 1) {π : Fin k → Fin k} (hM'2 : ∀ i j, M' 2 i j = if j = π i then 1 else 0)
    {σ : κ → κ} (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0)
    (hσ : ∀ x y, M 2 x y = if y = σ x then 1 else 0) {f : Fin k → κ}
    (hf : Function.Injective f) (hfσ : ∀ i, σ (f i) = f (π i))
    (hclosed : ∀ i z, z ∉ Set.range f → M 1 (f i) z = 0)
    (hentries : ∀ i j, M 1 (f i) (f j) = M' 1 i j) : IsNIMRepSummand M M' f := by
  have ha : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  refine ⟨hf, fun a i z hz => ?_, fun a i j => ?_⟩
  · have hne : ∀ l, f l ≠ z := fun l h => hz ⟨l, h⟩
    rcases ha a with rfl | rfl | rfl
    · simp [hunit, hne i]
    · exact hclosed i z hz
    · simp [hσ, hfσ, Ne.symm (hne (π i))]
  · rcases ha a with rfl | rfl | rfl
    · rw [hunit, hM'0]
      by_cases h : i = j
      · subst h
        simp
      · simp only [hf.ne h, ↓reduceIte, Matrix.one_apply_ne h]
    · exact hentries i j
    · simp [hσ, hfσ, hM'2, hf.eq_iff]

/-- The local facts behind the classification: the involution `σ` of `ψ`, symmetry of `T = M_π`,
`T (σx) = T x`, the diagonal relation `∑_z T_{xz}² = 1 + T_{xx} + [σx = x]`, and the off-diagonal
relation `∑_z T_{xz} T_{zy} = T_{xy}` away from `y = x` and `y = σx`. -/
theorem repS3_exists_local (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) :
    ∃ σ : κ → κ, (∀ x y, M 2 x y = if y = σ x then 1 else 0) ∧ (∀ x, σ (σ x) = x) ∧
      (∀ x y, M 1 (σ x) y = M 1 x y) ∧ (∀ x y, M 1 x y = M 1 y x) ∧
      (∀ x, ∑ z, M 1 x z * M 1 x z = 1 + M 1 x x + if σ x = x then 1 else 0) ∧
      ∀ x y, x ≠ y → y ≠ σ x → ∑ z, M 1 x z * M 1 z y = M 1 x y := by
  obtain ⟨σ, hσ, hσσ, hTσ⟩ := repS3_exists_involution hM hunit hdual
  have hT : ∀ x y, M 1 x y = M 1 y x := fun x y => (hdual 1 y x).symm
  have hrow : ∀ x, ∑ z, M 1 x z * M 1 x z = 1 + M 1 x x + if σ x = x then 1 else 0 :=
    fun x => by
      have h := (repS3_relations hM hunit x x).2.2
      have e : (if x = σ x then 1 else 0) = (if σ x = x then 1 else 0) := by simp only [eq_comm]
      rw [hσ, e] at h
      simp only [↓reduceIte] at h
      rw [← h]
      exact Finset.sum_congr rfl fun z _ => by rw [hT z x]
  have hoff : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, M 1 x z * M 1 z y = M 1 x y :=
    fun x y hxy hyσ => by
      have h := (repS3_relations hM hunit x y).2.2
      rw [hσ] at h
      simpa [hxy, hyσ] using h
  exact ⟨σ, hσ, hσσ, hTσ, hT, hrow, hoff⟩

omit [Fintype κ] [DecidableEq κ] in
/-- A block outside the range of a family differs from every member of the family. -/
theorem ne_of_notMem_range {k : ℕ} {f : Fin k → κ} {z : κ} (hz : z ∉ Set.range f)
    (i : Fin k) : z ≠ f i := fun h => hz ⟨i, h.symm⟩

/-- The summand of a block moved by the involution of `ψ`: the `ℤ₂` or the `S₃` phase. -/
private theorem repS3_summand_of_ne {σ : κ → κ}
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0)
    (hσ : ∀ x y, M 2 x y = if y = σ x then 1 else 0) (hσσ : ∀ x, σ (σ x) = x)
    (hT : ∀ x y, M 1 x y = M 1 y x) (hTσ : ∀ x y, M 1 (σ x) y = M 1 x y)
    (hrow : ∀ x, ∑ z, M 1 x z * M 1 x z = 1 + M 1 x x + if σ x = x then 1 else 0)
    (hoff : ∀ x y, x ≠ y → y ≠ σ x → ∑ z, M 1 x z * M 1 z y = M 1 x y)
    {x : κ} (hx : σ x ≠ x) :
    (∃ f : Fin 2 → κ, IsNIMRepSummand M repS3Z2 f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 3 → κ, IsNIMRepSummand M repS3Fusion f ∧ x ∈ Set.range f) := by
  have hxy : x ≠ σ x := fun h => hx h.symm
  have hTxy : M 1 x (σ x) = M 1 x x := by rw [hT, hTσ]
  have hTyx : M 1 (σ x) x = M 1 x x := hTσ x x
  have hTyy : M 1 (σ x) (σ x) = M 1 x x := by rw [hTσ, hTxy]
  rcases repS3_of_ne hT hTσ hrow hoff hx with
    ⟨h1, h0⟩ | ⟨h0, w, hwx, hwy, hwfix, hxw, hww, hx0, hw0⟩
  · left
    refine ⟨![x, σ x], isNIMRepSummand_repS3_of (π := ![1, 0]) rfl
      (fun i j => by fin_cases i <;> fin_cases j <;> rfl) hunit hσ
      (injective_vecCons_two hxy) (fun i => ?_) (fun i z hz => ?_) (fun i j => ?_), 0, rfl⟩
    · fin_cases i <;> simp [hσσ]
    · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
      have hz1 : z ≠ σ x := by simpa using ne_of_notMem_range hz 1
      fin_cases i
      · simpa using h0 z hz0 hz1
      · simpa [hTσ] using h0 z hz0 hz1
    · fin_cases i <;> fin_cases j <;> simp [repS3Z2, h1, hTxy, hTyx, hTyy]
  · right
    have hTwx : M 1 w x = 1 := by rw [hT]; exact hxw
    have hTwy : M 1 w (σ x) = 1 := by rw [hT, hTσ]; exact hxw
    have hTyw : M 1 (σ x) w = 1 := by rw [hTσ]; exact hxw
    refine ⟨![x, w, σ x], isNIMRepSummand_repS3_of (π := ![2, 1, 0]) rfl
      (fun i j => by fin_cases i <;> fin_cases j <;> rfl) hunit hσ
      (injective_vecCons_three (Ne.symm hwx) hxy hwy) (fun i => ?_) (fun i z hz => ?_)
      (fun i j => ?_), 0, rfl⟩
    · fin_cases i <;> simp [hσσ, hwfix]
    · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
      have hz1 : z ≠ w := by simpa using ne_of_notMem_range hz 1
      have hz2 : z ≠ σ x := by simpa using ne_of_notMem_range hz 2
      fin_cases i
      · simpa using hx0 z hz1
      · simpa using hw0 z hz0 hz2 hz1
      · simpa [hTσ] using hx0 z hz1
    · fin_cases i <;> fin_cases j <;>
        simp [repS3Fusion, h0, hxw, hww, hTxy, hTyx, hTyy, hTwx, hTwy, hTyw]

/-- **Classification of the dual representations of `Rep(S₃)`** (arXiv:2203.12563,
lines 1933–1989). In a nonnegative integer representation of `Rep(S₃)` on any finite set of
blocks, with the unit acting trivially and every label acting by a symmetric matrix (the
duality of a module category, all labels being self-dual), every block lies in a direct summand
isomorphic to one of the four printed phases: `ℤ₁` (one block), `ℤ₂` (two blocks), `ℤ₃` (three
blocks, with the `ψ` row corrected as in `MPOTensor.repS3Z3`) or `S₃` (the regular
representation). -/
theorem exists_isNIMRepSummand_repS3 (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id) (x : κ) :
    (∃ f : Fin 1 → κ, IsNIMRepSummand M repS3Z1 f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 2 → κ, IsNIMRepSummand M repS3Z2 f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 3 → κ, IsNIMRepSummand M repS3Z3 f ∧ x ∈ Set.range f) ∨
    (∃ f : Fin 3 → κ, IsNIMRepSummand M repS3Fusion f ∧ x ∈ Set.range f) := by
  obtain ⟨σ, hσ, hσσ, hTσ, hT, hrow, hoff⟩ := repS3_exists_local hM hunit hdual
  by_cases hx : σ x = x
  swap
  · rcases repS3_summand_of_ne hunit hσ hσσ hT hTσ hrow hoff hx with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  rcases repS3_of_eq hT hσσ hTσ hrow hoff hx with ⟨h2, h0⟩ | ⟨-, w, hw, hxw⟩ |
      ⟨h0, w, v, hwx, hvx, hwv, hwfix, hvfix, hxw, hxv, hTwv, hww, hvv, hzero⟩
  · left
    refine ⟨![x], isNIMRepSummand_repS3_of (π := ![0]) rfl
      (fun i j => by fin_cases i; fin_cases j; rfl) hunit hσ
      (fun i j _ => Subsingleton.elim i j) (fun i => ?_) (fun i z hz => ?_) (fun i j => ?_),
      0, rfl⟩
    · fin_cases i
      simpa using hx
    · fin_cases i
      simpa using h0 z (by simpa using ne_of_notMem_range hz 0)
    · fin_cases i
      fin_cases j
      simpa [repS3Z1] using h2
  · -- `x` is the middle block of the `S₃` summand of `w`
    have hwx : M 1 w x ≠ 0 := by rwa [hT]
    right; right; right
    rcases repS3_summand_of_ne hunit hσ hσσ hT hTσ hrow hoff hw with
      ⟨f, hf, i, rfl⟩ | ⟨f, hf, i, rfl⟩
    · obtain ⟨j, hj⟩ := hf.mem_range hwx
      have h1 := hf.2.2 2 j j
      rw [hj, hσ, hx] at h1
      fin_cases j <;> simp [repS3Z2] at h1
    · exact ⟨f, hf, hf.mem_range hwx⟩
  · right; right; left
    have hTwx : M 1 w x = 1 := by rw [hT]; exact hxw
    have hTvx : M 1 v x = 1 := by rw [hT]; exact hxv
    have hTvw : M 1 v w = 1 := by rw [hT]; exact hTwv
    refine ⟨![x, w, v], isNIMRepSummand_repS3_of (π := ![0, 1, 2]) rfl
      (fun i j => by fin_cases i <;> fin_cases j <;> rfl) hunit hσ
      (injective_vecCons_three (Ne.symm hwx) (Ne.symm hvx) hwv) (fun i => ?_)
      (fun i z hz => ?_) (fun i j => ?_), 0, rfl⟩
    · fin_cases i <;> simp [hx, hwfix, hvfix]
    · have hz0 : z ≠ x := by simpa using ne_of_notMem_range hz 0
      have hz1 : z ≠ w := by simpa using ne_of_notMem_range hz 1
      have hz2 : z ≠ v := by simpa using ne_of_notMem_range hz 2
      have h := hzero z hz0 hz1 hz2
      fin_cases i
      · simpa using h.1
      · simpa using h.2.1
      · simpa using h.2.2
    · fin_cases i <;> fin_cases j <;>
        simp [repS3Z3, h0, hxw, hxv, hTwv, hww, hvv, hTwx, hTvx, hTvw]

/-- **The indecomposable dual representations of `Rep(S₃)` are the four printed phases**
(arXiv:2203.12563, lines 1933–1989: the phases are labelled by the subgroups `ℤ₁`, `ℤ₂`, `ℤ₃`,
`S₃`). A nonempty dual representation with trivial unit on which `π` acts indecomposably is, up to
relabelling the blocks, the `ℤ₁`, `ℤ₂`, `ℤ₃` or `S₃` phase. -/
theorem exists_equiv_of_isIndecomposable_repS3 [Nonempty κ] (hM : IsNIMRep repS3Fusion M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) (hdual : IsTransposeDual M id)
    (hind : Matrix.IsIndecomposable (M 1)) :
    (∃ e : κ ≃ Fin 1, ∀ a x y, M a x y = repS3Z1 a (e x) (e y)) ∨
    (∃ e : κ ≃ Fin 2, ∀ a x y, M a x y = repS3Z2 a (e x) (e y)) ∨
    (∃ e : κ ≃ Fin 3, ∀ a x y, M a x y = repS3Z3 a (e x) (e y)) ∨
    (∃ e : κ ≃ Fin 3, ∀ a x y, M a x y = repS3Fusion a (e x) (e y)) := by
  obtain ⟨x⟩ := ‹Nonempty κ›
  rcases exists_isNIMRepSummand_repS3 hM hunit hdual x with
    ⟨f, hf, -⟩ | ⟨f, hf, -⟩ | ⟨f, hf, -⟩ | ⟨f, hf, -⟩
  · exact Or.inl (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))
  · exact Or.inr (Or.inl (hf.exists_equiv (hf.surjective_of_isIndecomposable hind)))
  · exact Or.inr (Or.inr (Or.inl (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))))
  · exact Or.inr (Or.inr (Or.inr (hf.exists_equiv (hf.surjective_of_isIndecomposable hind))))

end RepS3

/-! ### A representation that is not dual -/

/-- **A two-block representation of `Rep(S₃)` that is not dual**: `ψ` fixes both blocks and
`π · x₀ = x₁`, `π · x₁ = 2 x₀ + x₁`. It is recorded in
`docs/paper-gaps/glm23_reps3_su24_module_list.tex` as the reason the duality hypothesis of the
classification cannot be dropped. -/
def repS3NonDual : Fin 3 → Matrix (Fin 2) (Fin 2) ℕ
  | 0 => 1
  | 1 => !![0, 1; 2, 1]
  | 2 => 1

/-- The representation `MPOTensor.repS3NonDual` satisfies the relation of arXiv:2203.12563,
lines 564–565. -/
theorem isNIMRep_repS3NonDual : IsNIMRep repS3Fusion repS3NonDual := by
  unfold IsNIMRep; decide +kernel

/-- The representation `MPOTensor.repS3NonDual` is not dual: `M_π` is not symmetric although `π`
is self-dual. So it is neither the `ℤ₂` phase nor a sum of two `ℤ₁` phases. -/
theorem not_isTransposeDual_repS3NonDual : ¬ IsTransposeDual repS3NonDual id := by
  intro h
  have := h 1 0 1
  simp [repS3NonDual] at this

end MPOTensor
