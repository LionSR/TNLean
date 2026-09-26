/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ControlledGateProducts

/-!
# Decomposition of a unitary into two-level rotations and phases

Every unitary `X` on `ℂ^ι` with `det X = 1` is a product of at most `f (card ι)` two-level
operators `twoLevel a b g` with `g` a real rotation `rotTwo z` or a phase `diagTwo ν`
(`MPSPreparation.isTwoLevelWord_of_det_eq_one`). The proof is the column-by-column
elimination of Givens: the column of `X` at `a` is rotated onto `|a⟩` by two-level operators on
the pairs `{a, b}`, after which `X` acts on the orthogonal complement of `|a⟩`.

This is the first step of writing a unitary on a constant number of sites as a product of
two-site gates, the statement "can be further expressed with a low-depth circuit of local
gates" of arXiv:2307.01696 (caption of Fig. 1).
-/

open Matrix
open scoped BigOperators ComplexConjugate

namespace MPSPreparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Words of two-level operators -/

/-- `X` is a product of at most `K` two-level rotations and phases on pairs of distinct basis
vectors. -/
def IsTwoLevelWord (K : ℕ) (X : Matrix ι ι ℂ) : Prop :=
  ∃ l : List (ι × ι × Matrix (Fin 2) (Fin 2) ℂ), l.length ≤ K ∧
    (∀ p ∈ l, p.1 ≠ p.2.1 ∧ IsSpecialTwo p.2.2) ∧
    X = (l.map fun p => twoLevel p.1 p.2.1 p.2.2).prod

namespace IsTwoLevelWord

theorem one (K : ℕ) : IsTwoLevelWord K (1 : Matrix ι ι ℂ) :=
  ⟨[], by simp, by simp, by simp⟩

theorem mono {K K' : ℕ} (h : K ≤ K') {X : Matrix ι ι ℂ} (hX : IsTwoLevelWord K X) :
    IsTwoLevelWord K' X := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  exact ⟨l, hl.trans h, hg, rfl⟩

theorem mul {K K' : ℕ} {X Y : Matrix ι ι ℂ} (hX : IsTwoLevelWord K X)
    (hY : IsTwoLevelWord K' Y) : IsTwoLevelWord (K + K') (X * Y) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  obtain ⟨l', hl', hg', rfl⟩ := hY
  refine ⟨l ++ l', by simp; omega, fun p hp => ?_, by simp⟩
  rcases List.mem_append.mp hp with h | h
  · exact hg p h
  · exact hg' p h

theorem single {a b : ι} (hab : a ≠ b) {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : IsSpecialTwo g) :
    IsTwoLevelWord 1 (twoLevel a b g) :=
  ⟨[(a, b, g)], by simp, by simpa using ⟨hab, hg⟩, by simp⟩

theorem conjTranspose {K : ℕ} {X : Matrix ι ι ℂ} (hX : IsTwoLevelWord K X) :
    IsTwoLevelWord K Xᴴ := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  refine ⟨(l.map fun p => (p.1, p.2.1, p.2.2ᴴ)).reverse, by simpa using hl, fun p hp => ?_, ?_⟩
  · simp only [List.mem_reverse, List.mem_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    exact ⟨(hg p' hp').1, (hg p' hp').2.conjTranspose⟩
  · clear hl hg
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, conjTranspose_mul, List.reverse_cons,
        List.map_append, List.prod_append, ih, List.map_nil, List.prod_nil, mul_one,
        twoLevel_conjTranspose, List.prod_cons]

theorem mem_unitary {K : ℕ} {X : Matrix ι ι ℂ} (hX : IsTwoLevelWord K X) :
    X ∈ unitary (Matrix ι ι ℂ) := by
  obtain ⟨l, -, hg, rfl⟩ := hX
  induction l with
  | nil => exact Submonoid.one_mem _
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Submonoid.mul_mem _ (twoLevel_mem_unitary (hg p (by simp)).1
      (hg p (by simp)).2.mem_unitary) (ih fun q hq => hg q (by simp [hq]))

end IsTwoLevelWord

/-! ### Operators fixing the basis vectors outside a set -/

/-- `X` acts as the identity on the basis vectors outside `T` and maps the span of `T` to
itself. -/
def FixesOutside (T : Finset ι) (X : Matrix ι ι ℂ) : Prop :=
  ∀ x y, (x ∉ T ∨ y ∉ T) → X x y = if x = y then 1 else 0

theorem FixesOutside.mono {T T' : Finset ι} (h : T ⊆ T') {X : Matrix ι ι ℂ}
    (hX : FixesOutside T X) : FixesOutside T' X := fun x y hxy =>
  hX x y (hxy.imp (fun hx hx' => hx (h hx')) fun hy hy' => hy (h hy'))

theorem FixesOutside.mul {T : Finset ι} {X Y : Matrix ι ι ℂ} (hX : FixesOutside T X)
    (hY : FixesOutside T Y) : FixesOutside T (X * Y) := by
  intro x y hxy
  rw [mul_apply]
  rcases hxy with hx | hy
  · simp_rw [hX x _ (Or.inl hx)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hY x y (Or.inl hx)
  · simp_rw [hY _ y (Or.inr hy)]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hX x y (Or.inr hy)

theorem fixesOutside_twoLevel (a b : ι) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    FixesOutside {a, b} (twoLevel a b g) := by
  rintro x y (hx | hy)
  · exact twoLevel_apply_of_not_mem_left g (by simpa using hx) y
  · exact twoLevel_apply_of_not_mem_right g x (by simpa using hy)

theorem fixesOutside_empty {X : Matrix ι ι ℂ} (hX : FixesOutside ∅ X) : X = 1 := by
  ext x y; rw [hX x y (Or.inl (Finset.notMem_empty x)), one_apply]

/-! ### Determinants -/

/-- The two-level operator has the determinant of its `2 × 2` block. -/
theorem det_twoLevel {a b : ι} (hab : a ≠ b) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (twoLevel a b g).det = g.det := by
  let p : ι → Prop := fun x => x = a ∨ x = b
  let e₂ : Fin 2 ≃ {x // p x} :=
    { toFun := fun i => ⟨![a, b] i, by fin_cases i <;> simp [p]⟩
      invFun := fun x => twoLevelIdx a x.1
      left_inv := fun i => by fin_cases i <;> simp [twoLevelIdx, Ne.symm hab]
      right_inv := fun x => by
        obtain ⟨x, rfl | rfl⟩ := x
        · simp [twoLevelIdx]
        · simp [twoLevelIdx, Ne.symm hab] }
  let e : Fin 2 ⊕ {x // ¬p x} ≃ ι := (Equiv.sumCongr e₂ (Equiv.refl _)).trans (Equiv.sumCompl p)
  have h : (twoLevel a b g).submatrix e e = fromBlocks g 0 0 1 := by
    ext (i | x) (j | y)
    · simp only [submatrix_apply, fromBlocks_apply₁₁, e, e₂, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.coe_fn_mk, Equiv.sumCompl_apply_inl, twoLevel,
        of_apply]
      have hi : p (![a, b] i) := by fin_cases i <;> simp [p]
      have hj : p (![a, b] j) := by fin_cases j <;> simp [p]
      rw [ite_eq_left ⟨hi, hj⟩]
      congr 1
      · fin_cases i <;> simp [twoLevelIdx, Ne.symm hab]
      · fin_cases j <;> simp [twoLevelIdx, Ne.symm hab]
    · simp only [submatrix_apply, fromBlocks_apply₁₂, e, e₂, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.coe_fn_mk,
        Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, Equiv.refl_apply, Matrix.zero_apply]
      rw [twoLevel_apply_of_not_mem_right g _ y.2, ite_eq_right]
      intro h; exact y.2 (h ▸ (by fin_cases i <;> simp [p]))
    · simp only [submatrix_apply, fromBlocks_apply₂₁, e, e₂, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.coe_fn_mk,
        Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, Equiv.refl_apply, Matrix.zero_apply]
      rw [twoLevel_apply_of_not_mem_left g x.2, ite_eq_right]
      intro h; exact x.2 (h ▸ (by fin_cases j <;> simp [p]))
    · simp only [submatrix_apply, fromBlocks_apply₂₂, e, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr, Equiv.refl_apply,
        one_apply]
      rw [twoLevel_apply_of_not_mem_left g x.2]
      simp [Subtype.ext_iff]
  rw [← det_submatrix_equiv_self e, h, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem IsSpecialTwo.det_eq_one {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : IsSpecialTwo g) :
    g.det = 1 := by
  rcases hg with ⟨z, hz, rfl⟩ | ⟨ν, hν, rfl⟩
  · rw [det_fin_two]
    simp only [rotTwo, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons,
      empty_val', cons_val_fin_one, head_fin_const]
    have h := Complex.sq_norm z
    rw [hz, one_pow, Complex.normSq_apply] at h
    rw [neg_mul, sub_neg_eq_add]
    exact_mod_cast h.symm
  · rw [det_fin_two]
    simp only [diagTwo, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons,
      empty_val', cons_val_fin_one, head_fin_const, mul_zero, sub_zero]
    rw [Complex.star_def, Complex.mul_conj', hν]; simp

theorem IsTwoLevelWord.det_eq_one {K : ℕ} {X : Matrix ι ι ℂ} (hX : IsTwoLevelWord K X) :
    X.det = 1 := by
  obtain ⟨l, -, hg, rfl⟩ := hX
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, det_mul, det_twoLevel (hg p (by simp)).1,
      (hg p (by simp)).2.det_eq_one, one_mul]
    exact ih fun q hq => hg q (by simp [hq])

/-! ### Eliminating one entry -/

theorem quarterTwo_eq_rotTwo : quarterTwo = rotTwo (-Complex.I) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quarterTwo, rotTwo]

/-- For every pair `(x, y)` there is a product `g` of at most two rotations and phases with
`(g (x, y))₁ = 0`. -/
theorem exists_twoLevel_elim (x y : ℂ) :
    ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ), l.length ≤ 2 ∧ (∀ g ∈ l, IsSpecialTwo g) ∧
      l.prod 1 0 * x + l.prod 1 1 * y = 0 := by
  by_cases hy : y = 0
  · exact ⟨[], by simp, by simp, by simp [hy]⟩
  by_cases hx : x = 0
  · refine ⟨[quarterTwo], by simp, ?_, by simp [quarterTwo, hx]⟩
    simp only [List.mem_singleton, forall_eq]
    exact Or.inl ⟨-Complex.I, by simp, quarterTwo_eq_rotTwo⟩
  -- `x = |x| p`, `y = |y| q` with `|p| = |q| = 1`; choose `ν² = p̄ q`.
  have hxn : (‖x‖ : ℂ) ≠ 0 := by simpa using hx
  have hyn : (‖y‖ : ℂ) ≠ 0 := by simpa using hy
  set p := x / ‖x‖
  set q := y / ‖y‖
  have hp : ‖p‖ = 1 := by simp [p, norm_div, hx]
  have hq : ‖q‖ = 1 := by simp [q, norm_div, hy]
  have hpc : conj p * p = 1 := by rw [Complex.conj_mul', hp]; simp
  obtain ⟨ν, hν, hνν⟩ := exists_sq_eq_of_norm_eq_one (z := conj p * q) (by simp [hp, hq])
  have hνc : star ν * ν = 1 := by rw [Complex.star_def, Complex.conj_mul', hν]; simp
  have hq' : q = ν * ν * p := by
    rw [hνν, mul_comm (conj p), mul_assoc, hpc, mul_one]
  have hω : star ν * q = ν * p := by
    rw [hq', ← mul_assoc, ← mul_assoc, hνc, one_mul]
  -- the rotation with `cos = |x| / r`, `sin = -|y| / r`.
  set r := Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  let z : ℂ := ⟨‖x‖ / r, -‖y‖ / r⟩
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_eq_one]
    simp only [z]
    field_simp
    exact (Real.sq_sqrt (by positivity)).symm
  refine ⟨[rotTwo z, diagTwo ν], by simp, ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨Or.inl ⟨z, hz, rfl⟩, Or.inr ⟨ν, hν, rfl⟩⟩
  · have hx' : x = ‖x‖ * p := by simp only [p]; field_simp
    have hy' : y = ‖y‖ * q := by simp only [q]; field_simp
    simp only [List.prod_cons, List.prod_nil, mul_one, rotTwo, diagTwo, mul_apply,
      Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, empty_val',
      cons_val_fin_one, head_fin_const, mul_zero, zero_mul, add_zero, zero_add, z]
    push_cast
    linear_combination (-(‖y‖ : ℂ) / r * ν) * hx' + ((‖x‖ : ℂ) / r * star ν) * hy' +
      ((‖x‖ : ℂ) * ‖y‖ / r) * hω

/-! ### Column elimination -/

/-- The rows of `twoLevel a b g * Y`. -/
theorem twoLevel_mul_apply {a b : ι} (hab : a ≠ b) (g : Matrix (Fin 2) (Fin 2) ℂ)
    (Y : Matrix ι ι ℂ) (x y : ι) :
    (twoLevel a b g * Y) x y =
      if x = a then g 0 0 * Y a y + g 0 1 * Y b y
      else if x = b then g 1 0 * Y a y + g 1 1 * Y b y else Y x y := by
  have h := twoLevel_mulVec_apply hab g (fun i => Y i y) x
  rw [← h]
  rfl

theorem twoLevel_list_prod {a b : ι} (hab : a ≠ b) (l : List (Matrix (Fin 2) (Fin 2) ℂ)) :
    twoLevel a b l.prod = (l.map (twoLevel a b)).prod := by
  induction l with
  | nil => simp
  | cons g l ih => rw [List.prod_cons, ← twoLevel_mul hab, ih, List.map_cons, List.prod_cons]

theorem isTwoLevelWord_twoLevel_list_prod {a b : ι} (hab : a ≠ b)
    (l : List (Matrix (Fin 2) (Fin 2) ℂ)) (hl : ∀ g ∈ l, IsSpecialTwo g) :
    IsTwoLevelWord l.length (twoLevel a b l.prod) := by
  refine ⟨l.map fun g => (a, b, g), by simp, fun p hp => ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
    exact ⟨hab, hl g hg⟩
  · rw [twoLevel_list_prod hab, List.map_map]
    rfl

/-- **Eliminating a column below its diagonal entry.** For a basis vector `a` and a set `R`
of other basis vectors there is a product `W` of at most `2 |R|` two-level rotations and
phases on the pairs `{a, b}`, `b ∈ R`, with `(W X)_{c a} = 0` for every `c ∈ R`. -/
theorem exists_isTwoLevelWord_elim (a : ι) (X : Matrix ι ι ℂ) :
    ∀ R : Finset ι, a ∉ R → ∃ W : Matrix ι ι ℂ, IsTwoLevelWord (2 * R.card) W ∧
      FixesOutside (insert a R) W ∧ ∀ c ∈ R, (W * X) c a = 0 := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨1, IsTwoLevelWord.one _, fun x y _ => Matrix.one_apply, by simp⟩
  | insert b R hbR ih =>
    intro ha
    have hab : a ≠ b := fun h => ha (h ▸ Finset.mem_insert_self a R)
    have haR : a ∉ R := fun h => ha (Finset.mem_insert_of_mem h)
    obtain ⟨W, hW, hWfix, hWX⟩ := ih haR
    obtain ⟨l, hl, hlg, hel⟩ := exists_twoLevel_elim ((W * X) a a) ((W * X) b a)
    refine ⟨twoLevel a b l.prod * W, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hbR]
      exact ((isTwoLevelWord_twoLevel_list_prod hab l hlg).mul hW).mono (by omega)
    · refine FixesOutside.mul ((fixesOutside_twoLevel a b _).mono ?_) (hWfix.mono ?_)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp
      · intro x hx
        simp only [Finset.mem_insert] at hx ⊢
        tauto
    · intro c hc
      rw [Matrix.mul_assoc, twoLevel_mul_apply hab]
      rcases Finset.mem_insert.mp hc with rfl | hc
      · rw [ite_eq_right (Ne.symm hab), ite_eq_left rfl]
        exact hel
      · have hca : c ≠ a := fun h => haR (h ▸ hc)
        have hcb : c ≠ b := fun h => hbR (h ▸ hc)
        rw [ite_eq_right hca, ite_eq_right hcb]
        exact hWX c hc

theorem mem_unitary_iff_conjTranspose {X : Matrix ι ι ℂ} :
    X ∈ unitary (Matrix ι ι ℂ) ↔ Xᴴ * X = 1 ∧ X * Xᴴ = 1 := by
  rw [Unitary.mem_iff]; rfl

/-- **Givens decomposition.** A unitary `X` with `det X = 1` acting as the identity outside a
set `T` of basis vectors is a product of at most `3 |T|²` two-level rotations and phases on
pairs of elements of `T`. -/
theorem isTwoLevelWord_of_fixesOutside :
    ∀ T : Finset ι, ∀ X : Matrix ι ι ℂ, X ∈ unitary (Matrix ι ι ℂ) → X.det = 1 →
      FixesOutside T X → IsTwoLevelWord (3 * T.card * T.card) X := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro X _ _ hX
    rw [fixesOutside_empty hX]
    exact IsTwoLevelWord.one _
  | insert a T haT ih =>
    intro X hXu hXdet hXfix
    obtain ⟨W, hW, hWfix, hWX⟩ := exists_isTwoLevelWord_elim a X T haT
    set Y := W * X with hY
    have hWu := hW.mem_unitary
    have hYu : Y ∈ unitary (Matrix ι ι ℂ) := Submonoid.mul_mem _ hWu hXu
    have hYdet : Y.det = 1 := by rw [hY, det_mul, hW.det_eq_one, hXdet, one_mul]
    have hYfix : FixesOutside (insert a T) Y := hWfix.mul hXfix
    -- the column `a` of `Y` is `λ |a⟩`
    have hcol : ∀ c, c ≠ a → Y c a = 0 := by
      intro c hca
      by_cases hc : c ∈ T
      · exact hWX c hc
      · rw [hYfix c a (Or.inl (by simp [hca, hc])), ite_eq_right hca]
    set lam := Y a a with hlam
    have hYu' := mem_unitary_iff_conjTranspose.mp hYu
    have hlam1 : star lam * lam = 1 := by
      have h := congrFun (congrFun hYu'.1 a) a
      rw [mul_apply, one_apply_eq, Finset.sum_eq_single a] at h
      · simpa [conjTranspose_apply] using h
      · intro c _ hca; simp [conjTranspose_apply, hcol c hca]
      · simp
    have hrow : ∀ c, c ≠ a → Y a c = 0 := by
      intro c hca
      have h := congrFun (congrFun hYu'.1 a) c
      rw [mul_apply, one_apply_ne (Ne.symm hca), Finset.sum_eq_single a] at h
      · simp only [conjTranspose_apply] at h
        have hl0 : star lam ≠ 0 := fun h0 => by
          rw [h0, zero_mul] at hlam1; exact zero_ne_one hlam1
        exact (mul_eq_zero.mp h).resolve_left hl0
      · intro k _ hka; simp [conjTranspose_apply, hcol k hka]
      · simp
    have hlamn : ‖lam‖ = 1 := by
      have h : (‖lam‖ : ℂ) ^ 2 = 1 := by
        rw [← Complex.conj_mul', ← hlam1]; rfl
      exact_mod_cast (pow_eq_one_iff_of_nonneg (norm_nonneg lam) two_ne_zero).mp
        (by exact_mod_cast h)
    have hXW : X = Wᴴ * Y := by
      rw [hY, ← Matrix.mul_assoc, (mem_unitary_iff_conjTranspose.mp hWu).1, Matrix.one_mul]
    rcases T.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · -- `Y` is the identity
      have hY1 : Y = 1 := by
        have hdiag : Y = diagonal fun x => if x = a then lam else 1 := by
          ext x y
          rw [diagonal_apply]
          by_cases hxy : x = y
          · subst hxy
            by_cases hxa : x = a
            · subst hxa; simp [hlam]
            · rw [hYfix x x (Or.inl (by simp [hxa])), ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hxa]
          · rw [ite_eq_right hxy]
            by_cases hxa : x = a
            · subst hxa; exact hrow y (Ne.symm hxy)
            · rw [hYfix x y (Or.inl (by simp [hxa])), ite_eq_right hxy]
        have hl : lam = 1 := by
          rw [← hYdet, hdiag, det_diagonal, Finset.prod_eq_single a]
          · simp
          · intro x _ hxa; rw [ite_eq_right hxa]
          · simp
        rw [hdiag, hl]
        simp
      rw [hXW, hY1, Matrix.mul_one]
      exact hW.conjTranspose.mono (by simp)
    · have hab : a ≠ b := fun h => haT (h ▸ hb)
      set G := twoLevel a b (diagTwo (star lam)) with hG
      have hGspec : IsSpecialTwo (diagTwo (star lam)) := Or.inr ⟨star lam, by simpa using hlamn, rfl⟩
      have hGu : G ∈ unitary (Matrix ι ι ℂ) := twoLevel_mem_unitary hab hGspec.mem_unitary
      set Z := G * Y with hZ
      have hZu : Z ∈ unitary (Matrix ι ι ℂ) := Submonoid.mul_mem _ hGu hYu
      have hZdet : Z.det = 1 := by
        rw [hZ, det_mul, det_twoLevel hab, hGspec.det_eq_one, hYdet, one_mul]
      have hZfix : FixesOutside T Z := by
        intro x y hxy
        rw [hZ, twoLevel_mul_apply hab]
        simp only [diagTwo, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons,
          empty_val', cons_val_fin_one, head_fin_const, zero_mul, add_zero, zero_add]
        by_cases hxa : x = a
        · subst hxa
          rw [ite_eq_left rfl]
          by_cases hya : y = x
          · subst hya; rw [ite_eq_left rfl, ← hlam]; exact hlam1
          · rw [hrow y hya, mul_zero, ite_eq_right (Ne.symm hya)]
        · rw [ite_eq_right hxa]
          by_cases hxb : x = b
          · subst hxb
            rw [ite_eq_left rfl]
            by_cases hya : y = a
            · subst hya; rw [hcol x hxa, mul_zero, ite_eq_right hxa]
            · rcases hxy with hx | hy
              · exact absurd hb hx
              · rw [hYfix x y (Or.inr (by simp [hya, hy])), ite_eq_right (by rintro rfl; contradiction)]
                simp
          · rw [ite_eq_right hxb]
            rcases hxy with hx | hy
            · exact hYfix x y (Or.inl (by simp [hxa, hx]))
            · by_cases hya : y = a
              · subst hya; rw [hcol x hxa, ite_eq_right hxa]
              · exact hYfix x y (Or.inr (by simp [hya, hy]))
      have hZw := ih Z hZu hZdet hZfix
      have hYZ : Y = twoLevel a b (diagTwo lam) * Z := by
        have hGG : twoLevel a b (diagTwo lam) * G = 1 := by
          rw [hG, twoLevel_mul hab]
          have : diagTwo lam * diagTwo (star lam) = 1 := by
            have h' : lam * star lam = 1 := by rw [mul_comm]; exact hlam1
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [diagTwo, mul_apply, Fin.sum_univ_two] <;> first | exact h' | exact hlam1
          rw [this, twoLevel_one]
        rw [hZ, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
      rw [hXW, hYZ, ← Matrix.mul_assoc, Finset.card_insert_of_notMem haT]
      have hlamspec : IsSpecialTwo (diagTwo lam) := Or.inr ⟨lam, hlamn, rfl⟩
      refine ((hW.conjTranspose.mul (IsTwoLevelWord.single hab hlamspec)).mul hZw).mono ?_
      nlinarith

/-- **Givens decomposition of a special unitary.** Every unitary `X` on `ℂ^ι` with
`det X = 1` is a product of at most `3 (card ι)²` two-level rotations and phases. -/
theorem isTwoLevelWord_of_det_eq_one {X : Matrix ι ι ℂ} (hX : X ∈ unitary (Matrix ι ι ℂ))
    (hdet : X.det = 1) : IsTwoLevelWord (3 * Fintype.card ι * Fintype.card ι) X :=
  isTwoLevelWord_of_fixesOutside Finset.univ X hX hdet fun x y h => by simp at h

end MPSPreparation
