import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Scalar reduction for three exposed PEPS legs

This file formalizes the finite-dimensional tensor-factor step in
arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2.

After inverting the two injective tensors, the paper obtains one operator on
three exposed virtual legs which simultaneously has the forms
$I\otimes Z$, $U\otimes I$, and a third form with the identity on the middle
leg.  The intersection of these three tensor-product subspaces is the scalar
line.

The file also records the many-leg version `piProduct_forms_scalar`: if two
families of invertible per-leg matrices have equal products of entries over
every configuration pair, they are proportional leg by leg with proportionality
constants multiplying to one. This is the uniqueness input for the balanced
edge-scalar quotient in the Fundamental Theorem (arXiv:1804.04964, Section 3),
recorded in `docs/paper-gaps/peps_gauge_edge_scalars.tex`.
-/

open scoped Matrix BigOperators

namespace TNLean
namespace PEPS

variable {α β γ : Type*}
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The form $I_\alpha\otimes Z$ on
$\alpha\otimes\beta\otimes\gamma$.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2;
`Papers/1804.04964/paper_normal.tex`, lines 1194--1204. -/
def threeLegLeftIdentityForm (Z : Matrix (β × γ) (β × γ) ℂ) :
    Matrix (α × β × γ) (α × β × γ) ℂ :=
  fun x y =>
    if x.1 = y.1 then Z (x.2.1, x.2.2) (y.2.1, y.2.2) else 0

/-- The form $U\otimes I_\gamma$ on
$\alpha\otimes\beta\otimes\gamma$.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2;
`Papers/1804.04964/paper_normal.tex`, lines 1194--1204. -/
def threeLegRightIdentityForm (U : Matrix (α × β) (α × β) ℂ) :
    Matrix (α × β × γ) (α × β × γ) ℂ :=
  fun x y =>
    if x.2.2 = y.2.2 then U (x.1, x.2.1) (y.1, y.2.1) else 0

/-- The form with identity on the middle leg $\beta$.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2;
`Papers/1804.04964/paper_normal.tex`, lines 1194--1204. -/
def threeLegMiddleIdentityForm (W : Matrix (α × γ) (α × γ) ℂ) :
    Matrix (α × β × γ) (α × β × γ) ℂ :=
  fun x y =>
    if x.2.1 = y.2.1 then W (x.1, x.2.2) (y.1, y.2.2) else 0

/-- Three compatible two-leg residual forms are scalar.

This is the algebraic scalar-reduction step in arXiv:1804.04964, Section 3,
Lemma inj_equal_tensors_2.  In the notation of the paper, the equality
$$
  I\otimes Z = U\otimes I = W
$$
with the identity in the three complementary positions forces the residual
operators $Z$, $U$, and $W$ to be scalar multiples of the identity.

The nonempty hypotheses express the paper's standing convention that virtual
Hilbert spaces are nonzero finite-dimensional spaces. -/
theorem threeLeg_residual_forms_scalar [Nonempty α] [Nonempty β] [Nonempty γ]
    (Z : Matrix (β × γ) (β × γ) ℂ)
    (U : Matrix (α × β) (α × β) ℂ)
    (W : Matrix (α × γ) (α × γ) ℂ)
    (hZU : threeLegLeftIdentityForm (α := α) Z = threeLegRightIdentityForm U)
    (hZW : threeLegLeftIdentityForm (α := α) Z = threeLegMiddleIdentityForm W) :
    ∃ lam : ℂ, Z = lam • 1 ∧ U = lam • 1 ∧ W = lam • 1 := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  let b₀ : β := Classical.choice ‹Nonempty β›
  let c₀ : γ := Classical.choice ‹Nonempty γ›
  let lam : ℂ := Z (b₀, c₀) (b₀, c₀)
  have hZscalar : Z = lam • 1 := by
    ext p q
    rcases p with ⟨b, c⟩
    rcases q with ⟨b', c'⟩
    by_cases hb : b = b'
    · subst b'
      by_cases hc : c = c'
      · subst c'
        have hZW₁ := congrFun (congrFun hZW (a₀, b, c)) (a₀, b, c)
        have hZW₂ := congrFun (congrFun hZW (a₀, b₀, c)) (a₀, b₀, c)
        have hZU₁ := congrFun (congrFun hZU (a₀, b₀, c)) (a₀, b₀, c)
        have hZU₂ := congrFun (congrFun hZU (a₀, b₀, c₀)) (a₀, b₀, c₀)
        have h₁ : Z (b, c) (b, c) = W (a₀, c) (a₀, c) := by
          simpa [threeLegLeftIdentityForm, threeLegMiddleIdentityForm] using hZW₁
        have h₂ : Z (b₀, c) (b₀, c) = W (a₀, c) (a₀, c) := by
          simpa [threeLegLeftIdentityForm, threeLegMiddleIdentityForm] using hZW₂
        have h₃ : Z (b₀, c) (b₀, c) = U (a₀, b₀) (a₀, b₀) := by
          simpa [threeLegLeftIdentityForm, threeLegRightIdentityForm] using hZU₁
        have h₄ : Z (b₀, c₀) (b₀, c₀) = U (a₀, b₀) (a₀, b₀) := by
          simpa [threeLegLeftIdentityForm, threeLegRightIdentityForm] using hZU₂
        calc
          Z (b, c) (b, c) = W (a₀, c) (a₀, c) := h₁
          _ = Z (b₀, c) (b₀, c) := h₂.symm
          _ = U (a₀, b₀) (a₀, b₀) := h₃
          _ = lam := h₄.symm
          _ = (lam • 1 : Matrix (β × γ) (β × γ) ℂ) (b, c) (b, c) := by
            simp [Matrix.smul_apply]
      · have hZU₁ := congrFun (congrFun hZU (a₀, b, c)) (a₀, b, c')
        have hzero : Z (b, c) (b, c') = 0 := by
          simpa [threeLegLeftIdentityForm, threeLegRightIdentityForm, hc] using hZU₁
        simpa [Matrix.smul_apply, Matrix.one_apply, hc] using hzero
    · have hZW₁ := congrFun (congrFun hZW (a₀, b, c)) (a₀, b', c')
      have hzero : Z (b, c) (b', c') = 0 := by
        simpa [threeLegLeftIdentityForm, threeLegMiddleIdentityForm, hb] using hZW₁
      simpa [Matrix.smul_apply, Matrix.one_apply, hb] using hzero
  have hUscalar : U = lam • 1 := by
    ext p q
    rcases p with ⟨a, b⟩
    rcases q with ⟨a', b'⟩
    by_cases hpq : (a, b) = (a', b')
    · cases hpq
      have hZU₁ := congrFun (congrFun hZU (a, b, c₀)) (a, b, c₀)
      have hZentry := congrFun (congrFun hZscalar (b, c₀)) (b, c₀)
      calc
        U (a, b) (a, b) = Z (b, c₀) (b, c₀) := by
          simpa [threeLegLeftIdentityForm, threeLegRightIdentityForm] using hZU₁.symm
        _ = (lam • 1 : Matrix (β × γ) (β × γ) ℂ) (b, c₀) (b, c₀) := hZentry
        _ = (lam • 1 : Matrix (α × β) (α × β) ℂ) (a, b) (a, b) := by
          simp [Matrix.smul_apply]
    · by_cases ha : a = a'
      · subst a'
        have hb_ne : b ≠ b' := by
          intro hb
          exact hpq (by cases hb; rfl)
        have hZU₁ := congrFun (congrFun hZU (a, b, c₀)) (a, b', c₀)
        have hZentry := congrFun (congrFun hZscalar (b, c₀)) (b', c₀)
        calc
          U (a, b) (a, b') = Z (b, c₀) (b', c₀) := by
            simpa [threeLegLeftIdentityForm, threeLegRightIdentityForm] using hZU₁.symm
          _ = (lam • 1 : Matrix (β × γ) (β × γ) ℂ) (b, c₀) (b', c₀) := hZentry
          _ = (lam • 1 : Matrix (α × β) (α × β) ℂ) (a, b) (a, b') := by
            simp [Matrix.smul_apply, hb_ne]
      · have hZU₁ := congrFun (congrFun hZU (a, b, c₀)) (a', b', c₀)
        have hzero : U (a, b) (a', b') = 0 := by
          simpa [threeLegLeftIdentityForm, threeLegRightIdentityForm, ha] using hZU₁.symm
        simpa [Matrix.smul_apply, Matrix.one_apply, hpq] using hzero
  have hWscalar : W = lam • 1 := by
    ext p q
    rcases p with ⟨a, c⟩
    rcases q with ⟨a', c'⟩
    by_cases hpq : (a, c) = (a', c')
    · cases hpq
      have hZW₁ := congrFun (congrFun hZW (a, b₀, c)) (a, b₀, c)
      have hZentry := congrFun (congrFun hZscalar (b₀, c)) (b₀, c)
      calc
        W (a, c) (a, c) = Z (b₀, c) (b₀, c) := by
          simpa [threeLegLeftIdentityForm, threeLegMiddleIdentityForm] using hZW₁.symm
        _ = (lam • 1 : Matrix (β × γ) (β × γ) ℂ) (b₀, c) (b₀, c) := hZentry
        _ = (lam • 1 : Matrix (α × γ) (α × γ) ℂ) (a, c) (a, c) := by
          simp [Matrix.smul_apply]
    · by_cases ha : a = a'
      · subst a'
        have hc_ne : c ≠ c' := by
          intro hc
          exact hpq (by cases hc; rfl)
        have hZW₁ := congrFun (congrFun hZW (a, b₀, c)) (a, b₀, c')
        have hZentry := congrFun (congrFun hZscalar (b₀, c)) (b₀, c')
        calc
          W (a, c) (a, c') = Z (b₀, c) (b₀, c') := by
            simpa [threeLegLeftIdentityForm, threeLegMiddleIdentityForm] using hZW₁.symm
          _ = (lam • 1 : Matrix (β × γ) (β × γ) ℂ) (b₀, c) (b₀, c') := hZentry
          _ = (lam • 1 : Matrix (α × γ) (α × γ) ℂ) (a, c) (a, c') := by
            simp [Matrix.smul_apply, hc_ne]
      · have hZW₁ := congrFun (congrFun hZW (a, b₀, c)) (a', b₀, c')
        have hzero : W (a, c) (a', c') = 0 := by
          simpa [threeLegLeftIdentityForm, threeLegMiddleIdentityForm, ha] using hZW₁.symm
        simpa [Matrix.smul_apply, Matrix.one_apply, hpq] using hzero
  exact ⟨lam, hZscalar, hUscalar, hWscalar⟩

/-! ### Many-leg scalar extraction -/

section PiProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*}
variable [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
/-- Each row of an invertible matrix has a nonzero entry. -/
theorem exists_ne_zero_row_of_isUnit {m : Type*} [Fintype m] [DecidableEq m]
    {N : Matrix m m ℂ} (hN : IsUnit N) (r : m) :
    ∃ c : m, N r c ≠ 0 := by
  obtain ⟨Ninv, hNinv⟩ := hN.exists_right_inv
  by_contra h
  have h0 : ∀ c, N r c = 0 := by
    intro c; by_contra hc; exact h ⟨c, hc⟩
  have hval : (N * Ninv) r r = 1 := by rw [hNinv]; simp
  rw [Matrix.mul_apply] at hval
  simp only [h0, zero_mul, Finset.sum_const_zero] at hval
  exact one_ne_zero hval.symm

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] [Fintype ι] [DecidableEq ι] in
/-- A reference configuration: per leg, a base row paired with a column on which
the invertible per-leg matrix is nonzero. -/
theorem exists_ref_config (N : (i : ι) → Matrix (n i) (n i) ℂ)
    (hN : ∀ i, IsUnit (N i)) (r : (i : ι) → n i) :
    ∃ q : (i : ι) → n i, ∀ i, N i (r i) (q i) ≠ 0 := by
  choose q hq using fun i => exists_ne_zero_row_of_isUnit (hN i) (r i)
  exact ⟨q, hq⟩

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
/-- **Many-leg scalar extraction.** If the product of per-leg matrix entries
agrees with another such product for every configuration pair, every leg is a
nonempty index type, and the per-leg matrices `N i` are invertible, then the two
families are proportional, leg by leg, with proportionality constants
multiplying to one.

This generalizes `threeLeg_residual_forms_scalar` to an arbitrary finite number
of legs. Source: arXiv:1804.04964, Section 3; the balanced edge-scalar
uniqueness route is recorded in `docs/paper-gaps/peps_gauge_edge_scalars.tex`. -/
theorem piProduct_forms_scalar (M N : (i : ι) → Matrix (n i) (n i) ℂ)
    (hN : ∀ i, IsUnit (N i)) [hne : ∀ i, Nonempty (n i)]
    (h : ∀ (p q : (i : ι) → n i),
        (∏ i, M i (p i) (q i)) = ∏ i, N i (p i) (q i)) :
    ∃ c : ι → ℂ, (∀ i, M i = c i • N i) ∧ (∏ i, c i) = 1 := by
  classical
  -- Reference configuration with all-nonzero `N` entries.
  let p₀ : (i : ι) → n i := fun i => Classical.choice (hne i)
  obtain ⟨q₀, hq₀⟩ := exists_ref_config N hN p₀
  -- Reference product equality and its consequences.
  have hrefN : (∏ i, N i (p₀ i) (q₀ i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hq₀ i)
  have href : (∏ i, M i (p₀ i) (q₀ i)) = ∏ i, N i (p₀ i) (q₀ i) := h p₀ q₀
  have hrefM : (∏ i, M i (p₀ i) (q₀ i)) ≠ 0 := href ▸ hrefN
  have hMne : ∀ i, M i (p₀ i) (q₀ i) ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.mp hrefM) i (Finset.mem_univ i)
  -- Define the scalars.
  refine ⟨fun i => M i (p₀ i) (q₀ i) / N i (p₀ i) (q₀ i), ?_, ?_⟩
  · -- Proportionality at each leg, by varying only that leg from the reference.
    intro i
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    have hsplit : ∀ (P : (k : ι) → Matrix (n k) (n k) ℂ),
        (∏ j, P j ((Function.update p₀ i a) j) ((Function.update q₀ i b) j)) =
          P i a b * ∏ j ∈ Finset.univ.erase i, P j (p₀ j) (q₀ j) := by
      intro P
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => P j ((Function.update p₀ i a) j) ((Function.update q₀ i b) j))
        (Finset.mem_univ i)]
      rw [Function.update_self, Function.update_self]
      refine congrArg _ (Finset.prod_congr rfl ?_)
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj),
        Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have key : M i a b * (∏ j ∈ Finset.univ.erase i, M j (p₀ j) (q₀ j)) =
        N i a b * (∏ j ∈ Finset.univ.erase i, N j (p₀ j) (q₀ j)) := by
      have hM := h (Function.update p₀ i a) (Function.update q₀ i b)
      rwa [hsplit M, hsplit N] at hM
    have keyRef : M i (p₀ i) (q₀ i) * (∏ j ∈ Finset.univ.erase i, M j (p₀ j) (q₀ j)) =
        N i (p₀ i) (q₀ i) * (∏ j ∈ Finset.univ.erase i, N j (p₀ j) (q₀ j)) := by
      rw [Finset.mul_prod_erase Finset.univ (fun j => M j (p₀ j) (q₀ j)) (Finset.mem_univ i),
        Finset.mul_prod_erase Finset.univ (fun j => N j (p₀ j) (q₀ j)) (Finset.mem_univ i)]
      exact href
    have hKMne : (∏ j ∈ Finset.univ.erase i, M j (p₀ j) (q₀ j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hMne j)
    have hNref_ne : N i (p₀ i) (q₀ i) ≠ 0 := hq₀ i
    set KM := ∏ j ∈ Finset.univ.erase i, M j (p₀ j) (q₀ j)
    set KN := ∏ j ∈ Finset.univ.erase i, N j (p₀ j) (q₀ j)
    have hKNval : N i (p₀ i) (q₀ i) * KN = M i (p₀ i) (q₀ i) * KM := keyRef.symm
    refine mul_right_cancel₀ hKMne ?_
    calc M i a b * KM = N i a b * KN := key
      _ = N i a b * KN * (N i (p₀ i) (q₀ i) / N i (p₀ i) (q₀ i)) := by
            rw [div_self hNref_ne, mul_one]
      _ = (N i a b * (N i (p₀ i) (q₀ i) * KN)) / N i (p₀ i) (q₀ i) := by ring
      _ = (N i a b * (M i (p₀ i) (q₀ i) * KM)) / N i (p₀ i) (q₀ i) := by rw [hKNval]
      _ = M i (p₀ i) (q₀ i) / N i (p₀ i) (q₀ i) * N i a b * KM := by ring
  · -- The product of the proportionality constants is one.
    rw [Finset.prod_div_distrib, href, div_self hrefN]

end PiProduct

end PEPS
end TNLean
