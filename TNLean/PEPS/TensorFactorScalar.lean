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
-/

open scoped Matrix

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

end PEPS
end TNLean
