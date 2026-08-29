/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.LSymbol
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Finite-group generalized cocycles

This file proves the finite-group power-trivialization lemma from
arXiv:2502.20257, `lemma:G_cocycle`, lines 5931--5948. For generalized
2-cocycles `Ωˣ_{g,h}` attached to an action of a finite group `G` on block
labels `X`, it constructs the regular-action matrices

`Xˣ_g |k⟩ = Ω^{k⁻¹ • x}_{g,k} |gk⟩`

and uses their determinants to prove that `Ω ^ |G|` is a generalized
coboundary. No transitivity or finiteness assumption is imposed on `X`.

**Local fix (determinant numerator):** The determinant display in the source
repeats `det Xˣ_g`. Taking determinants of the preceding operator identity
gives `det X^{h • x}_g det Xˣ_h`. See
`docs/paper-gaps/fbc25_generalized_cocycle_determinant_typo.tex`.

## Main definitions

* `ActionTensorGauge.coboundary`: the generalized coboundary `dχ`.
* `LSymbol.IsGeneralizedCocycle`: the equation `dΩ = 1`.
* `LSymbol.regularMatrix`: the regular-action matrix `Xˣ_g`.
* `LSymbol.determinantCochain`: the cochain `χˣ_g = det Xˣ_g`.

## Main results

* `LSymbol.regularMatrix_mul`: `X^{h • x}_g Xˣ_h = Ωˣ_{g,h} Xˣ_{gh}`.
* `LSymbol.pow_card_eq_coboundary`: `Ω ^ |G| = dχ`.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X]

namespace ActionTensorGauge

/-- The generalized coboundary of a block-dependent scalar one-cochain:

`(dχ)ˣ_{g,h} = χ^{h • x}_g χˣ_h / χˣ_{gh}`.

This is arXiv:2502.20257, lines 5908--5910. -/
def coboundary (χ : ActionTensorGauge G X) : LSymbol G X :=
  fun x g h => (χ g (h • x) * χ h x) / χ (g * h) x

end ActionTensorGauge

namespace LSymbol

/-- A generalized scalar 2-cocycle is an L-symbol compatible with the constant
scalar 3-cochain one. Equivalently,

`Ωˣ_{g,hk} Ωˣ_{h,k} = Ω^{k • x}_{g,h} Ωˣ_{gh,k}`.

This is the equation `dΩ = 1` in arXiv:2502.20257, `lemma:G_cocycle`. -/
def IsGeneralizedCocycle (Ω : LSymbol G X) : Prop :=
  IsCompatible Ω (fun _ _ _ => 1)

/-- The regular-action matrix from arXiv:2502.20257, `lemma:G_cocycle`:

`Xˣ_g |k⟩ = Ω^{k⁻¹ • x}_{g,k} |gk⟩`.

Rows and columns are indexed by `G`; thus the entry in row `i` and column `k`
is nonzero exactly when `i = gk`. -/
noncomputable def regularMatrix (Ω : LSymbol G X) (g : G) (x : X) : Matrix G G ℂ := by
  classical
  exact fun i k => if i = g * k then (Ω (k⁻¹ • x) g k : ℂ) else 0

/-- The nonzero entry of a generalized-cocycle regular-action matrix. -/
theorem regularMatrix_apply_of_eq (Ω : LSymbol G X) (g i k : G) (x : X)
    (hi : i = g * k) :
    regularMatrix Ω g x i k = (Ω (k⁻¹ • x) g k : ℂ) := by
  classical
  simp [regularMatrix, hi]

/-- Every other entry of a generalized-cocycle regular-action matrix vanishes. -/
theorem regularMatrix_apply_of_ne (Ω : LSymbol G X) (g i k : G) (x : X)
    (hi : i ≠ g * k) : regularMatrix Ω g x i k = 0 := by
  classical
  simp [regularMatrix, hi]

/-- The permutation factor in the regular-action matrix. The inverse is forced
by Mathlib's row-to-column convention for permutation matrices. -/
noncomputable def regularPermutationMatrix (g : G) : Matrix G G ℂ := by
  classical
  exact Equiv.Perm.permMatrix ℂ (Equiv.mulLeft g⁻¹)

/-- The diagonal coefficient factor in the regular-action matrix. -/
noncomputable def regularDiagonal (Ω : LSymbol G X) (g : G) (x : X) : Matrix G G ℂ := by
  classical
  exact Matrix.diagonal (fun k => (Ω (k⁻¹ • x) g k : ℂ))

/-- The regular-action matrix is a permutation matrix times its diagonal
coefficient matrix. -/
theorem regularMatrix_eq_permutation_mul_diagonal [Fintype G]
    (Ω : LSymbol G X) (g : G) (x : X) :
    regularMatrix Ω g x = regularPermutationMatrix g * regularDiagonal Ω g x := by
  classical
  ext i k
  by_cases hi : i = g * k
  · subst i
    simp [regularMatrix, regularPermutationMatrix, regularDiagonal, Matrix.mul_apply]
  · have hi' : g⁻¹ * i ≠ k := by
      intro hik
      apply hi
      calc
        i = g * (g⁻¹ * i) := by simp
        _ = g * k := by rw [hik]
    simp [regularMatrix, regularPermutationMatrix, regularDiagonal, Matrix.mul_apply, hi, hi']

/-- The generalized cocycle equation gives the projective multiplication law
for the regular-action matrices:

`X^{h • x}_g Xˣ_h = Ωˣ_{g,h} Xˣ_{gh}`.

This is arXiv:2502.20257, `lemma:G_cocycle`, lines 5941--5943. -/
theorem regularMatrix_mul [Fintype G] {Ω : LSymbol G X}
    (hΩ : IsGeneralizedCocycle Ω) (x : X) (g h : G) :
    regularMatrix Ω g (h • x) * regularMatrix Ω h x =
      (Ω x g h : ℂ) • regularMatrix Ω (g * h) x := by
  classical
  ext i k
  rw [Matrix.mul_apply, Fintype.sum_eq_single (h * k)]
  · rw [regularMatrix_apply_of_eq Ω h (h * k) k x rfl]
    change regularMatrix Ω g (h • x) i (h * k) * (Ω (k⁻¹ • x) h k : ℂ) =
      (Ω x g h : ℂ) * regularMatrix Ω (g * h) x i k
    by_cases hi : i = g * (h * k)
    · rw [regularMatrix_apply_of_eq Ω g i (h * k) (h • x) hi,
        regularMatrix_apply_of_eq Ω (g * h) i k x (by simpa only [mul_assoc] using hi)]
      have hcocycle := congrArg Units.val (hΩ (k⁻¹ • x) g h k)
      push_cast at hcocycle
      simpa [mul_inv_rev, mul_smul] using hcocycle
    · rw [regularMatrix_apply_of_ne Ω g i (h * k) (h • x) hi,
        regularMatrix_apply_of_ne Ω (g * h) i k x (by simpa only [mul_assoc] using hi)]
      simp
  · intro j hj
    rw [regularMatrix_apply_of_ne Ω h j k x hj]
    simp

/-- The determinant of a regular-action matrix, defined without exposing a
choice of decidable equality on `G`. -/
noncomputable def regularDeterminant [Fintype G] (Ω : LSymbol G X) (g : G) (x : X) : ℂ := by
  classical
  exact (regularMatrix Ω g x).det

/-- Every regular-action matrix has nonzero determinant. The proof uses the
permutation-times-diagonal factorization from the source construction. -/
theorem regularDeterminant_ne_zero [Fintype G] (Ω : LSymbol G X) (g : G) (x : X) :
    regularDeterminant Ω g x ≠ 0 := by
  classical
  change (regularMatrix Ω g x).det ≠ 0
  rw [regularMatrix_eq_permutation_mul_diagonal, Matrix.det_mul]
  simp only [regularPermutationMatrix, regularDiagonal, Matrix.det_permutation,
    Matrix.det_diagonal]
  apply mul_ne_zero
  · exact_mod_cast Units.ne_zero (Equiv.Perm.sign (Equiv.mulLeft g⁻¹))
  · exact Finset.prod_ne_zero_iff.mpr fun k _ => Units.ne_zero (Ω (k⁻¹ • x) g k)

/-- The block-dependent determinant cochain from arXiv:2502.20257,
`lemma:G_cocycle`: `χˣ_g = det Xˣ_g`. -/
noncomputable def determinantCochain [Fintype G] (Ω : LSymbol G X) :
    ActionTensorGauge G X :=
  fun g x => Units.mk0 (regularDeterminant Ω g x) (regularDeterminant_ne_zero Ω g x)

/-- Apply form of finite-group power trivialization:

`(Ωˣ_{g,h})^|G| = (dχ)ˣ_{g,h}` for `χˣ_g = det Xˣ_g`.

This is arXiv:2502.20257, `lemma:G_cocycle`. The determinant numerator is the
locally corrected `det X^{h • x}_g det Xˣ_h`. -/
theorem pow_card_eq_coboundary_apply [Fintype G] {Ω : LSymbol G X}
    (hΩ : IsGeneralizedCocycle Ω) (x : X) (g h : G) :
    Ω x g h ^ Fintype.card G =
      ActionTensorGauge.coboundary (determinantCochain Ω) x g h := by
  classical
  apply Units.ext
  change (Ω x g h : ℂ) ^ Fintype.card G =
    (regularDeterminant Ω g (h • x) * regularDeterminant Ω h x) /
      regularDeterminant Ω (g * h) x
  have hdet := congrArg Matrix.det (regularMatrix_mul hΩ x g h)
  rw [Matrix.det_mul, Matrix.det_smul] at hdet
  change regularDeterminant Ω g (h • x) * regularDeterminant Ω h x =
    (Ω x g h : ℂ) ^ Fintype.card G * regularDeterminant Ω (g * h) x at hdet
  apply (eq_div_iff (regularDeterminant_ne_zero Ω (g * h) x)).2
  exact hdet.symm

/-- For a finite group, the `|G|`-th power of every generalized scalar
2-cocycle is the generalized coboundary of its determinant cochain.

This is arXiv:2502.20257, `lemma:G_cocycle`. -/
theorem pow_card_eq_coboundary [Fintype G] {Ω : LSymbol G X}
    (hΩ : IsGeneralizedCocycle Ω) :
    Ω ^ Fintype.card G = ActionTensorGauge.coboundary (determinantCochain Ω) := by
  funext x g h
  exact pow_card_eq_coboundary_apply hΩ x g h

end LSymbol

end TNLean.Algebra
