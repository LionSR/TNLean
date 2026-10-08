/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicResidualProjectionSum
import TNLean.MPS.ParentHamiltonian.ResidualBoundaryGram

/-!
# Word sums in the inverse cyclic projection convention

For the convention \(P_{j+1}A_i=A_iP_j\), the adjoint transfer of a
length-\(r\) word shifts the projection label from \(j\) to \(j-r\).
This is the forward cyclic word identity after reversing the labels.

Source: arXiv:1708.00029, equation Aoffdiag; Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675.
-/

open scoped Matrix BigOperators
namespace MPSTensor
variable {d D m : ℕ}

/-- The cyclic word Gram in the inverse projection convention. Source:
arXiv:1708.00029, equation Aoffdiag; Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem sum_word_conjTranspose_inverseCyclic_projection_mul_word
    [NeZero m] (A : MPSTensor d D) (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hTP : IsLeftCanonical A) (hShift : ∀ j i, P (j + 1) * A i = A i * P j)
    (j : Fin m) (r : ℕ) :
    (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * P j *
      Kraus.evalWord A (List.ofFn τ)) = P (j - r • (1 : Fin m)) := by
  let P' : Fin m → Matrix (Fin D) (Fin D) ℂ := fun a => P (-a)
  have hShift' : ∀ a i, P' a * A i = A i * P' (a + 1) := by
    intro a i
    have hIdx : ((-a - 1) + 1 : Fin m) = -a := by abel
    have hIdx' : (-a - 1 : Fin m) = -(a + 1) := by abel
    have h := hShift (-a - 1) i
    rw [hIdx] at h
    simpa only [P', hIdx'] using h
  have hIdx : -(-j + r • (1 : Fin m)) = j - r • (1 : Fin m) := by abel
  simpa only [P', neg_neg, hIdx] using
    sum_word_conjTranspose_cyclic_projection_mul_word A P' hTP hShift' (-j) r

end MPSTensor
