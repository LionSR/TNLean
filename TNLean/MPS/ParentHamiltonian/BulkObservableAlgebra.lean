/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableInsertion
import TNLean.MPS.Preparation.WindowOperatorSupport

/-!
# Algebra and norm of observables in the interior of a chain

An observable on a fixed nonempty interval, placed between free intervals,
is the usual nonwrapping window inclusion. It preserves products and adjoints
and does not increase operator norm. These identities relate the transfer
insertion limits to the squared norms and expectations in the finite-volume
commutator estimate of Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {d : ℕ}

/-- Placing an observable between free intervals is the existing nonwrapping
window inclusion. Source: Nachtergaele, arXiv:cond-mat/9410110, the local
observable convention in lines 933--947 and 2649--2675. -/
theorem bulkObservable_eq_chainWindowOperator {k : ℕ} (hk : 0 < k)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    bulkObservable X ℓ r = chainWindowOperator ((ℓ + k) + r) ℓ X := by
  have h := chainWindowOperator_add_left (L := k) (p := ℓ + k) (q := r)
    (a := ℓ) (by omega) (le_refl (ℓ + k)) X
  rw [chainWindowOperator_add_right (p := ℓ) (q := k) (a := ℓ) le_rfl
    (by omega) (le_refl (ℓ + k)), Nat.sub_self, chainWindowOperator_self hk] at h
  exact h.symm

/-- Placing two observables on the same interior interval preserves their product. -/
theorem bulkObservable_mul {k : ℕ}
    (X Y : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    bulkObservable (X * Y) ℓ r = bulkObservable X ℓ r * bulkObservable Y ℓ r := by
  simp only [bulkObservable, appendObservable_mul, Matrix.one_mul]

/-- The interior inclusion preserves adjoints. -/
theorem bulkObservable_conjTranspose {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    bulkObservable Xᴴ ℓ r = (bulkObservable X ℓ r)ᴴ := by
  simp only [bulkObservable, appendObservable, Matrix.conjTranspose_reindex,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- Placing an observable on a nonempty interior interval does not increase
its operator norm. -/
theorem norm_toEuclideanCLM_bulkObservable_le {k : ℕ} (hk : 0 < k)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    ‖Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
      (bulkObservable X ℓ r)‖ ≤
        ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖ := by
  rw [bulkObservable_eq_chainWindowOperator hk]
  exact norm_toEuclideanCLM_chainWindowOperator_le (by omega) (by omega) X


end MPSTensor
