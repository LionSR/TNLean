/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableInsertion
import TNLean.MPS.CanonicalForm.Correlation.WindowOperatorSupport
import QICLean.ManyBody.Sites.Placement.PlaceAlong
import QICLean.ManyBody.Sites.Lattice.Chain

/-!
# Algebra and norm of observables in the interior of a chain

An observable on a fixed interval, placed between free intervals, is the
observable placed on the window of consecutive sites that does not wrap around
the chain (`ManyBody.placeAlong` along `ManyBody.chainWindow`). It preserves
products and adjoints and does not increase operator norm. These identities
relate the transfer insertion limits to the squared norms and expectations in
the finite-volume commutator estimate of Nachtergaele, arXiv:cond-mat/9410110,
lines 2649--2675.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Placing an observable between free intervals is placing it on the window of
the chain starting after the left free interval. Source: Nachtergaele,
arXiv:cond-mat/9410110, the local observable convention in lines 933--947 and
2649--2675. -/
theorem bulkObservable_eq_placeAlong_chainWindow {k : ℕ}
    (X : Matrix (Fin k → α) (Fin k → α) ℂ) (ℓ r : ℕ) :
    bulkObservable X ℓ r =
      ManyBody.placeAlong (X := fun _ ↦ α)
        (ManyBody.chainWindow ℓ (Nat.le_add_right (ℓ + k) r)) X := by
  classical
  ext τ σ
  simp only [ManyBody.placeAlong_apply, bulkObservable, appendObservable_apply,
    Matrix.one_apply]
  have hw : ∀ ν : (Fin ((ℓ + k) + r) → α), (fun i ↦ ν (Fin.castAdd r (Fin.natAdd ℓ i))) =
      fun u ↦ ν (ManyBody.chainWindow ℓ (Nat.le_add_right (ℓ + k) r) u) :=
    fun ν ↦ funext fun i ↦ congrArg ν (Fin.ext rfl)
  have hiff : (∀ v, (∀ u, ManyBody.chainWindow ℓ (Nat.le_add_right (ℓ + k) r) u ≠ v) →
        τ v = σ v) ↔
      ((fun i ↦ τ (Fin.castAdd r (Fin.castAdd k i))) =
          fun i ↦ σ (Fin.castAdd r (Fin.castAdd k i))) ∧
        ((fun i ↦ τ (Fin.natAdd (ℓ + k) i)) = fun i ↦ σ (Fin.natAdd (ℓ + k) i)) := by
    constructor
    · intro h
      refine ⟨funext fun i ↦ h _ fun u hu ↦ ?_, funext fun i ↦ h _ fun u hu ↦ ?_⟩
      · have hval := congrArg Fin.val hu
        simp only [ManyBody.val_chainWindow, Fin.val_castAdd] at hval
        omega
      · have hval := congrArg Fin.val hu
        simp only [ManyBody.val_chainWindow, Fin.val_natAdd] at hval
        omega
    · rintro ⟨h₁, h₂⟩ v hv
      by_cases hvℓ : v.val < ℓ
      · have h := congrFun h₁ ⟨v.val, hvℓ⟩
        have hv' : Fin.castAdd r (Fin.castAdd k (⟨v.val, hvℓ⟩ : Fin ℓ)) = v := Fin.ext rfl
        simp only [hv'] at h
        exact h
      · by_cases hvk : ℓ + k ≤ v.val
        · have h := congrFun h₂ ⟨v.val - (ℓ + k), by omega⟩
          have hv' : Fin.natAdd (ℓ + k) (⟨v.val - (ℓ + k), by omega⟩ : Fin r) = v :=
            Fin.ext (by simp only [Fin.val_natAdd]; omega)
          simp only [hv'] at h
          exact h
        · exact absurd (Fin.ext (by simp only [ManyBody.val_chainWindow]; omega))
            (hv ⟨v.val - ℓ, by omega⟩)
  rw [hw τ, hw σ]
  by_cases h₁ : (fun i ↦ τ (Fin.castAdd r (Fin.castAdd k i))) =
      fun i ↦ σ (Fin.castAdd r (Fin.castAdd k i))
  · by_cases h₂ : (fun i ↦ τ (Fin.natAdd (ℓ + k) i)) = fun i ↦ σ (Fin.natAdd (ℓ + k) i)
    · rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_left (hiff.2 ⟨h₁, h₂⟩), one_mul, mul_one]
    · rw [ite_eq_right h₂, ite_eq_right fun h ↦ h₂ (hiff.1 h).2, mul_zero]
  · rw [ite_eq_right h₁, ite_eq_right fun h ↦ h₁ (hiff.1 h).1, zero_mul, zero_mul]

/-- Placing two observables on the same interior interval preserves their product. -/
theorem bulkObservable_mul {k : ℕ}
    (X Y : Matrix (Fin k → α) (Fin k → α) ℂ) (ℓ r : ℕ) :
    bulkObservable (X * Y) ℓ r = bulkObservable X ℓ r * bulkObservable Y ℓ r := by
  simp only [bulkObservable, appendObservable_mul, Matrix.one_mul]

/-- The interior inclusion preserves adjoints. -/
theorem bulkObservable_conjTranspose {k : ℕ}
    (X : Matrix (Fin k → α) (Fin k → α) ℂ) (ℓ r : ℕ) :
    bulkObservable Xᴴ ℓ r = (bulkObservable X ℓ r)ᴴ := by
  simp only [bulkObservable, appendObservable, Matrix.conjTranspose_reindex,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- Placing an observable on an interior interval does not increase its
operator norm. -/
theorem norm_toEuclideanCLM_bulkObservable_le {k : ℕ}
    (X : Matrix (Fin k → α) (Fin k → α) ℂ) (ℓ r : ℕ) :
    ‖Matrix.toEuclideanCLM (n := (Fin ((ℓ + k) + r) → α)) (𝕜 := ℂ)
      (bulkObservable X ℓ r)‖ ≤
        ‖Matrix.toEuclideanCLM (n := (Fin k → α)) (𝕜 := ℂ) X‖ := by
  open scoped Matrix.Norms.L2Operator in
  have h := ManyBody.norm_placeAlong_le (X := fun _ ↦ α)
    (ManyBody.chainWindow ℓ (Nat.le_add_right (ℓ + k) r)) X
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def] at h
  rw [bulkObservable_eq_placeAlong_chainWindow]
  exact h


end MPSTensor
