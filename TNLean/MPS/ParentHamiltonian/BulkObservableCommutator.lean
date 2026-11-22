/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BulkObservableAlgebra
import TNLean.MPS.ParentHamiltonian.IsometricDeformationSymmetry
import Mathlib.Algebra.BigOperators.Intervals
import QICLean.ManyBody.Sites.Lattice.Ring

/-!
# Localization of open-chain commutators

For an interaction of range \(R\), only terms whose supports meet the support
of a local observable contribute to its commutator with the open Hamiltonian.
If the observable has at least \(R-1\) free sites on either side, the commutator
is the placement of a fixed operator on the enlarged interval. The same holds
for the operator \(X^\dagger[H,X]\) used in the finite-volume energy estimate.
Operators are placed on windows of consecutive sites that do not wrap around
the chain (`ManyBody.placeAlong` along `ManyBody.chainWindow`).

These are finite-dimensional locality identities underlying the passage to
infinite-volume local expectations in Nachtergaele, arXiv:cond-mat/9410110,
lines 2649--2675. They do not assert the infinite-volume spectral-gap theorem.
The interaction is arbitrary; positivity and self-adjointness are not needed.

**Transitional (#10948).**
`openInteractionHamiltonianES_eq_toEuclideanLin_hamiltonian_chainTranslates` and
`toEuclideanCLM_hamiltonian_chainTranslates_parentInteraction` compare the Euclidean-space
operators `openInteractionHamiltonianES` and `openParentHamiltonianES` with the Hamiltonians of
`ManyBody.Interaction.chainTranslates`; they are kept until their last users are converted and
are then deleted with those operators.
-/

open scoped Matrix BigOperators
open ManyBody (placeAlong chainWindow)

open ManyBody.Interaction (chainTranslates hamiltonian_chainTranslates_eq_sum_range)

namespace MPSTensor
variable {d R k N a : ℕ}

private theorem sum_range_eq_sum_range_shift {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {a m n : ℕ} (ham : a + m ≤ n)
    (hz : ∀ i ∈ Finset.range n, i < a ∨ a + m ≤ i → f i = 0) :
    (∑ i ∈ Finset.range n, f i) = ∑ j ∈ Finset.range m, f (a + j) := by
  refine (Finset.sum_subset (s₁ := Finset.Ico a (a + m))
    (s₂ := Finset.range n) ?_ ?_).symm.trans ?_
  · exact fun i hi => Finset.mem_range.mpr ((Finset.mem_Ico.mp hi).2.trans_le ham)
  · exact fun i hi hnot => hz i hi
      (by simpa only [Finset.mem_Ico, not_and_or, not_le, not_lt] using hnot)
  · simpa only [Nat.Ico_zero_eq_range, zero_add, Nat.add_comm] using
      (Finset.sum_Ico_add f 0 m a).symm

/-- The fixed local observable \(X^\dagger[H,X]\) on the interval obtained by
adding \(R-1\) sites on either side of the support of \(X\). This definition
requires neither self-adjointness nor positivity of the interaction. -/
noncomputable def localCommutatorObservable
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    Matrix (Cfg d ((R - 1 + k) + (R - 1))) (Cfg d ((R - 1 + k) + (R - 1))) ℂ :=
  (bulkObservable X (R - 1) (R - 1))ᴴ *
    ((chainTranslates R ((R - 1 + k) + (R - 1)) h).hamiltonian * bulkObservable X (R - 1) (R - 1) -
      bulkObservable X (R - 1) (R - 1) * (chainTranslates R ((R - 1 + k) + (R - 1)) h).hamiltonian)

/-- The commutator of an open-chain interaction sum with an interior observable
is supported on the interval enlarged by \(R-1\) sites on either side. -/
theorem hamiltonian_chainTranslates_commutator_placeAlong_chainWindow
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R)
    (ha : a + ((R - 1 + k) + (R - 1)) ≤ N) :
    (chainTranslates R N h).hamiltonian *
          placeAlong (X := fun _ ↦ Fin d) (chainWindow (a + (R - 1)) (by omega)) X -
        placeAlong (X := fun _ ↦ Fin d) (chainWindow (a + (R - 1)) (by omega)) X *
          (chainTranslates R N h).hamiltonian =
      placeAlong (X := fun _ ↦ Fin d) (chainWindow a ha)
        ((chainTranslates R ((R - 1 + k) + (R - 1)) h).hamiltonian *
            placeAlong (X := fun _ ↦ Fin d) (chainWindow (R - 1) (by omega)) X -
          placeAlong (X := fun _ ↦ Fin d) (chainWindow (R - 1) (by omega)) X *
            (chainTranslates R ((R - 1 + k) + (R - 1)) h).hamiltonian) := by
  have hP : a + (R - 1) + k ≤ N := by omega
  simp only [hamiltonian_chainTranslates_eq_sum_range, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  rw [ManyBody.placeAlong_sum]
  simp only [ManyBody.placeAlong_sub, ManyBody.placeAlong_mul]
  rw [ManyBody.placeAlong_placeAlong, ManyBody.chainWindow_trans_chainWindow]
  refine (sum_range_eq_sum_range_shift
    (fun i => (if hi : i + R ≤ N then placeAlong (X := fun _ ↦ Fin d) (chainWindow i hi) h
          else 0) * placeAlong (X := fun _ ↦ Fin d) (chainWindow (a + (R - 1)) hP) X -
      placeAlong (X := fun _ ↦ Fin d) (chainWindow (a + (R - 1)) hP) X *
        (if hi : i + R ≤ N then placeAlong (X := fun _ ↦ Fin d) (chainWindow i hi) h else 0))
    (a := a) (m := (R - 1 + k) + (R - 1) + 1 - R) (by omega) ?_).trans ?_
  · intro i hi hsep
    simp only [Finset.mem_range] at hi
    simp only [dite_eq_left (show i + R ≤ N by omega)]
    refine sub_eq_zero.mpr (ManyBody.commute_placeAlong_of_disjoint (X := fun _ ↦ Fin d)
      (chainWindow i (show i + R ≤ N by omega)) ?_ h X).eq
    rw [ManyBody.map_chainWindow, ManyBody.map_chainWindow, Finset.disjoint_left]
    intro s hs hs'
    rw [ManyBody.mem_interval] at hs hs'
    omega
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    simp only [dite_eq_left (show a + j + R ≤ N by omega),
      dite_eq_left (show j + R ≤ (R - 1 + k) + (R - 1) by omega)]
    rw [ManyBody.placeAlong_placeAlong, ManyBody.chainWindow_trans_chainWindow]

/-- Localization of the open-chain commutator for an observable between
free intervals of lengths at least \(R-1\). -/
theorem hamiltonian_chainTranslates_commutator_bulkObservable {ℓ r : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hℓ : R - 1 ≤ ℓ) (hr : R - 1 ≤ r) :
    (chainTranslates R ((ℓ + k) + r) h).hamiltonian * bulkObservable X ℓ r -
        bulkObservable X ℓ r * (chainTranslates R ((ℓ + k) + r) h).hamiltonian =
      placeAlong (X := fun _ ↦ Fin d) (chainWindow (ℓ - (R - 1)) (by omega))
        ((chainTranslates R ((R - 1 + k) + (R - 1)) h).hamiltonian *
            bulkObservable X (R - 1) (R - 1) -
          bulkObservable X (R - 1) (R - 1) *
            (chainTranslates R ((R - 1 + k) + (R - 1)) h).hamiltonian) := by
  have hlocal := hamiltonian_chainTranslates_commutator_placeAlong_chainWindow
    (N := (ℓ + k) + r) (a := ℓ - (R - 1)) h X hR (by omega)
  have hw : chainWindow (ℓ - (R - 1) + (R - 1))
      (show ℓ - (R - 1) + (R - 1) + k ≤ (ℓ + k) + r by omega) =
        chainWindow ℓ (Nat.le_add_right (ℓ + k) r) := by
    ext j
    rw [ManyBody.val_chainWindow, ManyBody.val_chainWindow]
    omega
  rw [hw] at hlocal
  rw [bulkObservable_eq_placeAlong_chainWindow, bulkObservable_eq_placeAlong_chainWindow]
  exact hlocal

/-- The finite-volume operator \(X^\dagger[H,X]\) is the placement of a fixed
local observable on the enlarged support interval. -/
theorem placeAlong_chainWindow_adjoint_mul_hamiltonian_chainTranslates_commutator
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (ha : a + ((R - 1 + k) + (R - 1)) ≤ N) :
    (placeAlong (X := fun _ ↦ Fin d) (chainWindow (a + (R - 1)) (by omega)) X)ᴴ *
        ((chainTranslates R N h).hamiltonian *
            placeAlong (X := fun _ ↦ Fin d) (chainWindow (a + (R - 1)) (by omega)) X -
          placeAlong (X := fun _ ↦ Fin d) (chainWindow (a + (R - 1)) (by omega)) X *
            (chainTranslates R N h).hamiltonian) =
      placeAlong (X := fun _ ↦ Fin d) (chainWindow a ha) (localCommutatorObservable h X) := by
  rw [hamiltonian_chainTranslates_commutator_placeAlong_chainWindow h X hR ha,
    localCommutatorObservable, bulkObservable_eq_placeAlong_chainWindow,
    ManyBody.placeAlong_mul, ManyBody.placeAlong_conjTranspose, ManyBody.placeAlong_placeAlong,
    ManyBody.chainWindow_trans_chainWindow]

/-- For an interior observable, the commutator energy operator is the
placement of the fixed local commutator observable. -/
theorem bulkObservable_adjoint_mul_hamiltonian_chainTranslates_commutator {ℓ r : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hℓ : R - 1 ≤ ℓ) (hr : R - 1 ≤ r) :
    (bulkObservable X ℓ r)ᴴ *
        ((chainTranslates R ((ℓ + k) + r) h).hamiltonian * bulkObservable X ℓ r -
          bulkObservable X ℓ r * (chainTranslates R ((ℓ + k) + r) h).hamiltonian) =
      placeAlong (X := fun _ ↦ Fin d) (chainWindow (ℓ - (R - 1)) (by omega))
        (localCommutatorObservable h X) := by
  have hlocal := placeAlong_chainWindow_adjoint_mul_hamiltonian_chainTranslates_commutator
    (N := (ℓ + k) + r) (a := ℓ - (R - 1)) h X hR (by omega)
  have hw : chainWindow (ℓ - (R - 1) + (R - 1))
      (show ℓ - (R - 1) + (R - 1) + k ≤ (ℓ + k) + r by omega) =
        chainWindow ℓ (Nat.le_add_right (ℓ + k) r) := by
    ext j
    rw [ManyBody.val_chainWindow, ManyBody.val_chainWindow]
    omega
  rw [hw] at hlocal
  rw [bulkObservable_eq_placeAlong_chainWindow]
  exact hlocal

private theorem hamiltonian_chainTranslates_eq_sum_nonwrappingStart
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hRN : R ≤ N) :
    (chainTranslates R N h).hamiltonian =
      ∑ i : NonwrappingStart R N,
        placeAlong (X := fun _ ↦ Fin d) (chainWindow i.1.val i.2) h := by
  rw [hamiltonian_chainTranslates_eq_sum_range]
  symm
  refine Finset.sum_bij (fun i _ => i.1.val) ?_ ?_ ?_ ?_
  · intro i _
    have hi := i.2
    exact Finset.mem_range.mpr (by omega)
  · exact fun i _ j _ hij => Subtype.ext (Fin.ext hij)
  · intro b hb
    simp only [Finset.mem_range] at hb
    exact ⟨⟨⟨b, by omega⟩, by change b + R ≤ N; omega⟩, Finset.mem_univ _, rfl⟩
  · exact fun i _ => by rw [dite_eq_left (show i.1.val + R ≤ N from i.2)]

/-- The matrix interaction sum agrees with the Euclidean open-chain
Hamiltonian. Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem openInteractionHamiltonianES_eq_toEuclideanLin_hamiltonian_chainTranslates
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hRN : R ≤ N) :
    openInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      Matrix.toEuclideanLin ((chainTranslates R N h).hamiltonian) := by
  rw [hamiltonian_chainTranslates_eq_sum_nonwrappingStart h hR hRN, map_sum,
    openInteractionHamiltonianES]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [periodicLocalInteractionES_eq_toEuclideanLin_placeAlong_ringWindow hRN i.1]
  have hw : chainWindow i.1.val i.2 = ManyBody.ringWindow hRN i.1 := by
    ext j
    have hj : i.1.val + j.val < N := by
      have hi := i.2
      omega
    rw [ManyBody.val_chainWindow, ManyBody.ringWindow_apply, Fin.val_add, Fin.val_castLE,
      Nat.mod_eq_of_lt hj]
  rw [hw]

/-- The canonical local ground-space complement projection gives the
Euclidean open parent Hamiltonian under the matrix representation. -/
theorem toEuclideanCLM_hamiltonian_chainTranslates_parentInteraction {D : ℕ}
    (A : MPSTensor d D) (hR : 0 < R) (hRN : R ≤ N) :
    (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      ((chainTranslates _ N ((Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)).symm
          (groundSpaceES A R)ᗮ.starProjection)).hamiltonian)).toLinearMap =
      Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian := by
  change Matrix.toEuclideanLin ((chainTranslates _ N _).hamiltonian) = _
  rw [← openInteractionHamiltonianES_eq_toEuclideanLin_hamiltonian_chainTranslates _ hR hRN]
  have hlocal : Matrix.toEuclideanLin
      ((Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)).symm
        (groundSpaceES A R)ᗮ.starProjection) = parentInteractionES A R := by
    change (Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)
      ((Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)).symm
        (groundSpaceES A R)ᗮ.starProjection)).toLinearMap = _
    rw [StarAlgEquiv.apply_symm_apply]
    rfl
  rw [hlocal, openInteractionHamiltonianES_parentInteractionES A hR]

end MPSTensor
