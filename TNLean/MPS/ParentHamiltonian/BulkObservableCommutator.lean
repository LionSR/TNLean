/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BulkObservableAlgebra
import TNLean.MPS.ParentHamiltonian.IsometricDeformationSymmetry
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Localization of open-chain commutators

For an interaction of range `R`, only terms whose supports meet the support
of a local observable contribute to its commutator with the open Hamiltonian.
If the observable has at least `R - 1` free sites on either side, the commutator
is the inclusion of a fixed operator on the enlarged interval. The same holds
for the operator $X^\dagger[H,X]$ used in the finite-volume energy estimate.

These are finite-dimensional locality identities underlying the passage to
infinite-volume local expectations in Nachtergaele, arXiv:cond-mat/9410110,
lines 2649--2675. They do not assert the infinite-volume spectral-gap theorem.
The interaction is arbitrary; positivity and self-adjointness are not needed.
-/

open scoped Matrix BigOperators

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

/-- Operators on disjoint nonwrapping intervals commute. -/
theorem chainWindowOperator_commute_of_disjoint {L K N a b : ℕ}
    (ha : a < N) (haL : a + L ≤ N) (hb : b < N) (hbK : b + K ≤ N)
    (hSep : a + L ≤ b ∨ b + K ≤ a)
    (X : Matrix (Cfg d L) (Cfg d L) ℂ) (Y : Matrix (Cfg d K) (Cfg d K) ℂ) :
    Commute (chainWindowOperator N a X) (chainWindowOperator N b Y) := by
  refine QuantumCircuit.commute_of_mem_supportedOperators ?_
    (chainWindowOperator_mem_supportedOperators ha haL X)
    (chainWindowOperator_mem_supportedOperators hb hbK Y)
  refine Set.disjoint_left.2 (fun i hi hj => ?_)
  simp only [Set.mem_ofPred_eq] at hi hj
  omega

/-- The matrix of the open-chain interaction sum. Source: Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
noncomputable def openInteractionMatrix (h : Matrix (Cfg d R) (Cfg d R) ℂ) (N : ℕ) :
    Matrix (Cfg d N) (Cfg d N) ℂ :=
  ∑ i ∈ Finset.range (N + 1 - R), chainWindowOperator N i h

/-- The fixed local observable $X^\dagger[H,X]$ on the interval obtained by
adding `R - 1` sites on either side of the support of `X`. This definition
requires neither self-adjointness nor positivity of the interaction. -/
noncomputable def localCommutatorObservable
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    Matrix (Cfg d ((R - 1 + k) + (R - 1))) (Cfg d ((R - 1 + k) + (R - 1))) ℂ :=
  (bulkObservable X (R - 1) (R - 1))ᴴ *
    (openInteractionMatrix h ((R - 1 + k) + (R - 1)) * bulkObservable X (R - 1) (R - 1) -
      bulkObservable X (R - 1) (R - 1) * openInteractionMatrix h ((R - 1 + k) + (R - 1)))

/-- The commutator of an open-chain interaction sum with an interior observable
is supported on the interval enlarged by `R - 1` sites on either side. -/
theorem openInteractionMatrix_commutator_chainWindowOperator (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k)
    (ha : a + ((R - 1 + k) + (R - 1)) ≤ N) :
    openInteractionMatrix h N * chainWindowOperator N (a + (R - 1)) X -
        chainWindowOperator N (a + (R - 1)) X * openInteractionMatrix h N =
      chainWindowOperator N a
        (openInteractionMatrix h ((R - 1 + k) + (R - 1)) *
            chainWindowOperator ((R - 1 + k) + (R - 1)) (R - 1) X -
          chainWindowOperator ((R - 1 + k) + (R - 1)) (R - 1) X *
            openInteractionMatrix h ((R - 1 + k) + (R - 1))) := by
  simp only [openInteractionMatrix, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [chainWindowOperator_eq_embedLocalOperatorAlgHom (by omega) ha, map_sum]
  simp only [map_sub, map_mul]
  simp only [← chainWindowOperator_eq_embedLocalOperatorAlgHom (by omega) ha]
  refine (sum_range_eq_sum_range_shift
    (fun i => chainWindowOperator N i h * chainWindowOperator N (a + (R - 1)) X -
      chainWindowOperator N (a + (R - 1)) X * chainWindowOperator N i h)
    (a := a) (m := (R - 1 + k) + (R - 1) + 1 - R) (by omega) ?_).trans ?_
  · intro i hi hsep
    simp only [Finset.mem_range] at hi
    exact sub_eq_zero.mpr (chainWindowOperator_commute_of_disjoint
      (by omega) (by omega) (by omega) (by omega) (by omega) h X).eq
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    rw [chainWindowOperator_chainWindowOperator (by omega) ha (by omega) (by omega) h,
      chainWindowOperator_chainWindowOperator (by omega) ha (by omega) (by omega) X]

/-- Localization of the open-chain commutator for an observable between
free intervals of lengths at least `R - 1`. -/
theorem openInteractionMatrix_commutator_bulkObservable {ℓ r : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hk : 0 < k) (hℓ : R - 1 ≤ ℓ) (hr : R - 1 ≤ r) :
    openInteractionMatrix h ((ℓ + k) + r) * bulkObservable X ℓ r -
        bulkObservable X ℓ r * openInteractionMatrix h ((ℓ + k) + r) =
      chainWindowOperator ((ℓ + k) + r) (ℓ - (R - 1))
        (openInteractionMatrix h ((R - 1 + k) + (R - 1)) *
            bulkObservable X (R - 1) (R - 1) -
          bulkObservable X (R - 1) (R - 1) *
            openInteractionMatrix h ((R - 1 + k) + (R - 1))) := by
  have hlocal := openInteractionMatrix_commutator_chainWindowOperator
    (N := (ℓ + k) + r) (a := ℓ - (R - 1)) h X hR hk (by omega)
  simpa only [bulkObservable_eq_chainWindowOperator hk, Nat.sub_add_cancel hℓ] using hlocal

/-- The finite-volume operator $X^\dagger[H,X]$ is the inclusion of a fixed
local observable on the enlarged support interval. -/
theorem chainWindowOperator_adjoint_mul_openInteractionMatrix_commutator
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hk : 0 < k) (ha : a + ((R - 1 + k) + (R - 1)) ≤ N) :
    (chainWindowOperator N (a + (R - 1)) X)ᴴ *
        (openInteractionMatrix h N * chainWindowOperator N (a + (R - 1)) X -
          chainWindowOperator N (a + (R - 1)) X * openInteractionMatrix h N) =
      chainWindowOperator N a (localCommutatorObservable h X) := by
  simp only [localCommutatorObservable, bulkObservable_eq_chainWindowOperator hk]
  rw [openInteractionMatrix_commutator_chainWindowOperator h X hR hk ha]
  rw [chainWindowOperator_mul (by omega) ha, chainWindowOperator_conjTranspose (by omega) ha,
    chainWindowOperator_chainWindowOperator (by omega) ha (by omega) (by omega) X]

/-- For an interior observable, the commutator energy operator is the
inclusion of the fixed local commutator observable. -/
theorem bulkObservable_adjoint_mul_openInteractionMatrix_commutator {ℓ r : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hk : 0 < k) (hℓ : R - 1 ≤ ℓ) (hr : R - 1 ≤ r) :
    (bulkObservable X ℓ r)ᴴ *
        (openInteractionMatrix h ((ℓ + k) + r) * bulkObservable X ℓ r -
          bulkObservable X ℓ r * openInteractionMatrix h ((ℓ + k) + r)) =
      chainWindowOperator ((ℓ + k) + r) (ℓ - (R - 1))
        (localCommutatorObservable h X) := by
  have hlocal := chainWindowOperator_adjoint_mul_openInteractionMatrix_commutator
    (N := (ℓ + k) + r) (a := ℓ - (R - 1)) h X hR hk (by omega)
  simpa only [bulkObservable_eq_chainWindowOperator hk, Nat.sub_add_cancel hℓ] using hlocal

private theorem openInteractionMatrix_eq_sum_nonwrappingStart
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hRN : R ≤ N) :
    openInteractionMatrix h N =
      ∑ i : NonwrappingStart R N, chainWindowOperator N i.1.val h := by
  unfold openInteractionMatrix
  symm
  refine Finset.sum_bij (fun i _ => i.1.val) ?_ ?_ ?_ ?_
  · intro i _
    have hi := i.2
    exact Finset.mem_range.mpr (by omega)
  · exact fun i _ j _ hij => Subtype.ext (Fin.ext hij)
  · intro b hb
    simp only [Finset.mem_range] at hb
    exact ⟨⟨⟨b, by omega⟩, by change b + R ≤ N; omega⟩, Finset.mem_univ _, rfl⟩
  · exact fun _ _ => rfl

/-- The matrix interaction sum agrees with the Euclidean open-chain
Hamiltonian. Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hRN : R ≤ N) :
    openInteractionHamiltonianES (Matrix.toEuclideanLin h) N =
      Matrix.toEuclideanLin (openInteractionMatrix h N) := by
  rw [openInteractionMatrix_eq_sum_nonwrappingStart h hR hRN, map_sum,
    openInteractionHamiltonianES]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator hRN i.1]
  rw [chainWindowOperator, dite_eq_left ⟨hRN, i.1.isLt⟩]

/-- The canonical local ground-space complement projection gives the
Euclidean open parent Hamiltonian under the matrix representation. -/
theorem toEuclideanCLM_openInteractionMatrix_parentInteraction {D : ℕ}
    (A : MPSTensor d D) (hR : 0 < R) (hRN : R ≤ N) :
    (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (openInteractionMatrix
        ((Matrix.toEuclideanCLM (n := Cfg d R) (𝕜 := ℂ)).symm
          (groundSpaceES A R)ᗮ.starProjection) N)).toLinearMap =
      openParentHamiltonianES A R N := by
  change Matrix.toEuclideanLin (openInteractionMatrix _ N) = _
  rw [← openInteractionHamiltonianES_eq_toEuclideanLin_openInteractionMatrix _ hR hRN]
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
