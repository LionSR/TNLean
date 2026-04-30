/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Decorrelation
import Mathlib.Tactic.Abel

/-!
# RFP decorrelation theory — commuting idempotent algebra

This file develops the algebraic theory of commuting idempotent endomorphisms
needed for the decorrelation ⟺ commuting parent Hamiltonian equivalence
(Proposition D.3, arXiv:1606.00608 Appendix D).

Building on the backward direction proved in
`TNLean.MPS.ParentHamiltonian.Decorrelation`, this file:
1. Develops the **product algebra** of commuting idempotents — absorption,
   cross-absorption, complement commutativity, and the frustration-free
   Hamiltonian identity.
2. Extends the `HasCommutingParentHam` properties with absorption, reverse-product,
   complement commutativity, and a ground-space membership characterisation.
3. Provides `IsDecorrelated` properties — monotonicity and triviality lemmas.

All results are fully proved (no `sorry`).

## Main results

### Commuting idempotent algebra (`LinearMap` namespace)

* `comp_idem_of_comm_idem` — product of commuting idempotents is idempotent
* `idem_comp_left_absorb` — `P ∘ (P ∘ Q) = P ∘ Q`
* `idem_comp_right_absorb` — `(P ∘ Q) ∘ Q = P ∘ Q`
* `comm_idem_cross_absorb_left` — `(P ∘ Q) ∘ P = P ∘ Q` when `[P, Q] = 0`
* `comm_idem_cross_absorb_right` — `Q ∘ (P ∘ Q) = P ∘ Q` when `[P, Q] = 0`
* `complement_comm_of_comm` — `[P, Q] = 0 → [1 − P, 1 − Q] = 0`
* `comm_of_complement_comm` — `[1 − P, 1 − Q] = 0 → [P, Q] = 0`
* `frustration_free_ham_eq` — `(1−P) + (1−Q) − (1−P)∘(1−Q) = 1 − P∘Q`

### `Decorrelation.HasCommutingParentHam` properties

* `pK_idem` — `P_K ∘ P_K = P_K`
* `pAX_comp_pK` — `P_AX ∘ P_K = P_K`
* `pK_comp_pXB` — `P_K ∘ P_XB = P_K`
* `pXB_comp_pK` — `P_XB ∘ P_K = P_K`
* `pK_comp_pAX` — `P_K ∘ P_AX = P_K`
* `reverse_product` — `P_XB ∘ P_AX = P_K`
* `complement_comm` — `(id − P_AX) ∘ (id − P_XB) = (id − P_XB) ∘ (id − P_AX)`
* `mem_ground_iff` — `P_K v = v ↔ P_AX v = v ∧ P_XB v = v`

### `Decorrelation.IsDecorrelated` properties

* `mono_obsA` / `mono_obsB` — monotone in observable sets
* `empty_obsA` / `empty_obsB` — trivially decorrelated for empty sets
* `of_pK_zero` — decorrelated when `P_K = 0`
* `of_pK_id` — decorrelated when `P_K = id`

## References

* arXiv:1606.00608, Appendix D, §D.2 (Definitions D.1–D.2, Proposition D.3)
-/

/-!
### Commuting idempotent product algebra

Algebraic lemmas for pairs of commuting idempotent endomorphisms.
These are the workhorses behind `HasCommutingParentHam`.
-/

section CommutingIdempotentAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

namespace LinearMap

/-- Product of commuting idempotent endomorphisms is idempotent.
This wraps Mathlib's `IsIdempotentElem.mul_of_commute`. -/
theorem comp_idem_of_comm_idem
    {P Q : E →ₗ[ℂ] E}
    (hP : P ∘ₗ P = P) (hQ : Q ∘ₗ Q = Q)
    (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    (P ∘ₗ Q) ∘ₗ (P ∘ₗ Q) = P ∘ₗ Q :=
  IsIdempotentElem.mul_of_commute hcomm hP hQ

/-- Left absorption: `P ∘ (P ∘ Q) = P ∘ Q` when `P` is idempotent. -/
theorem idem_comp_left_absorb
    {P Q : E →ₗ[ℂ] E} (hP : P ∘ₗ P = P) :
    P ∘ₗ (P ∘ₗ Q) = P ∘ₗ Q := by
  rw [← comp_assoc, hP]

/-- Right absorption: `(P ∘ Q) ∘ Q = P ∘ Q` when `Q` is idempotent. -/
theorem idem_comp_right_absorb
    {P Q : E →ₗ[ℂ] E} (hQ : Q ∘ₗ Q = Q) :
    (P ∘ₗ Q) ∘ₗ Q = P ∘ₗ Q := by
  rw [comp_assoc, hQ]

/-- Cross absorption (left): `(P ∘ Q) ∘ P = P ∘ Q` when `P` is idempotent
and `P`, `Q` commute. -/
theorem comm_idem_cross_absorb_left
    {P Q : E →ₗ[ℂ] E}
    (hP : P ∘ₗ P = P) (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    (P ∘ₗ Q) ∘ₗ P = P ∘ₗ Q := by
  rw [comp_assoc, ← hcomm, ← comp_assoc, hP]

/-- Cross absorption (right): `Q ∘ (P ∘ Q) = P ∘ Q` when `Q` is idempotent
and `P`, `Q` commute. -/
theorem comm_idem_cross_absorb_right
    {P Q : E →ₗ[ℂ] E}
    (hQ : Q ∘ₗ Q = Q) (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    Q ∘ₗ (P ∘ₗ Q) = P ∘ₗ Q := by
  rw [← comp_assoc, ← hcomm, comp_assoc, hQ]

/-- Commuting endomorphisms have commuting complements:
`[P, Q] = 0 → [1 − P, 1 − Q] = 0`. -/
theorem complement_comm_of_comm
    {P Q : E →ₗ[ℂ] E} (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    (id - P) ∘ₗ (id - Q) = (id - Q) ∘ₗ (id - P) := by
  simp only [comp_sub, sub_comp, comp_id, id_comp, hcomm]
  abel

/-- Commuting complements imply commuting originals:
`[1 − P, 1 − Q] = 0 → [P, Q] = 0`. -/
theorem comm_of_complement_comm
    {P Q : E →ₗ[ℂ] E}
    (hcomm : (id - P) ∘ₗ (id - Q) = (id - Q) ∘ₗ (id - P)) :
    P ∘ₗ Q = Q ∘ₗ P := by
  have expand_l : (id - P) ∘ₗ (id - Q) = id - P - Q + P ∘ₗ Q := by
    simp only [comp_sub, sub_comp, comp_id, id_comp]; abel
  have expand_r : (id - Q) ∘ₗ (id - P) = id - Q - P + Q ∘ₗ P := by
    simp only [comp_sub, sub_comp, comp_id, id_comp]; abel
  rw [expand_l, expand_r] at hcomm
  have key : (id : E →ₗ[ℂ] E) - P - Q = id - Q - P := by abel
  rw [key] at hcomm
  exact add_left_cancel hcomm

/-- The frustration-free Hamiltonian identity (pure algebra, no commutativity
needed): `(1 − P) + (1 − Q) − (1 − P) ∘ (1 − Q) = 1 − P ∘ Q`.

For commuting parent Hamiltonians, this shows that the "Hamiltonian"
`Q_AX + Q_XB − Q_AX ∘ Q_XB` (with `Q = 1 − P`) equals `1 − P_K`.
See arXiv:1606.00608, Appendix D, §D.2. -/
theorem frustration_free_ham_eq
    {P Q : E →ₗ[ℂ] E} :
    (id - P) + (id - Q) - (id - P) ∘ₗ (id - Q) = id - P ∘ₗ Q := by
  simp only [comp_sub, sub_comp, comp_id, id_comp]
  abel

/-- Complement-product cancellation identity:
`P ∘ (id − Q ∘ P) ∘ Q = 0` for commuting idempotents.
This is `comp_complement_comm_zero` with swapped roles. -/
theorem comp_complement_comm_zero_swap
    {P Q : E →ₗ[ℂ] E}
    (hP : P ∘ₗ P = P) (hQ : Q ∘ₗ Q = Q)
    (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    P ∘ₗ (id - Q ∘ₗ P) ∘ₗ Q = 0 :=
  comp_complement_comm_zero hQ hP hcomm.symm

end LinearMap

end CommutingIdempotentAlgebra

/-!
### Extended `HasCommutingParentHam` properties

Absorption, reverse-product, and ground-space characterisation lemmas
for the commuting parent Hamiltonian structure.
-/

section HasCommutingParentHamProperties

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

namespace Decorrelation

/-- `P_K` is idempotent. -/
theorem HasCommutingParentHam.pK_idem {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    P_K ∘ₗ P_K = P_K := by
  simpa [h.hK] using
    (LinearMap.comp_idem_of_comm_idem (P := h.P_AX) (Q := h.P_XB)
      h.hAX_idem h.hXB_idem h.hcomm)

/-- `P_AX ∘ P_K = P_K`: the AX-projector absorbs `P_K` from the left. -/
theorem HasCommutingParentHam.pAX_comp_pK {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    h.P_AX ∘ₗ P_K = P_K := by
  simpa [h.hK] using
    (LinearMap.idem_comp_left_absorb (P := h.P_AX) (Q := h.P_XB) h.hAX_idem)

/-- `P_K ∘ P_XB = P_K`: `P_K` absorbs the XB-projector on the right. -/
theorem HasCommutingParentHam.pK_comp_pXB {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    P_K ∘ₗ h.P_XB = P_K := by
  simpa [h.hK] using
    (LinearMap.idem_comp_right_absorb (P := h.P_AX) (Q := h.P_XB) h.hXB_idem)

/-- `P_XB ∘ P_K = P_K`: the XB-projector absorbs `P_K` from the left. -/
theorem HasCommutingParentHam.pXB_comp_pK {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    h.P_XB ∘ₗ P_K = P_K := by
  simpa [h.hK] using
    (LinearMap.comm_idem_cross_absorb_right (P := h.P_AX) (Q := h.P_XB)
      h.hXB_idem h.hcomm)

/-- `P_K ∘ P_AX = P_K`: `P_K` absorbs the AX-projector on the right. -/
theorem HasCommutingParentHam.pK_comp_pAX {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    P_K ∘ₗ h.P_AX = P_K := by
  simpa [h.hK] using
    (LinearMap.comm_idem_cross_absorb_left (P := h.P_AX) (Q := h.P_XB)
      h.hAX_idem h.hcomm)

/-- The reverse product equals `P_K`: `P_XB ∘ P_AX = P_K`.
Follows from `hK : P_AX ∘ P_XB = P_K` and commutativity. -/
theorem HasCommutingParentHam.reverse_product {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    h.P_XB ∘ₗ h.P_AX = P_K := by
  simpa [h.hK] using h.hcomm.symm

/-- The complements `Q_AX = id − P_AX` and `Q_XB = id − P_XB` commute. -/
theorem HasCommutingParentHam.complement_comm {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    (LinearMap.id - h.P_AX) ∘ₗ (LinearMap.id - h.P_XB) =
      (LinearMap.id - h.P_XB) ∘ₗ (LinearMap.id - h.P_AX) :=
  LinearMap.complement_comm_of_comm h.hcomm

/-- The frustration-free Hamiltonian identity for a commuting parent
Hamiltonian: `Q_AX + Q_XB − Q_AX ∘ Q_XB = id − P_K`. -/
theorem HasCommutingParentHam.hamiltonian_eq {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    (LinearMap.id - h.P_AX) + (LinearMap.id - h.P_XB) -
      (LinearMap.id - h.P_AX) ∘ₗ (LinearMap.id - h.P_XB) =
      LinearMap.id - P_K := by
  simpa [h.hK] using
    (LinearMap.frustration_free_ham_eq (P := h.P_AX) (Q := h.P_XB))

/-- Ground-space membership: `P_K v = v` iff both `P_AX v = v` and
`P_XB v = v`. This is the algebraic form of
`K_{AXB} = (K_{AX} ⊗ H_B) ∩ (H_A ⊗ K_{XB})`
from arXiv:1606.00608, equation (D.2). -/
theorem HasCommutingParentHam.mem_ground_iff {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) (v : E) :
    P_K v = v ↔ h.P_AX v = v ∧ h.P_XB v = v := by
  constructor
  · intro hv
    constructor
    · have : h.P_AX (P_K v) = P_K v := by
        change (h.P_AX ∘ₗ P_K) v = P_K v
        rw [h.pAX_comp_pK]
      rw [hv] at this; exact this
    · have : h.P_XB (P_K v) = P_K v := by
        change (h.P_XB ∘ₗ P_K) v = P_K v
        rw [h.pXB_comp_pK]
      rw [hv] at this; exact this
  · rintro ⟨hAX, hXB⟩
    have : (h.P_AX ∘ₗ h.P_XB) v = v := by
      simp only [LinearMap.comp_apply]; rw [hXB, hAX]
    rwa [h.hK] at this

/-- Ground-space vectors are fixed by `P_AX`. -/
theorem HasCommutingParentHam.pAX_of_ground {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K)
    {v : E} (hv : P_K v = v) : h.P_AX v = v :=
  ((h.mem_ground_iff v).mp hv).1

/-- Ground-space vectors are fixed by `P_XB`. -/
theorem HasCommutingParentHam.pXB_of_ground {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K)
    {v : E} (hv : P_K v = v) : h.P_XB v = v :=
  ((h.mem_ground_iff v).mp hv).2

end Decorrelation

end HasCommutingParentHamProperties

/-!
### `IsDecorrelated` properties

Monotonicity and triviality lemmas for the decorrelation predicate.
-/

section IsDecorrelatedProperties

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

namespace Decorrelation

/-- Decorrelation is monotone in the first observable set: restricting
observables on region A preserves decorrelation. -/
theorem IsDecorrelated.mono_obsA {P_K : E →ₗ[ℂ] E}
    {ObsA ObsA' ObsB : Set (E →ₗ[ℂ] E)}
    (h : IsDecorrelated P_K ObsA' ObsB) (hsub : ObsA ⊆ ObsA') :
    IsDecorrelated P_K ObsA ObsB :=
  fun O_A hOA O_B hOB => h O_A (hsub hOA) O_B hOB

/-- Decorrelation is monotone in the second observable set: restricting
observables on region B preserves decorrelation. -/
theorem IsDecorrelated.mono_obsB {P_K : E →ₗ[ℂ] E}
    {ObsA ObsB ObsB' : Set (E →ₗ[ℂ] E)}
    (h : IsDecorrelated P_K ObsA ObsB') (hsub : ObsB ⊆ ObsB') :
    IsDecorrelated P_K ObsA ObsB :=
  fun O_A hOA O_B hOB => h O_A hOA O_B (hsub hOB)

/-- Decorrelation holds trivially when the A-observable set is empty. -/
theorem IsDecorrelated.empty_obsA {P_K : E →ₗ[ℂ] E}
    (ObsB : Set (E →ₗ[ℂ] E)) :
    IsDecorrelated P_K ∅ ObsB := by
  intro _ hOA; exact hOA.elim

/-- Decorrelation holds trivially when the B-observable set is empty. -/
theorem IsDecorrelated.empty_obsB {P_K : E →ₗ[ℂ] E}
    (ObsA : Set (E →ₗ[ℂ] E)) :
    IsDecorrelated P_K ObsA ∅ := by
  intro _ _ _ hOB; exact hOB.elim

/-- Decorrelation holds trivially when `P_K = 0`. -/
theorem IsDecorrelated.of_pK_zero
    (ObsA ObsB : Set (E →ₗ[ℂ] E)) :
    IsDecorrelated (0 : E →ₗ[ℂ] E) ObsA ObsB := by
  intro O_A _ O_B _
  simp only [LinearMap.comp_zero]

/-- Decorrelation holds trivially when `P_K = id` (the full space),
since `P_K⊥ = 0`. -/
theorem IsDecorrelated.of_pK_id
    (ObsA ObsB : Set (E →ₗ[ℂ] E)) :
    IsDecorrelated (LinearMap.id : E →ₗ[ℂ] E) ObsA ObsB := by
  intro O_A _ O_B _
  ext x
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.zero_apply, sub_self, map_zero]

/-- Restricting both observable sets simultaneously preserves
decorrelation. -/
theorem IsDecorrelated.mono {P_K : E →ₗ[ℂ] E}
    {ObsA ObsA' ObsB ObsB' : Set (E →ₗ[ℂ] E)}
    (h : IsDecorrelated P_K ObsA' ObsB')
    (hA : ObsA ⊆ ObsA') (hB : ObsB ⊆ ObsB') :
    IsDecorrelated P_K ObsA ObsB :=
  (h.mono_obsA hA).mono_obsB hB

/-- Decorrelation for observable singletons: it suffices to check
`P_K ∘ O_A ∘ P_K⊥ ∘ O_B ∘ P_K = 0` for a single pair. -/
theorem IsDecorrelated.singleton {P_K O_A O_B : E →ₗ[ℂ] E}
    (h : P_K ∘ₗ O_A ∘ₗ (LinearMap.id - P_K) ∘ₗ O_B ∘ₗ P_K = 0) :
    IsDecorrelated P_K {O_A} {O_B} := by
  intro O_A' hA O_B' hB
  rw [Set.mem_singleton_iff.mp hA, Set.mem_singleton_iff.mp hB]
  exact h

/-- Decorrelation is preserved under unions of A-observable sets. -/
theorem IsDecorrelated.union_obsA {P_K : E →ₗ[ℂ] E}
    {ObsA₁ ObsA₂ ObsB : Set (E →ₗ[ℂ] E)}
    (h₁ : IsDecorrelated P_K ObsA₁ ObsB)
    (h₂ : IsDecorrelated P_K ObsA₂ ObsB) :
    IsDecorrelated P_K (ObsA₁ ∪ ObsA₂) ObsB := by
  intro O_A hOA O_B hOB
  rcases hOA with h | h
  · exact h₁ O_A h O_B hOB
  · exact h₂ O_A h O_B hOB

/-- Decorrelation is preserved under unions of B-observable sets. -/
theorem IsDecorrelated.union_obsB {P_K : E →ₗ[ℂ] E}
    {ObsA ObsB₁ ObsB₂ : Set (E →ₗ[ℂ] E)}
    (h₁ : IsDecorrelated P_K ObsA ObsB₁)
    (h₂ : IsDecorrelated P_K ObsA ObsB₂) :
    IsDecorrelated P_K ObsA (ObsB₁ ∪ ObsB₂) := by
  intro O_A hOA O_B hOB
  rcases hOB with h | h
  · exact h₁ O_A hOA O_B h
  · exact h₂ O_A hOA O_B h

end Decorrelation

end IsDecorrelatedProperties
