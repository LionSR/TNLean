/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Decorrelation
import Mathlib.Tactic.Abel

/-!
# RFP decorrelation theory — commuting idempotent algebra

This file develops the algebraic theory of commuting idempotent endomorphisms
needed for the decorrelation ↔ commuting parent Hamiltonian equivalence
(Proposition D.3, arXiv:1606.00608 Appendix D).

Building on the backward direction proved in
`TNLean.MPS.ParentHamiltonian.Decorrelation`, this file:
1. Uses the product algebra of commuting idempotents directly in the
   commuting-parent-Hamiltonian consequences below.
2. Extends the `HasCommutingParentHam` properties with absorption, reverse-product,
   complement commutativity, and a ground-space membership characterisation.
3. Provides `IsDecorrelated` properties — monotonicity and triviality lemmas.

All results are fully proved (no `sorry`).

## Main results

### Frustration-free algebra

* `LinearMap.frustration_free_ham_eq` — `(1−P) + (1−Q) − (1−P)∘(1−Q) =
  1 − P∘Q`

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

* arXiv:1606.00608, Appendix D, Section D.2 (Definitions D.1–D.2, Proposition D.3)
-/

section FrustrationFreeIdentity

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

namespace LinearMap

/-- The frustration-free Hamiltonian identity:
`(1 − P) + (1 − Q) − (1 − P) ∘ (1 − Q) = 1 − P ∘ Q`.

For commuting parent Hamiltonians, this shows that the "Hamiltonian"
`Q_AX + Q_XB − Q_AX ∘ Q_XB` (with `Q = 1 − P`) equals `1 − P_K`.
See arXiv:1606.00608, Appendix D, Section D.2. -/
theorem frustration_free_ham_eq {P Q : E →ₗ[ℂ] E} :
    (id - P) + (id - Q) - (id - P) ∘ₗ (id - Q) = id - P ∘ₗ Q := by
  simp only [comp_sub, sub_comp, comp_id, id_comp]
  abel

end LinearMap

end FrustrationFreeIdentity

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
  change IsIdempotentElem P_K
  simpa [h.hK, Module.End.mul_eq_comp] using
    (IsIdempotentElem.mul_of_commute h.hcomm h.hAX_idem h.hXB_idem)

/-- `P_AX ∘ P_K = P_K`: the AX-projector absorbs `P_K` from the left. -/
theorem HasCommutingParentHam.pAX_comp_pK {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    h.P_AX ∘ₗ P_K = P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  have hAX : P_AX ∘ₗ P_AX = P_AX := h.hAX_idem
  change P_AX ∘ₗ P_K = P_K
  rw [← hK, ← LinearMap.comp_assoc, hAX, hK]

/-- `P_K ∘ P_XB = P_K`: `P_K` absorbs the XB-projector on the right. -/
theorem HasCommutingParentHam.pK_comp_pXB {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    P_K ∘ₗ h.P_XB = P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  have hXB : P_XB ∘ₗ P_XB = P_XB := h.hXB_idem
  change P_K ∘ₗ P_XB = P_K
  rw [← hK, LinearMap.comp_assoc, hXB, hK]

/-- `P_XB ∘ P_K = P_K`: the XB-projector absorbs `P_K` from the left. -/
theorem HasCommutingParentHam.pXB_comp_pK {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    h.P_XB ∘ₗ P_K = P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  have hXB : P_XB ∘ₗ P_XB = P_XB := h.hXB_idem
  have hcomm : P_AX ∘ₗ P_XB = P_XB ∘ₗ P_AX := h.hcomm
  change P_XB ∘ₗ P_K = P_K
  rw [← hK, ← LinearMap.comp_assoc, ← hcomm, LinearMap.comp_assoc, hXB, hK]

/-- `P_K ∘ P_AX = P_K`: `P_K` absorbs the AX-projector on the right. -/
theorem HasCommutingParentHam.pK_comp_pAX {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    P_K ∘ₗ h.P_AX = P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  have hAX : P_AX ∘ₗ P_AX = P_AX := h.hAX_idem
  have hcomm : P_AX ∘ₗ P_XB = P_XB ∘ₗ P_AX := h.hcomm
  change P_K ∘ₗ P_AX = P_K
  rw [← hK, LinearMap.comp_assoc, ← hcomm, ← LinearMap.comp_assoc, hAX, hK]

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
  by
    have hcomm : Commute h.P_AX h.P_XB := by
      change h.P_AX * h.P_XB = h.P_XB * h.P_AX
      simpa [Module.End.mul_eq_comp] using h.hcomm
    have hP_comp : Commute h.P_AX (LinearMap.id - h.P_XB) :=
      (Commute.one_right h.P_AX).sub_right hcomm
    have hcomp : Commute (LinearMap.id - h.P_AX) (LinearMap.id - h.P_XB) :=
      (Commute.one_left (LinearMap.id - h.P_XB)).sub_left hP_comp
    simpa [Module.End.mul_eq_comp] using hcomp.eq

/-- The frustration-free Hamiltonian identity for a commuting parent
Hamiltonian: `Q_AX + Q_XB − Q_AX ∘ Q_XB = id − P_K`. -/
theorem HasCommutingParentHam.hamiltonian_eq {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    (LinearMap.id - h.P_AX) + (LinearMap.id - h.P_XB) -
      (LinearMap.id - h.P_AX) ∘ₗ (LinearMap.id - h.P_XB) =
      LinearMap.id - P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  change (LinearMap.id - P_AX) + (LinearMap.id - P_XB) -
      (LinearMap.id - P_AX) ∘ₗ (LinearMap.id - P_XB) =
    LinearMap.id - P_K
  simpa [hK] using (LinearMap.frustration_free_ham_eq (P := P_AX) (Q := P_XB))

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
        rw [← LinearMap.comp_apply, h.pAX_comp_pK]
      rwa [hv] at this
    · have : h.P_XB (P_K v) = P_K v := by
        rw [← LinearMap.comp_apply, h.pXB_comp_pK]
      rwa [hv] at this
  · rintro ⟨hAX, hXB⟩
    have : (h.P_AX ∘ₗ h.P_XB) v = v := by
      simp only [LinearMap.comp_apply]; rw [hXB, hAX]
    rwa [h.hK] at this

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

end Decorrelation

end IsDecorrelatedProperties
