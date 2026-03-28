/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Decorrelation and commuting parent Hamiltonians

This file defines the notion of **decorrelation** for a subspace with
respect to two disjoint regions, and proves the dimension-independent
equivalence: a subspace corresponds to a commuting parent Hamiltonian
if and only if the two regions are decorrelated.

This is Proposition D.1 from arXiv:1606.00608, Appendix D.2.

## Main definitions

* `IsDecorrelated` — regions A and B are decorrelated w.r.t. a subspace K
  when `P_K O_A (1 - P_K) O_B P_K = 0` for all observables O_A, O_B on
  the respective regions.
* `HasCommutingParentHam` — a subspace K equals the intersection of two
  local kernels `K_AX ⊗ H_B ∩ H_A ⊗ K_XB` where the corresponding
  projectors commute.

## Main results

* `decorrelated_iff_commutingHam` — decorrelation ⟺ commuting parent
  Hamiltonian (Proposition D.1)

## References

* arXiv:1606.00608, Appendix D.2 (lines 2181–2290)
-/

open scoped BigOperators

/-!
### Abstract operator-algebraic formulation

We work in an abstract setting with finite-dimensional Hilbert spaces
`H_A`, `H_X`, `H_B` and a subspace `K ≤ H_A ⊗ H_X ⊗ H_B`.

Since the full formalization of the tensor product of Hilbert spaces is
not yet available in Mathlib, we state the main definitions and the
equivalence theorem using abstract orthogonal projectors on a
finite-dimensional inner product space.
-/

section AbstractDecorrelation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Decorrelation**: given an orthogonal projection `P_K` (projecting onto a
subspace K) and families of operators `O_A` and `O_B` representing observables
on regions A and B, regions A and B are **decorrelated** w.r.t. K when
`P_K ∘ O_A ∘ (1 - P_K) ∘ O_B ∘ P_K = 0` for all observables `O_A`, `O_B`.

See arXiv:1606.00608, Appendix D.2, Definition before Proposition D.1. -/
def IsDecorrelated (P_K : E →ₗ[ℂ] E)
    (ObsA ObsB : Set (E →ₗ[ℂ] E)) : Prop :=
  ∀ O_A ∈ ObsA, ∀ O_B ∈ ObsB,
    P_K ∘ₗ O_A ∘ₗ (LinearMap.id - P_K) ∘ₗ O_B ∘ₗ P_K = 0

/-- **Commuting parent Hamiltonian structure**: a subspace (given by its
orthogonal projector `P_K`) corresponds to a commuting parent Hamiltonian
if there exist projectors `P_AX` and `P_XB` (acting on regions AX and XB
respectively) that commute and whose intersection recovers `P_K`.

Formally: `[Q_AX, Q_XB] = 0` where `Q = 1 - P`, and
`K = (K_AX ⊗ H_B) ∩ (H_A ⊗ K_XB)`, which in projector language means
`P_AX ∘ P_XB = P_K`.

See arXiv:1606.00608, Appendix D.2, Definition before Proposition D.1. -/
def HasCommutingParentHam (P_K : E →ₗ[ℂ] E) : Prop :=
  ∃ P_AX P_XB : E →ₗ[ℂ] E,
    -- P_AX, P_XB are idempotent (projectors)
    P_AX ∘ₗ P_AX = P_AX ∧
    P_XB ∘ₗ P_XB = P_XB ∧
    -- The complementary projectors commute: [1 - P_AX, 1 - P_XB] = 0,
    -- equivalently [P_AX, P_XB] = 0
    P_AX ∘ₗ P_XB = P_XB ∘ₗ P_AX ∧
    -- P_K projects onto the intersection: P_AX ∘ P_XB = P_K
    P_AX ∘ₗ P_XB = P_K ∧
    -- P_K is contained in both: P_α ∘ P_K = P_K
    P_AX ∘ₗ P_K = P_K ∧
    P_XB ∘ₗ P_K = P_K

/-- **Proposition D.1** (arXiv:1606.00608, Appendix D.2):
A subspace K_{AXB} corresponds to a commuting parent Hamiltonian
if and only if regions A and B are decorrelated w.r.t. K.

The proof proceeds in two directions:

**(⟸ decorrelated ⟹ commuting Ham):**
Define `P_AX`, `P_XB` as the support projectors of the partial traces of K.
The decorrelation condition forces `P_AX ∘ P_XB = P_XB ∘ P_AX = P_K`,
hence the complementary projectors `Q = 1 - P` commute and
`K = (K_AX ⊗ H_B) ∩ (H_A ⊗ K_XB)`.

**(⟹ commuting Ham ⟹ decorrelated):**
From `[P_AX, P_XB] = 0` we get `P_AX ∘ P_XB = P_K`.
Then `P_XB ∘ (1 - P_K) ∘ P_AX = P_XB ∘ P_AX - P_K = 0`,
so for any `O_A` on A (commuting with `P_XB`) and `O_B` on B
(commuting with `P_AX`):
`P_K O_A (1 - P_K) O_B P_K = P_K P_XB O_A (1 - P_K) O_B P_AX P_K`
`= P_K O_A P_XB (1 - P_K) P_AX O_B P_K = 0`.

TODO: complete the proof once tensor-product Hilbert space infrastructure
is available. The key missing piece is the ability to express that `O_A`
commutes with `P_XB` (because they act on different tensor factors).
-/
theorem decorrelated_iff_commutingHam
    (P_K : E →ₗ[ℂ] E)
    (hP_idem : P_K ∘ₗ P_K = P_K)
    (ObsA ObsB : Set (E →ₗ[ℂ] E))
    (hA_comm : ∀ O_A ∈ ObsA, ∀ P_XB : E →ₗ[ℂ] E,
      P_XB ∘ₗ O_A = O_A ∘ₗ P_XB)
    (hB_comm : ∀ O_B ∈ ObsB, ∀ P_AX : E →ₗ[ℂ] E,
      P_AX ∘ₗ O_B = O_B ∘ₗ P_AX) :
    IsDecorrelated P_K ObsA ObsB ↔ HasCommutingParentHam P_K := by
  sorry

end AbstractDecorrelation

/-!
### Auxiliary lemmas for commuting projectors

These lemmas are used in the proof of Proposition D.1 and may be
useful elsewhere.
-/

section CommutingProjectors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- If two idempotent linear maps commute, their composition is idempotent. -/
theorem comp_idempotent_of_comm_of_idempotent
    {P Q : E →ₗ[ℂ] E}
    (hP : P ∘ₗ P = P)
    (hQ : Q ∘ₗ Q = Q)
    (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    (P ∘ₗ Q) ∘ₗ (P ∘ₗ Q) = P ∘ₗ Q := by
  -- Pointwise: P(Q(P(Qx))) = P(Qx)
  ext x; simp only [LinearMap.comp_apply]
  -- Use hcomm pointwise: P(Qy) = Q(Py)
  have hPQ : ∀ y, P (Q y) = Q (P y) := LinearMap.ext_iff.mp hcomm
  -- Use hQ pointwise: Q(Qy) = Qy
  have hQQ : ∀ y, Q (Q y) = Q y := LinearMap.ext_iff.mp hQ
  -- Use hP pointwise: P(Py) = Py
  have hPP : ∀ y, P (P y) = P y := LinearMap.ext_iff.mp hP
  -- P(Q(P(Qx)))
  --   = Q(P(P(Qx)))    by hPQ
  --   = Q(P(Qx))        by hPP
  --   = P(Q(Qx))        by hPQ⁻¹
  --   = P(Qx)            by hQQ
  rw [hPQ, hPP, ← hPQ, hQQ]

/-- If `P` and `Q` are commuting idempotents and `R = P ∘ Q`, then
`P ∘ R = R`. -/
theorem left_absorb_of_comm_idempotent
    {P Q : E →ₗ[ℂ] E}
    (hP : P ∘ₗ P = P)
    (_hQ : Q ∘ₗ Q = Q)
    (_hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    P ∘ₗ (P ∘ₗ Q) = P ∘ₗ Q := by
  rw [← LinearMap.comp_assoc, hP]

/-- If `P` and `Q` are commuting idempotents and `R = P ∘ Q`, then
`Q ∘ R = R`. -/
theorem right_absorb_of_comm_idempotent
    {P Q : E →ₗ[ℂ] E}
    (_hP : P ∘ₗ P = P)
    (hQ : Q ∘ₗ Q = Q)
    (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    Q ∘ₗ (P ∘ₗ Q) = P ∘ₗ Q := by
  rw [← LinearMap.comp_assoc, ← hcomm, LinearMap.comp_assoc, hQ]

/-- For commuting idempotents, `Q ∘ (1 - P ∘ Q) ∘ P = 0`. This is the
key cancellation used in the "only if" direction of Prop D.1:
`P_XB ∘ P_K^⊥ ∘ P_AX = 0`. -/
theorem comp_complement_comm_zero
    {P Q : E →ₗ[ℂ] E}
    (hP : P ∘ₗ P = P)
    (hQ : Q ∘ₗ Q = Q)
    (hcomm : P ∘ₗ Q = Q ∘ₗ P) :
    Q ∘ₗ (LinearMap.id - P ∘ₗ Q) ∘ₗ P = 0 := by
  -- Q ∘ (id - PQ) ∘ P = Q∘P - Q∘(PQ)∘P = QP - (Q∘P∘Q)∘P
  -- We work pointwise.
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.zero_apply]
  -- Goal: Q (P x - P (Q (P x))) = 0
  have hPQ : ∀ y, P (Q y) = Q (P y) := LinearMap.ext_iff.mp hcomm
  have hQQ : ∀ y, Q (Q y) = Q y := LinearMap.ext_iff.mp hQ
  have hPP : ∀ y, P (P y) = P y := LinearMap.ext_iff.mp hP
  rw [map_sub]
  -- Goal: Q (P x) - Q (P (Q (P x))) = 0
  suffices h : Q (P (Q (P x))) = Q (P x) by rw [h, sub_self]
  -- Q(P(Q(Px)))
  --   rewrite inner P(Q(Px)) using hPQ: P(Q(Px)) = Q(P(Px))
  rw [hPQ (P x)]
  --   Q(Q(P(Px)))
  rw [hQQ]
  --   Q(P(Px))
  --   rewrite P(Px) using hPP
  rw [hPP]

end CommutingProjectors
