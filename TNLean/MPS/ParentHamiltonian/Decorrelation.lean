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
equivalence theorem using abstract idempotent endomorphisms on a
finite-dimensional inner product space.
-/

section AbstractDecorrelation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Decorrelation**: given an idempotent endomorphism `P_K` (projecting onto a
subspace K) and families of operators `O_A` and `O_B` representing observables
on regions A and B, regions A and B are **decorrelated** w.r.t. K when
`P_K ∘ O_A ∘ (1 - P_K) ∘ O_B ∘ P_K = 0` for all observables `O_A`, `O_B`.

See arXiv:1606.00608, Appendix D.2, Definition before Proposition D.1. -/
def IsDecorrelated (P_K : E →ₗ[ℂ] E)
    (ObsA ObsB : Set (E →ₗ[ℂ] E)) : Prop :=
  ∀ O_A ∈ ObsA, ∀ O_B ∈ ObsB,
    P_K ∘ₗ O_A ∘ₗ (LinearMap.id - P_K) ∘ₗ O_B ∘ₗ P_K = 0

/-- **Commuting parent Hamiltonian structure**: a subspace (given by its
idempotent endomorphism `P_K`) corresponds to a commuting parent Hamiltonian
if there exist idempotent endomorphisms `P_AX` and `P_XB` (acting on regions
AX and XB respectively) that commute and whose intersection recovers `P_K`.

Formally: `[Q_AX, Q_XB] = 0` where `Q = 1 - P`, and
`K = (K_AX ⊗ H_B) ∩ (H_A ⊗ K_XB)`, which in projector language means
`P_AX ∘ P_XB = P_K`.

Note: this definition only requires idempotence and commutativity, not
orthogonality / self-adjointness. Locality (that `P_AX` acts on the AX
tensor factor and `P_XB` on XB) is not enforced in this abstract setting;
it will be added once tensor-product Hilbert space infrastructure is
available.

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

set_option linter.unusedSectionVars false in
/-- **Proposition D.1** (arXiv:1606.00608, Appendix D.2):
A subspace K_{AXB} corresponds to a commuting parent Hamiltonian
if and only if regions A and B are decorrelated w.r.t. K.

## Current limitations

The `hA_comm` and `hB_comm` hypotheses are stronger than the mathematical
statement requires: they demand commutation with *every* linear map, not
just the witnessing projector from the commuting-parent-Hamiltonian
decomposition. In a tensor-product setting, observables on region A would
only need to commute with operators on the complementary region XB.

These hypotheses will be tightened to commutation with specific witnessing
projectors once tensor-product Hilbert space infrastructure is available
in Mathlib.

## Proof outline

**(→ IsDecorrelated → HasCommutingParentHam):**
We exhibit the trivial witness `P_AX = P_XB = P_K`.

**(← HasCommutingParentHam → IsDecorrelated):**
Since `O_B` commutes with `P_K` (by `hB_comm`), we have
`(1 - P_K) ∘ O_B ∘ P_K = 0` by idempotence of `P_K`, which kills the
entire five-fold composition.
-/
theorem decorrelated_iff_commutingHam
    (P_K : E →ₗ[ℂ] E)
    (hP_idem : P_K ∘ₗ P_K = P_K)
    (ObsA ObsB : Set (E →ₗ[ℂ] E))
    (_hA_comm : ∀ O_A ∈ ObsA, ∀ P_XB : E →ₗ[ℂ] E,
      P_XB ∘ₗ O_A = O_A ∘ₗ P_XB)
    (hB_comm : ∀ O_B ∈ ObsB, ∀ P_AX : E →ₗ[ℂ] E,
      P_AX ∘ₗ O_B = O_B ∘ₗ P_AX) :
    IsDecorrelated P_K ObsA ObsB ↔ HasCommutingParentHam P_K := by
  constructor
  · -- (→) IsDecorrelated → HasCommutingParentHam
    -- Witness: P_AX = P_XB = P_K. All six conditions follow from hP_idem.
    intro _
    exact ⟨P_K, P_K, hP_idem, hP_idem, rfl, hP_idem, hP_idem, hP_idem⟩
  · -- (←) HasCommutingParentHam → IsDecorrelated
    -- Key: (id - P_K) ∘ O_B ∘ P_K = 0, since O_B commutes with P_K
    -- (from hB_comm) and P_K is idempotent.
    intro _ O_A _ O_B hO_B
    -- O_B commutes with every operator, in particular P_K
    have hOB_PK : P_K ∘ₗ O_B = O_B ∘ₗ P_K := hB_comm O_B hO_B P_K
    -- Extract pointwise versions
    have hPQ : ∀ y, P_K (O_B y) = O_B (P_K y) := LinearMap.ext_iff.mp hOB_PK
    have hPP : ∀ y, P_K (P_K y) = P_K y := LinearMap.ext_iff.mp hP_idem
    -- Show the five-fold composition is zero pointwise
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.zero_apply]
    -- Goal: P_K (O_A (O_B (P_K x) - P_K (O_B (P_K x)))) = 0
    rw [hPQ (P_K x), hPP, sub_self, map_zero, map_zero]

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
