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
respect to two disjoint regions, and proves the backward direction of the
decorrelation–commuting-parent-Hamiltonian equivalence: a commuting parent
Hamiltonian implies decorrelation when observables respect locality.

This is the backward direction of Proposition D.1 from arXiv:1606.00608,
Appendix D.2. The forward direction requires tensor-product infrastructure
and is deferred.

## Main definitions

* `IsDecorrelated` — regions A and B are decorrelated w.r.t. a subspace K
  when `P_K O_A (1 - P_K) O_B P_K = 0` for all observables O_A, O_B on
  the respective regions.
* `HasCommutingParentHam` — a subspace K equals the intersection of two
  local kernels `K_AX ⊗ H_B ∩ H_A ⊗ K_XB` where the corresponding
  projectors commute.

## Main results

* `commutingHam_isDecorrelated` — commuting parent Hamiltonian →
  decorrelation (Proposition D.1, backward direction)

## References

* arXiv:1606.00608, Appendix D.2 (lines 2181–2290)
-/

open scoped BigOperators

/-!
### Auxiliary lemmas for commuting projectors

These lemmas are used in the proof of Proposition D.1 and may be
useful elsewhere.
-/

section CommutingProjectors

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

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
    (hP : P ∘ₗ P = P) :
    P ∘ₗ (P ∘ₗ Q) = P ∘ₗ Q := by
  rw [← LinearMap.comp_assoc, hP]

/-- If `P` and `Q` are commuting idempotents and `R = P ∘ Q`, then
`Q ∘ R = R`. -/
theorem right_absorb_of_comm_idempotent
    {P Q : E →ₗ[ℂ] E}
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
available. In particular, the trivial witness `P_AX = P_XB = P_K` always
satisfies this predicate for any idempotent `P_K`; non-trivial content
arises only when combined with locality constraints (see
`commutingHam_isDecorrelated`).

See arXiv:1606.00608, Appendix D.2, Definition before Proposition D.1.

TODO(tensor-product): add locality constraints requiring `P_AX` to act on
`H_A ⊗ H_X` and `P_XB` to act on `H_X ⊗ H_B`. Without these, the predicate
is trivially satisfiable by `P_AX = P_XB = P_K`. -/
def HasCommutingParentHam (P_K : E →ₗ[ℂ] E) : Prop :=
  ∃ P_AX P_XB : E →ₗ[ℂ] E,
    -- P_AX, P_XB are idempotent (projectors)
    P_AX ∘ₗ P_AX = P_AX ∧
    P_XB ∘ₗ P_XB = P_XB ∧
    -- The complementary projectors commute: [1 - P_AX, 1 - P_XB] = 0,
    -- equivalently [P_AX, P_XB] = 0
    P_AX ∘ₗ P_XB = P_XB ∘ₗ P_AX ∧
    -- P_K projects onto the intersection: P_AX ∘ P_XB = P_K
    P_AX ∘ₗ P_XB = P_K

omit [FiniteDimensional ℂ E] in
/-- If `P_K` has a commuting parent Hamiltonian with witnesses `P_AX`, `P_XB`,
then `P_AX ∘ P_K = P_K` (the left witness absorbs `P_K`). -/
theorem HasCommutingParentHam.left_absorb {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    ∃ P_AX P_XB : E →ₗ[ℂ] E, P_AX ∘ₗ P_XB = P_K ∧ P_AX ∘ₗ P_K = P_K := by
  obtain ⟨P_AX, P_XB, hAX, _, _, hK⟩ := h
  exact ⟨P_AX, P_XB, hK, by rw [← hK, ← LinearMap.comp_assoc, hAX]⟩

omit [FiniteDimensional ℂ E] in
/-- If `P_K` has a commuting parent Hamiltonian with witnesses `P_AX`, `P_XB`,
then `P_XB ∘ P_K = P_K` (the right witness absorbs `P_K`). -/
theorem HasCommutingParentHam.right_absorb {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    ∃ P_AX P_XB : E →ₗ[ℂ] E, P_AX ∘ₗ P_XB = P_K ∧ P_XB ∘ₗ P_K = P_K := by
  obtain ⟨P_AX, P_XB, _, hXB, hcomm, hK⟩ := h
  exact ⟨P_AX, P_XB, hK, by rw [← hK, ← LinearMap.comp_assoc, ← hcomm,
    LinearMap.comp_assoc, hXB]⟩

omit [FiniteDimensional ℂ E] in
/-- **Proposition D.1, backward direction** (arXiv:1606.00608, Appendix D.2):
If a subspace K has a commuting parent Hamiltonian decomposition
`P_K = P_AX ∘ P_XB` with `[P_AX, P_XB] = 0`, and observables on region A
commute with `P_XB` while observables on region B commute with `P_AX`, then
regions A and B are decorrelated w.r.t. K.

The commutation hypotheses are scoped to the *specific* witnessing projectors
`P_AX` and `P_XB`, not all linear maps. This captures the locality structure:
A-observables commute with the XB-projector and vice versa.

## Proof outline

The key identity is `P_XB ∘ (1 - P_AX ∘ P_XB) ∘ P_AX = 0` (see
`comp_complement_comm_zero`). Using the commutation hypotheses to slide
`O_A` past `P_XB` and `O_B` past `P_AX`, the five-fold composition
`P_K ∘ O_A ∘ (1 - P_K) ∘ O_B ∘ P_K` factors as
`P_AX ∘ O_A ∘ [P_XB ∘ (1 - P_AX ∘ P_XB) ∘ P_AX] ∘ O_B ∘ P_XB = 0`.

## Note on the forward direction

The converse (IsDecorrelated → HasCommutingParentHam) requires constructing
*local* projectors `P_AX` and `P_XB` on the AX and XB tensor factors.
In this abstract (non-tensor-product) setting, `HasCommutingParentHam` is
trivially satisfiable by `P_AX = P_XB = P_K`, so an abstract iff would be
vacuous. The forward direction is deferred to the tensor-product setting.

See arXiv:1606.00608, Appendix D.2, Proposition D.1. -/
theorem commutingHam_isDecorrelated
    (P_K P_AX P_XB : E →ₗ[ℂ] E)
    (hAX_idem : P_AX ∘ₗ P_AX = P_AX)
    (hXB_idem : P_XB ∘ₗ P_XB = P_XB)
    (hcomm : P_AX ∘ₗ P_XB = P_XB ∘ₗ P_AX)
    (hK : P_AX ∘ₗ P_XB = P_K)
    (ObsA ObsB : Set (E →ₗ[ℂ] E))
    (hA_comm : ∀ O_A ∈ ObsA, O_A ∘ₗ P_XB = P_XB ∘ₗ O_A)
    (hB_comm : ∀ O_B ∈ ObsB, O_B ∘ₗ P_AX = P_AX ∘ₗ O_B) :
    IsDecorrelated P_K ObsA ObsB := by
  intro O_A hOA O_B hOB
  -- Substitute P_K = P_AX ∘ P_XB
  rw [← hK]
  -- Key cancellation: P_XB ∘ (id - P_AX ∘ P_XB) ∘ P_AX = 0
  have key := comp_complement_comm_zero hAX_idem hXB_idem hcomm
  -- Extract pointwise commutativity
  have hA : ∀ y, O_A (P_XB y) = P_XB (O_A y) :=
    LinearMap.ext_iff.mp (hA_comm O_A hOA)
  have hB : ∀ y, O_B (P_AX y) = P_AX (O_B y) :=
    LinearMap.ext_iff.mp (hB_comm O_B hOB)
  -- Pointwise key: P_XB (P_AX w - P_AX (P_XB (P_AX w))) = 0
  have key_pw : ∀ w, P_XB (P_AX w - P_AX (P_XB (P_AX w))) = 0 := by
    intro w
    have h := LinearMap.ext_iff.mp key w
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at h
    exact h
  -- Work pointwise
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.zero_apply]
  -- Goal: P_AX (P_XB (O_A (O_B (P_AX (P_XB x)) - P_AX (P_XB (O_B (P_AX (P_XB x))))))) = 0
  -- Step 1: Slide O_B past P_AX using hB
  rw [hB (P_XB x)]
  -- Goal: P_AX (P_XB (O_A (P_AX (O_B (P_XB x)) - P_AX (P_XB (P_AX (O_B (P_XB x))))))) = 0
  -- Step 2: Slide P_XB past O_A using hA (reversed)
  rw [(hA _).symm]
  -- Goal: P_AX (O_A (P_XB (P_AX (O_B (P_XB x)) - P_AX (P_XB (P_AX (O_B (P_XB x))))))) = 0
  -- Step 3: Apply key cancellation (P_XB kills the middle)
  rw [key_pw, map_zero, map_zero]

end AbstractDecorrelation
