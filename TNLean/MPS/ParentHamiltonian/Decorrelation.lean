/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Decorrelation and commuting parent Hamiltonians

This file defines the notion of **decorrelation** for a subspace with
respect to two disjoint regions, and proves the backward direction of the
decorrelation–commuting-parent-Hamiltonian equivalence: a commuting parent
Hamiltonian implies decorrelation when observables respect locality.

This is the backward direction of Proposition D.3 from arXiv:1606.00608,
Appendix D, §D.2. The forward direction requires tensor-product infrastructure
and is deferred.

## Main definitions

* `Decorrelation.IsDecorrelated` — regions A and B are decorrelated w.r.t. a
  subspace K when `P_K O_A (1 - P_K) O_B P_K = 0` for all observables
  O_A, O_B on the respective regions.
* `Decorrelation.HasCommutingParentHam` — a subspace K equals the intersection
  of two local kernels `K_AX ⊗ H_B ∩ H_A ⊗ K_XB` where the corresponding
  projectors commute.

## Main results

* `Decorrelation.commutingHam_isDecorrelated` — commuting parent Hamiltonian →
  decorrelation (Proposition D.3, backward direction)

## References

* arXiv:1606.00608, Appendix D, §D.2 (lines 2181–2290). The definitions
  are numbered D.1 (decorrelated) and D.2 (parent commuting Hamiltonian);
  the equivalence proposition is D.3.
-/

/-!
### Auxiliary lemma for commuting projectors

The key cancellation lemma used in the proof of Proposition D.3.
-/

section CommutingProjectors

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

namespace LinearMap

/-- For commuting idempotents, `Q ∘ (1 - P ∘ Q) ∘ P = 0`. This is the
key cancellation used in the "only if" direction of Prop D.3:
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

end LinearMap

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

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

namespace Decorrelation

/-- **Decorrelation**: given an idempotent endomorphism `P_K` (projecting onto a
subspace K) and families of operators `O_A` and `O_B` representing observables
on regions A and B, regions A and B are **decorrelated** w.r.t. K when
`P_K ∘ O_A ∘ (1 - P_K) ∘ O_B ∘ P_K = 0` for all observables `O_A`, `O_B`.

See arXiv:1606.00608, Appendix D, §D.2, Definition D.1. -/
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

See arXiv:1606.00608, Appendix D, §D.2, Definition D.2.

TODO(tensor-product): add locality constraints requiring `P_AX` to act on
`H_A ⊗ H_X` and `P_XB` to act on `H_X ⊗ H_B`. Without these, the predicate
is trivially satisfiable by `P_AX = P_XB = P_K`. -/
structure HasCommutingParentHam (P_K : E →ₗ[ℂ] E) where
  /-- Projector onto the AX region. -/
  P_AX : E →ₗ[ℂ] E
  /-- Projector onto the XB region. -/
  P_XB : E →ₗ[ℂ] E
  /-- `P_AX` is idempotent. -/
  hAX_idem : P_AX ∘ₗ P_AX = P_AX
  /-- `P_XB` is idempotent. -/
  hXB_idem : P_XB ∘ₗ P_XB = P_XB
  /-- The projectors commute: `[P_AX, P_XB] = 0`. -/
  hcomm : P_AX ∘ₗ P_XB = P_XB ∘ₗ P_AX
  /-- `P_K` is the intersection projector: `P_AX ∘ P_XB = P_K`. -/
  hK : P_AX ∘ₗ P_XB = P_K

/-- **Proposition D.3, backward direction** (arXiv:1606.00608, Appendix D, §D.2):
If a subspace K has a commuting parent Hamiltonian decomposition
`P_K = P_AX ∘ P_XB` with `[P_AX, P_XB] = 0`, and observables on region A
commute with `P_XB` while observables on region B commute with `P_AX`, then
regions A and B are decorrelated w.r.t. K.

The commutation hypotheses are scoped to the *specific* witnessing projectors
`P_AX` and `P_XB`, not all linear maps. This captures the locality structure:
A-observables commute with the XB-projector and vice versa.

## Proof outline

The key identity is `P_XB ∘ (1 - P_AX ∘ P_XB) ∘ P_AX = 0` (see
`LinearMap.comp_complement_comm_zero`). Using the commutation hypotheses to
slide `O_A` past `P_XB` and `O_B` past `P_AX`, the five-fold composition
`P_K ∘ O_A ∘ (1 - P_K) ∘ O_B ∘ P_K` factors as
`P_AX ∘ O_A ∘ [P_XB ∘ (1 - P_AX ∘ P_XB) ∘ P_AX] ∘ O_B ∘ P_XB = 0`.

## Note on the forward direction

The converse (IsDecorrelated → HasCommutingParentHam) requires constructing
*local* projectors `P_AX` and `P_XB` on the AX and XB tensor factors.
In this abstract (non-tensor-product) setting, `HasCommutingParentHam` is
trivially satisfiable by `P_AX = P_XB = P_K`, so an abstract iff would be
vacuous. The forward direction is deferred to the tensor-product setting.

See arXiv:1606.00608, Appendix D, §D.2, Proposition D.3. -/
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
  have key := LinearMap.comp_complement_comm_zero hAX_idem hXB_idem hcomm
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

/-- Convenience wrapper that consumes `HasCommutingParentHam` directly.

The witnessing projectors `P_AX`, `P_XB` are extracted from the structure
fields. See `commutingHam_isDecorrelated` for the version with explicit
witnesses. -/
theorem HasCommutingParentHam.isDecorrelated
    {P_K : E →ₗ[ℂ] E}
    (hCPH : HasCommutingParentHam P_K)
    (ObsA ObsB : Set (E →ₗ[ℂ] E))
    (hA_comm : ∀ O_A ∈ ObsA, O_A ∘ₗ hCPH.P_XB = hCPH.P_XB ∘ₗ O_A)
    (hB_comm : ∀ O_B ∈ ObsB, O_B ∘ₗ hCPH.P_AX = hCPH.P_AX ∘ₗ O_B) :
    IsDecorrelated P_K ObsA ObsB :=
  commutingHam_isDecorrelated P_K hCPH.P_AX hCPH.P_XB
    hCPH.hAX_idem hCPH.hXB_idem hCPH.hcomm hCPH.hK
    ObsA ObsB hA_comm hB_comm

end Decorrelation

end AbstractDecorrelation
