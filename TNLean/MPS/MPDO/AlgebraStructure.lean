/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.FusionIsometries

/-!
# Algebra-structure formulation of the MPDO renormalization fixed point

This file records the **algebra-structure** side of the general MPDO RFP
equivalence of arXiv:1606.00608 §4.5, Theorem IV.13
(Cirac–Pérez-García–Schuch–Verstraete).

Theorem IV.13 of the paper characterises renormalization-fixed-point MPDOs by
the existence of a tower of support algebras `𝒜_n` with structure coefficients
`c_{αβγ}^{(L)}` and compatible multiplication/blocking maps. The support
algebras are indexed C*-subalgebras of matrix algebras; the multiplication is
the blocking map `𝒜_n × 𝒜_n → 𝒜_{2n}` arising from physically concatenating
two blocks; and the inclusions `𝒜_n ↪ 𝒜_{n+1}` arise from appending a single
site at the boundary.

The development of the C*-algebraic API required for the full statement is
deferred. This file records the **shape** of the data as a plain Lean
structure, uses `Prop`-valued provisional conditions, and names the
relation to a given MPO tensor through `AlgebraStructureData.CompatibleWith`.
Each provisional choice is flagged with a `-- TODO (#612)` comment citing
the corresponding paper reference.

## Main declarations

* `AlgebraStructureData`: the tower of support algebras with blocking and
  inclusion maps.
* `AlgebraStructureData.CompatibleWith`: relation linking algebra-structure
  data to an MPO tensor, currently the trivial proposition `True`.
* `IsRFP_MPDO_via_algebra_scaffold`: the provisional RFP predicate built from
  the existence of algebra-structure data related to the tensor by
  `CompatibleWith`. The `_scaffold` suffix marks that the relation
  `CompatibleWith` is currently `True` and the predicate consequently vacuous.

## References

* [CPGSV17] arXiv:1606.00608, §4.5 and Appendix C.3
  (Cirac–Pérez-García–Schuch–Verstraete, Ann. Phys. 378, 100–149), in
  particular Theorem IV.13 and its proof in C.3.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The *support algebra at size `n`*.

-- TODO (#612): replace with a `Subalgebra ℂ (Matrix (Fin D^n) (Fin D^n) ℂ)`
cut out by the span of operator matrix elements at size `n`, matching `𝒜_n`
from Theorem IV.13. The current definition uses `Matrix (Fin D) (Fin D) ℂ` as
a stand-in for every `n`. -/
abbrev SupportAlgebra (D : ℕ) (_n : ℕ) : Type :=
  Matrix (Fin D) (Fin D) ℂ

/-- **Algebra-structure data** for a putative MPDO renormalization fixed
point.

In the paper (Theorem IV.13 of arXiv:1606.00608), such data consists of a
family of support algebras `𝒜_n`, blocking maps
`m_n : 𝒜_n × 𝒜_n → 𝒜_{2n}` realising the horizontal concatenation of
blocks, and unital inclusion maps `ι_n : 𝒜_n → 𝒜_{n+1}` that add a single
site. The coherence conditions (associativity of blocking, interplay with
inclusions, existence of the positive structure coefficients
`c_{αβγ}^{(L)} = tr(χ_{αβγ}^L)`, and the idempotence relation
`m_γ = Σ c_{αβγ}^{(1)} m_α m_β`) are recorded as a single `Prop`-valued
hypothesis, weaker than the conjunction of the conditions of the paper.

In the present formulation the support algebra at every size is represented
by `SupportAlgebra D n = Matrix (Fin D) (Fin D) ℂ`; the multiplication and
inclusion fields are typed against this stand-in.

-- TODO (#612): tighten fields to `Subalgebra`/`AlgHom` types and install
the coherence hypotheses of Theorem IV.13. -/
structure AlgebraStructureData (d D : ℕ) where
  /-- Multiplication / blocking map at each size `n`.

  -- TODO (#612): upgrade to a linear map `A n ⊗ A n →ₗ[ℂ] A (2 * n)` once
  the support algebras are genuine subalgebras. -/
  m : ∀ n : ℕ,
    SupportAlgebra D n →ₗ[ℂ] SupportAlgebra D n →ₗ[ℂ] SupportAlgebra D (2 * n)
  /-- Unital inclusion at each size `n`.

  -- TODO (#612): upgrade to an `AlgHom` once the support algebras are
  genuine subalgebras. -/
  iota : ∀ n : ℕ, SupportAlgebra D n →ₗ[ℂ] SupportAlgebra D (n + 1)
  /-- Coherence relation between blocking at consecutive sizes.

  -- TODO (#612): replace by the associativity/compatibility condition of
  §4.5, in particular the condition that `m_n` and `iota_n` satisfy the
  diagram implicit in equation (29) of the paper. -/
  coherence : Prop
  /-- The coherence relation holds. -/
  coherence_holds : coherence

namespace AlgebraStructureData

variable {d D : ℕ}

/-- Compatibility relation between algebra-structure data and an MPO tensor
`M`. In the final formulation this asserts that the structure coefficients
carried by `data` match the BNT decomposition of `M`, following
Theorem IV.13 (ii) of arXiv:1606.00608. The present definition is the trivial
proposition `True`, which is satisfied by every pair `(data, M)`.
-- TODO (#612): replace by the compatibility condition relating
`c_{αβγ}^{(L)}` to the BNT decomposition of `M`. -/
def CompatibleWith (_data : AlgebraStructureData d D) (_M : MPOTensor d D) :
    Prop :=
  True

end AlgebraStructureData

/-- **Provisional algebra-structure formulation of the MPDO renormalization
fixed point.**

In the paper, an MPDO `M` is a renormalization fixed point whenever its
operators `O_L(M_α)` span an algebra with positive structure coefficients
satisfying the idempotence relation (equations (29)–(30) of §4.5). The
definition below asserts the existence of algebra-structure data related to
`M` by the relation `AlgebraStructureData.CompatibleWith`.

The `_scaffold` suffix marks that `AlgebraStructureData.CompatibleWith` is
currently `True` and that `AlgebraStructureData d D` is inhabited (e.g. by
zero multiplication, zero inclusion, and `coherence := True`). The predicate
is consequently satisfied by every `M`, and must not be used as a hypothesis
or conclusion of any nontrivial result until the relation is tightened.

-- TODO (#612): replace `AlgebraStructureData.CompatibleWith` with the
compatibility condition between `M` and the data, following
Theorem IV.13 (ii): the structure coefficients `c_{αβγ}^{(L)}` of the algebra
associated to `data` must match the BNT decomposition of `M`. Drop the
`_scaffold` suffix once the relation is no longer trivial. -/
def IsRFP_MPDO_via_algebra_scaffold (M : MPOTensor d D) : Prop :=
  ∃ data : AlgebraStructureData d D, data.CompatibleWith M

end MPOTensor
