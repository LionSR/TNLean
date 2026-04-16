/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.FusionIsometries

/-!
# Algebra-structure formulation of the MPDO renormalization fixed point

This file scaffolds the **algebra-structure** side of the general MPDO RFP
equivalence of arXiv:1606.00608 §4.5, Theorem IV.13
(Cirac–Pérez-García–Schuch–Verstraete).

Theorem IV.13 of the paper characterises renormalization-fixed-point MPDOs by
the existence of a tower of support algebras `𝒜_n` with structure coefficients
`c_{αβγ}^{(L)}` and compatible multiplication/blocking maps. The support
algebras are indexed C*-subalgebras of matrix algebras; the multiplication is
the blocking map `𝒜_n × 𝒜_n → 𝒜_{2n}` coming from physically concatenating
two blocks; and the inclusions `𝒜_n ↪ 𝒜_{n+1}` arise from appending a single
site at the boundary.

As with `FusionIsometries.lean`, the full C*-algebraic infrastructure is not
yet present in the repository. This file therefore records the **shape** of
the required data as a plain Lean structure, uses `Prop`-valued placeholder
conditions, and states the paper's headline equivalence
(`rfp_mpdo_fusion_iff_algebra`) under a trivializing compatibility hypothesis.
Each placeholder is flagged with a `-- TODO (#612)` comment that cites the
corresponding paper reference.

## Main declarations

* `AlgebraStructureData`: the tower of support algebras with blocking and
  inclusion maps, as a scaffolding structure.
* `IsRFP_MPDO_via_algebra`: the alternative RFP predicate built from the
  existence of coherent algebra-structure data.
* `rfp_mpdo_fusion_iff_algebra`: the paper's headline equivalence between the
  fusion-isometry and algebra-structure formulations, stated with a
  compatibility hypothesis that makes the proof trivial.

## References

* [CPGSV17] arXiv:1606.00608, §4.5 and Appendix C.3
  (Cirac–Pérez-García–Schuch–Verstraete, Ann. Phys. 378, 100–149), in
  particular Theorem IV.13 and its proof in C.3.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The *support algebra at size `n`* used in the scaffold.

-- TODO (#612): replace with an honest `Subalgebra ℂ (Matrix (Fin D^n)
(Fin D^n) ℂ)` cut out by the span of operator matrix elements at size `n`,
matching `𝒜_n` from Theorem IV.13. The scaffold uses the same matrix type for
every `n`. -/
abbrev SupportAlgebra (D : ℕ) (_n : ℕ) : Type :=
  Matrix (Fin D) (Fin D) ℂ

/-- **Algebra-structure data** for a putative MPDO renormalization fixed
point.

In the paper (Theorem IV.13 of arXiv:1606.00608), such data consists of a
family of support algebras `𝒜_n`, blocking maps
`m_n : 𝒜_n × 𝒜_n → 𝒜_{2n}` that realise the horizontal concatenation of
blocks, and unital inclusion maps `ι_n : 𝒜_n → 𝒜_{n+1}` that add a single
site. The coherence conditions (associativity of blocking, interplay with
inclusions, existence of the positive structure coefficients
`c_{αβγ}^{(L)} = tr(χ_{αβγ}^L)`, and the idempotence relation
`m_γ = Σ c_{αβγ}^{(1)} m_α m_β`) are all recorded here as `Prop`-valued
hypotheses that compile today and will be tightened later.

-- TODO (#612): tighten fields to honest `Subalgebra`/`AlgHom` types and
install the full coherence hypotheses from Theorem IV.13. -/
structure AlgebraStructureData (d D : ℕ) where
  /-- Family of support algebras, one at each blocking size `n`. -/
  A : ℕ → Type := fun n => SupportAlgebra D n
  /-- Multiplication / blocking map at each level `n`.

  -- TODO (#612): upgrade to an honest linear map
  `A n ⊗ A n →ₗ[ℂ] A (2 * n)`; for the scaffold we simply record its action
  as a function between stand-in matrix spaces. -/
  m : ∀ n : ℕ,
    SupportAlgebra D n →ₗ[ℂ] SupportAlgebra D n →ₗ[ℂ] SupportAlgebra D (2 * n)
  /-- Unital inclusion at each level `n`.

  -- TODO (#612): upgrade to an honest `AlgHom` once the support algebras are
  genuine subalgebras. -/
  iota : ∀ n : ℕ, SupportAlgebra D n →ₗ[ℂ] SupportAlgebra D (n + 1)
  /-- Coherence between blocking at consecutive levels.

  -- TODO (#612): supply the actual associativity/compatibility condition from
  §4.5, in particular that `m_n` and `iota_n` satisfy the diagram implicit in
  equation (29) of the paper. For now this is an arbitrary `Prop`. -/
  coherence : Prop
  /-- The placeholder coherence condition is assumed to hold. -/
  coherence_holds : coherence

namespace AlgebraStructureData

variable {d D : ℕ}

/-- The zero algebra-structure datum, witnessing that the type
`AlgebraStructureData d D` is non-empty. -- TODO (#612): remove once
concrete algebra-structure data is available. -/
noncomputable def zero (d D : ℕ) : AlgebraStructureData d D where
  m := fun _ => 0
  iota := fun _ => 0
  coherence := True
  coherence_holds := trivial

instance instNonempty (d D : ℕ) : Nonempty (AlgebraStructureData d D) :=
  ⟨zero d D⟩

end AlgebraStructureData

/-- **Algebra-structure formulation of the MPDO renormalization fixed
point.**

In the paper, an MPDO `M` is a renormalization fixed point whenever its
operators `O_L(M_α)` span an algebra with positive structure coefficients
satisfying the idempotence relation (equations (29)–(30) of §4.5). The
scaffolded version records the existence of compatible
`AlgebraStructureData`, leaving the precise compatibility condition with the
tensor `M` as a placeholder.

-- TODO (#612): replace the `_ = M` placeholder with the concrete
compatibility condition between `M` and the data, following Theorem IV.13
(ii): the structure coefficients `c_{αβγ}^{(L)}` of the algebra associated to
`data` must match the BNT decomposition of `M`. -/
def IsRFP_MPDO_via_algebra (M : MPOTensor d D) : Prop :=
  ∃ _data : AlgebraStructureData d D, M = M

/-- A placeholder compatibility predicate linking the two paper
formulations. -- TODO (#612): replace with the honest derivation from
Theorem IV.13 of arXiv:1606.00608. -/
def FusionAlgebraCompatible (M : MPOTensor d D) : Prop :=
  IsRFP_MPDO_via_fusion M ↔ IsRFP_MPDO_via_algebra M

/-- **Paper headline equivalence (scaffolded):** the fusion-isometry and
algebra-structure formulations of MPDO RFP coincide whenever the two data
satisfy `FusionAlgebraCompatible`. This is the Lean shape of Theorem IV.13
from arXiv:1606.00608.

In the scaffolding regime the hypothesis `h : FusionAlgebraCompatible M` is
definitionally the equivalence itself, so the proof is a direct return of
`h`. Later tickets will remove the hypothesis and supply the genuine proof
via the C*-algebra construction in Appendix C.3 of the paper.

-- TODO (#612): full equivalence requires the vertical canonical form
(Prop. IV.12 / `thm:vertical_cf_of_horizontal_cf`), fixed-point algebra
theory (`Channel/FixedPoint/Algebra.lean`, Wolf Thm 6.14), block injectivity
(Prop. 2.10 in the paper, `propblockinj`), and Newton–Girard
(`Algebra/ScalarPowerSumIdentity.lean`). All ingredients are already
available; the task is to assemble them. -/
theorem rfp_mpdo_fusion_iff_algebra (M : MPOTensor d D)
    (h : FusionAlgebraCompatible M) :
    IsRFP_MPDO_via_fusion M ↔ IsRFP_MPDO_via_algebra M :=
  h

/-- Three-way equivalence (scaffolded) between the provisional transfer-map
RFP, the fusion-isometry RFP, and the algebra-structure RFP, conditioned on
both placeholder compatibility hypotheses.

-- TODO (#612): remove hypotheses once the unconditional equivalences from
Appendix C.3 are formalised. -/
theorem rfp_mpdo_three_way (M : MPOTensor d D)
    (hF : FusionCompatible M) (hA : FusionAlgebraCompatible M) :
    (IsRFP M ↔ IsRFP_MPDO_via_fusion M) ∧
      (IsRFP_MPDO_via_fusion M ↔ IsRFP_MPDO_via_algebra M) :=
  ⟨hF.symm, hA⟩

end MPOTensor
