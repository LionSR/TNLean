/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KoashiImoto.FiniteRealization
import TNLean.Channel.KoashiImoto.PooledKrausFamily

/-!
# A single preserving Kraus family realizing the common invariant algebra

HJPW, arXiv:quant-ph/0304007v2, lines 846-849: "in fact there is `F_0 ∈ F` such that
`A_0 = A_{F_0}`. We may take, for example, `F_0 = (1/M) ∑_μ F_μ`." This file combines the
finite realization of `A_0` (`Kraus.exists_finset_preservingKrausFamily_iInf_eq`) with the
pooled/averaged Kraus family of a finite indexed family
(`Kraus.averagedPreservingKrausFamily`, `Kraus.adjointFixedPointsStarSubalgebra_pooledKfam_eq_iInf`)
to produce that single witness `F_0`.

## Main declarations

* `Kraus.exists_preservingKrausFamily_adjointFixedPointsStarSubalgebra_eq`: there is a single
  preserving Kraus family `F_0` whose adjoint fixed-point subalgebra is exactly the common
  invariant algebra `A_0` (HJPW, arXiv:quant-ph/0304007v2, lines 846-847).

The declarations below state the finite state-family instances in their own signatures. This keeps
dependent projections through `averagedPreservingKrausFamily` stable during elaboration. The
projection lemmas `Kraus.averagedPreservingKrausFamily_Kfam` and
`Kraus.averagedPreservingKrausFamily_isTP` expose the corresponding fields without unfolding the
bundled family.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A finite nonempty `Finset` gives the same infimum whether taken over the `Finset`-bounded
quantifier or over its enumeration by `Fin S.card`. Stated for a fully generic, opaque `A` so
that this purely order-theoretic reindexing step never has to unfold `PreservingKrausFamily` or
`IsPreserving` during unification. -/
private theorem iInf_enum_eq {ι : Type*} {α : Type*} [CompleteLattice α]
    (A : ι → α) (S : Finset ι) :
    ⨅ k : Fin S.card, A (S.equivFin.symm k : ι) = ⨅ F ∈ S, A F := by
  have h1 := Equiv.iInf_comp (g := fun y : { x // x ∈ S } => A (y : ι)) S.equivFin.symm
  rw [h1]
  exact iInf_subtype'' (S : Set ι) A

/-- The pooled/averaged witness of an arbitrary enumerated finite family realizes the
intersection of the adjoint fixed-point subalgebras of that family. Stated for a fully generic,
opaque `Fenum` (a bound parameter, not a `let`) so that this is a single beta-reduction away
from `Kraus.adjointFixedPointsStarSubalgebra_pooledKfam_eq_iInf`, without forcing unification to
unfold `Fenum` itself. -/
private theorem adjointFixedPointsStarSubalgebra_averaged_eq_iInf
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    {M : ℕ} [NeZero M]
    (Fenum : Fin M → PreservingKrausFamily ρ) (hρbar : (commonAverage ρ).PosDef) :
    adjointFixedPointsStarSubalgebra (averagedPreservingKrausFamily Fenum).Kfam
        (averagedPreservingKrausFamily Fenum).isPreserving.1 hρbar
        (averagedPreservingKrausFamily Fenum).map_commonAverage
      = ⨅ μ, adjointFixedPointsStarSubalgebra (Fenum μ).Kfam (Fenum μ).isPreserving.1 hρbar
          (Fenum μ).map_commonAverage := by
  simp only [averagedPreservingKrausFamily_Kfam]
  exact adjointFixedPointsStarSubalgebra_pooledKfam_eq_iInf (fun μ => (Fenum μ).Kfam)
    (fun μ => (Fenum μ).isPreserving.1) hρbar (fun μ => (Fenum μ).map_commonAverage)

/-- **A single preserving Kraus family realizes the common invariant algebra.**

HJPW, arXiv:quant-ph/0304007v2, lines 846-849: "there is `F_0 ∈ F` such that `A_0 = A_{F_0}`.
We may take, for example, `F_0 = (1/M) ∑_μ F_μ`." Combines the finite realization of `A_0`
(`Kraus.exists_finset_preservingKrausFamily_iInf_eq`) with the pooled/averaged Kraus family of
that finite family (`Kraus.averagedPreservingKrausFamily`).

**Scope restriction (joint support):** inherits the `PosDef (commonAverage ρ)` hypothesis of
`commonInvariantStarSubalgebra` in place of HJPW's joint-support reduction
(arXiv:quant-ph/0304007v2, lines 761-763). Documented in
`docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex`. -/
theorem exists_preservingKrausFamily_adjointFixedPointsStarSubalgebra_eq
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) :
    ∃ F₀ : PreservingKrausFamily ρ,
      adjointFixedPointsStarSubalgebra F₀.Kfam F₀.isPreserving.1 hρbar F₀.map_commonAverage
        = commonInvariantStarSubalgebra ρ hρbar := by
  obtain ⟨S, hS, hSeq⟩ := exists_finset_preservingKrausFamily_iInf_eq ρ hρbar
  haveI : NeZero S.card := ⟨hS.card_pos.ne'⟩
  refine ⟨averagedPreservingKrausFamily (fun k => (S.equivFin.symm k : PreservingKrausFamily ρ)),
    ?_⟩
  rw [adjointFixedPointsStarSubalgebra_averaged_eq_iInf]
  rw [iInf_enum_eq
    (fun F => adjointFixedPointsStarSubalgebra F.Kfam F.isPreserving.1 hρbar F.map_commonAverage)
    S]
  exact hSeq

end Kraus
