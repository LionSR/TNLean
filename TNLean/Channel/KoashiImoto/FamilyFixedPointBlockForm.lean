/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.TraceAdjointDensityBlocks
import TNLean.Channel.KoashiImoto.MeanErgodicProjection

/-!
# A simultaneous fixed-point block form for a preserved family of states

The single preserving channel `F₀` constructed from a finite family of states fixes every
member of that family.  The full-support density-block classification of its Schrödinger
fixed points therefore gives one simultaneous direct-sum tensor form for all family members.
The density matrix on the multiplicity factor is independent of the family member.

This is the algebraic fixed-point statement underlying the projection classification in HJPW,
arXiv:quant-ph/0304007v2, Appendix A, lines 853--856.  It stops before deriving positivity
and normalizing the member-dependent matrix blocks into the probabilities and density
matrices of Property 1 (lines 785--789); those steps begin at lines 857--858.

## Main declaration

* `Kraus.exists_commonInvariant_fixedPointBlockForm`: every state preserved by the common
  witness `F₀` has the same density factors in one direct-sum tensor decomposition.

**Scope restriction (full support):** The common average is assumed positive definite on the
ambient space, in place of HJPW's reduction to the joint support (lines 761--763).  This is
documented in `docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker
open Matrix

namespace Kraus

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Simultaneous density-block form of a full-support invariant family.**

For the single channel `F₀` preserving every `ρ x`, its Schrödinger fixed-point space has
the form
\[
  U\left(\bigoplus_j \sigma_j\otimes M_{d_j}(\mathbb C)\right)U^*.
\]
Consequently every family member has one such block form, with the density matrices
`σ j` independent of `x`.  This is the fixed-point step used in HJPW,
arXiv:quant-ph/0304007v2, Appendix A, lines 853--856.

No positivity or trace normalization is asserted for the matrices `X j`.  Thus the theorem
does not claim the probability-density decomposition of HJPW Property 1 (lines 785--789);
that normalization begins at lines 857--858.

**Scope restriction (full support):** `hρbar` replaces HJPW's joint-support reduction
(lines 761--763).  Documented in
`docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex`. -/
theorem exists_commonInvariant_fixedPointBlockForm
    {Kidx : Type*} [Fintype Kidx] [Nonempty Kidx] {ρ : Kidx → Mat}
    (hρbar : (commonAverage ρ).PosDef) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin D)
      (U : Mat) (σ : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ j, 0 < d j) ∧ (∀ j, 0 < m j) ∧
        (∀ j, (σ j).PosSemidef) ∧ (∀ j, (σ j).trace = 1) ∧
        ∀ x, ∃ X : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ,
          star U * ρ x * U =
            Matrix.reindex e e (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ X j) := by
  have hSchwarz :
      IsSchwarzMap (Matrix.traceAdjointMap (commonInvariantMapLM hρbar)) := by
    exact isSchwarzMap_traceAdjointMap_mapLM_of_isTP _
      (commonInvariantKrausFamily hρbar).isPreserving.1
  have hρbarFix : commonInvariantMapLM hρbar (commonAverage ρ) = commonAverage ρ := by
    exact (commonInvariantKrausFamily hρbar).map_commonAverage
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, hσpos, hσtrace, -, hfixed⟩ :=
    (isPositiveMap_commonInvariantMapLM hρbar).exists_block_densities_of_meanErgodicProjection
      (isTracePreservingMap_commonInvariantMapLM hρbar) hSchwarz hρbar hρbarFix
  refine ⟨K, d, m, e, U, σ, hU, hd, hm, hσpos, hσtrace, ?_⟩
  intro x
  apply (hfixed (ρ x)).1
  simpa only [commonInvariantMapLM, mapLM_apply] using
    (commonInvariantKrausFamily hρbar).isPreserving.2 x

end Kraus
