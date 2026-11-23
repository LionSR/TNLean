/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.Counting
import TNLean.MPS.AreaLaw.Chain.EntropyInequalities

/-!
# Interaction budgets on finite integer domains

An admissible support in a finite induced integer domain is also an admissible
support in the chain of its increasing labels. Restricting the existing chain
estimates gives the same per-site interaction budget and a crossing count linear
in the number of domain sites. These statements include the empty domain.

Source: TNLean one-dimensional note, `part0_preamble.tex`, eq:ham, lines 191–201,
and `part2a_mps_information.tex`, lines 260–265 and 355–363.
-/

open ManyBody (ChainSupport DomainSupport DomainSupport.toChainSupport
  DomainSupport.toChainSupport_injective IsDomainSupport boundaryEdges DomainInteraction)

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {Λ : Finset ℤ} {q R : ℕ} {J : ℝ}

/-- A single domain site is an admissible support at every range.
Source: TNLean note, part0_preamble.tex, eq:ham, lines 191–201. -/
lemma IsDomainSupport.singleton (x : Fin Λ.card) : IsDomainSupport Λ R {x} := by
  simp [IsDomainSupport]

/-- The interaction bound is nonnegative at every actual domain site.
Source: TNLean note, part0_preamble.tex, eq:ham, lines 191–201. -/
lemma _root_.ManyBody.DomainInteraction.norm_bound_nonneg (h : DomainInteraction Λ q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (x : Fin Λ.card) : 0 ≤ J := by
  exact (norm_nonneg (h.term ⟨{x}, IsDomainSupport.singleton x⟩)).trans (hhJ _)

/-- The original domain interactions satisfy the chain per-site norm budget.
No sign or nonempty-domain hypothesis is added.
Source: TNLean note, part2a_mps_information.tex, lines 260–265. -/
lemma _root_.ManyBody.DomainInteraction.sum_norm_terms_containing_le (h : DomainInteraction Λ q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (x : Fin Λ.card) :
    (∑ X ∈ Finset.univ.filter (fun X : DomainSupport Λ R ↦ x ∈ X.1),
      ‖h.term X‖) ≤ ((2 ^ (2 * R + 1) : ℕ) : ℝ) * J := by
  let hc : ManyBody.ChainInteraction Λ.card q R :=
    h.extend DomainSupport.toChainSupport DomainSupport.toChainSupport_injective (fun Y ↦ Y.1)
      fun _ ↦ subset_rfl
  refine (Finset.sum_le_sum_of_injOn
    (g := fun Y : ChainSupport Λ.card R ↦ ‖hc.term Y‖)
    DomainSupport.toChainSupport DomainSupport.toChainSupport_injective.injOn
    ?_ ?_ (fun _ _ _ ↦ norm_nonneg _)).trans
      (hc.sum_norm_terms_containing_le
        (ManyBody.Interaction.norm_extend_term_le (h.norm_bound_nonneg hhJ x) hhJ) x)
  · exact fun Y hY ↦ (Finset.mem_image.mp hY).elim fun X hX ↦
      hX.2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX.1).2⟩
  · exact fun X _ ↦
      le_of_eq (congrArg norm (ManyBody.Interaction.extend_term_apply (Φ := h) X).symm)

/-- The original domain crossing supports inject into the chain crossing supports.
The chain boundary is used only as an upper counting bound.
Source: TNLean note, part1_arealaw.tex, eq:count, and
part2a_mps_information.tex, lines 355–363. -/
lemma card_domain_crossingTerms_le_mul_card_boundaryEdges (Λ : Finset ℤ) (R : ℕ)
    (D : Finset (Fin Λ.card)) :
    (ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D).card ≤
      2 ^ (2 * R) * (boundaryEdges Λ.card D).card := by
  refine (Finset.card_le_card_of_injOn
    DomainSupport.toChainSupport ?_
    DomainSupport.toChainSupport_injective.injOn).trans
      (card_crossingTerms_le_mul_card_boundaryEdges Λ.card R D)
  exact fun X hX ↦ by
    simpa only [ManyBody.crossingTerms, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, DomainSupport.toChainSupport] using hX

/-- Counting both replicas of the actual crossing supports gives a bound linear
in the number of domain sites, with the same range constant as on a chain.
Source: TNLean note, part2a_mps_information.tex, lines 355–363. -/
lemma card_domain_crossingTerms_mul_two_le (Λ : Finset ℤ) (R : ℕ)
    (D : Finset (Fin Λ.card)) :
    (ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D).card * 2 ≤
      chainCrossConst R * Λ.card := by
  have hb : (boundaryEdges Λ.card D).card ≤ Λ.card :=
    (Finset.card_le_card fun p hp ↦ Finset.mem_range.mpr
      (by have := (ManyBody.mem_boundaryEdges.mp hp).1; omega)).trans (Finset.card_range _).le
  simpa only [chainCrossConst, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_le_mul_right 2
      ((card_domain_crossingTerms_le_mul_card_boundaryEdges Λ R D).trans
        (Nat.mul_le_mul_left (2 ^ (2 * R)) hb))

end TNLean.MPS.AreaLaw
