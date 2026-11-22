/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.DomainInteractionBudget
import TNLean.MPS.AreaLaw.Chain.PartialSwap

/-!
# Regional swaps of doubled finite-domain Hamiltonians

The doubled family is `ManyBody.Interaction.doubledFin`; its sum `K` and the conjugate `F K Fᴴ`
by the regional sheet swap `F` are the actual doubled and swapped operators. The difference of
these operators is the sum of the two replica perturbations over crossing
supports. Each perturbation is supported on its original support, is Hermitian,
and has norm at most twice the interaction bound.

The number of replica perturbations is bounded by a range-dependent constant
times the number of domain sites. This is the coarse count needed for a
localization estimate linear in the domain size.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–363.
-/

open ManyBody (DomainSupport DomainSupport.toChainSupport DomainInteraction)

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {Λ : Finset ℤ} {q R : ℕ} {J : ℝ}

private theorem norm_bound_nonneg_of_support (h : ManyBody.DomainInteraction Λ q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J) (X : DomainSupport Λ R) : 0 ≤ J :=
  h.norm_bound_nonneg hhJ (Classical.choose X.2.1)

/-- Each original domain interaction gives two supported Hermitian perturbations
of norm at most `2J`. Source: TNLean note, part2a_mps_information.tex, 355–363. -/
theorem _root_.ManyBody.DomainInteraction.partialSwap_term_difference_spec
    (h : DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (D : Finset (Fin Λ.card))
    (X : DomainSupport Λ R) (b : Bool) :
    let e := sitePairConfigurationEquiv (Fin Λ.card) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    let T := Matrix.reindex e e
      (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
        else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
    let K := F * T * Fᴴ - T
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin (q * q)) K X.1 ∧ K.IsHermitian ∧ ‖K‖ ≤ 2 * J := by
  have hterm : (h.extend DomainSupport.toChainSupport
      ManyBody.DomainSupport.toChainSupport_injective (fun Y ↦ Y.1)
        fun _ ↦ subset_rfl).term X.toChainSupport = h.term X :=
    ManyBody.DomainSupport.toChainSupport_injective.extend_apply _ _ _
  have hs :=
    ManyBody.ChainInteraction.partialSwap_term_difference_spec
      (h.extend DomainSupport.toChainSupport ManyBody.DomainSupport.toChainSupport_injective
        (fun Y ↦ Y.1) fun _ ↦ subset_rfl)
      (ManyBody.Interaction.isHermitian_extend_term hh)
      (ManyBody.Interaction.norm_extend_term_le (norm_bound_nonneg_of_support h hhJ X) hhJ)
      D X.toChainSupport b
  rw [hterm] at hs
  simpa only [DomainSupport.toChainSupport] using hs

/-- The difference of the actual domain operators is the sum over crossing
supports and both replica labels. Source: TNLean note, part2a_mps_information.tex,
355–363; the count uses the original domain-support injection. -/
theorem _root_.ManyBody.DomainInteraction.partialSwap_difference_eq_sum_crossing
    (h : DomainInteraction Λ q R) (D : Finset (Fin Λ.card)) :
    let e := sitePairConfigurationEquiv (Fin Λ.card) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    let T (X : DomainSupport Λ R) (b : Bool) := Matrix.reindex e e
      (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
        else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
    let C := ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
    (F * h.doubledFin.hamiltonian * Fᴴ - h.doubledFin.hamiltonian =
      ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b)) ∧
      C.card * 2 ≤ chainCrossConst R * Λ.card := by
  classical
  let e := sitePairConfigurationEquiv (Fin Λ.card) q q
  let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
  let T (X : DomainSupport Λ R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
  let C := ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
  let δ : Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ →ₗ[ℂ]
      Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ :=
    LinearMap.mulLeftRight ℂ (F, Fᴴ) - LinearMap.id
  have hcancel (X : DomainSupport Λ R) (hX : X ∉ C) : δ (h.doubledFin.term X) = 0 := by
    have hside : X.1 ⊆ D ∨ Disjoint X.1 D := by
      simp only [C, ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
      simp only [Finset.disjoint_left]
      grind
    change F * Matrix.reindex e e (doubledHamiltonian (h.term X)) * Fᴴ -
      Matrix.reindex e e (doubledHamiltonian (h.term X)) = 0
    apply sub_eq_zero.mpr
    simpa only [F, Matrix.conjTranspose_submatrix, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv] using
      congrArg (Matrix.reindex e e)
        (TNLean.Lattice.sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
          ((h.mem X)) hside)
  refine ⟨?_, card_domain_crossingTerms_mul_two_le Λ R D⟩
  change δ h.doubledFin.hamiltonian = ∑ X ∈ C, ∑ b : Bool, δ (T X b)
  change δ (∑ X, h.doubledFin.term X) = _
  rw [map_sum]
  calc
    _ = ∑ X ∈ C, δ (h.doubledFin.term X) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      exact fun X _ hX ↦ hcancel X hX
    _ = _ := by
      apply Finset.sum_congr rfl
      intro X _
      rw [← map_sum]
      congr 1
      rw [Fintype.sum_bool]
      change Matrix.reindex e e (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X) =
        Matrix.reindex e e (1 ⊗ₖ h.term X) + Matrix.reindex e e (h.term X ⊗ₖ 1)
      simpa only [Matrix.coe_reindexAddEquiv] using
        ((Matrix.reindexAddEquiv ℂ e e).map_add (h.term X ⊗ₖ 1) (1 ⊗ₖ h.term X)).trans
          (add_comm _ _)

end TNLean.MPS.AreaLaw
