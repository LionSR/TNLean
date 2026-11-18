/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainInteractionBudget
import TNLean.MPS.AreaLaw.SwappedDoubledHamiltonian
import TNLean.MPS.AreaLaw.PartialSwap

/-!
# Regional swaps of doubled finite-domain Hamiltonians

The doubled and regionally swapped families retain the original domain supports.
Their sums are the actual doubled and conjugated operators. The difference of
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

/-- Two replicas of the original domain interactions, paired at each actual site.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–360. This definition
preserves the actual domain supports and asserts no ground-state or reset conclusion. -/
noncomputable def _root_.ManyBody.DomainInteraction.doubled (h : ManyBody.DomainInteraction Λ q R) :
    ManyBody.DomainInteraction Λ (q * q) R where
  term X := Matrix.reindex (sitePairConfigurationEquiv (Fin Λ.card) q q)
    (sitePairConfigurationEquiv (Fin Λ.card) q q)
      (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)
  mem X := by
    have hs := h.toChain.doubled.mem X.toChainSupport
    simp only [ManyBody.ChainInteraction.doubled, ManyBody.DomainInteraction.toChain_term] at hs
    simpa only [DomainSupport.toChainSupport] using hs

/-- The paired domain terms of Hermitian terms are Hermitian.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.DomainInteraction.isHermitian_doubled_term
    (h : ManyBody.DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
    (X : DomainSupport Λ R) : (h.doubled.term X).IsHermitian := by
  simpa only [ManyBody.DomainInteraction.doubled, ManyBody.ChainInteraction.doubled,
    ManyBody.DomainInteraction.toChain_term] using
    h.toChain.isHermitian_doubled_term (h.isHermitian_toChain_term hh) X.toChainSupport

/-- Each paired domain term has norm at most `2 * J`.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.DomainInteraction.norm_doubled_term_le
    (h : ManyBody.DomainInteraction Λ q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (X : DomainSupport Λ R) : ‖h.doubled.term X‖ ≤ 2 * J := by
  simpa only [ManyBody.DomainInteraction.doubled, ManyBody.ChainInteraction.doubled,
    ManyBody.DomainInteraction.toChain_term] using
    h.toChain.norm_doubled_term_le
      (h.norm_toChain_term_le hhJ (norm_bound_nonneg_of_support h hhJ X)) X.toChainSupport

/-- Summing the original doubled terms gives exactly the paired two-copy operator.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–360. -/
lemma _root_.ManyBody.DomainInteraction.doubled_hamiltonian (h : DomainInteraction Λ q R) :
    h.doubled.hamiltonian = Matrix.reindex (sitePairConfigurationEquiv (Fin Λ.card) q q)
      (sitePairConfigurationEquiv (Fin Λ.card) q q)
      (h.hamiltonian ⊗ₖ 1 + 1 ⊗ₖ h.hamiltonian) := by
  ext σ τ
  simp only [ManyBody.Interaction.hamiltonian, ManyBody.DomainInteraction.doubled, Matrix.sum_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.kroneckerMap_apply, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

/-- Conjugate each original doubled domain interaction by the actual regional swap.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
noncomputable def _root_.ManyBody.DomainInteraction.swappedDoubled
    (h : ManyBody.DomainInteraction Λ q R) (D : Finset (Fin Λ.card)) :
    ManyBody.DomainInteraction Λ (q * q) R where
  term X :=
    let e := sitePairConfigurationEquiv (Fin Λ.card) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    F * h.doubled.term X * Fᴴ
  mem X := by
    exact isSupportedOn_of_mem_supportedOperators
      (TNLean.Lattice.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators
        D X.1 (mem_supportedOperators_of_isSupportedOn (h.mem X)))

/-- The swapped doubled domain terms of Hermitian terms are Hermitian.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.DomainInteraction.isHermitian_swappedDoubled_term
    (h : ManyBody.DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
    (D : Finset (Fin Λ.card)) (X : DomainSupport Λ R) :
    ((h.swappedDoubled D).term X).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ (h.isHermitian_doubled_term hh X)

/-- Each swapped doubled domain term has norm at most `2 * J`.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.DomainInteraction.norm_swappedDoubled_term_le
    (h : ManyBody.DomainInteraction Λ q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin Λ.card)) (X : DomainSupport Λ R) :
    ‖(h.swappedDoubled D).term X‖ ≤ 2 * J := by
  simpa only [ManyBody.DomainInteraction.swappedDoubled, ManyBody.ChainInteraction.swappedDoubled,
    ManyBody.ChainInteraction.doubled, ManyBody.DomainInteraction.toChain_term,
    ManyBody.DomainInteraction.doubled] using
    (h.toChain.norm_swappedDoubled_term_le
      (h.norm_toChain_term_le hhJ (norm_bound_nonneg_of_support h hhJ X)) D X.toChainSupport)

/-- The sum of the original swapped interactions is the conjugated doubled operator.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
lemma _root_.ManyBody.DomainInteraction.swappedDoubled_hamiltonian
    (h : DomainInteraction Λ q R) (D : Finset (Fin Λ.card)) :
    let e := sitePairConfigurationEquiv (Fin Λ.card) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    (h.swappedDoubled D).hamiltonian = F * h.doubled.hamiltonian * Fᴴ := by
  simp only [ManyBody.Interaction.hamiltonian, ManyBody.DomainInteraction.swappedDoubled,
    Matrix.sum_mul, Matrix.mul_sum]

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
    Entropy.IsSupportedOn (n := fun _ ↦ q * q) K X.1 ∧ K.IsHermitian ∧ ‖K‖ ≤ 2 * J := by
  have hs :=
    (h.toChain).partialSwap_term_difference_spec (h.isHermitian_toChain_term hh)
        (h.norm_toChain_term_le hhJ (norm_bound_nonneg_of_support h hhJ X))
      D X.toChainSupport b
  simp only [ManyBody.DomainInteraction.toChain_term] at hs
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
    let C := Entropy.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
    ((h.swappedDoubled D).hamiltonian - h.doubled.hamiltonian =
      ∑ X ∈ C, ∑ b : Bool, (F * T X b * Fᴴ - T X b)) ∧
      C.card * 2 ≤ chainCrossConst R * Λ.card := by
  classical
  let e := sitePairConfigurationEquiv (Fin Λ.card) q q
  let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
  let T (X : DomainSupport Λ R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
  let C := Entropy.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
  let δ : Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ →ₗ[ℂ]
      Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ :=
    LinearMap.mulLeftRight ℂ (F, Fᴴ) - LinearMap.id
  have hcancel (X : DomainSupport Λ R) (hX : X ∉ C) : δ (h.doubled.term X) = 0 := by
    have hside : (X.1 : Set (Fin Λ.card)) ⊆ (D : Set (Fin Λ.card)) ∨
        Disjoint (X.1 : Set (Fin Λ.card)) (D : Set (Fin Λ.card)) := by
      simp only [C, Entropy.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
      simp only [Finset.coe_subset, Finset.disjoint_coe, Finset.disjoint_left]
      grind
    change F * Matrix.reindex e e (doubledHamiltonian (h.term X)) * Fᴴ -
      Matrix.reindex e e (doubledHamiltonian (h.term X)) = 0
    apply sub_eq_zero.mpr
    simpa only [F, Matrix.conjTranspose_submatrix, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv] using
      congrArg (Matrix.reindex e e)
        (TNLean.Lattice.sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
          (mem_supportedOperators_of_isSupportedOn (h.mem X)) hside)
  refine ⟨?_, card_domain_crossingTerms_mul_two_le Λ R D⟩
  rw [h.swappedDoubled_hamiltonian D]
  change δ h.doubled.hamiltonian = ∑ X ∈ C, ∑ b : Bool, δ (T X b)
  change δ (∑ X, h.doubled.term X) = _
  rw [map_sum]
  calc
    _ = ∑ X ∈ C, δ (h.doubled.term X) := by
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
