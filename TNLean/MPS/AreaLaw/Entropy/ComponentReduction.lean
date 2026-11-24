/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Entropy.AreaLaw
import QICLean.ManyBody.Entropy.ChainInterval
import QICLean.ManyBody.Sites.Lattice.Line
import Mathlib.Combinatorics.SimpleGraph.Metric
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# The one-dimensional area law on a finite set of integers

Theorem A of the one-dimensional note is stated for every finite set `Λ ⊂ ℤ` with its
induced path graph, whose edges join consecutive integers that both lie in `Λ`. This module
states the model on such a domain and reduces Theorem A to the chain of `|Λ|` sites.

The sites of `Λ` are labelled `0, …, |Λ| - 1` in increasing order (`sitePos`). A support of
range `R` is a nonempty set of sites of diameter at most `R` in the graph distance of the
induced path graph; such a support never contains two sites on opposite sides of a gap of
`Λ`, and its labels span at most `R + 1` consecutive values, so it is also a support of range
`R` of the chain of `|Λ|` sites. An admissible Hamiltonian on `Λ` is therefore a finite-range
Hamiltonian on that chain, with zero terms on the chain supports that straddle a gap.

The chain bound counts the chain edges at the gaps of `Λ`, which are not edges of `Λ`. The
reduction removes them. At a gap no term crosses, so the gapped ground vector has zero
entropy on the prefix of the chain ending at the gap: in cut coordinates the Hamiltonian is
`H₁ ⊗ 1 + 1 ⊗ H₂`, whose gapped ground vector is a product vector. On a region `P` of zero
entropy, the Araki–Lieb inequality and strong subadditivity give `S(A ∆ P) = S(A)` for every
region `A`, and flipping a prefix toggles exactly one boundary edge of the chain. Flipping
the prefixes at the gaps where the region changes leaves a region of the same entropy whose
boundary edges on the chain are the edges of `∂_Λ A`.

This replaces the factorization of the note, under which the ground vector is a product of
component ground vectors and entropy and edge boundary add over components, by the vanishing
entropy of unions of components; only the two-factor product lemma is used.

## Main definitions

An interaction on `Λ`, one term for each support of range `R` in the sense of
`ManyBody.IsDomainSupport`, is an interaction on the chain by its extension
`ManyBody.Interaction.extend` along the injection `ManyBody.DomainSupport.toChainSupport`.

* `ManyBody.domainBoundaryEdges` and `ManyBody.domainRegion` give the boundary `∂_Λ A`
  and the sites in `A`.

## Main results

The zero entropy of a cut that splits no term and the flips of regions of zero entropy are the
site-generic lemmas `ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint` and
`ManyBody.regionEntropy_symmDiff_eq_of_eq_zero`.

* `regionEntropy_le_mul_card_domainBoundaryEdges`: Theorem A on `Λ` with the constant
  `C_int(q, R, J, Δ)`.
* `domainAreaLaw`: Theorem A with the constant `C₀(q, R) (1 + J/Δ)`.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), `part0_preamble.tex`, the setting and
  Theorem A (`thm:A`), and `part1_arealaw.tex`, Section 2 (`sec:setting`), first reduction.
-/

open ManyBody (ChainSupport DomainSupport DomainSupport.toChainSupport
  DomainSupport.toChainSupport_injective IsChainSupport IsDomainSupport boundaryEdges
  exists_sitePos_eq interval mem_boundaryEdges mem_interval sitePos sitePos_mem
  val_eq_add_one_of_sitePos_eq_add_one DomainInteraction)

open Matrix
open scoped ComplexOrder Kronecker symmDiff Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-! ### Theorem A on a finite set of integers -/

section TheoremA

variable {Λ : Finset ℤ} {q R : ℕ} {J Δ : ℝ}

/-- Removing boundary cuts across gaps preserves entropy and leaves the actual domain boundary.
Source: the one-dimensional note, part1_arealaw.tex, lines 64–93. -/
theorem _root_.ManyBody.DomainInteraction.exists_regionEntropy_eq_card_boundaryEdges_eq
    {Λ : Finset ℤ} {q R : ℕ} {E₀ Δ : ℝ}
    (h : DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
    {Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)}
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (A : Finset ℤ) :
    ∃ A' : Finset (Fin Λ.card),
      ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω A' =
        ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (ManyBody.domainRegion Λ A) ∧
      (boundaryEdges Λ.card A').card = (ManyBody.domainBoundaryEdges Λ A).card := by
  classical
  set G := (boundaryEdges Λ.card (ManyBody.domainRegion Λ A)).filter
    fun p ↦ ¬ ManyBody.IsDomainEdge Λ p
  have hG : ∀ p ∈ G, p + 1 < Λ.card ∧ ManyBody.regionEntropy (X := fun _ ↦ Fin q)
      Ω (interval Λ.card 0 (p + 1)) = 0 := by
    intro p hp
    obtain ⟨hpb, hpe⟩ := Finset.mem_filter.mp hp
    have hp1 := (mem_boundaryEdges.mp hpb).1
    refine ⟨hp1,
      ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint (Φ := h) hh hΔ hΩ hgap
        hspan (B := interval Λ.card 0 (p + 1)) fun X ↦ ?_⟩
    exact X.2.subset_or_disjoint_of_gap hp1 fun he ↦ hpe ⟨hp1, he⟩
  obtain ⟨A', hS, hB⟩ :=
    ManyBody.exists_regionEntropy_eq_boundaryEdges_eq_symmDiff hΩ G hG (ManyBody.domainRegion Λ A)
  have hsymm : boundaryEdges Λ.card (ManyBody.domainRegion Λ A) ∆ G =
      (boundaryEdges Λ.card (ManyBody.domainRegion Λ A)).filter (ManyBody.IsDomainEdge Λ) := by
    ext p
    simp only [G, Finset.mem_symmDiff, Finset.mem_filter]
    tauto
  exact ⟨A', hS, by rw [hB, hsymm, ManyBody.card_domainBoundaryEdges]⟩

/-- **Theorem A on a finite set of integers.** For a gapped ground vector `Ω` of an
admissible Hamiltonian on a finite set `Λ ⊂ ℤ`, the entropy of the sites in every `A ⊆ ℤ` is
at most `C_int(q, R, J, Δ)` times the number of edges of `∂_Λ A`.

The proof is the component reduction of the note. At an edge of the chain of `|Λ|` sites
that joins sites at nonconsecutive integers no support crosses, so the prefix ending there
has zero entropy (`ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint`), and
flipping the region on that prefix changes neither its entropy nor any boundary edge but that
one. After the flips at the boundary edges of this kind, the region has exactly `|∂_Λ A|`
boundary edges on the chain, and the chain bound `regionEntropy_le_mul_card_boundaryEdges` applies.
TNLean note, `part0_preamble.tex`, Theorem A (`thm:A`), and `part1_arealaw.tex`, Section 2
(`sec:setting`), first reduction. -/
theorem regionEntropy_le_mul_card_domainBoundaryEdges (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset ℤ) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (ManyBody.domainRegion Λ A) ≤
      chainIntervalEntropyBound q R J Δ * (ManyBody.domainBoundaryEdges Λ A).card := by
  obtain ⟨A', hS, hB⟩ := h.exists_regionEntropy_eq_card_boundaryEdges_eq hh hΔ hΩ hgap hspan A
  let hc : ManyBody.ChainInteraction Λ.card q R :=
    h.extend DomainSupport.toChainSupport DomainSupport.toChainSupport_injective (fun Y ↦ Y.1)
      fun _ ↦ subset_rfl
  have hext : hc.hamiltonian = h.hamiltonian := ManyBody.Interaction.hamiltonian_extend
  rw [← hext] at hgap hspan
  have hchain := regionEntropy_le_mul_card_boundaryEdges hq hJ hΔ hc
      (ManyBody.Interaction.isHermitian_extend_term hh)
      (ManyBody.Interaction.norm_extend_term_le hJ hhJ) hΩ hgap hspan A'
  simpa only [hS, hB] using hchain

/-- **The one-dimensional area law** (Theorem A). For every local dimension `q ≥ 1`, range
`R`, term norm `J ≥ 0` and gap `Δ > 0` there is a constant, namely `C₀(q, R) (1 + J/Δ)`, such
that for every finite set `Λ ⊂ ℤ`, every admissible Hamiltonian on `Λ`, every gapped ground
vector `Ω` and every `A ⊆ ℤ`, the sites of `Λ` in `A` satisfy `S_Ω(A) ≤ C |∂_Λ A|`.
TNLean note, `part0_preamble.tex`, Theorem A (`thm:A`). -/
theorem domainAreaLaw (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C = chainAreaLawConst q R * (1 + J / Δ) ∧
      ∀ Λ : Finset ℤ, ∀ h : DomainInteraction Λ q R, (∀ X, (h.term X).IsHermitian) →
          (∀ X, ‖h.term X‖ ≤ J) → ∀ E₀ : ℝ,
        ∀ Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q),
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} → ∀ A : Finset ℤ,
            ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (ManyBody.domainRegion Λ A) ≤
              C * (ManyBody.domainBoundaryEdges Λ A).card := by
  have hle := chainIntervalEntropyBound_le (q := q) (R := R) hq hJ hΔ
  have h0 := chainIntervalEntropyBound_nonneg (q := q) (R := R) hq hJ hΔ
  refine ⟨chainAreaLawConst q R * (1 + J / Δ), h0.trans hle, rfl, ?_⟩
  intro Λ h hh hhJ E₀ Ω hΩ hgap hspan A
  refine (regionEntropy_le_mul_card_domainBoundaryEdges hq hJ hΔ h hh hhJ hΩ hgap hspan A).trans ?_
  exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)

end TheoremA

end TNLean.MPS.AreaLaw
