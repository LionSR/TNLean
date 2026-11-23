/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Entropy.AreaLaw
import QICLean.ManyBody.Entropy.ZeroEntropy
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

* `domainBoundaryEdges`, `domainRegion`: the edge boundary `∂_Λ A` and the sites in `A`.

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
  DomainSupport.toChainSupport_injective IsChainSupport IsDomainSupport exists_sitePos_eq interval
  mem_interval sitePos sitePos_mem val_eq_add_one_of_sitePos_eq_add_one DomainInteraction)

open Matrix
open scoped ComplexOrder Kronecker symmDiff Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

section Toggle

variable {L : ℕ}

/-- Position membership in a region of the chain, for an in-range position. -/
theorem exists_mem_val_eq_iff {A : Finset (Fin L)} {r : ℕ} (hr : r < L) :
    (∃ i ∈ A, i.val = r) ↔ (⟨r, hr⟩ : Fin L) ∈ A := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro h
    exact ⟨_, h, rfl⟩

/-- **Flipping a prefix toggles one boundary edge.** Replacing the region `A` by its
symmetric difference with the prefix `[0, p + 1)` of the chain changes its set of boundary
edges exactly at the edge `p`. -/
theorem boundaryEdges_symmDiff_interval {A : Finset (Fin L)} {p : ℕ} (hp : p + 1 < L) :
    boundaryEdges L (A ∆ interval L 0 (p + 1)) = boundaryEdges L A ∆ {p} := by
  ext r
  rw [Finset.mem_symmDiff, mem_boundaryEdges, mem_boundaryEdges, Finset.mem_singleton]
  by_cases hr : r + 1 < L
  · rw [exists_mem_val_eq_iff (by omega), exists_mem_val_eq_iff hr,
      exists_mem_val_eq_iff (A := A) (by omega), exists_mem_val_eq_iff (A := A) hr]
    simp only [Finset.mem_symmDiff, mem_interval]
    rcases lt_trichotomy r p with h | h | h
    · have h1 : r < p + 1 := by omega
      have h2 : r + 1 < p + 1 := by omega
      simp only [zero_le, true_and, h1, h2, not_true_eq_false, and_false, false_or, hr,
        h.ne, not_false_eq_true]
      tauto
    · subst h
      simp only [zero_le, true_and, lt_add_iff_pos_right, Nat.lt_irrefl, not_true_eq_false,
        and_false, hr, not_false_eq_true, and_true, Nat.lt_add_one]
      tauto
    · have h1 : ¬ r < p + 1 := by omega
      have h2 : ¬ r + 1 < p + 1 := by omega
      simp only [zero_le, true_and, h1, h2, not_false_eq_true, and_true, or_false, hr,
        h.ne', false_and]
  · have : r ≠ p := by omega
    simp [hr, this]

end Toggle

section FlipInduction

variable {L q : ℕ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}

/-- **Flipping prefixes of zero entropy.** If every prefix `[0, p + 1)` with `p ∈ G` is an
inner edge cut of zero entropy, then every region `A` has a region `A'` of the same entropy
whose boundary edges are those of `A` toggled exactly at the edges of `G`. -/
theorem exists_regionEntropy_eq_boundaryEdges_eq_symmDiff (hΩ : ‖Ω‖ = 1) (G : Finset ℕ)
    (hG : ∀ p ∈ G, p + 1 < L ∧
      ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (interval L 0 (p + 1)) = 0)
    (A : Finset (Fin L)) :
    ∃ A' : Finset (Fin L), ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω A' =
        ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω A ∧
      boundaryEdges L A' = boundaryEdges L A ∆ G := by
  induction G using Finset.induction_on with
  | empty => exact ⟨A, rfl, by ext; simp [Finset.mem_symmDiff]⟩
  | insert p G hp ih =>
    obtain ⟨A₁, h1, h2⟩ := ih fun r hr ↦ hG r (Finset.mem_insert_of_mem hr)
    obtain ⟨hp1, hP⟩ := hG p (Finset.mem_insert_self p G)
    refine ⟨A₁ ∆ interval L 0 (p + 1),
      by rw [ManyBody.regionEntropy_symmDiff_eq_of_eq_zero _ hΩ hP, h1], ?_⟩
    rw [boundaryEdges_symmDiff_interval hp1, h2, symmDiff_assoc]
    congr 1
    ext r
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    by_cases hr : r = p
    · subst hr
      simp [hp]
    · simp [hr]

end FlipInduction

/-! ### Finite domains of the integers -/

section Domain

variable {Λ : Finset ℤ} {q R : ℕ} {J : ℝ}

/-- The edge boundary `∂_Λ A`: the edges `{x, x + 1} ⊆ Λ` with exactly one end in `A`, each
recorded by its left end `x`. TNLean note, `part0_preamble.tex`, the setting. -/
def domainBoundaryEdges (Λ A : Finset ℤ) : Finset ℤ :=
  Λ.filter fun x ↦ x + 1 ∈ Λ ∧ ¬ (x ∈ A ↔ x + 1 ∈ A)

/-- The sites of `Λ` whose positions lie in `A`. -/
noncomputable def domainRegion (Λ A : Finset ℤ) : Finset (Fin Λ.card) :=
  Finset.univ.filter fun i ↦ sitePos Λ i ∈ A

/-- The edge `p` of the chain of `|Λ|` sites joins sites at consecutive integers. -/
def IsDomainEdge (Λ : Finset ℤ) (p : ℕ) : Prop :=
  ∃ hp : p + 1 < Λ.card, sitePos Λ ⟨p + 1, hp⟩ = sitePos Λ ⟨p, by omega⟩ + 1

/-- The boundary edges of `A` in `Λ` correspond to the boundary edges of its sites on the
chain of `|Λ|` sites that join sites at consecutive integers. -/
theorem card_domainBoundaryEdges [DecidablePred (IsDomainEdge Λ)] (A : Finset ℤ) :
    ((boundaryEdges Λ.card (domainRegion Λ A)).filter (IsDomainEdge Λ)).card =
      (domainBoundaryEdges Λ A).card := by
  have hmem : ∀ {r : ℕ} (hr : r < Λ.card),
      (∃ i ∈ domainRegion Λ A, i.val = r) ↔ sitePos Λ ⟨r, hr⟩ ∈ A := fun hr ↦ by
    rw [exists_mem_val_eq_iff hr, domainRegion, Finset.mem_filter]
    simp
  refine Finset.card_bij (fun p hp ↦ sitePos Λ ⟨p, ?_⟩) ?_ ?_ ?_
  · have := (mem_boundaryEdges.mp (Finset.mem_filter.mp hp).1).1
    omega
  · intro p hp
    obtain ⟨hpb, hp1, hcons⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpL, hpA⟩ := mem_boundaryEdges.mp hpb
    rw [hmem (by omega), hmem hpL, hcons] at hpA
    rw [domainBoundaryEdges, Finset.mem_filter]
    refine ⟨sitePos_mem _, ?_, hpA⟩
    rw [← hcons]
    exact sitePos_mem _
  · intro p hp p' hp' h
    have := (sitePos Λ).injective h
    simpa using this
  · intro x hx
    rw [domainBoundaryEdges, Finset.mem_filter] at hx
    obtain ⟨hxΛ, hx1, hxA⟩ := hx
    obtain ⟨i, rfl⟩ := exists_sitePos_eq hxΛ
    obtain ⟨j, hj⟩ := exists_sitePos_eq hx1
    have hji := val_eq_add_one_of_sitePos_eq_add_one hj
    have hpL : i.val + 1 < Λ.card := hji ▸ j.2
    have hjeq : j = ⟨i.val + 1, hpL⟩ := Fin.ext hji
    subst hjeq
    refine ⟨i.val, Finset.mem_filter.mpr ⟨mem_boundaryEdges.mpr ⟨hpL, ?_⟩, hpL, hj⟩, rfl⟩
    rw [hmem (by omega), hmem hpL, hj]
    exact hxA

end Domain

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
        ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (domainRegion Λ A) ∧
      (boundaryEdges Λ.card A').card = (domainBoundaryEdges Λ A).card := by
  classical
  set G := (boundaryEdges Λ.card (domainRegion Λ A)).filter fun p ↦ ¬ IsDomainEdge Λ p
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
    exists_regionEntropy_eq_boundaryEdges_eq_symmDiff hΩ G hG (domainRegion Λ A)
  have hsymm : boundaryEdges Λ.card (domainRegion Λ A) ∆ G =
      (boundaryEdges Λ.card (domainRegion Λ A)).filter (IsDomainEdge Λ) := by
    ext p
    simp only [G, Finset.mem_symmDiff, Finset.mem_filter]
    tauto
  exact ⟨A', hS, by rw [hB, hsymm, card_domainBoundaryEdges]⟩

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
    ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (domainRegion Λ A) ≤
      chainIntervalEntropyBound q R J Δ * (domainBoundaryEdges Λ A).card := by
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
            ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (domainRegion Λ A) ≤
              C * (domainBoundaryEdges Λ A).card := by
  have hle := chainIntervalEntropyBound_le (q := q) (R := R) hq hJ hΔ
  have h0 := chainIntervalEntropyBound_nonneg (q := q) (R := R) hq hJ hΔ
  refine ⟨chainAreaLawConst q R * (1 + J / Δ), h0.trans hle, rfl, ?_⟩
  intro Λ h hh hhJ E₀ Ω hΩ hgap hspan A
  refine (regionEntropy_le_mul_card_domainBoundaryEdges hq hJ hΔ h hh hhJ hΩ hgap hspan A).trans ?_
  exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)

end TheoremA

end TNLean.MPS.AreaLaw
