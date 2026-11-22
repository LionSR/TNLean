/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.MovementEtaRegional
import QICLean.ManyBody.Entropy.RegionCovariance
import TNLean.PEPS.AreaLaw.Interactions.RectangularHamiltonian
import TNLean.PEPS.Tensor.SquareLattice.Basic
import TNLean.PEPS.Tensor.SquareLattice.SquareGridContraction
import TNLean.PEPS.AreaLaw.Templates.AmbientBoundary
import TNLean.PEPS.AreaLaw.Regions.TheoremStatements
import TNLean.PEPS.AreaLaw.Templates.TwoFamilies
import TNLean.PEPS.Tensor.Region.RegionBlock
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# The square-grid entropy area law at range one

The polynomial-PEPS argument imports the companion area law only for the
original open square with site and nearest-neighbor interactions. This module
states that specialization on the original grid, with regional entropy taken
in the original configuration coordinates and the boundary counted on the
original edges. It derives the specialization from the uniform finite-domain
area law at range one.

The uniform finite-domain area law is an explicit hypothesis of the derivation.
It is proved as `TNLean.PEPS.AreaLaw.uniformAreaLaw`, and the unconditional
specialization is `TNLean.PEPS.AreaLaw.squareEntropyAreaLaw`.

## Main definitions and results

* `finiteProductEntropy_relabel`: regional entropy is unchanged by relabeling sites.
* `card_edgeBoundary_rectangle`: original crossing edges and integer-domain
  crossing edges have the same number.
* `SquareEntropyAreaLawAt`: the square-grid area law for a family of states at a given
  constant.
* `SquareEntropyAreaLaw`: the range-one square-grid area law, as a proposition: some
  constant works for the ground states at every admissible `q`, `J` and `Δ`.
* `finiteProductEntropy_le_of_areaLawBound`: a range-one finite-domain area-law constant
  bounds the square-grid entropies.
* `AreaLaw.UniformAreaLaw.squareEntropyAreaLaw`: the uniform finite-domain area
  law implies the square-grid specialization.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `01-preliminaries.tex`, lines 39–58, Proposition 2.1
  (`prop:area-law`); `00-introduction.tex`, lines 36–49, `eq:model` and
  `eq:global-gap`.
* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 and Corollary 1.2.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

open scoped Matrix.Norms.L2Operator

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph SquareLatticeSiteOrEdge SquareInteraction
  PlaneInteraction)

open scoped BigOperators ComplexOrder

noncomputable section

open TNLean.Lattice

open ManyBody (IsGapped groundSpace)

namespace TNLean.PEPS.Approximation

section Relabel

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabeling the sites of a finite product state along a bijection leaves the
entropy of every region unchanged, once the region is relabeled as well. This is
the constant-dimension case of `Entropy.regionEntropy_relabel`, with identity
basis maps. Source: polynomial-PEPS `01-preliminaries.tex`, lines 23–31,
definition of `S_ω(A)`. -/
theorem finiteProductEntropy_relabel (σ : V ≃ W) (q : ℕ)
    (Ω : EuclideanSpace ℂ (V → Fin q)) (A : Finset V) :
    ManyBody.regionEntropy
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (σ.arrowCongr (Equiv.refl (Fin q))) Ω)
        (A.map σ.toEmbedding) =
      ManyBody.regionEntropy Ω A := by
  have h := Entropy.regionEntropy_relabel (n := fun _ : V ↦ q) (n' := fun _ : W ↦ q)
    A (A.map σ.toEmbedding) σ (by simp) (fun _ ↦ Equiv.refl _) Ω
  convert h using 2
  ext x
  rfl

end Relabel

/-- The original crossing edges of a cut correspond bijectively to the crossing
edges of the transported cut in the integer rectangle. Source: polynomial-PEPS
`01-preliminaries.tex`, lines 47–50, definition of `∂_Λ A`, and area-law
Section 1. -/
theorem card_edgeBoundary_rectangle {L : ℕ} (A : Finset (Vertex L)) :
    (ManyBody.edgeBoundary (ManyBody.planeDomainGraph (ManyBody.rectangularDomain L L))
        (A.map (ManyBody.rectangleSiteEquiv L L).toEmbedding)).card =
      Fintype.card {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge A e} := by
  classical
  let σ := ManyBody.rectangleSiteEquiv L L
  have hadj : ∀ a b : Vertex L,
      (ManyBody.planeDomainGraph (ManyBody.rectangularDomain L L)).Adj (σ a) (σ b) ↔
        (squareLatticeGraph L L).Adj a b :=
    fun a b ↦ (ManyBody.rectangleGraphIso L L).map_rel_iff
  have hmem : ∀ a : Vertex L, σ a ∈ A.map σ.toEmbedding ↔ a ∈ A := fun a ↦ by simp [σ]
  rw [Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun e _ ↦ s(σ e.1.1, σ e.1.2)) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he
    rw [ManyBody.mk_mem_edgeBoundary_iff, hadj, hmem, hmem]
    refine ⟨e.2.2, ?_⟩
    rcases he.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  · intro e _ f _ hef
    rcases Sym2.eq_iff.mp hef with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Subtype.ext (Prod.ext (σ.injective h₁) (σ.injective h₂))
    · have h₁ := σ.injective h₁
      have h₂ := σ.injective h₂
      have he := e.2.1
      have hf := f.2.1
      rw [h₁, h₂] at he
      exact (@lt_asymm (SquareLatticeVertex L L)
        instDistribLatticeOfLinearOrder.toSemilatticeInf.toPartialOrder.toPreorder _ _
        he hf).elim
  · intro z hz
    induction z using Sym2.ind with
    | h x y =>
      rw [ManyBody.mk_mem_edgeBoundary_iff] at hz
      obtain ⟨hxy, hcut⟩ := hz
      obtain ⟨a, rfl⟩ := σ.surjective x
      obtain ⟨b, rfl⟩ := σ.surjective y
      rw [hadj] at hxy
      rw [hmem, hmem] at hcut
      refine ⟨ManyBody.Edge.ofAdj hxy, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold IsRegionBoundaryEdge ManyBody.Edge.ofAdj
        split_ifs <;> tauto
      · unfold ManyBody.Edge.ofAdj
        split_ifs
        · rfl
        · exact Sym2.eq_swap

/-- The square-grid entropy area law at fixed local dimension `q` for the family of states `G`,
with the given constant `C_A ≥ 0`: the entropy of every region of every state of the family `G`
is at most `C_A` times the number of original edges crossing the cut. Proposition 2.1
concerns the family `IsSquareGroundState q J Δ` of unit gapped ground vectors.
`SquareEntropyAreaLaw` asserts that some such constant exists for that family for all
`q ≥ 2` and `J, Δ > 0`.

Source: polynomial-PEPS Proposition 2.1 (`prop:area-law`),
`01-preliminaries.tex`, lines 39–52. -/
def SquareEntropyAreaLawAt (q : ℕ) (G : ∀ L : ℕ, StateSpace L q → Prop) (C_A : ℝ) : Prop :=
  0 ≤ C_A ∧
    ∀ L : ℕ, ∀ Ω : StateSpace L q, G L Ω → ∀ A : Finset (Vertex L),
        ManyBody.regionEntropy Ω A ≤
          C_A * Fintype.card {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge A e}

/-- The square-grid entropy area law of the polynomial-PEPS paper: for fixed
`q ≥ 2` and `J, Δ > 0`, one constant `C_A ≥ 0` bounds the entropy of every
region of every unit gapped ground vector of every open-square Hamiltonian of
the model, by `C_A` times the number of original edges crossing the cut.
The constant is chosen before the grid size, Hamiltonian, ground vector, and cut.
Source: polynomial-PEPS Proposition 2.1 (`prop:area-law`),
`01-preliminaries.tex`, lines 39–52, under `eq:model` and `eq:global-gap`
(`00-introduction.tex`, lines 36–49). This proposition is a theorem statement,
not a proof of that theorem. -/
def SquareEntropyAreaLaw : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C_A : ℝ, SquareEntropyAreaLawAt q (IsSquareGroundState q J Δ) C_A

/-- The square-grid bound at a given constant: if the constant `C` bounds the entropy of
every cut of every finite induced domain, for every gapped ground vector of every range-one
Hamiltonian with term bound `J`, then the same `C` bounds the entropy of every region of
every gapped ground vector of every open-square Hamiltonian by `C` times the number of
original edges crossing the cut. The original Hamiltonian is placed on the integer rectangle
with its Hermitian interaction parts, and the ground vector, gap, entropies, and crossing
edges are transported along the coordinate bijection.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), derived from
area-law Theorem 1.1 and Corollary 1.2. -/
theorem finiteProductEntropy_le_of_areaLawBound {q : ℕ} {J Δ C : ℝ}
    (hbound : ∀ Λ : Finset (ℤ × ℤ), ∀ h : PlaneInteraction Λ q 1, (∀ X, (h.term X).IsHermitian) →
        (∀ X, ‖h.term X‖ ≤ J) → ∀ E₀ : ℝ,
      ∀ Ω : Lattice.StateSpace Λ q, ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ A : Finset (Lattice.Site Λ),
          ManyBody.regionEntropy Ω A ≤
            C * (ManyBody.edgeBoundary (ManyBody.planeDomainGraph Λ) A).card)
    {L : ℕ} (h : SquareInteraction L q) (hh : h.hamiltonian.IsHermitian) (hhJ : ∀ i, ‖h.term i‖ ≤ J)
        {E₀ : ℝ} {Ω : StateSpace L q}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (Vertex L)) :
    ManyBody.regionEntropy Ω A ≤
      C * Fintype.card {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge A e} := by
  obtain ⟨hΩ', hgap', hspan'⟩ := h.isGapped_toPlaneInteraction_hermitianPart hh hΩ hgap hspan
  have := hbound (ManyBody.rectangularDomain L L)
    (ManyBody.RectangleInteraction.toPlaneInteraction h.hermitianPart)
    h.isHermitian_toPlaneInteraction_hermitianPart_term
    (h.norm_toPlaneInteraction_hermitianPart_term_le hhJ) E₀
    (AreaLaw.rectangleAreaLawState Ω) hΩ' hgap' hspan'
        (A.map (ManyBody.rectangleSiteEquiv L L).toEmbedding)
  rw [card_edgeBoundary_rectangle] at this
  exact (finiteProductEntropy_relabel (ManyBody.rectangleSiteEquiv L L) q Ω A).symm.trans_le
    this

/-- The uniform finite-domain area law at range one implies the square-grid
specialization, with the constant `C(q, 1, J, Δ)` of the finite-domain statement; see
`finiteProductEntropy_le_of_areaLawBound`.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–58),
derived from area-law Theorem 1.1 and Corollary 1.2. The uniform
finite-domain area law is an explicit hypothesis. -/
theorem _root_.TNLean.PEPS.AreaLaw.UniformAreaLaw.squareEntropyAreaLaw
    (harea : AreaLaw.UniformAreaLaw) : SquareEntropyAreaLaw := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, hC, hbound⟩ := harea q (by omega) 1 J Δ hJ hΔ
  exact ⟨C, hC, fun _ _ ⟨h, hh, hhJ, _, hΩ, hgap, hspan⟩ A ↦
    finiteProductEntropy_le_of_areaLawBound hbound h hh hhJ hΩ hgap hspan A⟩

end TNLean.PEPS.Approximation
