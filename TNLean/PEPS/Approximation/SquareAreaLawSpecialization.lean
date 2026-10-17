/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.MovementEtaRegional
import QICLean.Entropy.RegionCovariance
import TNLean.PEPS.Approximation.SquareAreaLawHamiltonian
import TNLean.PEPS.AreaLaw.EdgeBoundaryCalculus
import TNLean.PEPS.AreaLaw.TwoFamilies
import TNLean.PEPS.RegionBlock.Basic

/-!
# The square-grid entropy area law at range one

The polynomial-PEPS argument imports the companion area law only for the
original open square with site and nearest-neighbor interactions. This module
states that specialization on the original grid, with regional entropy taken
in the original configuration coordinates and the boundary counted on the
original edges. It derives the specialization from the uniform finite-domain
area law at range one.

The derivation is conditional: the uniform finite-domain area law is an
explicit hypothesis, and this module does not prove it.

## Main definitions and results

* `squareAreaLawSupport_isAdmissibleSupport`: designated supports are
  admissible at range one.
* `finiteProductEntropy_relabel`: regional entropy is unchanged by relabeling sites.
* `card_edgeBoundary_rectangle`: original crossing edges and integer-domain
  crossing edges have the same number.
* `SquareEntropyAreaLaw`: the range-one square-grid area law, as a proposition.
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

open scoped BigOperators ComplexOrder

noncomputable section

namespace TNLean.PEPS.Approximation

/-- Every designated support is a nonempty set of induced graph diameter at
most one in the integer rectangle. Source: polynomial-PEPS `eq:model`
(`00-introduction.tex`, lines 40–45) and area-law Corollary 1.2. -/
theorem squareAreaLawSupport_isAdmissibleSupport (L : ℕ) (i : SquareInteraction L) :
    AreaLaw.IsAdmissibleSupport (AreaLaw.rectangularDomain L L) 1
      (squareAreaLawSupport L i).1 :=
  (squareAreaLawSupport L i).2

section Relabel

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabeling the sites of a finite product state along a bijection leaves the
entropy of every region unchanged, once the region is relabeled as well. This is
the constant-dimension case of `Entropy.regionEntropy_relabel`, with identity
basis maps. Source: polynomial-PEPS `01-preliminaries.tex`, lines 23–31,
definition of `S_ω(A)`. -/
theorem finiteProductEntropy_relabel (σ : V ≃ W) (q : ℕ)
    (Ω : EuclideanSpace ℂ (V → Fin q)) (A : Finset V) :
    FiniteProduct.entropy (fun _ : W ↦ Fin q)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (σ.arrowCongr (Equiv.refl (Fin q))) Ω)
        (A.map σ.toEmbedding) =
      FiniteProduct.entropy (fun _ : V ↦ Fin q) Ω A := by
  have h := Entropy.regionEntropy_relabel (n := fun _ : V ↦ q) (n' := fun _ : W ↦ q)
    A (A.map σ.toEmbedding) σ (by simp) (fun _ ↦ Equiv.refl _) Ω
  rw [Entropy.regionEntropy_eq_entropy, Entropy.regionEntropy_eq_entropy] at h
  convert h using 2
  ext x
  rfl

end Relabel

/-- The original crossing edges of a cut correspond bijectively to the crossing
edges of the transported cut in the integer rectangle. Source: polynomial-PEPS
`01-preliminaries.tex`, lines 47–50, definition of `∂_Λ A`, and area-law
Section 1. -/
theorem card_edgeBoundary_rectangle {L : ℕ} (A : Finset (Vertex L)) :
    (AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L)
        (A.map (AreaLaw.rectangleSiteEquiv L L).toEmbedding)).card =
      Fintype.card {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge A e} := by
  classical
  let σ := AreaLaw.rectangleSiteEquiv L L
  have hadj : ∀ a b : Vertex L,
      (AreaLaw.domainGraph (AreaLaw.rectangularDomain L L)).Adj (σ a) (σ b) ↔
        (squareLatticeGraph L L).Adj a b :=
    fun a b ↦ (AreaLaw.rectangleGraphIso L L).map_rel_iff
  have hmem : ∀ a : Vertex L, σ a ∈ A.map σ.toEmbedding ↔ a ∈ A := fun a ↦ by simp [σ]
  rw [Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun e _ ↦ s(σ e.1.1, σ e.1.2)) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he
    rw [AreaLaw.mem_edgeBoundary_pair_iff, hadj, hmem, hmem]
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
      rw [AreaLaw.mem_edgeBoundary_pair_iff] at hz
      obtain ⟨hxy, hcut⟩ := hz
      obtain ⟨a, rfl⟩ := σ.surjective x
      obtain ⟨b, rfl⟩ := σ.surjective y
      rw [hadj] at hxy
      rw [hmem, hmem] at hcut
      refine ⟨Edge.ofAdj hxy, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold IsRegionBoundaryEdge Edge.ofAdj
        split_ifs <;> tauto
      · unfold Edge.ofAdj
        split_ifs
        · rfl
        · exact Sym2.eq_swap

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
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ L : ℕ, ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ → ∀ A : Finset (Vertex L),
          FiniteProduct.entropy (fun _ : Vertex L ↦ Fin q) Ω A ≤
            C * Fintype.card {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge A e}

/-- The uniform finite-domain area law at range one implies the square-grid
specialization, with the constant `C(q, 1, J, Δ)` of the finite-domain statement.
The original Hamiltonian is placed on the integer rectangle with its Hermitian
interaction parts, and the ground vector, gap, entropies, and crossing edges are
transported along the coordinate bijection.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–58),
derived from area-law Theorem 1.1 and Corollary 1.2. The uniform
finite-domain area law is an explicit hypothesis. -/
theorem _root_.TNLean.PEPS.AreaLaw.UniformAreaLaw.squareEntropyAreaLaw
    (harea : AreaLaw.UniformAreaLaw) : SquareEntropyAreaLaw := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, hC, hbound⟩ := harea q (by omega) 1 J Δ hJ hΔ
  refine ⟨C, hC, fun L h E₀ Ω hΩ A ↦ ?_⟩
  have hgap := h.isGappedGroundState_toAreaLawHamiltonian hΩ
  have := hbound (AreaLaw.rectangularDomain L L) h.toAreaLawHamiltonian E₀
    (squareAreaLawState Ω) hgap (A.map (AreaLaw.rectangleSiteEquiv L L).toEmbedding)
  rw [AreaLaw.regionalEntropy_eq_finiteProduct, card_edgeBoundary_rectangle] at this
  exact (finiteProductEntropy_relabel (AreaLaw.rectangleSiteEquiv L L) q Ω A).symm.trans_le
    this

end TNLean.PEPS.Approximation
