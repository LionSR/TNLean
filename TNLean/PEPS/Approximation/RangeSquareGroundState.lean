/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OriginalNestedPatchEntropy

/-!
# Ground states of range-`R` Hamiltonians on the square

The polynomial-PEPS manuscript treats site and nearest-neighbour interactions. This file
introduces the family of states for interactions of range `R`: the unit gapped ground vectors,
read in the original coordinates of the `L × L` square, of Hamiltonians on the integer square
whose terms have supports of diameter at most `R` and norms at most `J`.

## Main definitions and results

* `IsRangeSquareGroundState`: the family of range-`R` ground vectors.
* `IsSquareGroundState.isRangeSquareGroundState`: every gapped ground vector of a square-grid
  Hamiltonian belongs to the range-one family.
* `SquareEntropyAreaLawAt.mono`: the square-grid area law passes to smaller families.
* `squareEntropyAreaLawAt_range_of_areaLawBound`: a finite-domain area-law constant at range `R`
  bounds the square-grid entropies of the range-`R` family.

The range-`R` family is an auxiliary notion; its range-one case contains the nearest-neighbour
model of the source.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
`eq:model` and `eq:global-gap` (`00-introduction.tex`, lines 36–49) and Proposition 2.1
(`01-preliminaries.tex`, lines 39–58), read with interactions of range `R`, and
*A two-dimensional area law from a global spectral gap*, Theorem 1.1 and Corollary 1.2, at
revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

/-- The unit gapped ground vectors of range-`R` Hamiltonians on the `L × L` square, in the
original coordinates: `Ω` belongs to the family when, placed on the integer square
`rectangularDomain L L`, it is a unit ground vector with gap at least `Δ` of some Hamiltonian
whose terms have supports of diameter at most `R` and norms at most `J`.

Source: polynomial-PEPS `eq:model` and `eq:global-gap` (`00-introduction.tex`, lines 36–49),
read with interactions of range `R` as in area-law Theorem 1.1. -/
def IsRangeSquareGroundState (q R : ℕ) (J Δ : ℝ) (L : ℕ) (Ω : StateSpace L q) : Prop :=
  ∃ (H : Lattice.LocalHamiltonian (AreaLaw.rectangularDomain L L) q R J) (E₀ : ℝ),
    Lattice.IsGappedGroundState (AreaLaw.rectangularDomain L L) q H.operator E₀
      (squareAreaLawState Ω) Δ

/-- A ground vector of the range-`R` family is a unit vector.
Source: polynomial-PEPS `eq:global-gap` (`00-introduction.tex`, lines 46–49). -/
theorem IsRangeSquareGroundState.norm_eq_one {q R : ℕ} {J Δ : ℝ} {L : ℕ}
    {Ω : StateSpace L q} (hΩ : IsRangeSquareGroundState q R J Δ L Ω) : ‖Ω‖ = 1 := by
  obtain ⟨_, _, hgap⟩ := hΩ
  exact (norm_squareAreaLawState Ω).symm.trans hgap.1

/-- Every gapped ground vector of a square-grid Hamiltonian belongs to the range-one family:
the Hamiltonian is placed on the integer square with its Hermitian interaction parts at the
range-one supports.
Source: polynomial-PEPS `eq:model` (`00-introduction.tex`, lines 40–45) and area-law
Corollary 1.2. -/
theorem IsSquareGroundState.isRangeSquareGroundState {q : ℕ} {J Δ : ℝ}
    {L : ℕ} {Ω : StateSpace L q} (hΩ : IsSquareGroundState q J Δ L Ω) :
    IsRangeSquareGroundState q 1 J Δ L Ω := by
  obtain ⟨h, E₀, hgap⟩ := hΩ
  exact ⟨h.toAreaLawHamiltonian, E₀, h.isGappedGroundState_toAreaLawHamiltonian hgap⟩

/-- The square-grid area law passes to a smaller family of states at the same constant.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–52). -/
theorem SquareEntropyAreaLawAt.mono {q : ℕ} {G G' : ∀ L : ℕ, StateSpace L q → Prop}
    {C_A : ℝ} (hA : SquareEntropyAreaLawAt q G' C_A)
    (hG : ∀ L : ℕ, ∀ Ω : StateSpace L q, G L Ω → G' L Ω) :
    SquareEntropyAreaLawAt q G C_A :=
  ⟨hA.1, fun L Ω hΩ ↦ hA.2 L Ω (hG L Ω hΩ)⟩

/-- A finite-domain area-law constant at range `R` bounds the square-grid entropies of the
range-`R` family: if `C ≥ 0` bounds the entropy of every cut of every finite induced domain,
for every gapped ground vector of every range-`R` Hamiltonian with term bound `J`, then the
square-grid area law holds for `IsRangeSquareGroundState q R J Δ` with the constant `C`. The
entropies and the crossing edges are transported along the coordinate bijection.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), read with
interactions of range `R`, derived from area-law Theorem 1.1 and Corollary 1.2. -/
theorem squareEntropyAreaLawAt_range_of_areaLawBound {q R : ℕ} {J Δ C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ Λ : Finset (ℤ × ℤ), ∀ H : Lattice.LocalHamiltonian Λ q R J,
      ∀ E₀ : ℝ, ∀ Ω : Lattice.StateSpace Λ q,
        Lattice.IsGappedGroundState Λ q H.operator E₀ Ω Δ →
        ∀ A : Finset (Lattice.Site Λ),
          Lattice.regionalEntropy Λ q Ω A ≤ C * (Lattice.edgeBoundary Λ A).card) :
    SquareEntropyAreaLawAt q (IsRangeSquareGroundState q R J Δ) C := by
  refine ⟨hC, fun L Ω ⟨H, E₀, hgap⟩ A ↦ ?_⟩
  have := hbound (AreaLaw.rectangularDomain L L) H E₀ (squareAreaLawState Ω) hgap
    (A.map (AreaLaw.rectangleSiteEquiv L L).toEmbedding)
  rw [Lattice.regionalEntropy_eq_finiteProduct, card_edgeBoundary_rectangle] at this
  exact (finiteProductEntropy_relabel (AreaLaw.rectangleSiteEquiv L L) q Ω A).symm.trans_le
    this

end TNLean.PEPS.Approximation
