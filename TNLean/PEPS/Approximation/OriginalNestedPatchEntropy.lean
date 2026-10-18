/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareAreaLawSpecialization
import TNLean.PEPS.AreaLaw.Geometry.NestedPatches

/-!
# Original-state entropy on the selected nested squares

The square-grid entropy area law implies one bound `C_S * (1 + u)` for every
selected square of every original gapped ground state. The constant is chosen
before the lattice size, Hamiltonian, vector, center and scale. For a square
area law at a given constant `C_A`, the bound holds with the explicit constant
`C_S = max 1 (16 * C_A)`.

**Scope restriction (conditional area law):** The square entropy area law is an
explicit hypothesis `harea`. Its deduction from the original spectral-gap
hypotheses remains to be supplied by the uniform finite-domain area law and its
square specialization. This restriction is recorded in
`docs/paper-gaps/arealaw2d_rectangular_specialization_scope.tex`.

The state is the original ground vector in integer-domain coordinates.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 362–374
with the selected radii of lines 60–66 and the boundary count of lines 323–326;
revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- The square-grid entropy area law at fixed local dimension `q`, interaction
bound `J` and gap `Δ`, with the given constant `C_A ≥ 0`: the entropy of every
region of every unit gapped ground vector of every open-square Hamiltonian is
at most `C_A` times the number of original edges crossing the cut.
`SquareEntropyAreaLaw` asserts that some such constant exists for all
`q ≥ 2` and `J, Δ > 0`.

Source: polynomial-PEPS Proposition 2.1 (`prop:area-law`),
`01-preliminaries.tex`, lines 39–52. -/
def SquareEntropyAreaLawAt (q : ℕ) (J Δ C_A : ℝ) : Prop :=
  0 ≤ C_A ∧
    ∀ L : ℕ, ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
      h.IsGappedGroundState E₀ Ω Δ → ∀ A : Finset (Vertex L),
        FiniteProduct.entropy (fun _ : Vertex L ↦ Fin q) Ω A ≤
          C_A * Fintype.card {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge A e}

/-- The square entropy area law supplies a constant at each admissible `q`, `J`
and `Δ` (`01-preliminaries.tex`, lines 39–52). -/
theorem SquareEntropyAreaLaw.exists_squareEntropyAreaLawAt
    (harea : SquareEntropyAreaLaw) {q : ℕ} (hq : 2 ≤ q)
    {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ C_A : ℝ, SquareEntropyAreaLawAt q J Δ C_A :=
  harea q hq J Δ hJ hΔ

/-- The original-state entropy of every selected nested square is at most
`C_S * (1 + u)` with `C_S = max 1 (16 * C_A)`, for a square entropy area law at
the constant `C_A`. Empty sampled squares, repeated samples, zero lattice size,
and `u = 0` are included.

Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 362–368; the square
entropy area law at `C_A` is the explicit premise supplied by Proposition 2.1. -/
theorem SquareEntropyAreaLawAt.nestedPatch_entropy_le
    {q : ℕ} {J Δ C_A : ℝ} (hA : SquareEntropyAreaLawAt q J Δ C_A) :
    ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
      h.IsGappedGroundState E₀ Ω Δ →
      ∀ (z : ℝ × ℝ) (u : ℝ), 0 ≤ u →
        ∀ j : Fin (AreaLaw.Geometry.nestedPatchCount u),
          Entropy.regionEntropy
            (AreaLaw.Geometry.nestedPatch (AreaLaw.rectangularDomain L L) z u j.val)
            (squareAreaLawState Ω) ≤ max 1 (16 * C_A) * (1 + u) := by
  intro L h E₀ Ω hgs z u hu j
  obtain ⟨hCA, hA⟩ := hA
  let D := AreaLaw.Geometry.nestedPatch (AreaLaw.rectangularDomain L L) z u j.val
  have hcut := hA L h E₀ Ω hgs
    (D.map (AreaLaw.rectangleSiteEquiv L L).symm.toEmbedding)
  rw [← finiteProductEntropy_relabel (AreaLaw.rectangleSiteEquiv L L) q Ω,
    ← card_edgeBoundary_rectangle] at hcut
  simp only [Finset.map_map, Function.Embedding.mk_trans_mk, Equiv.self_comp_symm,
    Function.Embedding.mk_id, Finset.map_refl] at hcut
  have hbound : Entropy.regionEntropy D (squareAreaLawState Ω) ≤
      C_A * (AreaLaw.edgeBoundary (AreaLaw.rectangularDomain L L) D).card := by
    simpa only [Entropy.regionEntropy_eq_entropy, squareAreaLawState,
      AreaLaw.rectangleConfigurationEquiv] using hcut
  refine (hbound.trans (mul_le_mul_of_nonneg_left
    (AreaLaw.Geometry.card_edgeBoundary_nestedPatch_le
      (AreaLaw.rectangularDomain L L) z hu j.isLt) hCA)).trans ?_
  nlinarith [mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (16 * C_A))
    (show 0 ≤ 1 + u by positivity)]

/-- The original-state entropy of every selected nested square is at most
`C_S * (1 + u)`, for one `C_S ≥ 1` independent of the physical instance and the
center and scale. The choice from an area-law constant `C_A` is
`C_S = max 1 (16 * C_A)`, as in `SquareEntropyAreaLawAt.nestedPatch_entropy_le`.

Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 362–374; the square
entropy area law is the explicit premise supplied by Proposition 2.1. -/
theorem SquareEntropyAreaLaw.exists_nestedPatch_entropy_le
    (harea : SquareEntropyAreaLaw) {q : ℕ} (hq : 2 ≤ q)
    {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ C_S : ℝ, 1 ≤ C_S ∧
      ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (z : ℝ × ℝ) (u : ℝ), 0 ≤ u →
          ∀ j : Fin (AreaLaw.Geometry.nestedPatchCount u),
            Entropy.regionEntropy
              (AreaLaw.Geometry.nestedPatch (AreaLaw.rectangularDomain L L) z u j.val)
              (squareAreaLawState Ω) ≤ C_S * (1 + u) := by
  obtain ⟨C_A, hA⟩ := harea.exists_squareEntropyAreaLawAt hq hJ hΔ
  exact ⟨max 1 (16 * C_A), le_max_left _ _, hA.nestedPatch_entropy_le⟩

end TNLean.PEPS.Approximation
