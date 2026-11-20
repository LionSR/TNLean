/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FrustrationFree.Family
import TNLean.PEPS.AreaLaw.LatticeConstraints

/-!
# The positive quasi-local constraints are a frustration-free family

Proposition 4.3 of the two-dimensional area law replaces a gapped Hamiltonian by positive
contractions `k_i` with `k_i Ω = 0` and `(Δ/c)(1 - P) ≤ ∑_i k_i`
(`exists_latticePositiveConstraints`). These are the conditions of `IsFrustrationFree` with
strength `1` and gap `Δ/c`, so every statement proved for frustration-free families applies to
them; only their supports differ from the finite-range model, being connected components with
stretched-exponential tails instead of sets of bounded diameter.

## Main statements

* `TNLean.PEPS.AreaLaw.FrustrationFree.exists_isFrustrationFree_latticePositiveConstraints`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.3 (`prop:positive`, `03-quasilocal.tex`, lines 220–246).
* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  `eq:model`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open ManyBody (IsGapped groundSpace PlaneInteraction AdmissibleSupport)
open TNLean.Lattice SpectralFilter

namespace TNLean.PEPS.AreaLaw.FrustrationFree

/-- **The positive quasi-local constraints are frustration free** (Proposition 4.3,
`prop:positive`, `03-quasilocal.tex`, lines 220–246). For `p ≥ 1`, `R`, `J ≥ 0` and `Δ > 0`,
the constraints `k_i` of `exists_latticePositiveConstraints` of a gapped instance with unique
ground vector `Ω` form a frustration-free family with strength `1` and gap `Δ / c`, where
`c = positiveNormalization p (Δ / 2) J > 0`. -/
theorem exists_isFrustrationFree_latticePositiveConstraints {p : ℕ} (hp : 1 ≤ p) (R : ℕ)
    {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
    (h : PlaneInteraction Λ q R) (hherm : ∀ X, (h.term X).IsHermitian)
    (hnorm : ∀ X, ‖h.term X‖ ≤ J) (a : AdmissibleSupport Λ R → Site Λ) (ha : ∀ X, a X ∈ X.1)
    (E₀ : ℝ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hground : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) :
    0 < positiveNormalization p (Δ / 2) J ∧
      IsFrustrationFree (fun i ↦ positiveConstraint (positiveNormalization p (Δ / 2) J)
        (centeredFilter p (Δ / 2) h.hamiltonian Ω (h.term i))) 1
        (Δ / positiveNormalization p (Δ / 2) J) Ω := by
  obtain ⟨C, c, -, -, hk⟩ := exists_latticePositiveConstraints hp R hJ hΔ
  obtain ⟨hcs, hkb, -, -, hgap', -, -⟩ :=
    hk Λ h hherm hnorm a ha E₀ Ω hΩ hgap hground
  refine ⟨hcs, ⟨fun i ↦ ?_, fun i ↦ ?_, fun i ↦ (hkb i).2.2, hΩ, ?_⟩⟩
  · exact Matrix.nonneg_iff_posSemidef.mp (hkb i).1
  · simpa using (hkb i).2.1
  · simpa using hgap'

end TNLean.PEPS.AreaLaw.FrustrationFree
