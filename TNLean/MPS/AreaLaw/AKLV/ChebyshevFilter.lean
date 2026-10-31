/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.PolynomialRank
import QICLean.Analysis.ChebyshevGroundFilter

/-!
# An actual physical Chebyshev filter with the AKLV rank bound

The polynomial is constructed from the actual supported Hamiltonian, its unit ground
vector, positive global gap and spectral ceiling. Its ground action and squared
shrinking bound are combined with the spatial rank estimate for that same polynomial
of that same Hamiltonian. No approximate ground-space projector or rank estimate is
supplied as an input.

**Local fix (count):** The rank proof uses the corrected commuting-gap count recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Source: AKLV, arXiv:1301.1162v1, Section 4, Lemmas 4.1 and 4.2, lines 530--663.
The hard-truncation robustness theorem and subsequent entropy arguments are separate.
-/

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- The constructed degree-`ell` filter has both Chebyshev suppression and the sharp
physical AKLV operator-Schmidt-rank estimate. AKLV, arXiv:1301.1162v1, Section 4,
Lemmas 4.1 and 4.2, lines 530--663. -/
theorem exists_aklv_chebyshev_filter {L q a s : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L))
    (hG : (HL + (∑ j, H j) + HR).IsHermitian) {E0 gap u : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    (hGΓ : (HL + (∑ j, H j) + HR) *ᵥ WithLp.ofLp Γ =
      (E0 : ℂ) • WithLp.ofLp Γ)
    (hgap : (HL + (∑ j, H j) + HR - (E0 : ℂ) • 1 - (gap : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef)
    (hgap0 : 0 < gap) (hgu : E0 + gap ≤ u)
    (hupper : ∀ x ∈ spectrum ℝ (HL + (∑ j, H j) + HR), x ≤ u) (ell : ℕ) :
    ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval E0 = 1 ∧
      let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        Polynomial.aeval (HL + (∑ j, H j) + HR) p
      toEuclideanLin K Γ = Γ ∧
      ‖K - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
        2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt (gap / (u - E0))) ∧
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
        (leftBlock L (a + s / 2)) K) ≤
          (q * (ell + 1)) ^ (16 * (ell / s + Nat.sqrt ell + 1)) ∧
      ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, toEuclideanLin K ψ⟫_ℂ = 0 ∧
        ‖toEuclideanLin K ψ‖ ^ 2 ≤
          (2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt (gap / (u - E0)))) ^ 2 := by
  obtain ⟨p, hdegree, hp0, hfix, herror, horth⟩ :=
    hG.exists_chebyshev_ground_filter hΓ hGΓ hgap hgap0 hgu hupper ell
  let G := HL + (∑ j, H j) + HR
  have hmap : Polynomial.aeval G p = Polynomial.aeval G
      (p.map (algebraMap ℝ ℂ)) :=
    Polynomial.aeval_eq_aeval_map (R := ℝ) (T := ℂ)
      (φ := algebraMap ℝ ℂ) rfl p G
  have hdegreeMap : (p.map (algebraMap ℝ ℂ)).natDegree ≤ ell :=
    Polynomial.natDegree_map_le.trans hdegree.le
  have hrank := operatorSchmidtRank_aklv_polynomial_le hq hs hspace H hH HL HR hL hR
    (p.map (algebraMap ℝ ℂ)) hdegreeMap
  rw [← hmap] at hrank
  exact ⟨p, hdegree, hp0, hfix, herror, hrank, horth⟩

end TNLean.MPS.AreaLaw
