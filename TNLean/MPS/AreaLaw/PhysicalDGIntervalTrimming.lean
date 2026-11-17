/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalCollectiveTrimming
import TNLean.MPS.AreaLaw.PhysicalDGReferenceSpace

/-!
# Physical collective trimming on arbitrary intervals

One common reference is chosen from the actual full degenerate ground space
before every interval and every candidate viable space. The whole exterior
is retained, so an internal regional prefix has two global boundaries and
uses the squared reference bond. The actual trimming projections are formed
from an orthonormal basis of the given input space.

**Scope restriction (gap dependence and interval rank):** The reference bond
bound uses `min gamma 1`, as documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`. The squared reference
rank and its larger trimming cost are retained explicitly. This is an
auxiliary to ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805;
it does not establish the printed tree parameters or a recursively selected
viable family.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Actual collective trimming on any prescribed interval preserves viability
for the original full physical ground space. Its uniform reference rank is
chosen before the interval and viable input space; the full exterior is kept
and the squared reference bond is explicit. Supporting ALVV,
arXiv:1602.08828v2, `lem:trimming`, lines 660–697, and the reference-space
argument following `t:alg1`, lines 1801–1805. -/
theorem exists_physical_dg_interval_collective_trimming_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ),
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu nu gamma : ℝ),
      0 < gamma →
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let rG := Module.finrank ℂ G
      let g := min gamma 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      let b := 16 + Real.log (1 / g) +
        Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * b ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log b) ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
      ∀ (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))),
      ∀ delta : ℝ, 0 ≤ delta → ∀ xi : ℝ, 0 < xi →
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) →
      let basis := stdOrthonormalBasis ℂ S
      Submodule.IsViable
        (4 * delta + 6 * epsilon +
          4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (rG ^ 2 * B) ^ 2))
        (intervalTrimSubspace L q p r xi
          (fun k ↦ (basis k : EuclideanSpace ℂ (interval L p r → Fin q))))
        (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) := by
  obtain ⟨K, hK, hreference⟩ := exists_physical_dg_isOpenMPS_reference_subspace
  refine ⟨K, hK, ?_⟩
  intro L q h hs h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap G rG g u
    epsilon hepsilon hepsilon1 b
  obtain ⟨B, hB, hlogB, U, _hdim, hUG, hGU, hU⟩ :=
    hreference L q h hs h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
      epsilon hepsilon hepsilon1
  have hG : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hrG : 1 ≤ rG := Submodule.one_le_finrank_iff.mpr hG
  have hrG2 : 1 ≤ rG ^ 2 := by nlinarith only [hrG]
  have hD : 1 ≤ rG ^ 2 * B := by simpa only [one_mul] using Nat.mul_le_mul hrG2 hB
  refine ⟨B, hB, hlogB, ?_⟩
  intro p r _hpr _hrL S delta hdelta xi hxi hS
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    isViable_intervalTrimSubspace_of_reference hD hepsilon.le hdelta hxi
      hGU hUG hU (stdOrthonormalBasis ℂ S) hS

end TNLean.MPS.AreaLaw
