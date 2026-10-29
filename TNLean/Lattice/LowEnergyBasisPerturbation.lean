/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisTruncatedUniform

/-!
# Stability of the low-energy basis under truncation

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `apb` (lines 300–320 and
1521–1533), bounds the difference between the first Gaussian filter and the actual
truncated term. The basis constructed from the original terms controls the truncated
terms up to the sum of these errors. This is useful when the localization radius grows
with the system size: a uniform bound on the total approximation error gives a uniform
off-diagonal bound without a factor exponential in that radius.

**Scope restriction (geometric growth):** the physical basis-existence theorem uses
the original-term bound under polynomial sphere growth with size-independent constants.
The perturbation estimate does not remove that additional hypothesis, which is absent
from source lines 169–190. The unrestricted fixed-radius assertion is false; see the
mathematical counterexample in `docs/paper-gaps/hastings05_tree_basis_counterexample.tex`
and `docs/paper-gaps/hastings05_geometric_growth_scope.tex`. The abstract perturbation
inequalities hold without a geometric assumption.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

section OffDiagonal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {n : ℕ} [NeZero n]

/-- Taking the off-diagonal part is linear in the operator. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, definition of `o(i)` at lines 476–480. -/
theorem offDiagonalPartFamily_sub (v : Fin n → E) (A B : E →L[𝕜] E) :
    offDiagonalPartFamily v (A - B) = offDiagonalPartFamily v A - offDiagonalPartFamily v B := by
  simp only [offDiagonalPartFamily, shiftPart, sub_apply, inner_sub_right, sub_smul,
    Finset.sum_sub_distrib]

/-- The off-diagonal part has norm at most `n-1` times the original operator norm.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–480 and 1678–1708. -/
theorem norm_offDiagonalPartFamily_le_mul_norm {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    (A : E →L[𝕜] E) : ‖offDiagonalPartFamily v A‖ ≤ (n - 1 : ℕ) * ‖A‖ := by
  refine norm_offDiagonalPartFamily_le hv A (norm_nonneg _) fun a c _ => ?_
  refine (norm_inner_le_norm _ _).trans ?_
  simpa only [hv.1 a, hv.1 c, one_mul, mul_one] using A.le_opNorm (v c)

/-- Changing an operator by `ε` changes its off-diagonal norm by at most `(n-1)ε`.
This transfers the truncation error of Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eq. `apb` (lines 300–320), to the quantity in eq. `oibu`. -/
theorem norm_offDiagonalPartFamily_le_add {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    (A B : E →L[𝕜] E) :
    ‖offDiagonalPartFamily v A‖ ≤ ‖offDiagonalPartFamily v B‖ + (n - 1 : ℕ) * ‖A - B‖ := by
  have heq : offDiagonalPartFamily v A =
      offDiagonalPartFamily v B + offDiagonalPartFamily v (A - B) := by
    rw [offDiagonalPartFamily_sub]
    abel
  calc _ = ‖offDiagonalPartFamily v B + offDiagonalPartFamily v (A - B)‖ := congrArg norm heq
    _ ≤ ‖offDiagonalPartFamily v B‖ + ‖offDiagonalPartFamily v (A - B)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (norm_offDiagonalPartFamily_le_mul_norm hv (A - B))

end OffDiagonal

section Compression

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- Ground-space compression is contractive on differences. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `apb` and lines 1562–1564. -/
theorem norm_groundCompression_sub_le (H : Matrix ν ν ℂ) (E₀ : ℝ) (W B : Matrix ν ν ℂ) :
    ‖groundCompression H E₀ W - groundCompression H E₀ B‖ ≤ ‖W - B‖ := by
  have heq : groundCompression H E₀ W - groundCompression H E₀ B =
      groundCompression H E₀ (W - B) := by
    simp only [groundCompression, map_sub, sub_mul, mul_sub]
  rw [heq]
  exact norm_groundCompression_le H E₀ (W - B)

/-- Summed off-diagonal norms change by at most `n-1` times the total operator error.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eqs. `apb` and `oibu`,
lines 300–320 and 1678–1708. -/
theorem sum_norm_offDiagonalPartFamily_groundCompression_le {κ : Type*} [Fintype κ]
    {n : ℕ} [NeZero n] {v : Fin n → EuclideanSpace ℂ ν} (hv : Orthonormal ℂ v)
    (H : Matrix ν ν ℂ) (E₀ : ℝ) (W B : κ → Matrix ν ν ℂ) :
    ∑ i, ‖offDiagonalPartFamily v (groundCompression H E₀ (W i))‖ ≤
      ∑ i, ‖offDiagonalPartFamily v (groundCompression H E₀ (B i))‖ +
        (n - 1 : ℕ) * ∑ i, ‖W i - B i‖ := by
  calc _ ≤ ∑ i, (‖offDiagonalPartFamily v (groundCompression H E₀ (B i))‖ +
      (n - 1 : ℕ) * ‖W i - B i‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (norm_offDiagonalPartFamily_le_add hv
          (groundCompression H E₀ (W i)) (groundCompression H E₀ (B i))).trans (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (norm_groundCompression_sub_le H E₀ (W i) (B i))
            (Nat.cast_nonneg _)))
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

end Compression

section GroundSpace

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable local instance (H : Matrix (ι → Fin d) (ι → Fin d) ℂ) (E₀ : ℝ) :
    InnerProductSpace ℂ (groundEigenspace H E₀) := (groundEigenspace H E₀).innerProductSpace

set_option backward.isDefEq.respectTransparency false in
/-- A basis chosen from the original terms works for every truncated family, up to the
total truncation error. In particular, a radius depending on the system size is allowed
when that total error is controlled. No uniform bound along such a choice is inferred
from a fixed observable radius. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `apb` (lines 300–320 and 1521–1533) and eq. `oibu` (lines 1678–1708). -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_truncated_perturbation_le
    [NeZero d] (G : SimpleGraph ι) (X : ι → Finset ι) (hX : ∀ i, i ∈ X i)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ i, (h i).IsHermitian)
    (hSupport : ∀ i, h i ∈ supportedOperators d (X i : Set ι))
    (R : ℕ) (hDiam : ∀ i, ∀ x ∈ X i, ∀ z ∈ X i, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ i, (X i).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) (hH : (∑ i, h i).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    [NeZero (Module.finrank ℂ (groundEigenspace (∑ i, h i) E₀))] :
    let n := Module.finrank ℂ (groundEigenspace (∑ i, h i) E₀)
    let γ := commutatorRate R vR b₀ ΔE
    let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundEigenspace (∑ i, h i) E₀),
      ∀ r : ℝ, 0 ≤ r → ∀ s : ι → Finset ι,
        ∑ i, ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (ι → Fin d)))
          (groundCompression (∑ i, h i) E₀ (truncatedTerm r ΔE h s i))‖ ≤
          ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
              (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg)) +
            (n - 1 : ℕ) * ∑ i,
              ‖gaussianFilteredTerm r ΔE (∑ j, h j) (h i) - truncatedTerm r ΔE h s i‖ := by
  classical
  let V := groundEigenspace (∑ i, h i) E₀
  obtain ⟨b, hb⟩ := exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_uniform
    G X id hX h hHerm hSupport R hDiam vR hCard b₀ hBudget Kg kg hGrowth
    (q := 0) le_rfl hΔE hH hgap
  refine ⟨b, fun r hr s => ?_⟩
  have hv : Orthonormal ℂ (fun c => (b c : EuclideanSpace ℂ (ι → Fin d))) :=
    b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hpert := sum_norm_offDiagonalPartFamily_groundCompression_le hv (∑ i, h i) E₀
    (truncatedTerm r ΔE h s) (fun i => gaussianFilteredTerm r ΔE (∑ j, h j) (h i))
  simp only [groundCompression_gaussianFilteredTerm hr hH] at hpert
  simp only [groundCompression_gaussianFilteredTerm (q := 0) le_rfl hH] at hb
  simpa only [norm_sub_rev] using hpert.trans (add_le_add hb le_rfl)

end GroundSpace

end TNLean.Lattice
