/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisUniformGeneral
import TNLean.Lattice.LowEnergyObservableDecay
import TNLean.Lattice.TranslationSupercellTruncated

/-!
# A uniform ground-space basis bound for the actual truncated terms

The operators are Hastings' actual terms `M_i` of eq. `mid`: the Gaussian filter of `h_i`
under a locally truncated Hamiltonian. They are not replaced by filters under the full
Hamiltonian. Their ground-space commutators are estimated by applying a second Gaussian
filter under the original Hamiltonian, as in arXiv:cond-mat/0508554v3, lines 1548–1601.
The finite-dimensional basis construction then proves the size-independent summed bound
of eq. `oibu` and lines 1698–1708, with the corrected constants and weakened decay rate in
`docs/paper-gaps/hastings05_two_dim_ground_basis.tex`.

The Hamiltonian range and norm budget determine the propagation velocity. The larger
supports of the truncated observables enter their support cardinality and diameter only.
No cumulative error proportional to the number of terms is introduced.

**Scope restriction (geometric growth):** this physical sum assumes a polynomial
sphere bound with constants independent of system size. Source lines 169–190 do not
assume it. Thus the result proves eq. `oibu` under this additional hypothesis, with
fixed localization support parameters, rather than on every source metric lattice.
The unrestricted claim is false, as shown mathematically in
`docs/paper-gaps/hastings05_tree_basis_counterexample.tex`; the growth restriction is
recorded in `docs/paper-gaps/hastings05_geometric_growth_scope.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable local instance (H : Matrix (ι → Fin d) (ι → Fin d) ℂ) (E₀ : ℝ) :
    InnerProductSpace ℂ (groundEigenspace H E₀) := (groundEigenspace H E₀).innerProductSpace

set_option backward.isDefEq.respectTransparency false in
/-- A constructed basis bounds the summed off-diagonal parts of the actual truncated
operators, uniformly in the number of sites for fixed local data and ground-space dimension.
The truncation regions are arbitrary admissible local regions containing all generator
supports used there; their diameter and cardinality are displayed separately from those
of the Hamiltonian. No supplied basis, spectral separation or conditioning is assumed.
Hastings, arXiv:cond-mat/0508554v3, eq. `mid` (lines 285–307), second filtering at
lines 1548–1564, and eq. `oibu` with lines 1698–1708. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_truncated_le [NeZero d]
    (G : SimpleGraph ι) (X : ι → Finset ι) (hX : ∀ i, i ∈ X i)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ i, (h i).IsHermitian)
    (hSupport : ∀ i, h i ∈ supportedOperators d (X i : Set ι))
    (R : ℕ) (hDiam : ∀ i, ∀ x ∈ X i, ∀ z ∈ X i, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ i, (X i).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ X j), ‖h j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) (hH : (∑ i, h i).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    (r : ℝ) (s : ι → Finset ι) (K : ι → Finset ι)
    (hsK : ∀ i, ∀ j ∈ s i, X j ⊆ K i) (hXK : ∀ i, X i ⊆ K i)
    (Robs : ℕ) (hKDiam : ∀ i, ∀ x ∈ K i, ∀ z ∈ K i, G.edist x z ≤ Robs)
    (vObs : ℕ) (hKCard : ∀ i, (K i).card ≤ vObs)
    [NeZero (Module.finrank ℂ (groundEigenspace (∑ i, h i) E₀))] :
    let n := Module.finrank ℂ (groundEigenspace (∑ i, h i) E₀)
    let γ := commutatorRate R vR b₀ ΔE
    let C := commutatorConst R vObs b₀ |Kg| kg * Real.exp (γ * (2 * Robs + 1))
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundEigenspace (∑ i, h i) E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (ι → Fin d)))
        (groundCompression (∑ i, h i) E₀ (truncatedTerm r ΔE h s i))‖ ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
          (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg)) := by
  classical
  let V := groundEigenspace (∑ i, h i) E₀
  let M := truncatedTerm r ΔE h s
  let B := fun i ↦ groundSpaceCompression (∑ i, h i) E₀ (M i)
  let n := Module.finrank ℂ V
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  let C := commutatorConst R vObs b₀ |Kg| kg * Real.exp (γ * (2 * Robs + 1))
  have hC : 0 ≤ C := mul_nonneg
    (le_trans (by norm_num) (six_le_commutatorConst R vObs b₀ (abs_nonneg Kg) kg))
    (Real.exp_pos _).le
  have hMnorm (i : ι) : ‖M i‖ ≤ ‖h i‖ := norm_gaussianFilteredTerm_le r ΔE
    (Matrix.isHermitian_sum _ fun j _ ↦ hHerm j) (h i)
  have hMherm (i : ι) : (M i).IsHermitian := isHermitian_gaussianFilteredTerm r ΔE
    (Matrix.isHermitian_sum _ fun j _ ↦ hHerm j) (hHerm i)
  have hMsupp (i : ι) : M i ∈ supportedOperators d (K i : Set ι) :=
    gaussianFilteredTerm_mem_supportedOperators r ΔE
      (Submodule.sum_mem _ fun j hj ↦
        supportedOperators_mono (by exact_mod_cast hsK i j hj) (hSupport j))
      (supportedOperators_mono (by exact_mod_cast hXK i) (hSupport i))
  have hGrow : ∀ x (t : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = t).card : ℝ) ≤ |Kg| * ((t : ℝ) + 1) ^ kg :=
    fun x t ↦ (hGrowth x t).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  let k := fun i j ↦ graphDecayKernel G γ i j
  have hk0 : ∀ i j, 0 ≤ k i j := graphDecayKernel_nonneg G γ
  have hcomm (i j : ι) : ‖B i * B j - B j * B i‖ ≤ C * ‖h i‖ * ‖h j‖ * k i j := by
    refine (norm_groundSpaceCompression_commutator_le _ _ _ _).trans ?_
    refine (norm_groundCompression_observables_commutator_le_exp_edist G X id hX h hHerm
      hSupport R hDiam vR hCard b₀ hBudget Kg kg hGrowth hΔE hH hgap
      K id (fun i ↦ hXK i (hX i)) M hMsupp Robs hKDiam vObs hKCard j i).trans ?_
    change C * ‖M i‖ * ‖M j‖ * k i j ≤ C * ‖h i‖ * ‖h j‖ * k i j
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left (hMnorm i) hC) (hMnorm j)
        (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))) (hk0 i j)
  obtain ⟨b, anchors, hlen, hb⟩ := exists_orthonormalBasis_uniform_weighted_kernel B
    (fun i ↦ isSelfAdjoint_groundSpaceCompression _ _ (hMherm i)) (fun i ↦ ‖h i‖)
    (fun i ↦ norm_nonneg _) (fun i ↦ (norm_groundSpaceCompression_le _ _ _).trans (hMnorm i))
    k hk0 (graphDecayKernel_le_one G hγ.le) (graphDecayKernel_symm G γ)
    (graphDecayKernel_mul_le G hγ.le) hC hcomm
  refine ⟨b, ?_⟩
  have hv : Orthonormal ℂ (fun c ↦ (b c : EuclideanSpace ℂ (ι → Fin d))) :=
    b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hterm (i : ι) :
      ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (ι → Fin d)))
        (groundCompression (∑ j, h j) E₀ (M i))‖ ≤
      (n - 1 : ℕ) * (recursiveBasisCoeff n C * ‖h i‖ *
        listKernelSum (sqrtKernel k n) anchors i) :=
    norm_offDiagonalPartFamily_le hv _
      (mul_nonneg (mul_nonneg (recursiveBasisCoeff_nonneg n C) (norm_nonneg _))
        (listKernelSum_nonneg (sqrtKernel_nonneg hk0 n) anchors i))
      (fun c e hce ↦ hb i c e hce)
  have hβ : 0 < γ / 2 ^ n := div_pos hγ (pow_pos (by norm_num) n)
  have hBudget' : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ id i = x), ‖h i‖ ≤ |b₀| :=
    fun x ↦ (sum_weight_anchor_le_of_support_budget X id hX
      (fun i ↦ ‖h i‖) (fun i ↦ norm_nonneg _) b₀ hBudget x).trans (le_abs_self b₀)
  have hkpow : sqrtKernel k n = (fun i j ↦ graphDecayKernel G (γ / 2 ^ n) i j) :=
    funext fun i ↦ funext fun j ↦ sqrtKernel_graphDecayKernel G γ n i j
  have hrow : ∑ i, ‖h i‖ * listKernelSum (sqrtKernel k n) anchors i ≤
      (anchors.length : ℝ) * (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg)) := by
    rw [hkpow]
    exact sum_weight_list_graphDecayKernel_le G id (fun i ↦ ‖h i‖)
      (fun i ↦ norm_nonneg _) |b₀| hBudget' |Kg| kg hGrow hβ anchors
  have hlenR : (anchors.length : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hlen
  have hrow0 : 0 ≤ |b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (shellSumConst_nonneg hβ kg))
  calc
    _ ≤ ∑ i, (n - 1 : ℕ) * (recursiveBasisCoeff n C * ‖h i‖ *
        listKernelSum (sqrtKernel k n) anchors i) := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (n - 1 : ℕ) * recursiveBasisCoeff n C *
        ∑ i, ‖h i‖ * listKernelSum (sqrtKernel k n) anchors i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (n - 1 : ℕ) * recursiveBasisCoeff n C *
        ((n - 1 : ℕ) * (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg))) :=
      mul_le_mul_of_nonneg_left (hrow.trans (mul_le_mul_of_nonneg_right hlenR hrow0))
        (mul_nonneg (Nat.cast_nonneg _) (recursiveBasisCoeff_nonneg n C))
    _ = _ := by ring

end TNLean.Lattice
