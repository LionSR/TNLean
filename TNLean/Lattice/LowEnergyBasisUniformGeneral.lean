/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisUniform
import TNLean.Lattice.LowEnergyDecayKernel
import TNLean.Lattice.LowEnergyBasisRecursive

/-!
# A uniform basis bound for a ground space of arbitrary finite dimension

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1708, bounds the sum
of off-diagonal parts in a suitable ground-space basis. Normalizing by the original
term norms and summing over the selected spectral anchors gives a bound independent
of the number of lattice sites. The decay rate is weakened by the finite-dimensional
spectral refinement, with its cross terms retained.

**Scope restriction (geometric growth):** the physical summed theorem assumes a
polynomial sphere bound with constants independent of system size, absent from the
source hypotheses at lines 169–190. The unrestricted metric-lattice version of eq.
`oibu` is false, as shown mathematically in
`docs/paper-gaps/hastings05_tree_basis_counterexample.tex`; see also
`docs/paper-gaps/hastings05_geometric_growth_scope.tex`.
The normalization and recursive basis theorems themselves require no such geometry.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

section Normalization

variable {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Normalization by a norm envelope can be undone even for zero terms.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem smul_inv_smul_eq_of_norm_le (B : κ → E →L[ℂ] E) (w : κ → ℝ)
    (hNorm : ∀ i, ‖B i‖ ≤ w i) (i : κ) : w i • ((w i)⁻¹ • B i) = B i := by
  by_cases hi : w i = 0
  · have hBi : B i = 0 := norm_eq_zero.mp
      (((hNorm i).trans_eq hi).antisymm (norm_nonneg _))
    simp [hi, hBi]
  · simp only [smul_smul, mul_inv_cancel₀ hi, one_smul]

omit [CompleteSpace E] in
/-- Weighted commutator decay becomes an unweighted estimate after normalization.
No nonzero-term hypothesis is needed.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_inv_smul_le (B : κ → E →L[ℂ] E) (w : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    {C : ℝ} (hC : 0 ≤ C) (f : κ → κ → ℝ) (hf : ∀ i j, 0 ≤ f i j)
    (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * w i * w j * f i j) (i j : κ) :
    ‖((w i)⁻¹ • B i) * ((w j)⁻¹ • B j) -
        ((w j)⁻¹ • B j) * ((w i)⁻¹ • B i)‖ ≤ C * f i j := by
  by_cases hi : w i = 0
  · simp only [hi, inv_zero, zero_smul, zero_mul, mul_zero, sub_self, norm_zero]
    exact mul_nonneg hC (hf i j)
  by_cases hj : w j = 0
  · simp only [hj, inv_zero, zero_smul, zero_mul, mul_zero, sub_self, norm_zero]
    exact mul_nonneg hC (hf i j)
  have hwi : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
  have hwj : 0 < w j := lt_of_le_of_ne (hw j) (Ne.symm hj)
  have heq : ((w i)⁻¹ • B i) * ((w j)⁻¹ • B j) -
        ((w j)⁻¹ • B j) * ((w i)⁻¹ • B i) =
      ((w i)⁻¹ * (w j)⁻¹) • (B i * B j - B j * B i) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm ((w j)⁻¹) ((w i)⁻¹), smul_sub]
  rw [heq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hwi.le) (inv_nonneg.mpr hwj.le))]
  calc
    _ ≤ ((w i)⁻¹ * (w j)⁻¹) * (C * w i * w j * f i j) :=
      mul_le_mul_of_nonneg_left (hcomm i j) (by positivity)
    _ = _ := by field_simp

/-- Applying the recursive basis theorem after one normalization restores the original
term weights. Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exists_orthonormalBasis_uniform_weighted_kernel [FiniteDimensional ℂ E] [Finite κ]
    (B : κ → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i))
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hNorm : ∀ i, ‖B i‖ ≤ w i)
    (k : κ → κ → ℝ) (hk0 : ∀ i j, 0 ≤ k i j) (hk1 : ∀ i j, k i j ≤ 1)
    (hksymm : ∀ i j, k i j = k j i) (hktri : ∀ i j l, k i j * k j l ≤ k i l)
    {C : ℝ} (hC : 0 ≤ C)
    (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * w i * w j * k i j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (s : List κ),
      s.length ≤ Module.finrank ℂ E - 1 ∧
      ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤
        recursiveBasisCoeff (Module.finrank ℂ E) C * w i *
          listKernelSum (sqrtKernel k (Module.finrank ℂ E)) s i := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let D : κ → E →L[ℂ] E := fun i ↦ (w i)⁻¹ • B i
  have hD (i : κ) : IsSelfAdjoint (D i) := (IsSelfAdjoint.all ((w i)⁻¹)).smul (hB i)
  obtain ⟨b, s, hs, hb⟩ := exists_orthonormalBasis_uniform_kernel D hD k hk0 hk1 hksymm hktri
    hC (norm_commutator_inv_smul_le B w hw hC k hk0 hcomm)
  refine ⟨b, s, hs, fun i a c hac ↦ ?_⟩
  have heq : ‖⟪b a, B i (b c)⟫_ℂ‖ = w i * ‖⟪b a, D i (b c)⟫_ℂ‖ := by
    rw [← smul_inv_smul_eq_of_norm_le B w hNorm i]
    simp only [D, _root_.smul_apply, ← Complex.coe_smul, inner_smul_right, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left (hb i a c hac) (hw i)).trans_eq (by ring)

end Normalization

section AnchorSum

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Each anchor in a finite list contributes one weighted geometric row sum.
Repeated anchors are counted with their multiplicity.
Hastings, arXiv:cond-mat/0508554v3, eq. `oibu`, lines 1689–1708. -/
theorem sum_weight_list_graphDecayKernel_le (G : SimpleGraph ι) (a : κ → ι)
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ℝ)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ a i = x), w i ≤ B)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {β : ℝ} (hβ : 0 < β) (s : List κ) :
    ∑ i, w i * listKernelSum (fun i j ↦ graphDecayKernel G β (a i) (a j)) s i ≤
      (s.length : ℝ) * (B * (Kg * shellSumConst β kg)) := by
  induction s with
  | nil => simp only [listKernelSum_nil, mul_zero, Finset.sum_const_zero,
      List.length_nil, Nat.cast_zero, zero_mul]; exact le_rfl
  | cons j s ih =>
    have hrow : ∑ i, w i * graphDecayKernel G β (a i) (a j) ≤
        B * (Kg * shellSumConst β kg) := by
      calc
        _ = ∑ i, w i * graphDecayKernel G β (a j) (a i) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [graphDecayKernel_symm]
        _ ≤ _ := sum_weight_mul_exp_neg_edist_le G a w hw B hBudget (a j) Kg kg
          (hGrowth (a j)) hβ
    simp only [listKernelSum_cons, mul_add, Finset.sum_add_distrib, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    exact (add_le_add hrow ih).trans_eq (by ring)

omit [Fintype κ] in
/-- Iterated square roots commute with restriction of a kernel along an anchor map.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem sqrtKernel_comp {α : Type*} (k : α → α → ℝ) (a : κ → α) (n : ℕ) (i j : κ) :
    sqrtKernel (fun i j ↦ k (a i) (a j)) n i j = sqrtKernel k n (a i) (a j) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sqrtKernel_succ, ih]

end AnchorSum

noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) : InnerProductSpace ℂ (groundEigenspace H E₀) :=
  (groundEigenspace H E₀).innerProductSpace

section Graph

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]

set_option backward.isDefEq.respectTransparency false in
/-- An actual basis of an arbitrary nonzero finite-dimensional ground space has a
summed off-diagonal bound independent of the number of sites. Its constant depends
only on the ground-space dimension, the local norm budget, interaction geometry and gap.
No supplied basis, spectral separation or conditioning hypothesis is assumed.
Hastings, arXiv:cond-mat/0508554v3, eq. `oibu` and lines 1698–1708, with the retained
cross terms and weakened rate recorded in `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_uniform [NeZero d]
    (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ X j), ‖h j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    [NeZero (Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀))] :
    let n := Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀)
    let γ := commutatorRate R vR b₀ ΔE
    let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundEigenspace (∑ k, h k) E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (ι → Fin d)))
        (groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm q ΔE (∑ k, h k) (h i)))‖ ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
          (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg)) := by
  classical
  let K := groundEigenspace (∑ k, h k) E₀
  let B := fun i ↦ groundSpaceCompression (∑ k, h k) E₀ (h i)
  let n := Module.finrank ℂ K
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
  have hC : 0 ≤ C := mul_nonneg
    (le_trans (by norm_num) (six_le_commutatorConst R vR b₀ (abs_nonneg Kg) kg))
    (Real.exp_pos _).le
  have hGrow : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r ↦ (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  let k := fun i j ↦ graphDecayKernel G γ (a i) (a j)
  have hk0 : ∀ i j, 0 ≤ k i j := fun i j ↦ graphDecayKernel_nonneg G γ (a i) (a j)
  have hcomm (i j : κ) : ‖B i * B j - B j * B i‖ ≤ C * ‖h i‖ * ‖h j‖ * k i j :=
    (norm_groundSpaceCompression_commutator_le _ _ _ _).trans
      (norm_groundCompression_commutator_le_exp_edist G X a ha h hHerm hSupport R hDiam vR
        hCard b₀ hBudget |Kg| kg hGrow hΔE hH hgap j i)
  obtain ⟨b, s, hs, hb⟩ := exists_orthonormalBasis_uniform_weighted_kernel B
    (fun i ↦ isSelfAdjoint_groundSpaceCompression _ _ (hHerm i)) (fun i ↦ ‖h i‖)
    (fun i ↦ norm_nonneg _) (fun i ↦ norm_groundSpaceCompression_le _ _ _) k hk0
    (fun i j ↦ graphDecayKernel_le_one G hγ.le (a i) (a j))
    (fun i j ↦ graphDecayKernel_symm G γ (a i) (a j))
    (fun i j l ↦ graphDecayKernel_mul_le G hγ.le (a i) (a j) (a l)) hC hcomm
  refine ⟨b, ?_⟩
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  have hv : Orthonormal ℂ (fun c ↦ (b c : EuclideanSpace ℂ (ι → Fin d))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hterm (i : κ) :
      ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (ι → Fin d)))
        (groundCompression (∑ k, h k) E₀ (h i))‖ ≤
      (n - 1 : ℕ) * (recursiveBasisCoeff n C * ‖h i‖ * listKernelSum (sqrtKernel k n) s i) :=
    norm_offDiagonalPartFamily_le hv _
      (mul_nonneg (mul_nonneg (recursiveBasisCoeff_nonneg n C) (norm_nonneg _))
        (listKernelSum_nonneg (sqrtKernel_nonneg hk0 n) s i))
      (fun c e hce ↦ hb i c e hce)
  have hβ : 0 < γ / 2 ^ n := div_pos hγ (pow_pos (by norm_num) n)
  have hBudget' : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ a i = x), ‖h i‖ ≤ |b₀| :=
    fun x ↦ (sum_weight_anchor_le_of_support_budget X a ha
      (fun i ↦ ‖h i‖) (fun i ↦ norm_nonneg _) b₀ hBudget x).trans (le_abs_self b₀)
  have hkpow (i j : κ) : sqrtKernel k n i j =
      graphDecayKernel G (γ / 2 ^ n) (a i) (a j) := by
    rw [show k = (fun i j ↦ graphDecayKernel G γ (a i) (a j)) from rfl,
      sqrtKernel_comp, sqrtKernel_graphDecayKernel]
  have hrow : ∑ i, ‖h i‖ * listKernelSum (sqrtKernel k n) s i ≤
      (s.length : ℝ) * (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg)) := by
    rw [show sqrtKernel k n = (fun i j ↦ graphDecayKernel G (γ / 2 ^ n) (a i) (a j))
      from funext fun i ↦ funext fun j ↦ hkpow i j]
    exact sum_weight_list_graphDecayKernel_le G a
      (fun i ↦ ‖h i‖) (fun i ↦ norm_nonneg _) |b₀| hBudget' |Kg| kg hGrow hβ s
  have hlen : (s.length : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hs
  have hrow0 : 0 ≤ |b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (shellSumConst_nonneg hβ kg))
  calc
    _ ≤ ∑ i, (n - 1 : ℕ) *
        (recursiveBasisCoeff n C * ‖h i‖ * listKernelSum (sqrtKernel k n) s i) :=
      Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (n - 1 : ℕ) * recursiveBasisCoeff n C *
        ∑ i, ‖h i‖ * listKernelSum (sqrtKernel k n) s i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (n - 1 : ℕ) * recursiveBasisCoeff n C *
        ((n - 1 : ℕ) * (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg))) :=
      mul_le_mul_of_nonneg_left (hrow.trans (mul_le_mul_of_nonneg_right hlen hrow0))
        (mul_nonneg (Nat.cast_nonneg _) (recursiveBasisCoeff_nonneg n C))
    _ = _ := by ring

end Graph

end TNLean.Lattice
