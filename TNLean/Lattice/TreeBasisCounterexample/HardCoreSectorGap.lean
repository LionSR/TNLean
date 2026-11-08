/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TreeBasisCounterexample.PositiveLift
import TNLean.Lattice.TreeBasisCounterexample.HardCoreNumber
import QICLean.Channel.TrimmingEnergy
import Mathlib.Analysis.Real.Sqrt

/-!
# A checked hard-core multi-particle energy estimate

A normalized collective mode with tail mass at most `1/64` about one distinguished site
has squared lowering norm at most `49m/64` on the actual `m`-particle sector for `m ≥ 2`.
Positive lifting of a coefficient-matrix bound of `49/64` then gives the energy bound
`735/2048` on all these sectors.

Only the one-particle coefficient inequality is an input; the many-body sector bound is
proved from the actual qubit lowerings and number operator. This is a partial formal
certificate for the physical argument in
`docs/paper-gaps/hastings05_tree_basis_counterexample.tex`, concerning Hastings,
arXiv:cond-mat/0508554v3, equation `oibu`, lines 1690–1694. The specific tree incidence
matrix, its one-particle bound, and the full vacuum-plus-mode kernel statement are not
asserted by this module.
-/

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace MatrixOrder ComplexOrder

namespace TNLean.Lattice.TreeBasisCounterexample

private theorem norm_sum_smul_le_sqrt {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (t : Finset ι) (w : ι → ℂ) (v : ι → E) :
    ‖∑ i ∈ t, w i • v i‖ ≤
      Real.sqrt (∑ i ∈ t, ‖w i‖ ^ 2) * Real.sqrt (∑ i ∈ t, ‖v i‖ ^ 2) := by
  calc
    _ ≤ ∑ i ∈ t, ‖w i • v i‖ := norm_sum_le _ _
    _ = ∑ i ∈ t, ‖w i‖ * ‖v i‖ := by simp only [norm_smul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt t _ _

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- A mode concentrated at one site is a strict contraction in every sector with at least
 two particles. The sector condition is its lowering-norm identity, not an energy estimate. -/
theorem norm_mode_apply_le (s : ι → Matrix n n ℂ) (w : ι → ℂ) (root : ι)
    {φ : EuclideanSpace ℂ n} {m : ℕ} (hm : 2 ≤ m)
    (hnorm : ∑ i, ‖w i‖ ^ 2 = 1)
    (htail : ∑ i ∈ Finset.univ.erase root, ‖w i‖ ^ 2 ≤ (1 / 64 : ℝ))
    (hroot : ‖toEuclideanLin (s root) φ‖ ≤ ‖φ‖)
    (hsector : ∑ i, ‖toEuclideanLin (s i) φ‖ ^ 2 = (m : ℝ) * ‖φ‖ ^ 2) :
    ‖toEuclideanLin (modeOperator s w) φ‖ ≤ 7 / 8 * Real.sqrt (m : ℝ) * ‖φ‖ := by
  have hwroot : ‖w root‖ ≤ 1 := by
    have hsingle : ‖w root‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2 :=
      Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖w i‖) (Finset.mem_univ root)
    rw [hnorm] at hsingle
    nlinarith [norm_nonneg (w root)]
  have htailw : Real.sqrt (∑ i ∈ Finset.univ.erase root, ‖w i‖ ^ 2) ≤ 1 / 8 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [htail]⟩
  have htailv : Real.sqrt (∑ i ∈ Finset.univ.erase root,
      ‖toEuclideanLin (s i) φ‖ ^ 2) ≤ Real.sqrt (m : ℝ) * ‖φ‖ := by
    calc
      _ ≤ Real.sqrt (∑ i, ‖toEuclideanLin (s i) φ‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset root Finset.univ) (fun i _ _ ↦ sq_nonneg _))
      _ = _ := by rw [hsector, Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (norm_nonneg φ)]
  have htailnorm : ‖∑ i ∈ Finset.univ.erase root, w i • toEuclideanLin (s i) φ‖ ≤
      1 / 8 * (Real.sqrt (m : ℝ) * ‖φ‖) :=
    (norm_sum_smul_le_sqrt _ w _).trans
      (mul_le_mul htailw htailv (Real.sqrt_nonneg _) (by norm_num))
  have hrootnorm : ‖w root • toEuclideanLin (s root) φ‖ ≤ ‖φ‖ := by
    rw [norm_smul]
    exact (mul_le_mul hwroot hroot (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hsplit : toEuclideanLin (modeOperator s w) φ =
      w root • toEuclideanLin (s root) φ +
        ∑ i ∈ Finset.univ.erase root, w i • toEuclideanLin (s i) φ := by
    simp only [modeOperator, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ root)).symm
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  rw [hsplit]
  calc
    _ ≤ ‖φ‖ + 1 / 8 * (Real.sqrt (m : ℝ) * ‖φ‖) :=
      (norm_add_le _ _).trans (add_le_add hrootnorm htailnorm)
    _ = (1 + Real.sqrt (m : ℝ) / 8) * ‖φ‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg φ)

/-- The corresponding squared mode bound. -/
theorem norm_mode_apply_sq_le (s : ι → Matrix n n ℂ) (w : ι → ℂ) (root : ι)
    {φ : EuclideanSpace ℂ n} {m : ℕ} (hm : 2 ≤ m)
    (hnorm : ∑ i, ‖w i‖ ^ 2 = 1)
    (htail : ∑ i ∈ Finset.univ.erase root, ‖w i‖ ^ 2 ≤ (1 / 64 : ℝ))
    (hroot : ‖toEuclideanLin (s root) φ‖ ≤ ‖φ‖)
    (hsector : ∑ i, ‖toEuclideanLin (s i) φ‖ ^ 2 = (m : ℝ) * ‖φ‖ ^ 2) :
    ‖toEuclideanLin (modeOperator s w) φ‖ ^ 2 ≤ 49 / 64 * (m : ℝ) * ‖φ‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _)
    (norm_mode_apply_le s w root hm hnorm htail hroot hsector) 2).trans_eq ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  ring

/-- The squared collective-mode estimate for actual hard-core qubit lowerings. -/
theorem norm_hardCoreMode_apply_sq_le (w : ι → ℂ) (root : ι)
    {φ : EuclideanSpace ℂ (ι → Fin 2)} {m : ℕ} (hm : 2 ≤ m)
    (hnorm : ∑ i, ‖w i‖ ^ 2 = 1)
    (htail : ∑ i ∈ Finset.univ.erase root, ‖w i‖ ^ 2 ≤ (1 / 64 : ℝ))
    (hsector : IsParticleSector m φ) :
    ‖toEuclideanLin (modeOperator lowering w) φ‖ ^ 2 ≤ 49 / 64 * (m : ℝ) * ‖φ‖ ^ 2 := by
  apply norm_mode_apply_sq_le lowering w root hm hnorm htail _
    (sum_norm_lowering_sq_of_sector hsector)
  exact norm_lowering_apply_le root φ

/-- A one-particle gap of `49/64`, together with a mode of tail mass at most `1/64`,
gives a uniform energy gap `735/2048` on every physical sector with at least two particles.
Only the coefficient-matrix gap is assumed; the many-body conclusion is derived. -/
theorem hardCore_sector_energy_ge (w : ι → ℂ) (root : ι) {A : Matrix ι ι ℂ}
    (hA : (A - ((49 / 64 : ℝ) : ℂ) • (1 - vecMulVec (star w) w)).PosSemidef)
    (hnorm : ∑ i, ‖w i‖ ^ 2 = 1)
    (htail : ∑ i ∈ Finset.univ.erase root, ‖w i‖ ^ 2 ≤ (1 / 64 : ℝ))
    {φ : EuclideanSpace ℂ (ι → Fin 2)} {m : ℕ} (hm : 2 ≤ m)
    (hsector : IsParticleSector m φ) :
    (735 / 2048 : ℝ) * ‖φ‖ ^ 2 ≤
      (⟪φ, toEuclideanLin (quadraticLift lowering A) φ⟫_ℂ).re := by
  have hB := norm_hardCoreMode_apply_sq_le w root hm hnorm htail hsector
  have hN : (⟪φ, toEuclideanLin numberOperator φ⟫_ℂ).re = (m : ℝ) * ‖φ‖ ^ 2 := by
    rw [re_inner_numberOperator]
    exact sum_norm_lowering_sq_of_sector hsector
  have hmode : (⟪φ, toEuclideanLin
      ((modeOperator lowering w)ᴴ * modeOperator lowering w) φ⟫_ℂ).re =
      ‖toEuclideanLin (modeOperator lowering w) φ‖ ^ 2 := by
    rw [toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_right]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hpos := (quadraticLift_gap lowering w (49 / 64) hA).re_inner_toEuclideanLin_self_nonneg φ
  change 0 ≤ (⟪φ, toEuclideanLin (quadraticLift lowering A - ((49 / 64 : ℝ) : ℂ) •
    (numberOperator - (modeOperator lowering w)ᴴ * modeOperator lowering w)) φ⟫_ℂ).re at hpos
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hpos
  rw [hN, hmode] at hpos
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith [mul_nonneg (sub_nonneg.mpr hmreal) (sq_nonneg ‖φ‖)]

end TNLean.Lattice.TreeBasisCounterexample
