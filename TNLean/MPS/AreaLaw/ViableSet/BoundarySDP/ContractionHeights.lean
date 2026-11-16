/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.CommonDenominator
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalStorage

/-!
# Height bounds for contracted rational matrix product states

A common denominator controls the physical-coordinate heights without multiplying
denominators over virtual paths. The contraction norm accounts for the number of
paths; its logarithm, rather than the path count itself, enters the binary bound.
-/

namespace TNLean.MPS.AreaLaw

/-- Bounded rational coordinate height bounds the complex norm. -/
theorem HasRationalComplexCoordinatesOfHeight.norm_le_two_mul {H : ℕ} {z : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z) : ‖z‖ ≤ 2 * H := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  have hcoord (a : ℚ) (ha : rationalHeight a ≤ H) : |(a : ℝ)| ≤ H := by
    have hnum : |(a.num : ℝ)| ≤ H := by
      have h := (num_natAbs_le_rationalHeight a).trans ha
      have h' : (a.num.natAbs : ℝ) ≤ H := by exact_mod_cast h
      simpa only [Nat.cast_natAbs, Int.cast_abs] using h'
    rw [Rat.cast_def, abs_div]
    rw [show |(a.den : ℝ)| = (a.den : ℝ) from abs_of_nonneg (Nat.cast_nonneg a.den)]
    exact (div_le_self (abs_nonneg _) (by exact_mod_cast a.den_pos)).trans hnum
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
    change |(x : ℝ)| + |(y : ℝ)| ≤ 2 * H
    linarith [hcoord x hx, hcoord y hy])

/-- A uniform local-entry norm bound controls an open-chain coefficient by the
number of virtual paths times the product of the local bounds. -/
theorem OBCChainTensor.norm_coeff_le_of_entry_norm_le {q D n : ℕ}
    (A : OBCChainTensor q D n) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ p i a b, ‖A.tensor p i a b‖ ≤ C) (σ : Fin n → Fin q) :
    ‖A.coeff σ‖ ≤ (D : ℝ) ^ (n + 1) * C ^ n := by
  classical
  rw [OBCChainTensor.coeff]
  calc
    _ ≤ ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
        ‖∏ p : Fin n, A.tensor p (σ p) (α p.castSucc) (α p.succ)‖ := norm_sum_le _ _
    _ ≤ ∑ _α : (p : Fin (n + 1)) → Fin (A.bondDim p), C ^ n := by
      apply Finset.sum_le_sum
      intro α _hα
      rw [norm_prod]
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ ↦ norm_nonneg _)
          (fun p _hp ↦ hA p (σ p) (α p.castSucc) (α p.succ))
    _ = Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) * C ^ n := by simp
    _ ≤ (D : ℝ) ^ (n + 1) * C ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hC _)
      exact_mod_cast OBCChainTensor.virtualPath_card_le A

/-- The scalar-capped contraction has a norm bound with one factor per local
tensor and one for the scalar cap. -/
theorem OBCChainTensor.norm_scalar_mul_coeff_le_of_height {q D n H : ℕ}
    (A : OBCChainTensor q D n) {c : ℂ}
    (hc : HasRationalComplexCoordinatesOfHeight H c)
    (hA : ∀ p i a b, HasRationalComplexCoordinatesOfHeight H (A.tensor p i a b))
    (σ : Fin n → Fin q) :
    ‖c * A.coeff σ‖ ≤ (2 * H * D : ℝ) ^ (n + 1) := by
  rw [norm_mul]
  calc
    _ ≤ (2 * H : ℝ) * ((D : ℝ) ^ (n + 1) * (2 * H : ℝ) ^ n) :=
      mul_le_mul hc.norm_le_two_mul
        (OBCChainTensor.norm_coeff_le_of_entry_norm_le A (by positivity)
          (fun p i a b ↦ (hA p i a b).norm_le_two_mul) σ)
        (norm_nonneg _) (by positivity)
    _ = (2 * H * D : ℝ) ^ (n + 1) := by
      rw [mul_pow (2 * H : ℝ) (D : ℝ), pow_succ (2 * H : ℝ)]
      ring

/-- Physical-coordinate heights of rational MPS data have a bound whose logarithm
is polynomial in the chain length, bond bound, and parameter bit length. For each
physical configuration only one local matrix per site enters the contraction,
so the estimate is independent of the physical dimension. -/
theorem RationalLeftOpenMPSRepresentationOfHeight.coordinate_height_common_denominator
    {L q k H b : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    let D := max 1 b
    let P := 1 + k * D ^ 2
    HasRationalComplexCoordinatesOfHeight
      (H ^ (2 * P * (k + 1)) * (2 * H * D) ^ (k + 1)) (v x) := by
  intro D P
  let σ := (leftConfigOfFinEquiv (q := q) hk).symm x
  have hσ : leftConfigOfFin σ = x := (leftConfigOfFinEquiv hk).apply_symm_apply x
  let A : OBCChainTensor 1 (max 1 (max 1 b)) k :=
    { bondDim := R.data.tensor.bondDim
      bondDim_le := R.data.tensor.bondDim_le
      left_dim := R.data.tensor.left_dim
      right_dim := R.data.tensor.right_dim
      tensor := fun p _ ↦ R.data.tensor.tensor p (σ p) }
  have hA : ∀ p i a c, HasRationalComplexCoordinatesOfHeight H (A.tensor p i a c) :=
    fun p _i a c ↦ R.tensor_height p (σ p) a c
  have hcoeff : A.coeff (fun _ ↦ 0) = R.data.tensor.coeff σ := rfl
  have hvalue : v x = R.data.scalar * A.coeff (fun _ ↦ 0) := by
    rw [hcoeff, ← hσ, R.data.coeff_eq]
  have hH : 1 ≤ H := by
    obtain ⟨a, _, _, ha, _⟩ := R.scalar_height
    exact a.den_pos.trans_le ((den_le_rationalHeight a).trans ha)
  have hD : 1 ≤ D := le_max_left 1 b
  have hcard : Fintype.card (OBCChainTensor.ParameterIndex A) ≤ k * D ^ 2 := by
    simpa only [Nat.mul_one, D, ← max_assoc, max_self] using
      OBCChainTensor.card_parameterIndex_le A
  obtain ⟨M, hM, hMbound, hscalar, htensor⟩ :=
    OBCChainTensor.exists_common_parameter_denominator A R.scalar_height hA
  have hclear : HasGaussianIntegerDenominator (M ^ (k + 1)) (v x) := by
    rw [hvalue]
    exact OBCChainTensor.scalar_mul_coeff_gaussianInteger_denominator A hscalar htensor _
  have hMglobal : M ≤ H ^ (2 * P) := hMbound.trans
    (Nat.pow_le_pow_right hH
      (Nat.mul_le_mul_left 2 (Nat.add_le_add_left hcard 1)))
  have hMpower : M ^ (k + 1) ≤ H ^ (2 * P * (k + 1)) := by
    simpa only [pow_mul] using Nat.pow_le_pow_left hMglobal (k + 1)
  have hnorm : ‖v x‖ ≤ ((2 * H * D) ^ (k + 1) : ℕ) := by
    rw [hvalue]
    simpa only [D, ← max_assoc, max_self, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
      OBCChainTensor.norm_scalar_mul_coeff_le_of_height A R.scalar_height hA (fun _ ↦ 0)
  have hbase : 1 ≤ 2 * H * D := by
    have hHD := Nat.mul_le_mul hH hD
    nlinarith
  have hone : 1 ≤ (2 * H * D) ^ (k + 1) := one_le_pow₀ hbase
  have hheight := hclear.height_of_norm_le hnorm
  rw [max_eq_right hone] at hheight
  exact hheight.mono (Nat.mul_le_mul_right _ hMpower)

/-- The coordinate bound used by rational viable families follows from clearing
the selected tensor entries, independently of the number of virtual paths. -/
theorem RationalLeftOpenMPSRepresentationOfHeight.coordinate_height_le
    {L q k H b : ℕ} (_hH : 0 < H) {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound H b k) (v x) :=
  R.coordinate_height_common_denominator hk x

/-- An exponential bound on local height gives an explicit exponential bound on
contracted height. Its exponent is polynomial in the local bit bound, length,
and an upper bound for the bond dimension. -/
theorem contractionHeight_le_two_pow {H h D B k : ℕ}
    (hH : H ≤ 2 ^ h) (hD : D ≤ B) :
    H ^ (2 * (1 + k * D ^ 2) * (k + 1)) * (2 * H * D) ^ (k + 1) ≤
      2 ^ ((2 * h * (1 + k * B ^ 2) + 1 + h + B) * (k + 1)) := by
  have hfirst : H ^ (2 * (1 + k * D ^ 2)) ≤ 2 ^ (2 * h * (1 + k * B ^ 2)) := by
    calc
      _ ≤ (2 ^ h) ^ (2 * (1 + k * D ^ 2)) := Nat.pow_le_pow_left hH _
      _ ≤ (2 ^ h) ^ (2 * (1 + k * B ^ 2)) := by gcongr
      _ = 2 ^ (2 * h * (1 + k * B ^ 2)) := by rw [← pow_mul]; congr 1; ring
  have hsecond : 2 * H * D ≤ 2 ^ (1 + h + B) := by
    calc
      _ ≤ 2 * (2 ^ h) * (2 ^ B) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hH) (hD.trans Nat.lt_two_pow_self.le)
      _ = 2 ^ (1 + h + B) := by simp only [pow_add, pow_one]
  calc
    _ = (H ^ (2 * (1 + k * D ^ 2)) * (2 * H * D)) ^ (k + 1) := by
      simp only [pow_mul, mul_pow]
    _ ≤ (2 ^ (2 * h * (1 + k * B ^ 2)) * 2 ^ (1 + h + B)) ^ (k + 1) :=
      Nat.pow_le_pow_left (Nat.mul_le_mul hfirst hsecond) _
    _ = _ := by rw [← pow_add, ← pow_mul]; congr 1; ring

/-- An explicit binary exponent for every physical coordinate of rational MPS
data with exponentially bounded local height and a bounded bond dimension. -/
theorem RationalLeftOpenMPSRepresentationOfHeight.coordinate_height_le_two_pow
    {L q k H b h B : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (hH : H ≤ 2 ^ h) (hb : max 1 b ≤ B)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (2 ^ ((2 * h * (1 + k * B ^ 2) + 1 + h + B) * (k + 1))) (v x) :=
  (R.coordinate_height_common_denominator hk x).mono (contractionHeight_le_two_pow hH hb)

end TNLean.MPS.AreaLaw
