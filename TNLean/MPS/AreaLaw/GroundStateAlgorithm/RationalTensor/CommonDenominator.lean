/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.BoundarySDP.RationalCoordinates
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.RationalTensor.RationalTensorApproximation
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.RationalTensor.RationalLocalEnergy
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.RationalTensor.RationalStorage

/-!
# Common denominators for rational tensor contractions

A common denominator allows additions in a tensor contraction without
multiplying the denominators of all virtual paths. Products accumulate one
factor of the denominator per tensor, while sums retain that denominator.
This distinction is needed for polynomial bounds on the binary length of
rational contraction data.

## Common denominators for local-energy inputs

The two rational MPS representations and all two-site coefficient matrices
form one finite family. Clearing its denominators gives one denominator
valid for every local term, so subsequent summation need not multiply
denominators belonging to different terms.

### References

- LVV, arXiv:1307.5143, Claim 2.7: matrix elements for boundary minimization.
-/

section

namespace TNLean.MPS.AreaLaw

/-- Multiplication by a positive natural denominator gives a Gaussian integer. -/
def HasGaussianIntegerDenominator (M : ℕ) (z : ℂ) : Prop :=
  0 < M ∧ (M : ℂ) * z ∈ GaussianInt.toComplex.range

namespace HasGaussianIntegerDenominator

/-- A finite sum preserves a common positive denominator. -/
theorem finset_sum {ι : Type*} {s : Finset ι} {M : ℕ} (hM : 0 < M)
    {z : ι → ℂ} (hz : ∀ i ∈ s, HasGaussianIntegerDenominator M (z i)) :
    HasGaussianIntegerDenominator M (∑ i ∈ s, z i) := by
  refine ⟨hM, ?_⟩
  rw [Finset.mul_sum]
  exact GaussianInt.toComplex.range.sum_mem fun i hi ↦ (hz i hi).2

/-- Multiplication multiplies denominators, rather than their arithmetic heights. -/
theorem mul {M N : ℕ} {z w : ℂ}
    (hz : HasGaussianIntegerDenominator M z)
    (hw : HasGaussianIntegerDenominator N w) :
    HasGaussianIntegerDenominator (M * N) (z * w) := by
  refine ⟨Nat.mul_pos hz.1 hw.1, ?_⟩
  convert GaussianInt.toComplex.range.mul_mem hz.2 hw.2 using 1
  push_cast
  ring

/-- A product of tensors with common denominator has one denominator factor per
tensor, independently of the number of terms in a later contraction sum. -/
theorem finset_prod {ι : Type*} {s : Finset ι} {M : ℕ} (hM : 0 < M)
    {z : ι → ℂ} (hz : ∀ i ∈ s, HasGaussianIntegerDenominator M (z i)) :
    HasGaussianIntegerDenominator (M ^ s.card) (∏ i ∈ s, z i) := by
  refine ⟨pow_pos hM _, ?_⟩
  have heq : (M ^ s.card : ℂ) * ∏ i ∈ s, z i = ∏ i ∈ s, (M : ℂ) * z i := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Nat.cast_pow, heq]
  exact GaussianInt.toComplex.range.prod_mem fun i hi ↦ (hz i hi).2

end HasGaussianIntegerDenominator

/-- A multiple of the reduced denominator clears a rational coordinate. -/
theorem exists_intCast_eq_natCast_mul_of_den_dvd (x : ℚ) {M : ℕ} (h : x.den ∣ M) :
    ∃ a : ℤ, (a : ℚ) = (M : ℚ) * x := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨x.num * k, ?_⟩
  have hrep : (x.den : ℚ) * x = x.num := by
    have hx : x * (x.den : ℚ) = x.num :=
      (eq_div_iff (by exact_mod_cast x.den_ne_zero)).mp x.num_div_den.symm
    simpa only [mul_comm] using hx
  push_cast
  calc
    (x.num : ℚ) * k = ((x.den : ℚ) * x) * k := by rw [hrep]
    _ = ((x.den : ℚ) * k) * x := by ring

/-- A finite family of bounded-height Gaussian-rational coordinates has one
positive denominator with a bit bound proportional to the number of coordinates. -/
theorem exists_common_gaussianInteger_denominator
    {ι : Type*} [Fintype ι] {H : ℕ} {z : ι → ℂ}
    (hz : ∀ i, HasRationalComplexCoordinatesOfHeight H (z i)) :
    ∃ M : ℕ, 0 < M ∧ M ≤ H ^ (2 * Fintype.card ι) ∧
      ∀ i, HasGaussianIntegerDenominator M (z i) := by
  classical
  choose x y hxy hx hy using hz
  let d : ι → ℕ := fun i ↦ (x i).den * (y i).den
  let M := ∏ i, d i
  have hM : 0 < M := Finset.prod_pos fun i _ ↦ Nat.mul_pos (x i).den_pos (y i).den_pos
  refine ⟨M, hM, ?_, ?_⟩
  · calc
      M ≤ ∏ _i : ι, H * H := Finset.prod_le_prod fun i _ ↦
        Nat.mul_le_mul ((den_le_rationalHeight _).trans (hx i))
          ((den_le_rationalHeight _).trans (hy i))
      _ = (H * H) ^ Fintype.card ι := by simp
      _ = H ^ (2 * Fintype.card ι) := by rw [← pow_two, ← pow_mul]
  · intro i
    have hd : d i ∣ M := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
    have hxd : (x i).den ∣ M :=
      (show (x i).den ∣ d i from ⟨(y i).den, rfl⟩).trans hd
    have hyd : (y i).den ∣ M :=
      (show (y i).den ∣ d i from ⟨(x i).den, by simp only [d, Nat.mul_comm]⟩).trans hd
    obtain ⟨a, ha⟩ := exists_intCast_eq_natCast_mul_of_den_dvd (x i) hxd
    obtain ⟨b, hb⟩ := exists_intCast_eq_natCast_mul_of_den_dvd (y i) hyd
    have ha' : (a : ℝ) = (M : ℝ) * (x i : ℝ) := by exact_mod_cast ha
    have hb' : (b : ℝ) = (M : ℝ) * (y i : ℝ) := by exact_mod_cast hb
    refine ⟨hM, ⟨(⟨a, b⟩ : GaussianInt), ?_⟩⟩
    change ((⟨a, b⟩ : GaussianInt) : ℂ) = (M : ℂ) * z i
    apply Complex.ext
    · simpa [GaussianInt.toComplex_def₂, hxy i, Complex.mul_re] using ha'
    · simpa [GaussianInt.toComplex_def₂, hxy i, Complex.mul_im] using hb'

/-- An open-chain coefficient has one common denominator factor per site.
Summing over virtual paths does not introduce any additional factor. -/
theorem OBCChainTensor.coeff_gaussianInteger_denominator {q D n M : ℕ}
    (A : OBCChainTensor q D n) (hM : 0 < M)
    (hA : ∀ p i a c, HasGaussianIntegerDenominator M (A.tensor p i a c))
    (σ : Fin n → Fin q) :
    HasGaussianIntegerDenominator (M ^ n) (A.coeff σ) := by
  rw [OBCChainTensor.coeff]
  apply HasGaussianIntegerDenominator.finset_sum (pow_pos hM _)
  intro α _hα
  simpa only [Finset.card_univ, Fintype.card_fin] using
    HasGaussianIntegerDenominator.finset_prod (s := Finset.univ) hM
      (fun p _hp ↦ hA p (σ p) (α p.castSucc) (α p.succ))

/-- Including a scalar cap adds exactly one common denominator factor to an
open-chain coefficient. -/
theorem OBCChainTensor.scalar_mul_coeff_gaussianInteger_denominator {q D n M : ℕ}
    (A : OBCChainTensor q D n) {c : ℂ}
    (hc : HasGaussianIntegerDenominator M c)
    (hA : ∀ p i a b, HasGaussianIntegerDenominator M (A.tensor p i a b))
    (σ : Fin n → Fin q) :
    HasGaussianIntegerDenominator (M ^ (n + 1)) (c * A.coeff σ) := by
  simpa only [pow_succ'] using
    hc.mul (OBCChainTensor.coeff_gaussianInteger_denominator A hc.1 hA σ)

/-- A common height bound on the scalar cap and local entries gives a common
parameter denominator bounded exponentially in the number of stored parameters. -/
theorem OBCChainTensor.exists_common_parameter_denominator {q D n H : ℕ}
    (A : OBCChainTensor q D n) {c : ℂ}
    (hc : HasRationalComplexCoordinatesOfHeight H c)
    (hA : ∀ p i a b, HasRationalComplexCoordinatesOfHeight H (A.tensor p i a b)) :
    ∃ M : ℕ, 0 < M ∧
      M ≤ H ^ (2 * (1 + Fintype.card (OBCChainTensor.ParameterIndex A))) ∧
      HasGaussianIntegerDenominator M c ∧
      ∀ p i a b, HasGaussianIntegerDenominator M (A.tensor p i a b) := by
  let z : Unit ⊕ OBCChainTensor.ParameterIndex A → ℂ := fun e ↦
    match e with
    | Sum.inl _ => c
    | Sum.inr e => A.tensor e.1 e.2.1 e.2.2.1 e.2.2.2
  have hz : ∀ e, HasRationalComplexCoordinatesOfHeight H (z e) := by
    intro e
    cases e with
    | inl _ => exact hc
    | inr e => exact hA e.1 e.2.1 e.2.2.1 e.2.2.2
  obtain ⟨M, hM, hbound, hclear⟩ := exists_common_gaussianInteger_denominator hz
  exact ⟨M, hM, by simpa using hbound, hclear (Sum.inl ()),
    fun p i a b ↦ hclear (Sum.inr ⟨p, i, a, b⟩)⟩

/-- Reduction of an integer fraction does not enlarge its numerator or denominator. -/
theorem rationalHeight_int_div_nat_le (a : ℤ) {M : ℕ} (hM : 0 < M) :
    rationalHeight ((a : ℚ) / M) ≤ max a.natAbs M := by
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  rw [← Int.cast_natCast M, Rat.intCast_div_eq_divInt]
  apply max_le
  · calc
      (Rat.divInt a (M : ℤ)).num.natAbs =
          (((M : ℤ).sign * a) / (M : ℤ).gcd a).natAbs := by
        rw [Rat.num_divInt]
      _ ≤ ((M : ℤ).sign * a).natAbs := Int.natAbs_ediv_le_natAbs _ _
      _ = a.natAbs := by simp [Int.sign_eq_one_of_pos hMZ]
      _ ≤ max a.natAbs M := le_max_left _ _
  · calc
      (Rat.divInt a (M : ℤ)).den = M / (M : ℤ).gcd a := by
        rw [Rat.den_divInt, ite_eq_right (ne_of_gt hMZ), Int.natAbs_natCast]
      _ ≤ M := Nat.div_le_self _ _
      _ ≤ max a.natAbs M := le_max_right _ _

/-- A common Gaussian-integer denominator and a norm bound control reduced
coordinate heights linearly in that denominator. -/
theorem HasGaussianIntegerDenominator.height_of_norm_le {M R : ℕ} {z : ℂ}
    (hz : HasGaussianIntegerDenominator M z) (hR : ‖z‖ ≤ (R : ℝ)) :
    HasRationalComplexCoordinatesOfHeight (M * max 1 R) z := by
  obtain ⟨hM, a, ha⟩ := hz
  have hre : (a.re : ℝ) = (M : ℝ) * z.re := by
    rw [GaussianInt.intCast_re, ha]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have him : (a.im : ℝ) = (M : ℝ) * z.im := by
    rw [GaussianInt.intCast_im, ha]
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have habsre : a.re.natAbs ≤ M * R := by
    have h : |(a.re : ℝ)| ≤ (M : ℝ) * R := by
      rw [hre, abs_mul, abs_of_nonneg (Nat.cast_nonneg M)]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm z).trans hR)
        (Nat.cast_nonneg M)
    rw [← Nat.cast_le (α := ℝ), Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul]
    exact h
  have habsim : a.im.natAbs ≤ M * R := by
    have h : |(a.im : ℝ)| ≤ (M : ℝ) * R := by
      rw [him, abs_mul, abs_of_nonneg (Nat.cast_nonneg M)]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm z).trans hR)
        (Nat.cast_nonneg M)
    rw [← Nat.cast_le (α := ℝ), Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul]
    exact h
  have hheight (d : ℤ) (hd : d.natAbs ≤ M * R) :
      rationalHeight ((d : ℚ) / M) ≤ M * max 1 R := by
    apply (rationalHeight_int_div_nat_le d hM).trans
    apply max_le
    · exact hd.trans (Nat.mul_le_mul_left M (le_max_right 1 R))
    · simpa only [Nat.mul_one] using Nat.mul_le_mul_left M (le_max_left 1 R)
  refine ⟨(a.re : ℚ) / M, (a.im : ℚ) / M, ?_, hheight _ habsre, hheight _ habsim⟩
  apply Complex.ext
  · change z.re = (((a.re : ℚ) / M : ℚ) : ℝ)
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    apply (eq_div_iff hMreal).mpr
    nlinarith only [hre]
  · change z.im = (((a.im : ℚ) / M : ℚ) : ℝ)
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    apply (eq_div_iff hMreal).mpr
    nlinarith only [him]

/-- A real norm bound gives a coordinate-height bound with its natural ceiling. -/
theorem HasGaussianIntegerDenominator.height_of_norm_le_real {M : ℕ} {R : ℝ} {z : ℂ}
    (hz : HasGaussianIntegerDenominator M z) (hR : ‖z‖ ≤ R) :
    HasRationalComplexCoordinatesOfHeight (M * max 1 ⌈R⌉₊) z :=
  hz.height_of_norm_le (hR.trans (Nat.le_ceil R))

/-- Every physical coordinate of a height-bounded rational MPS has the same
denominator, with one factor per local tensor and one for the scalar cap.
The parameter denominator depends only on the number of stored local entries,
rather than on the number of virtual contraction paths. -/
theorem RationalLeftOpenMPSRepresentationOfHeight.exists_common_coordinate_denominator
    {L q k H b : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L) :
    ∃ M : ℕ, 0 < M ∧
      M ≤ H ^ (2 * (1 + Fintype.card (OBCChainTensor.ParameterIndex R.data.tensor))) ∧
      ∀ x, HasGaussianIntegerDenominator (M ^ (k + 1)) (v x) := by
  obtain ⟨M, hM, hbound, hscalar, htensor⟩ :=
    OBCChainTensor.exists_common_parameter_denominator R.data.tensor
      R.scalar_height R.tensor_height
  refine ⟨M, hM, hbound, ?_⟩
  intro x
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  have hxy : leftConfigOfFin y = x := (leftConfigOfFinEquiv hk).apply_symm_apply x
  rw [← hxy, R.data.coeff_eq]
  exact OBCChainTensor.scalar_mul_coeff_gaussianInteger_denominator R.data.tensor
    hscalar htensor y

end TNLean.MPS.AreaLaw

end

section

namespace TNLean.MPS.AreaLaw

/-- All actual rational inputs of a finite local-energy calculation have
one common denominator. The exponent counts both caps, the stored tensor
entries, and the fourth-power many coefficients of each local term. -/
theorem OBCChainTensor.exists_common_localEnergy_parameter_denominator
    {q Da Db n m H : ℕ} (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hcapA : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capA))
    (hcapB : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capB))
    (hPA : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PB e)))
    (hK : ∀ i a b, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (K i a b))) :
    ∃ M : ℕ, 0 < M ∧
      M ≤ H ^ (2 * (2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4)) ∧
      HasGaussianIntegerDenominator M (decodeRationalComplex capA) ∧
      HasGaussianIntegerDenominator M (decodeRationalComplex capB) ∧
      (∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e))) ∧
      (∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e))) ∧
      ∀ i a b, HasGaussianIntegerDenominator M (decodeRationalComplex (K i a b)) := by
  classical
  let I := Fin 2 ⊕ (OBCChainTensor.ParameterIndex A ⊕ OBCChainTensor.ParameterIndex B) ⊕
    (Fin m × (Fin q × Fin q) × (Fin q × Fin q))
  let z : I → ℂ := fun e ↦ match e with
    | Sum.inl c => if c = 0 then decodeRationalComplex capA else decodeRationalComplex capB
    | Sum.inr (Sum.inl (Sum.inl a)) => decodeRationalComplex (PA a)
    | Sum.inr (Sum.inl (Sum.inr b)) => decodeRationalComplex (PB b)
    | Sum.inr (Sum.inr k) => decodeRationalComplex (K k.1 k.2.1 k.2.2)
  have hz : ∀ e, HasRationalComplexCoordinatesOfHeight H (z e) := by
    intro e
    rcases e with c | ((a | b) | k)
    · dsimp only [z]
      split_ifs
      · exact hcapA
      · exact hcapB
    · exact hPA a
    · exact hPB b
    · exact hK k.1 k.2.1 k.2.2
  obtain ⟨M, hM, hbound, hclear⟩ := exists_common_gaussianInteger_denominator hz
  have hH : 1 ≤ H := by
    obtain ⟨x, _y, _hxy, hx, _hy⟩ := hcapA
    exact x.den_pos.trans_le ((den_le_rationalHeight x).trans hx)
  have hcard : Fintype.card I ≤ 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4 := by
    dsimp only [I]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have hA := OBCChainTensor.card_parameterIndex_le A
    have hB := OBCChainTensor.card_parameterIndex_le B
    nlinarith only [hA, hB]
  refine ⟨M, hM, hbound.trans (Nat.pow_le_pow_right hH (Nat.mul_le_mul_left 2 hcard)),
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [z, ↓reduceIte] using hclear (Sum.inl (0 : Fin 2))
  · have hne : (1 : Fin 2) ≠ 0 := by decide
    simpa only [z, hne, ↓reduceIte] using hclear (Sum.inl (1 : Fin 2))
  · exact fun e ↦ hclear (Sum.inr (Sum.inl (Sum.inl e)))
  · exact fun e ↦ hclear (Sum.inr (Sum.inl (Sum.inr e)))
  · exact fun i a b ↦ hclear (Sum.inr (Sum.inr (i, a, b)))

end TNLean.MPS.AreaLaw

end
