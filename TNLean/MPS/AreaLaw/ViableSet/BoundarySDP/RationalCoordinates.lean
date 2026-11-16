/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.Basic

/-!
# Rational scalar coordinates and arithmetic heights

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- The uniform real grid of order `M` on `[-1,1]`. -/
noncomputable def unitRealGrid (M : ℕ) : Finset ℝ := by
  classical
  exact (Finset.range (2 * M + 1)).image fun k : ℕ ↦ -1 + (k : ℝ) / M

/-- The uniform real grid of order `M` scaled to `[-R,R]`. -/
noncomputable def scaledRealGrid (M : ℕ) (R : ℝ) : Finset ℝ := by
  classical
  exact (unitRealGrid M).image fun x ↦ R * x

/-- The rational grid of denominator `M` on the interval `[-B,B]`.  Unlike the
real-scaled grids below, its elements carry an exact rational representation. -/
def rationalRealGrid (B M : ℕ) : Finset ℚ := by
  exact (Finset.range (2 * B * M + 1)).image fun k : ℕ ↦
    -(B : ℚ) + (k : ℚ) / M

/-- Membership in the rational grid is witnessed by a bounded natural-number
coordinate.  This is the discrete representation used in the eventual encoding bound. -/
theorem mem_rationalRealGrid_iff {B M : ℕ} {q : ℚ} :
    q ∈ rationalRealGrid B M ↔
      ∃ k < 2 * B * M + 1, q = -(B : ℚ) + (k : ℚ) / M := by
  simp [rationalRealGrid, eq_comm]

/-- The arithmetic height of a rational number: the larger of the absolute reduced
numerator and the reduced positive denominator. -/
def rationalHeight (q : ℚ) : ℕ :=
  max q.num.natAbs q.den

/-- One plus the base-two logarithm of rational height, a uniform bit-length bound
for the reduced numerator and denominator. -/
def rationalBitLength (q : ℚ) : ℕ :=
  Nat.log2 (rationalHeight q) + 1

theorem num_natAbs_le_rationalHeight (q : ℚ) : q.num.natAbs ≤ rationalHeight q :=
  le_max_left _ _

theorem den_le_rationalHeight (q : ℚ) : q.den ≤ rationalHeight q :=
  le_max_right _ _

theorem rationalBitLength_le {q : ℚ} {H : ℕ} (hq : rationalHeight q ≤ H) :
    rationalBitLength q ≤ Nat.log2 H + 1 := by
  apply Nat.add_le_add_right
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right hq

/-- The rational height is Mathlib's multiplicative Weil height specialized to
`ℚ`, expressed as a natural number. -/
theorem rationalHeight_cast (q : ℚ) :
    (rationalHeight q : ℝ) = Height.mulHeight₁ q := by
  rw [Rat.mulHeight₁_eq_max]
  rfl

/-- Negation does not change rational height. -/
theorem rationalHeight_neg (q : ℚ) : rationalHeight (-q) = rationalHeight q := by
  simp [rationalHeight]

/-- Multiplication increases rational height by at most the product of the two
input heights. -/
theorem rationalHeight_mul_le (x y : ℚ) :
    rationalHeight (x * y) ≤ rationalHeight x * rationalHeight y := by
  have h := Height.mulHeight₁_mul_le x y
  rw [← rationalHeight_cast, ← rationalHeight_cast, ← rationalHeight_cast] at h
  exact_mod_cast h

/-- Addition increases rational height by at most twice the product of the two
input heights. -/
theorem rationalHeight_add_le (x y : ℚ) :
    rationalHeight (x + y) ≤ 2 * rationalHeight x * rationalHeight y := by
  have h := Height.mulHeight₁_add_le x y
  rw [NumberField.totalWeight_eq_finrank] at h
  norm_num only [Module.finrank_self, pow_one, Nat.cast_ofNat] at h
  rw [← rationalHeight_cast, ← rationalHeight_cast, ← rationalHeight_cast] at h
  exact_mod_cast h

/-- Subtraction obeys the same rational-height bound as addition. -/
theorem rationalHeight_sub_le (x y : ℚ) :
    rationalHeight (x - y) ≤ 2 * rationalHeight x * rationalHeight y := by
  simpa [sub_eq_add_neg, rationalHeight_neg] using rationalHeight_add_le x (-y)

/-- Casting a natural number to the rationals has height at most one more than
that natural number; the extra one uniformly covers zero. -/
theorem rationalHeight_natCast_le (n : ℕ) :
    rationalHeight (n : ℚ) ≤ n + 1 := by
  simp [rationalHeight]

/-- Inversion preserves rational height. -/
theorem rationalHeight_inv (q : ℚ) : rationalHeight q⁻¹ = rationalHeight q := by
  have h := Height.mulHeight₁_inv q
  rw [← rationalHeight_cast, ← rationalHeight_cast] at h
  exact_mod_cast h

/-- Division increases rational height by at most the product of the two input
heights. -/
theorem rationalHeight_div_le (x y : ℚ) :
    rationalHeight (x / y) ≤ rationalHeight x * rationalHeight y := by
  simpa [div_eq_mul_inv, rationalHeight_inv] using rationalHeight_mul_le x y⁻¹

/-- The height of a nonempty finite rational sum is bounded by the number of
summands times the product of their heights. -/
theorem rationalHeight_finset_sum_le {α : Type*} {s : Finset α} (hs : s.Nonempty)
    (x : α → ℚ) :
    rationalHeight (∑ a ∈ s, x a) ≤ s.card * ∏ a ∈ s, rationalHeight (x a) := by
  have h := Height.mulHeight₁_sum_le hs x
  rw [NumberField.totalWeight_eq_finrank] at h
  norm_num only [Module.finrank_self, pow_one] at h
  rw [← rationalHeight_cast] at h
  simp_rw [← rationalHeight_cast] at h
  exact_mod_cast h

/-- A coordinate in the explicit presentation of the rational grid has polynomially
bounded reduced numerator and denominator. -/
theorem rationalGridCoordinate_height_le (B M k : ℕ) (hk : k < 2 * B * M + 1) :
    rationalHeight (-(B : ℚ) + (k : ℚ) / M) ≤
      2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
  calc
    rationalHeight (-(B : ℚ) + (k : ℚ) / M) ≤
        2 * rationalHeight (-(B : ℚ)) * rationalHeight ((k : ℚ) / M) :=
      rationalHeight_add_le _ _
    _ ≤ 2 * (B + 1) * ((k + 1) * (M + 1)) := by
      gcongr
      · simpa [rationalHeight_neg] using rationalHeight_natCast_le B
      · exact (rationalHeight_div_le _ _).trans <|
          Nat.mul_le_mul (rationalHeight_natCast_le k) (rationalHeight_natCast_le M)
    _ ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
      gcongr
      omega

/-- Every member of `rationalRealGrid B M` has polynomially bounded reduced
numerator and denominator. -/
theorem rationalHeight_le_of_mem_rationalRealGrid {B M : ℕ} {q : ℚ}
    (hq : q ∈ rationalRealGrid B M) :
    rationalHeight q ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
  obtain ⟨k, hk, rfl⟩ := mem_rationalRealGrid_iff.mp hq
  exact rationalGridCoordinate_height_le B M k hk

/-- Every rational-grid coordinate has logarithmic binary encoding length in the
explicit polynomial height bound. -/
theorem rationalBitLength_le_of_mem_rationalRealGrid {B M : ℕ} {q : ℚ}
    (hq : q ∈ rationalRealGrid B M) :
    rationalBitLength q ≤
      Nat.log2 (2 * (B + 1) * ((2 * B * M + 1) * (M + 1))) + 1 :=
  rationalBitLength_le (rationalHeight_le_of_mem_rationalRealGrid hq)

/-- The reduced numerator and denominator of every rational-grid coordinate obey the
same explicit polynomial bound. -/
theorem numerator_denominator_le_of_mem_rationalRealGrid {B M : ℕ} {q : ℚ}
    (hq : q ∈ rationalRealGrid B M) :
    q.num.natAbs ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) ∧
      q.den ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
  have hheight := rationalHeight_le_of_mem_rationalRealGrid hq
  exact ⟨(num_natAbs_le_rationalHeight q).trans hheight,
    (den_le_rationalHeight q).trans hheight⟩

/-- A canonical positive integer denominator for choosing a rational precision below
a prescribed positive real target. -/
noncomputable def rationalPositiveToleranceOrder (t : ℝ) : ℕ :=
  ⌈1 / t⌉₊ + 1

/-- A canonical positive rational precision below `t`: the reciprocal of one more than
the ceiling of `1/t`. -/
noncomputable def rationalPositiveTolerance (t : ℝ) : ℝ :=
  ((1 / (rationalPositiveToleranceOrder t : ℚ) : ℚ) : ℝ)

theorem rationalPositiveToleranceOrder_pos (t : ℝ) :
    0 < rationalPositiveToleranceOrder t := by
  unfold rationalPositiveToleranceOrder
  omega

theorem rationalPositiveTolerance_pos (t : ℝ) : 0 < rationalPositiveTolerance t := by
  have hM : (0 : ℚ) < rationalPositiveToleranceOrder t := by
    exact_mod_cast rationalPositiveToleranceOrder_pos t
  unfold rationalPositiveTolerance
  exact_mod_cast div_pos (by norm_num : (0 : ℚ) < 1) hM

theorem rationalPositiveTolerance_le {t : ℝ} (ht : 0 < t) :
    rationalPositiveTolerance t ≤ t := by
  let M := rationalPositiveToleranceOrder t
  have hM : (0 : ℝ) < M := by exact_mod_cast rationalPositiveToleranceOrder_pos t
  have hceil : 1 / t ≤ (⌈1 / t⌉₊ : ℝ) := Nat.le_ceil _
  have hMt : 1 / t ≤ (M : ℝ) := by
    dsimp only [M, rationalPositiveToleranceOrder]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hrecip : 1 / (M : ℝ) ≤ t := by
    rw [div_le_iff₀ hM]
    have := (div_le_iff₀ ht).mp hMt
    nlinarith
  simpa only [rationalPositiveTolerance, M, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast] using hrecip

/-- A canonical nonnegative rational upper bound for an arbitrary real number. -/
noncomputable def rationalNonnegativeUpperBound (x : ℝ) : ℚ :=
  (⌈max x 0⌉₊ : ℚ)

theorem le_rationalNonnegativeUpperBound (x : ℝ) :
    x ≤ (rationalNonnegativeUpperBound x : ℝ) := by
  calc
    x ≤ max x 0 := le_max_left _ _
    _ ≤ (⌈max x 0⌉₊ : ℕ) := Nat.le_ceil _
    _ = (rationalNonnegativeUpperBound x : ℝ) := by
      simp [rationalNonnegativeUpperBound]

theorem rationalNonnegativeUpperBound_height_le (x : ℝ) :
    rationalHeight (rationalNonnegativeUpperBound x) ≤ ⌈max x 0⌉₊ + 1 := by
  simpa only [rationalNonnegativeUpperBound] using
    rationalHeight_natCast_le ⌈max x 0⌉₊

/-- Rational upper rounding of `x` on the mesh determined by a positive target `t`.
Unlike the integer ceiling, its overshoot is at most `t`. -/
noncomputable def rationalNonnegativeUpperApproximation (x t : ℝ) : ℚ :=
  let M := rationalPositiveToleranceOrder t
  (⌈max x 0 * M⌉₊ : ℚ) / M

theorem le_rationalNonnegativeUpperApproximation (x t : ℝ) :
    x ≤ (rationalNonnegativeUpperApproximation x t : ℝ) := by
  let M := rationalPositiveToleranceOrder t
  have hM : (0 : ℝ) < M := by exact_mod_cast rationalPositiveToleranceOrder_pos t
  have hceil : max x 0 * M ≤ (⌈max x 0 * M⌉₊ : ℕ) := Nat.le_ceil _
  calc
    x ≤ max x 0 := le_max_left _ _
    _ ≤ (⌈max x 0 * M⌉₊ : ℝ) / M := by
      rw [le_div_iff₀ hM]
      exact_mod_cast hceil
    _ = (rationalNonnegativeUpperApproximation x t : ℝ) := by
      simp [rationalNonnegativeUpperApproximation, M]

theorem rationalNonnegativeUpperApproximation_le
    {x t : ℝ} (ht : 0 < t) :
    (rationalNonnegativeUpperApproximation x t : ℝ) ≤ max x 0 + t := by
  let M := rationalPositiveToleranceOrder t
  have hM : (0 : ℝ) < M := by exact_mod_cast rationalPositiveToleranceOrder_pos t
  have hceil : (⌈max x 0 * (M : ℝ)⌉₊ : ℝ) < max x 0 * M + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (le_max_right x 0) hM.le)
  have hround : (1 : ℝ) / M ≤ t := by
    simpa only [M, rationalPositiveTolerance, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast] using rationalPositiveTolerance_le ht
  have hstrict : (⌈max x 0 * M⌉₊ : ℝ) / M < max x 0 + 1 / M := by
    calc
      (⌈max x 0 * M⌉₊ : ℝ) / M < (max x 0 * M + 1) / M :=
        div_lt_div_of_pos_right hceil hM
      _ = max x 0 + 1 / M := by field_simp
  calc
    (rationalNonnegativeUpperApproximation x t : ℝ) =
        (⌈max x 0 * M⌉₊ : ℝ) / M := by
      simp [rationalNonnegativeUpperApproximation, M]
    _ ≤ max x 0 + 1 / M := hstrict.le
    _ ≤ max x 0 + t := by
      simpa only [add_comm] using add_le_add_right hround (max x 0)

theorem rationalNonnegativeUpperApproximation_height_le (x t : ℝ) :
    rationalHeight (rationalNonnegativeUpperApproximation x t) ≤
      (⌈max x 0 * rationalPositiveToleranceOrder t⌉₊ + 1) *
        (rationalPositiveToleranceOrder t + 1) := by
  unfold rationalNonnegativeUpperApproximation
  apply (rationalHeight_div_le _ _).trans
  exact Nat.mul_le_mul (rationalHeight_natCast_le _)
    (rationalHeight_natCast_le _)

/-- A complex number whose real and imaginary parts are rational. -/
def HasRationalComplexCoordinates (z : ℂ) : Prop :=
  ∃ x y : ℚ, z = ⟨(x : ℝ), (y : ℝ)⟩

/-- A complex number with rational coordinates whose reduced numerators and
denominators are uniformly bounded by `H`. -/
def HasRationalComplexCoordinatesOfHeight (H : ℕ) (z : ℂ) : Prop :=
  ∃ x y : ℚ, z = ⟨(x : ℝ), (y : ℝ)⟩ ∧ rationalHeight x ≤ H ∧ rationalHeight y ≤ H

theorem rationalPositiveTolerance_hasRationalCoordinatesOfHeight (t : ℝ) :
    HasRationalComplexCoordinatesOfHeight (rationalPositiveToleranceOrder t + 1)
      (rationalPositiveTolerance t : ℂ) := by
  let M := rationalPositiveToleranceOrder t
  let q : ℚ := 1 / M
  refine ⟨q, 0, ?_, ?_, ?_⟩
  · apply Complex.ext
    · simp [q, M, rationalPositiveTolerance]
    · simp
  · exact (rationalHeight_div_le 1 M).trans <| by
      have h1 : rationalHeight (1 : ℚ) = 1 := by norm_num [rationalHeight]
      rw [h1, one_mul]
      exact rationalHeight_natCast_le M
  · simp [rationalHeight]

namespace HasRationalComplexCoordinatesOfHeight

theorem forget {H : ℕ} {z : ℂ} (hz : HasRationalComplexCoordinatesOfHeight H z) :
    HasRationalComplexCoordinates z := by
  obtain ⟨x, y, hxy, _hx, _hy⟩ := hz
  exact ⟨x, y, hxy⟩

theorem mono {H K : ℕ} {z : ℂ} (hHK : H ≤ K)
    (hz : HasRationalComplexCoordinatesOfHeight H z) :
    HasRationalComplexCoordinatesOfHeight K z := by
  obtain ⟨x, y, hxy, hx, hy⟩ := hz
  exact ⟨x, y, hxy, hx.trans hHK, hy.trans hHK⟩

theorem exists_bitLength_le {H : ℕ} {z : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z) :
    ∃ x y : ℚ, z = ⟨(x : ℝ), (y : ℝ)⟩ ∧
      rationalBitLength x ≤ Nat.log2 H + 1 ∧
      rationalBitLength y ≤ Nat.log2 H + 1 := by
  obtain ⟨x, y, hxy, hx, hy⟩ := hz
  exact ⟨x, y, hxy, rationalBitLength_le hx, rationalBitLength_le hy⟩

theorem zero : HasRationalComplexCoordinatesOfHeight 1 0 := by
  exact ⟨0, 0, by apply Complex.ext <;> simp, by simp [rationalHeight], by simp [rationalHeight]⟩

theorem one : HasRationalComplexCoordinatesOfHeight 1 1 := by
  exact ⟨1, 0, by apply Complex.ext <;> simp, by simp [rationalHeight], by simp [rationalHeight]⟩

theorem half : HasRationalComplexCoordinatesOfHeight 2 ((2 : ℂ)⁻¹) := by
  refine ⟨1 / 2, 0, ?_, ?_, ?_⟩
  · apply Complex.ext <;> norm_num
  · norm_num [rationalHeight]
  · norm_num [rationalHeight]

theorem neg {H : ℕ} {z : ℂ} (hz : HasRationalComplexCoordinatesOfHeight H z) :
    HasRationalComplexCoordinatesOfHeight H (-z) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  exact ⟨-x, -y, by apply Complex.ext <;> simp, by simpa [rationalHeight_neg],
    by simpa [rationalHeight_neg]⟩

theorem star {H : ℕ} {z : ℂ} (hz : HasRationalComplexCoordinatesOfHeight H z) :
    HasRationalComplexCoordinatesOfHeight H (star z) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  exact ⟨x, -y, by apply Complex.ext <;> simp, hx, by simpa [rationalHeight_neg]⟩

theorem add {H K : ℕ} {z w : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z)
    (hw : HasRationalComplexCoordinatesOfHeight K w) :
    HasRationalComplexCoordinatesOfHeight (2 * H * K) (z + w) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  obtain ⟨u, v, rfl, hu, hv⟩ := hw
  exact ⟨x + u, y + v, by apply Complex.ext <;> simp,
    (rationalHeight_add_le x u).trans (by gcongr),
    (rationalHeight_add_le y v).trans (by gcongr)⟩

theorem sub {H K : ℕ} {z w : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z)
    (hw : HasRationalComplexCoordinatesOfHeight K w) :
    HasRationalComplexCoordinatesOfHeight (2 * H * K) (z - w) := by
  simpa [sub_eq_add_neg] using add hz hw.neg

theorem mul {H K : ℕ} {z w : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z)
    (hw : HasRationalComplexCoordinatesOfHeight K w) :
    HasRationalComplexCoordinatesOfHeight (2 * (H * K) * (H * K)) (z * w) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  obtain ⟨u, v, rfl, hu, hv⟩ := hw
  have hxu : rationalHeight (x * u) ≤ H * K :=
    (rationalHeight_mul_le x u).trans (by gcongr)
  have hyv : rationalHeight (y * v) ≤ H * K :=
    (rationalHeight_mul_le y v).trans (by gcongr)
  have hxv : rationalHeight (x * v) ≤ H * K :=
    (rationalHeight_mul_le x v).trans (by gcongr)
  have hyu : rationalHeight (y * u) ≤ H * K :=
    (rationalHeight_mul_le y u).trans (by gcongr)
  exact ⟨x * u - y * v, x * v + y * u, by apply Complex.ext <;> simp,
    (rationalHeight_sub_le _ _).trans (by gcongr),
    (rationalHeight_add_le _ _).trans (by gcongr)⟩

/-- A sum of `n` complex numbers of coordinate height at most `H` has coordinate
height at most `(2H)^n`.  The bound is deliberately multiplicative, since its
binary encoding length is linear in `n`. -/
theorem finset_sum {ι : Type*} {s : Finset ι} {H : ℕ} {f : ι → ℂ}
    (hf : ∀ i ∈ s, HasRationalComplexCoordinatesOfHeight H (f i)) :
    HasRationalComplexCoordinatesOfHeight ((2 * H) ^ s.card) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        add (hf a (Finset.mem_insert_self a s))
          (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- Coordinate-height bound for a product of `n` complex numbers, each of height at
most `H`.  The recurrence records exactly the elementary multiplication bound above. -/
def productHeight (H : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * (H * productHeight H n) * (H * productHeight H n)

/-- Products of positive-height coordinates retain a positive height bound. -/
theorem productHeight_pos {H : ℕ} (hH : 0 < H) :
    ∀ n, 0 < productHeight H n := by
  intro n
  induction n with
  | zero => simp [productHeight]
  | succ n ih =>
      simp only [productHeight]
      positivity

/-- A product of `n` complex numbers of coordinate height at most `H` has coordinate
height at most `productHeight H n`. -/
theorem finset_prod {ι : Type*} {s : Finset ι} {H : ℕ} {f : ι → ℂ}
    (hf : ∀ i ∈ s, HasRationalComplexCoordinatesOfHeight H (f i)) :
    HasRationalComplexCoordinatesOfHeight (productHeight H s.card) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [productHeight] using one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

end HasRationalComplexCoordinatesOfHeight

namespace HasRationalComplexCoordinates

/-- The real part of a complex number with rational coordinates is the coercion of a
rational number. -/
theorem exists_realPart {z : ℂ} (hz : HasRationalComplexCoordinates z) :
    ∃ x : ℚ, z.re = (x : ℝ) := by
  obtain ⟨x, y, rfl⟩ := hz
  exact ⟨x, rfl⟩

theorem zero : HasRationalComplexCoordinates 0 := ⟨0, 0, by apply Complex.ext <;> simp⟩

theorem one : HasRationalComplexCoordinates 1 := ⟨1, 0, by apply Complex.ext <;> simp⟩

theorem add {z w : ℂ} (hz : HasRationalComplexCoordinates z)
    (hw : HasRationalComplexCoordinates w) : HasRationalComplexCoordinates (z + w) := by
  obtain ⟨x, y, rfl⟩ := hz
  obtain ⟨u, v, rfl⟩ := hw
  exact ⟨x + u, y + v, by apply Complex.ext <;> simp⟩

theorem neg {z : ℂ} (hz : HasRationalComplexCoordinates z) :
    HasRationalComplexCoordinates (-z) := by
  obtain ⟨x, y, rfl⟩ := hz
  exact ⟨-x, -y, by apply Complex.ext <;> simp⟩

theorem sub {z w : ℂ} (hz : HasRationalComplexCoordinates z)
    (hw : HasRationalComplexCoordinates w) : HasRationalComplexCoordinates (z - w) :=
  hz.add hw.neg

theorem mul {z w : ℂ} (hz : HasRationalComplexCoordinates z)
    (hw : HasRationalComplexCoordinates w) : HasRationalComplexCoordinates (z * w) := by
  obtain ⟨x, y, rfl⟩ := hz
  obtain ⟨u, v, rfl⟩ := hw
  refine ⟨x * u - y * v, x * v + y * u, ?_⟩
  apply Complex.ext <;> simp

theorem star {z : ℂ} (hz : HasRationalComplexCoordinates z) :
    HasRationalComplexCoordinates (star z) := by
  obtain ⟨x, y, rfl⟩ := hz
  exact ⟨x, -y, by apply Complex.ext <;> simp⟩

theorem finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ}
    (hf : ∀ i ∈ s, HasRationalComplexCoordinates (f i)) :
    HasRationalComplexCoordinates (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem finset_prod {ι : Type*} {s : Finset ι} {f : ι → ℂ}
    (hf : ∀ i ∈ s, HasRationalComplexCoordinates (f i)) :
    HasRationalComplexCoordinates (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem fintype_sum {ι : Type*} [Fintype ι] {f : ι → ℂ}
    (hf : ∀ i, HasRationalComplexCoordinates (f i)) :
    HasRationalComplexCoordinates (∑ i, f i) :=
  finset_sum fun i _ ↦ hf i

theorem fintype_prod {ι : Type*} [Fintype ι] {f : ι → ℂ}
    (hf : ∀ i, HasRationalComplexCoordinates (f i)) :
    HasRationalComplexCoordinates (∏ i, f i) :=
  finset_prod fun i _ ↦ hf i

end HasRationalComplexCoordinates

end TNLean.MPS.AreaLaw
