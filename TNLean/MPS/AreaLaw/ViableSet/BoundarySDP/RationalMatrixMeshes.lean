/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalMatrixCodes

/-!
# Rational matrix meshes and isometry approximation

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- A natural radius which dominates a prescribed nonnegative real entry bound. -/
noncomputable def rationalMatrixGridRadius (R : ℝ) : ℕ := ⌈R⌉₊

/-- A natural denominator which gives coordinate error at most a prescribed positive
tolerance. -/
noncomputable def rationalMatrixGridOrder (δ : ℝ) : ℕ := ⌈1 / δ⌉₊

/-- A tolerance-driven matrix grid all of whose entries have rational real and
imaginary parts. -/
noncomputable def rationalBoundedMatrixGrid
    (ι : Type*) [Fintype ι] (R δ : ℝ) : Finset (Matrix ι ι ℂ) :=
  gaussianRationalMatrixGrid ι (rationalMatrixGridRadius R) (rationalMatrixGridOrder δ)

/-- Representation-preserving version of the tolerance-driven rational matrix grid. -/
noncomputable def rationalBoundedMatrixCodeGrid
    (ι : Type*) [Fintype ι] [DecidableEq ι] (R δ : ℝ) :
    Finset (RationalMatrixCode ι) :=
  rationalMatrixCodeGrid ι (rationalMatrixGridRadius R) (rationalMatrixGridOrder δ)

theorem rationalBoundedMatrixGrid_eq_image_decode
    (ι : Type*) [Fintype ι] [DecidableEq ι] (R δ : ℝ) :
    rationalBoundedMatrixGrid ι R δ =
      (rationalBoundedMatrixCodeGrid ι R δ).image RationalMatrixCode.decode := by
  exact gaussianRationalMatrixGrid_eq_image_decode ι _ _

/-- Uniform coordinate-height bound for the tolerance-driven rational matrix grid. -/
noncomputable def rationalBoundedMatrixGridHeight (R δ : ℝ) : ℕ :=
  let B := rationalMatrixGridRadius R
  let M := rationalMatrixGridOrder δ
  2 * (B + 1) * ((2 * B * M + 1) * (M + 1))

/-- At radius one and dyadic mesh `2⁻ᵗ`, the rational grid radius and denominator have
their expected exact values. -/
theorem rationalMatrixGridRadius_one : rationalMatrixGridRadius 1 = 1 := by
  simp [rationalMatrixGridRadius]

theorem rationalMatrixGridOrder_inv_two_pow (t : ℕ) :
    rationalMatrixGridOrder ((2 ^ t : ℝ)⁻¹) = 2 ^ t := by
  rw [rationalMatrixGridOrder, one_div, inv_inv]
  exact_mod_cast Nat.ceil_natCast (2 ^ t)

/-- Any mesh at least `2⁻ᵗ` needs denominator order at most `2ᵗ`. -/
theorem rationalMatrixGridOrder_le_two_pow {δ : ℝ} (t : ℕ)
    (hδ : (2 ^ t : ℝ)⁻¹ ≤ δ) :
    rationalMatrixGridOrder δ ≤ 2 ^ t := by
  rw [rationalMatrixGridOrder, Nat.ceil_le]
  have hpow : (0 : ℝ) < 2 ^ t := by positivity
  have hinv : (0 : ℝ) < (2 ^ t : ℝ)⁻¹ := inv_pos.mpr hpow
  calc
    1 / δ ≤ 1 / (2 ^ t : ℝ)⁻¹ := one_div_le_one_div_of_le hinv hδ
    _ = (2 ^ t : ℕ) := by simp

/-- The canonical positive rational tolerance below a dyadic target has denominator
order exactly one larger than that dyadic denominator. -/
theorem rationalPositiveToleranceOrder_inv_two_pow (t : ℕ) :
    rationalPositiveToleranceOrder ((2 ^ t : ℝ)⁻¹) = 2 ^ t + 1 := by
  change rationalMatrixGridOrder ((2 ^ t : ℝ)⁻¹) + 1 = 2 ^ t + 1
  rw [rationalMatrixGridOrder_inv_two_pow]

/-- The canonical rational tolerance below `2⁻ᵗ` has coordinate height at most
`2^(t+2)`. -/
theorem rationalPositiveTolerance_inv_two_pow_hasRationalCoordinatesOfHeight (t : ℕ) :
    HasRationalComplexCoordinatesOfHeight (2 ^ (t + 2))
      (rationalPositiveTolerance ((2 ^ t : ℝ)⁻¹) : ℂ) := by
  apply (rationalPositiveTolerance_hasRationalCoordinatesOfHeight
    ((2 ^ t : ℝ)⁻¹)).mono
  rw [rationalPositiveToleranceOrder_inv_two_pow, pow_add]
  have ht : 1 ≤ 2 ^ t := one_le_pow₀ (by omega)
  norm_num
  omega

/-- The explicit coordinate height at dyadic mesh `2⁻ᵗ` is at most `2^(2t+5)`.
Thus its binary logarithm grows linearly with the requested precision. -/
theorem rationalBoundedMatrixGridHeight_one_inv_two_pow_le (t : ℕ) :
    rationalBoundedMatrixGridHeight 1 ((2 ^ t : ℝ)⁻¹) ≤ 2 ^ (2 * t + 5) := by
  rw [rationalBoundedMatrixGridHeight, rationalMatrixGridRadius_one,
    rationalMatrixGridOrder_inv_two_pow]
  have hx : 1 ≤ 2 ^ t := one_le_pow₀ (by omega)
  calc
    2 * (1 + 1) * ((2 * 1 * 2 ^ t + 1) * (2 ^ t + 1)) ≤
        32 * (2 ^ t) ^ 2 := by nlinarith
    _ = 2 ^ (2 * t + 5) := by
      rw [← pow_mul, Nat.mul_comm t 2, pow_add]
      norm_num
      ac_rfl

/-- A real entry bound below `2^u` has natural grid radius at most `2^u`. -/
theorem rationalMatrixGridRadius_le_two_pow {R : ℝ} {u : ℕ}
    (hR : R ≤ (2 ^ u : ℕ)) : rationalMatrixGridRadius R ≤ 2 ^ u := by
  rw [rationalMatrixGridRadius, Nat.ceil_le]
  exact hR

/-- For entries of radius at most `2^u` and dyadic mesh `2⁻ᵗ`, the explicit rational
grid height is at most `2^(2u+2t+5)`. -/
theorem rationalBoundedMatrixGridHeight_inv_two_pow_le
    {R : ℝ} {u : ℕ} (hR : R ≤ (2 ^ u : ℕ)) (t : ℕ) :
    rationalBoundedMatrixGridHeight R ((2 ^ t : ℝ)⁻¹) ≤
      2 ^ (2 * u + 2 * t + 5) := by
  rw [rationalBoundedMatrixGridHeight, rationalMatrixGridOrder_inv_two_pow]
  let B := rationalMatrixGridRadius R
  let U := 2 ^ u
  let M := 2 ^ t
  have hB : B ≤ U := rationalMatrixGridRadius_le_two_pow hR
  have hU : 1 ≤ U := one_le_pow₀ (by omega)
  have hM : 1 ≤ M := one_le_pow₀ (by omega)
  have hUadd : U + 1 ≤ 2 * U := by omega
  have hUMadd : 2 * U * M + 1 ≤ 3 * U * M := by nlinarith
  have hMadd : M + 1 ≤ 2 * M := by omega
  calc
    2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) ≤
        2 * (U + 1) * ((2 * U * M + 1) * (M + 1)) := by gcongr
    _ ≤ 2 * (2 * U) * ((3 * U * M) * (2 * M)) := by gcongr
    _ = 24 * U ^ 2 * M ^ 2 := by ring
    _ ≤ 32 * U ^ 2 * M ^ 2 := by gcongr; omega
    _ = 2 ^ (2 * u + 2 * t + 5) := by
      dsimp only [U, M]
      rw [← pow_mul, Nat.mul_comm u 2, ← pow_mul, Nat.mul_comm t 2]
      simp only [pow_add]
      norm_num
      ac_rfl

/-- A dyadic lower bound on an arbitrary positive mesh gives the same explicit height
bound as the exact dyadic mesh. -/
theorem rationalBoundedMatrixGridHeight_le_two_pow_of_inv_two_pow_le
    {R δ : ℝ} {u : ℕ} (hR : R ≤ (2 ^ u : ℕ)) (t : ℕ)
    (hδ : (2 ^ t : ℝ)⁻¹ ≤ δ) :
    rationalBoundedMatrixGridHeight R δ ≤ 2 ^ (2 * u + 2 * t + 5) := by
  rw [rationalBoundedMatrixGridHeight]
  let B := rationalMatrixGridRadius R
  let U := 2 ^ u
  let M := rationalMatrixGridOrder δ
  let V := 2 ^ t
  have hB : B ≤ U := rationalMatrixGridRadius_le_two_pow hR
  have hM : M ≤ V := rationalMatrixGridOrder_le_two_pow t hδ
  have hU : 1 ≤ U := one_le_pow₀ (by omega)
  have hV : 1 ≤ V := one_le_pow₀ (by omega)
  have hUadd : U + 1 ≤ 2 * U := by omega
  have hUVadd : 2 * U * V + 1 ≤ 3 * U * V := by nlinarith
  have hVadd : V + 1 ≤ 2 * V := by omega
  calc
    2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) ≤
        2 * (U + 1) * ((2 * U * V + 1) * (V + 1)) := by gcongr
    _ ≤ 2 * (2 * U) * ((3 * U * V) * (2 * V)) := by gcongr
    _ = 24 * U ^ 2 * V ^ 2 := by ring
    _ ≤ 32 * U ^ 2 * V ^ 2 := by gcongr; omega
    _ = 2 ^ (2 * u + 2 * t + 5) := by
      dsimp only [U, V]
      rw [← pow_mul, Nat.mul_comm u 2, ← pow_mul, Nat.mul_comm t 2]
      simp only [pow_add]
      norm_num
      ac_rfl

theorem rationalBoundedMatrixGrid_hasRationalEntriesOfHeight
    {ι : Type*} [Fintype ι] {R δ : ℝ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ rationalBoundedMatrixGrid ι R δ) :
    Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight R δ) Q := by
  exact gaussianRationalMatrixGrid_hasRationalEntriesOfHeight hQ

theorem rationalMatrixGridOrder_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < rationalMatrixGridOrder δ := by
  rw [rationalMatrixGridOrder]
  exact Nat.ceil_pos.mpr (div_pos zero_lt_one hδ)

/-- The tolerance-driven rational grid has an explicit integer-coordinate cardinality
bound. -/
theorem rationalBoundedMatrixGrid_card_le
    {ι : Type*} [Fintype ι] (R δ : ℝ) :
    (rationalBoundedMatrixGrid ι R δ).card ≤
      (2 * rationalMatrixGridRadius R * rationalMatrixGridOrder δ + 1) ^
        (2 * Fintype.card ι ^ 2) :=
  gaussianRationalMatrixGrid_card_le _ _

/-- Every matrix with entry bound `R` has a Gaussian-rational approximation at
entrywise error `δ`. -/
theorem exists_mem_rationalBoundedMatrixGrid
    {ι : Type*} [Fintype ι] {R δ : ℝ} (hδ : 0 < δ)
    (A : Matrix ι ι ℂ) (hA : ∀ i j, ‖A i j‖ ≤ R) :
    ∃ Q ∈ rationalBoundedMatrixGrid ι R δ,
      (∀ i j, ∃ x y : ℚ, Q i j = ⟨(x : ℝ), (y : ℝ)⟩) ∧
      ∀ i j, ‖(A - Q) i j‖ ≤ δ := by
  let B := rationalMatrixGridRadius R
  let M := rationalMatrixGridOrder δ
  have hM : 0 < M := rationalMatrixGridOrder_pos hδ
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hRB : R ≤ B := Nat.le_ceil R
  have hentry : ∀ i j, ‖A i j‖ ≤ B := fun i j ↦ (hA i j).trans hRB
  have hratio : 1 / δ ≤ M := Nat.le_ceil _
  have hround : 1 / (M : ℝ) ≤ δ := by
    rw [div_le_iff₀ hMreal]
    have := (div_le_iff₀ hδ).mp hratio
    nlinarith
  obtain ⟨Q, hQ, hclose⟩ := exists_mem_gaussianRationalMatrixGrid hM A hentry
  refine ⟨Q, hQ, fun i j ↦ gaussianRationalMatrixGrid_entry hQ i j,
    fun i j ↦ (hclose i j).trans hround⟩

/-- Every bounded rectangular complex matrix has an entrywise Gaussian-rational
approximation with the same explicit coordinate-height bound as the square grid on
the disjoint union of its row and column indices. -/
theorem exists_rational_rectangular_approximation
    {m n : Type*} [Finite m] [Finite n] {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (A : Matrix m n ℂ) (hA : ∀ i j, ‖A i j‖ ≤ R) :
    ∃ Q : Matrix m n ℂ,
      Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight R δ) Q ∧
      ∀ i j, ‖(A - Q) i j‖ ≤ δ := by
  classical
  let _ := Fintype.ofFinite m
  let _ := Fintype.ofFinite n
  let A' : Matrix (m ⊕ n) (m ⊕ n) ℂ := fun i j ↦
    match i, j with
    | Sum.inl i, Sum.inr j => A i j
    | _, _ => 0
  have hA' : ∀ i j, ‖A' i j‖ ≤ R := by
    intro i j
    cases i <;> cases j <;> simp only [A']
    · simpa using hR
    · exact hA _ _
    · simpa using hR
    · simpa using hR
  obtain ⟨Q', hQ', _hQ'rat, hclose⟩ :=
    exists_mem_rationalBoundedMatrixGrid hδ A' hA'
  let Q : Matrix m n ℂ := fun i j ↦ Q' (Sum.inl i) (Sum.inr j)
  refine ⟨Q, ?_, ?_⟩
  · intro i j
    exact rationalBoundedMatrixGrid_hasRationalEntriesOfHeight hQ' (Sum.inl i) (Sum.inr j)
  · intro i j
    have hij := hclose (Sum.inl i) (Sum.inr j)
    change ‖A i j - Q' (Sum.inl i) (Sum.inr j)‖ ≤ δ at hij
    change ‖A i j - Q i j‖ ≤ δ
    exact hij

/-- A rectangular matrix with entry radius at most `2^u` has a dyadic rational
approximation at mesh `2⁻ᵗ` whose common coordinate height is at most
`2^(2u+2t+5)`. -/
theorem exists_dyadic_rational_rectangular_approximation
    {m n : Type*} [Finite m] [Finite n] {R : ℝ} {u t : ℕ}
    (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (A : Matrix m n ℂ) (hA : ∀ i j, ‖A i j‖ ≤ R) :
    ∃ Q : Matrix m n ℂ,
      Matrix.HasRationalEntriesOfHeight (2 ^ (2 * u + 2 * t + 5)) Q ∧
      ∀ i j, ‖(A - Q) i j‖ ≤ (2 ^ t : ℝ)⁻¹ := by
  have ht : 0 < (2 ^ t : ℝ) := by positivity
  obtain ⟨Q, hQ, hclose⟩ := exists_rational_rectangular_approximation
    (δ := (2 ^ t : ℝ)⁻¹) hR0 (inv_pos.mpr ht) A hA
  exact ⟨Q, hQ.mono (rationalBoundedMatrixGridHeight_inv_two_pow_le hR t), hclose⟩

/-- A bounded finite family of complex numbers admits simultaneous dyadic
approximation with an explicit common coordinate-height bound. -/
theorem exists_dyadic_rational_pi_approximation
    {ι : Type*} [Finite ι] {R : ℝ} {u t : ℕ}
    (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ R) :
    ∃ g : ι → ℂ,
      (∀ i, HasRationalComplexCoordinatesOfHeight (2 ^ (2 * u + 2 * t + 5)) (g i)) ∧
      ∀ i, ‖f i - g i‖ ≤ (2 ^ t : ℝ)⁻¹ := by
  let A : Matrix ι Unit ℂ := fun i _ ↦ f i
  obtain ⟨Q, hQ, hclose⟩ :=
    exists_dyadic_rational_rectangular_approximation hR0 hR A
      (fun i _ ↦ hf i)
  let g : ι → ℂ := fun i ↦ Q i ()
  refine ⟨g, fun i ↦ hQ i (), fun i ↦ ?_⟩
  have hi := hclose i ()
  change ‖f i - Q i ()‖ ≤ (2 ^ t : ℝ)⁻¹ at hi
  exact hi

/-- Perturbing every factor of a finite complex product by at most `δ`, while the
reference factors have norm at most one, changes the product by at most
`(1 + δ)^|s| - 1`. -/
theorem norm_finset_prod_sub_prod_le_one
    {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ 1)
    (hclose : ∀ i ∈ s, ‖f i - g i‖ ≤ δ) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ (1 + δ) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hga := hg a (Finset.mem_insert_self a s)
      have hca := hclose a (Finset.mem_insert_self a s)
      have hgs : ∀ i ∈ s, ‖g i‖ ≤ 1 :=
        fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
      have hcs : ∀ i ∈ s, ‖f i - g i‖ ≤ δ :=
        fun i hi ↦ hclose i (Finset.mem_insert_of_mem hi)
      have hfs : ‖∏ i ∈ s, f i‖ ≤ (1 + δ) ^ s.card := by
        calc
          ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := Finset.norm_prod_le _ _
          _ ≤ ∏ _i ∈ s, (1 + δ) := by
            apply Finset.prod_le_prod₀ (fun i _hi ↦ norm_nonneg (f i))
            intro i hi
            change ‖f i‖ ≤ 1 + δ
            calc
              ‖f i‖ = ‖(f i - g i) + g i‖ := by ring_nf
              _ ≤ ‖f i - g i‖ + ‖g i‖ := norm_add_le _ _
              _ ≤ δ + 1 := add_le_add (hcs i hi) (hgs i hi)
              _ = 1 + δ := by ring
          _ = (1 + δ) ^ s.card := by simp
      have hih := ih hgs hcs
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      calc
        ‖f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i‖ =
            ‖(f a - g a) * (∏ i ∈ s, f i) +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := by
                congr 1
                ring
        _ ≤ ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ +
            ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := by
              exact (norm_add_le _ _).trans
                (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ δ * (1 + δ) ^ s.card + 1 * ((1 + δ) ^ s.card - 1) := by
              gcongr
        _ = (1 + δ) ^ (s.card + 1) - 1 := by
              rw [pow_succ]
              ring

/-- A uniform coordinate bound gives the coarse `ℓ² ≤ ℓ¹` estimate for a
finite `PiLp 2` space. -/
theorem PiLp.norm_le_card_mul_of_forall_norm_le
    {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)]
    (x : PiLp 2 β) {C : ℝ} (hC : 0 ≤ C) (hx : ∀ i, ‖x i‖ ≤ C) :
    ‖x‖ ≤ (Fintype.card ι : ℝ) * C := by
  have hsq := PiLp.norm_sq_eq_of_L2 β x
  have hsum : ∑ i : ι, ‖x i‖ ^ 2 ≤ ∑ _i : ι, C ^ 2 := by
    apply Finset.sum_le_sum
    intro i _hi
    exact (sq_le_sq₀ (norm_nonneg _) hC).2 (hx i)
  have hcard : (∑ _i : ι, C ^ 2) = (Fintype.card ι : ℝ) * C ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard0 : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hnorm0 : 0 ≤ ‖x‖ := norm_nonneg _
  rw [hcard] at hsum
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      have hcardzero : Fintype.card ι = 0 := Fintype.card_eq_zero
      rw [hcardzero]
      simp only [Nat.cast_zero, zero_mul]
      have hxzero : ‖x‖ ^ 2 = 0 := by simpa using hsq
      nlinarith
  | inr hι =>
      have hcard1 : (1 : ℝ) ≤ Fintype.card ι := by
        exact_mod_cast Fintype.card_pos
      have hcard_sq : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by
        nlinarith
      have hmul : (Fintype.card ι : ℝ) * C ^ 2 ≤
          (Fintype.card ι : ℝ) ^ 2 * C ^ 2 :=
        mul_le_mul_of_nonneg_right hcard_sq (sq_nonneg C)
      have hsquares : ‖x‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * C) ^ 2 := by
        calc
          ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := hsq
          _ ≤ (Fintype.card ι : ℝ) * C ^ 2 := hsum
          _ ≤ (Fintype.card ι : ℝ) ^ 2 * C ^ 2 := hmul
          _ = ((Fintype.card ι : ℝ) * C) ^ 2 := by ring
      exact (sq_le_sq₀ hnorm0 (mul_nonneg hcard0 hC)).1 hsquares

/-- Every entry of a rectangular isometry has modulus at most one. -/
theorem norm_apply_le_one_of_conjTranspose_mul_self_eq_one
    {m n : Type*} [Fintype m] [DecidableEq n]
    (Z : Matrix m n ℂ) (hZ : Zᴴ * Z = 1) (i : m) (j : n) :
    ‖Z i j‖ ≤ 1 := by
  have hcol := Matrix.sum_star_mul_eq_ite_of_conjTranspose_mul_eq_one Z hZ j j
  have hsum : ∑ k, ‖Z k j‖ ^ 2 = 1 := by
    simp_rw [← Complex.normSq_eq_norm_sq]
    have hre := congrArg Complex.re hcol
    simpa only [ite_true, Complex.re_sum, Complex.star_def, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add, Complex.one_re,
      Complex.normSq_apply] using hre
  have hentry : ‖Z i j‖ ^ 2 ≤ ∑ k, ‖Z k j‖ ^ 2 :=
    Finset.single_le_sum (f := fun k ↦ ‖Z k j‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  rw [hsum] at hentry
  nlinarith [norm_nonneg (Z i j)]

/-- Every entry of a family of rectangular matrices whose stacked columns are
orthonormal has modulus at most one. -/
theorem norm_apply_le_one_of_sum_conjTranspose_mul_eq_one
    {d m n : Type*} [Fintype d] [Fintype m] [DecidableEq n]
    (A : d → Matrix m n ℂ) (hA : ∑ i, (A i)ᴴ * A i = 1)
    (i : d) (a : m) (c : n) :
    ‖A i a c‖ ≤ 1 := by
  let Z : Matrix (d × m) n ℂ := fun ia c ↦ A ia.1 ia.2 c
  have hZ : Zᴴ * Z = 1 := by
    ext c c'
    have hentry := congrArg (fun M : Matrix n n ℂ ↦ M c c') hA
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] at hentry ⊢
    rw [Fintype.sum_prod_type]
    exact hentry
  exact norm_apply_le_one_of_conjTranspose_mul_self_eq_one Z hZ (i, a) c

/-- A rectangular isometry admits a Gaussian-rational entrywise approximation at
every positive tolerance, with an explicit coordinate-height bound.  The approximating
matrix is not required to remain an exact isometry. -/
theorem exists_rational_isometry_approximation
    {m n : Type*} [Fintype m] [Finite n] [DecidableEq n] {δ : ℝ} (hδ : 0 < δ)
    (Z : Matrix m n ℂ) (hZ : Zᴴ * Z = 1) :
    ∃ Q : Matrix m n ℂ,
      Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight 1 δ) Q ∧
      ∀ i j, ‖(Z - Q) i j‖ ≤ δ :=
  exists_rational_rectangular_approximation zero_le_one hδ Z
    (norm_apply_le_one_of_conjTranspose_mul_self_eq_one Z hZ)

/-- Rational approximation of the coordinate isometry produces rational fixed data
for the compressed LVV boundary test, at the cost of the displayed entrywise residual
allowance.  This is the support-compressed boundary constraint of LVV13,
`algo53.tex`, lines 472--476. -/
theorem exists_rational_coordinate_map_with_boundary_residual
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (A : Matrix (Fin n) (Fin n) ℂ) (X P N : Matrix (s × b) (s × b) ℂ)
    {C δ ζ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hA : ∀ i j, ‖A i j‖ ≤ C)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ) :
    ∃ Q : Matrix ((a × s) × b) (Fin n) ℂ,
      Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight 1 δ) Q ∧
      ∀ i j, ‖((compressedBoundaryLM Q A - X) - (P - N)) i j‖ ≤
        ζ + Fintype.card a * (n : ℝ) ^ 2 * δ * C * (2 + δ) := by
  obtain ⟨Q, hQrat, hclose⟩ := exists_rational_isometry_approximation hδ Z hZ
  refine ⟨Q, hQrat, ?_⟩
  intro i j
  exact (compressedBoundaryResidual_entry_norm_le_of_coordinate_approximation
      Z Q A X P N zero_le_one hC hδ.le
        (norm_apply_le_one_of_conjTranspose_mul_self_eq_one Z hZ) hA hclose hresidual i j
    ).trans_eq (by ring)

/-- A positive coordinate-map mesh whose induced boundary error is at most the
prescribed positive allowance when the tested density entries have modulus at most
one. -/
noncomputable def rationalCoordinateMapTolerance (a n : ℕ) (ω : ℝ) : ℝ :=
  min 1 (ω / (3 * ((a : ℝ) * (n : ℝ) ^ 2 + 1)))

theorem rationalCoordinateMapTolerance_pos (a n : ℕ) {ω : ℝ} (hω : 0 < ω) :
    0 < rationalCoordinateMapTolerance a n ω := by
  apply lt_min zero_lt_one
  exact div_pos hω (mul_pos (by norm_num) (by positivity))

theorem rationalCoordinateMapTolerance_boundary_error_le
    (a n : ℕ) {ω : ℝ} (hω : 0 < ω) :
    (a : ℝ) * (n : ℝ) ^ 2 * rationalCoordinateMapTolerance a n ω *
        (2 + rationalCoordinateMapTolerance a n ω) ≤ ω := by
  let D : ℝ := (a : ℝ) * (n : ℝ) ^ 2
  let δ := rationalCoordinateMapTolerance a n ω
  have hD : 0 ≤ D := by positivity
  have hδ : 0 ≤ δ := (rationalCoordinateMapTolerance_pos a n hω).le
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδq : δ ≤ ω / (3 * (D + 1)) := min_le_right _ _
  have hden : 0 < 3 * (D + 1) := mul_pos (by norm_num) (by positivity)
  have hmain : 3 * (D + 1) * δ ≤ ω := by
    simpa only [mul_comm] using (le_div_iff₀ hden).mp hδq
  dsimp only [D, δ] at hmain hD hδ hδ1 ⊢
  nlinarith

/-- Coordinate-map mesh chosen so that the full boundary trace-norm perturbation,
rather than merely each entry, is at most `ω`. -/
noncomputable def rationalCoordinateMapTraceTolerance (a n r : ℕ) (ω : ℝ) : ℝ :=
  rationalCoordinateMapTolerance a n (ω / ((r : ℝ) ^ 2 + 1))

theorem rationalCoordinateMapTraceTolerance_pos (a n r : ℕ) {ω : ℝ} (hω : 0 < ω) :
    0 < rationalCoordinateMapTraceTolerance a n r ω := by
  apply rationalCoordinateMapTolerance_pos
  exact div_pos hω (by positivity)

theorem rationalCoordinateMapTraceTolerance_boundary_error_le
    (a n r : ℕ) {ω : ℝ} (hω : 0 < ω) :
    (r : ℝ) ^ 2 * ((a : ℝ) * (n : ℝ) ^ 2 *
      rationalCoordinateMapTraceTolerance a n r ω *
        (2 + rationalCoordinateMapTraceTolerance a n r ω)) ≤ ω := by
  let D : ℝ := (r : ℝ) ^ 2
  have hD : 0 ≤ D := sq_nonneg _
  have hden : 0 < D + 1 := by positivity
  have hω' : 0 < ω / (D + 1) := div_pos hω hden
  have hbase := rationalCoordinateMapTolerance_boundary_error_le
    a n hω'
  have hquot : 0 ≤ ω / (D + 1) := hω'.le
  have hcancel : (D + 1) * (ω / (D + 1)) = ω := by
    field_simp
  dsimp only [rationalCoordinateMapTraceTolerance, D] at hbase hD hden hω' hquot hcancel ⊢
  nlinarith

/-- Trace-allowance mesh for matrices whose entries have modulus at most `C`. -/
noncomputable def rationalCoordinateMapTraceToleranceOfBound
    (a n r : ℕ) (C ω : ℝ) : ℝ :=
  min 1 (ω / (3 * ((r : ℝ) ^ 2 * (a : ℝ) * (n : ℝ) ^ 2 * C + 1)))

theorem rationalCoordinateMapTraceToleranceOfBound_pos
    (a n r : ℕ) {C ω : ℝ} (hC : 0 ≤ C) (hω : 0 < ω) :
    0 < rationalCoordinateMapTraceToleranceOfBound a n r C ω := by
  apply lt_min zero_lt_one
  apply div_pos hω
  exact mul_pos (by norm_num) (by positivity)

theorem rationalCoordinateMapTraceToleranceOfBound_boundary_error_le
    (a n r : ℕ) {C ω : ℝ} (hC : 0 ≤ C) (hω : 0 < ω) :
    (r : ℝ) ^ 2 * ((a : ℝ) * (n : ℝ) ^ 2 *
      rationalCoordinateMapTraceToleranceOfBound a n r C ω * C *
        (2 + rationalCoordinateMapTraceToleranceOfBound a n r C ω)) ≤ ω := by
  let D : ℝ := (r : ℝ) ^ 2 * (a : ℝ) * (n : ℝ) ^ 2 * C
  let θ := rationalCoordinateMapTraceToleranceOfBound a n r C ω
  have hD : 0 ≤ D := by positivity
  have hθ : 0 ≤ θ :=
    (rationalCoordinateMapTraceToleranceOfBound_pos a n r hC hω).le
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθq : θ ≤ ω / (3 * (D + 1)) := min_le_right _ _
  have hden : 0 < 3 * (D + 1) := mul_pos (by norm_num) (by positivity)
  have hmain : 3 * (D + 1) * θ ≤ ω := by
    simpa only [mul_comm] using (le_div_iff₀ hden).mp hθq
  dsimp only [D, θ] at hD hθ hθ1 hmain ⊢
  nlinarith

/-- At every positive allowance, the coordinate isometry may be replaced by rational
fixed data while enlarging every entrywise boundary residual by at most that allowance.
The rational height is the explicit height of the corresponding uniform grid. -/
theorem exists_rational_coordinate_map_with_boundary_allowance
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (A : Matrix (Fin n) (Fin n) ℂ) (X P N : Matrix (s × b) (s × b) ℂ)
    {ω ζ : ℝ} (hω : 0 < ω) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ) :
    let δ := rationalCoordinateMapTolerance (Fintype.card a) n ω
    ∃ Q : Matrix ((a × s) × b) (Fin n) ℂ,
      Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight 1 δ) Q ∧
      ∀ i j, ‖((compressedBoundaryLM Q A - X) - (P - N)) i j‖ ≤ ζ + ω := by
  dsimp only
  let δ := rationalCoordinateMapTolerance (Fintype.card a) n ω
  have hδ : 0 < δ := rationalCoordinateMapTolerance_pos _ _ hω
  obtain ⟨Q, hQrat, hQresidual⟩ :=
    exists_rational_coordinate_map_with_boundary_residual
      Z hZ A X P N zero_le_one hδ hA hresidual
  refine ⟨Q, hQrat, ?_⟩
  intro i j
  apply (hQresidual i j).trans
  simpa only [δ, mul_one, add_comm] using add_le_add_left
    (rationalCoordinateMapTolerance_boundary_error_le (Fintype.card a) n hω) ζ

/-- At every positive trace-norm allowance, the coordinate isometry may be replaced
by rational fixed data while enlarging the compressed boundary residual by at most
that allowance. -/
theorem exists_rational_coordinate_map_with_boundary_trace_allowance
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (A : Matrix (Fin n) (Fin n) ℂ) (X P N : Matrix (s × b) (s × b) ℂ)
    {ω ζ : ℝ} (hω : 0 < ω) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ ζ) :
    let r := Fintype.card (s × b)
    let θ := rationalCoordinateMapTraceTolerance (Fintype.card a) n r ω
    ∃ Q : Matrix ((a × s) × b) (Fin n) ℂ,
      Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight 1 θ) Q ∧
      rectangularTraceNorm ((compressedBoundaryLM Q A - X) - (P - N)) ≤ ζ + ω := by
  dsimp only
  let r := Fintype.card (s × b)
  let θ := rationalCoordinateMapTraceTolerance (Fintype.card a) n r ω
  have hθ : 0 < θ := rationalCoordinateMapTraceTolerance_pos _ _ _ hω
  obtain ⟨Q, hQrat, hclose⟩ := exists_rational_isometry_approximation hθ Z hZ
  refine ⟨Q, hQrat, ?_⟩
  apply (compressedBoundaryResidual_rectangularTraceNorm_le_of_coordinate_approximation
    Z Q A X P N zero_le_one zero_le_one hθ.le
      (norm_apply_le_one_of_conjTranspose_mul_self_eq_one Z hZ) hA hclose hresidual).trans
  have hbound := rationalCoordinateMapTraceTolerance_boundary_error_le
    (Fintype.card a) n (Fintype.card (s × b)) hω
  simpa only [r, θ, one_mul, mul_one, add_comm] using add_le_add_left hbound ζ

end TNLean.MPS.AreaLaw
