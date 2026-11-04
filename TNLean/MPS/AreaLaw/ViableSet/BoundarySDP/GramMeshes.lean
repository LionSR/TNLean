/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalMatrixMeshes

/-!
# Finite meshes for Hermitian matrices and Gram factors

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- An integer entry radius for a Gram factor whose squared entries are bounded by
`C`.  The added unit avoids square roots and gives a positive radius uniformly. -/
noncomputable def rationalGramCertificateRadius (C : ℝ) : ℕ :=
  ⌈C⌉₊ + 1

/-- A common rational denominator sufficient for entrywise Gram error `ζ`. -/
noncomputable def rationalGramCertificateOrder
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : ℕ :=
  ⌈(Fintype.card ι : ℝ) * (2 * rationalGramCertificateRadius C + 1) / ζ⌉₊

/-- The exact-coordinate Gram-certificate grid.  It uses no square roots and every
real and imaginary coordinate is rational. -/
noncomputable def rationalGramCertificateGrid
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : Finset (Matrix ι ι ℂ) :=
  gaussianRationalMatrixGrid ι (rationalGramCertificateRadius C)
    (rationalGramCertificateOrder ι C ζ)

/-- Representation-preserving rational Gram-factor grid. -/
noncomputable def rationalGramCertificateCodeGrid
    (ι : Type*) [Fintype ι] [DecidableEq ι] (C ζ : ℝ) :
    Finset (RationalMatrixCode ι) :=
  rationalMatrixCodeGrid ι (rationalGramCertificateRadius C)
    (rationalGramCertificateOrder ι C ζ)

theorem rationalGramCertificateGrid_eq_image_decode
    (ι : Type*) [Fintype ι] [DecidableEq ι] (C ζ : ℝ) :
    rationalGramCertificateGrid ι C ζ =
      (rationalGramCertificateCodeGrid ι C ζ).image RationalMatrixCode.decode := by
  exact gaussianRationalMatrixGrid_eq_image_decode ι _ _

theorem RationalMatrixCode.decode_mem_rationalGramCertificateGrid
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C ζ : ℝ}
    {f : RationalMatrixCode ι}
    (hf : f ∈ rationalGramCertificateCodeGrid ι C ζ) :
    f.decode ∈ rationalGramCertificateGrid ι C ζ := by
  rw [rationalGramCertificateGrid_eq_image_decode]
  exact Finset.mem_image.mpr ⟨f, hf, rfl⟩

theorem exists_code_of_mem_rationalGramCertificateGrid
    {ι : Type*} [Fintype ι] [DecidableEq ι] {C ζ : ℝ}
    {Q : Matrix ι ι ℂ} (hQ : Q ∈ rationalGramCertificateGrid ι C ζ) :
    ∃ f ∈ rationalGramCertificateCodeGrid ι C ζ, f.decode = Q := by
  rw [rationalGramCertificateGrid_eq_image_decode, Finset.mem_image] at hQ
  exact hQ

theorem rationalGramCertificateCodeGrid_card_eq
    (ι : Type*) [Fintype ι] [DecidableEq ι] (C ζ : ℝ) :
    (rationalGramCertificateCodeGrid ι C ζ).card =
      (rationalGramCertificateGrid ι C ζ).card := by
  classical
  have h := congrArg Finset.card (rationalGramCertificateGrid_eq_image_decode ι C ζ)
  rw [Finset.card_image_of_injective _ RationalMatrixCode.decode_injective] at h
  exact h.symm

/-- Uniform coordinate-height bound for the rational Gram-certificate grid. -/
noncomputable def rationalGramCertificateGridHeight
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : ℕ :=
  let B := rationalGramCertificateRadius C
  let M := rationalGramCertificateOrder ι C ζ
  2 * (B + 1) * ((2 * B * M + 1) * (M + 1))

theorem rationalGramCertificateGrid_hasRationalEntriesOfHeight
    {ι : Type*} [Fintype ι] {C ζ : ℝ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ rationalGramCertificateGrid ι C ζ) :
    Matrix.HasRationalEntriesOfHeight (rationalGramCertificateGridHeight ι C ζ) Q := by
  exact gaussianRationalMatrixGrid_hasRationalEntriesOfHeight hQ

theorem rationalGramCertificateOrder_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ} (hζ : 0 < ζ) :
    0 < rationalGramCertificateOrder ι C ζ := by
  rw [rationalGramCertificateOrder]
  apply Nat.ceil_pos.mpr
  positivity

/-- The rational Gram grid has the coordinate-count cardinality expected from its
integer radius and denominator. -/
theorem rationalGramCertificateGrid_card_le
    {ι : Type*} [Fintype ι] (C ζ : ℝ) :
    (rationalGramCertificateGrid ι C ζ).card ≤
      (2 * rationalGramCertificateRadius C * rationalGramCertificateOrder ι C ζ + 1) ^
        (2 * Fintype.card ι ^ 2) :=
  gaussianRationalMatrixGrid_card_le _ _

theorem rationalGramCertificateGrid_entry
    {ι : Type*} [Fintype ι] {C ζ : ℝ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ rationalGramCertificateGrid ι C ζ) :
    ∀ i j, ∃ x y : ℚ, Q i j = ⟨(x : ℝ), (y : ℝ)⟩ := by
  intro i j
  exact gaussianRationalMatrixGrid_entry hQ i j

/-- Every bounded Gram factor has a representative in the exact-coordinate rational
grid whose Gram matrix is entrywise `ζ`-close. -/
theorem exists_mem_rationalGramCertificateGrid
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ}
    (hζ : 0 < ζ) (R : Matrix ι ι ℂ)
    (hR : ∀ i j, ‖R i j‖ ^ 2 ≤ C) :
    ∃ Q ∈ rationalGramCertificateGrid ι C ζ,
      (∀ i j, ∃ x y : ℚ, Q i j = ⟨(x : ℝ), (y : ℝ)⟩) ∧
      ∀ i j, ‖(R * Rᴴ - Q * Qᴴ) i j‖ ≤ ζ := by
  let B := rationalGramCertificateRadius C
  let M := rationalGramCertificateOrder ι C ζ
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast Nat.zero_lt_succ (rationalMatrixGridRadius C)
  have hCB : C ≤ B := by
    dsimp only [B, rationalGramCertificateRadius]
    exact (Nat.le_ceil C).trans (by norm_num)
  have hBone : (1 : ℝ) ≤ B := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by
      exact_mod_cast hBpos))
  have hentry : ∀ i j, ‖R i j‖ ≤ B := by
    intro i j
    have hsq : ‖R i j‖ ^ 2 ≤ (B : ℝ) := (hR i j).trans hCB
    nlinarith [sq_nonneg (‖R i j‖ - B), norm_nonneg (R i j)]
  have hM : 0 < M := rationalGramCertificateOrder_pos hζ
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hδnonneg : 0 ≤ (1 : ℝ) / M := by positivity
  have hδone : (1 : ℝ) / M ≤ 1 := by
    rw [div_le_one hMreal]
    exact_mod_cast hM
  let D : ℝ := Fintype.card ι * (2 * (B : ℝ) + 1)
  have hDpos : 0 < D := by
    dsimp only [D]
    positivity
  have hratio : D / ζ ≤ M := by
    dsimp only [D, M, rationalGramCertificateOrder, B]
    exact Nat.le_ceil _
  have hDround : D * ((1 : ℝ) / M) ≤ ζ := by
    rw [one_div, ← div_eq_mul_inv, div_le_iff₀ hMreal]
    have := (div_le_iff₀ hζ).mp hratio
    nlinarith
  obtain ⟨Q, hQ, hclose⟩ := exists_mem_gaussianRationalMatrixGrid hM R hentry
  refine ⟨Q, hQ, fun i j ↦ gaussianRationalMatrixGrid_entry hQ i j, fun i j ↦ ?_⟩
  calc
    ‖(R * Rᴴ - Q * Qᴴ) i j‖ ≤
        Fintype.card ι * ((1 : ℝ) / M) * (2 * B + (1 : ℝ) / M) :=
      norm_gram_sub_apply_le_of_entry_norm_le R Q hBpos.le hδnonneg hentry hclose i j
    _ ≤ Fintype.card ι * ((1 : ℝ) / M) * (2 * B + 1) := by gcongr
    _ = D * ((1 : ℝ) / M) := by dsimp only [D]; ring
    _ ≤ ζ := hDround

/-- The explicit complex matrix grid obtained by choosing the real and imaginary parts
of every entry independently from `scaledRealGrid`. -/
noncomputable def complexMatrixGrid
    (ι : Type*) [Fintype ι] (M : ℕ) (R : ℝ) : Finset (Matrix ι ι ℂ) := by
  classical
  let toMat : (ι × ι → ℝ × ℝ) → Matrix ι ι ℂ := fun f ↦
    Matrix.of fun i j ↦ ⟨(f (i, j)).1, (f (i, j)).2⟩
  exact (Fintype.piFinset fun _ : ι × ι ↦ scaledRealGrid M R ×ˢ scaledRealGrid M R).image toMat

/-- A point of `[-1,1]` is within `1/(2M)` of the explicit unit grid when `M>0`. -/
theorem exists_mem_unitRealGrid {M : ℕ} (hM : 0 < M) {t : ℝ} (ht : |t| ≤ 1) :
    ∃ g ∈ unitRealGrid M, |t - g| ≤ 1 / (2 * M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  set y := (t + 1) * M + 1 / 2 with hy
  have hy0 : 0 ≤ y := by rw [hy]; nlinarith
  refine ⟨-1 + (⌊y⌋₊ : ℝ) / M, ?_, ?_⟩
  · rw [unitRealGrid, Finset.mem_image]
    refine ⟨⌊y⌋₊, ?_, rfl⟩
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hylt : y < 2 * M + 1 := by rw [hy]; nlinarith
    have := Nat.floor_lt hy0 |>.mpr (by exact_mod_cast hylt)
    omega
  · have hfl := Nat.floor_le hy0
    have hlt := Nat.lt_floor_add_one y
    rw [abs_le]
    constructor
    · rw [show t - (-1 + (⌊y⌋₊ : ℝ) / M) =
          ((t + 1) * M - ⌊y⌋₊) / M by field_simp; ring,
        le_div_iff₀ hM']
      field_simp
      nlinarith
    · rw [show t - (-1 + (⌊y⌋₊ : ℝ) / M) =
          ((t + 1) * M - ⌊y⌋₊) / M by field_simp; ring,
        div_le_iff₀ hM']
      field_simp
      nlinarith

/-- A point of `[-R,R]` is within `R/(2M)` of the explicit scaled grid. -/
theorem exists_mem_scaledRealGrid {M : ℕ} (hM : 0 < M) {R t : ℝ}
    (hR : 0 < R) (ht : |t| ≤ R) :
    ∃ g ∈ scaledRealGrid M R, |t - g| ≤ R / (2 * M) := by
  have hscaled : |t / R| ≤ 1 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_le_one hR).2 ht
  obtain ⟨g, hg, hclose⟩ := exists_mem_unitRealGrid hM hscaled
  refine ⟨R * g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, ?_⟩
  rw [show t - R * g = R * (t / R - g) by field_simp, abs_mul, abs_of_pos hR]
  calc
    R * |t / R - g| ≤ R * (1 / (2 * M)) := mul_le_mul_of_nonneg_left hclose hR.le
    _ = R / (2 * M) := by ring

/-- The explicit complex matrix grid has at most `(2M+1)^(2d²)` elements. -/
theorem complexMatrixGrid_card_le
    {ι : Type*} [Fintype ι] (M : ℕ) (R : ℝ) :
    (complexMatrixGrid ι M R).card ≤
      (2 * M + 1) ^ (2 * Fintype.card ι ^ 2) := by
  classical
  let G := scaledRealGrid M R
  let toMat : (ι × ι → ℝ × ℝ) → Matrix ι ι ℂ := fun f ↦
    Matrix.of fun i j ↦ ⟨(f (i, j)).1, (f (i, j)).2⟩
  have hunit : (unitRealGrid M).card ≤ 2 * M + 1 :=
    Finset.card_image_le.trans (Finset.card_range _).le
  have hG : G.card ≤ 2 * M + 1 := Finset.card_image_le.trans hunit
  change ((Fintype.piFinset fun _ : ι × ι ↦ G ×ˢ G).image toMat).card ≤ _
  refine Finset.card_image_le.trans ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Finset.card_product]
  calc
    (G.card * G.card) ^ (Fintype.card ι * Fintype.card ι) ≤
        ((2 * M + 1) * (2 * M + 1)) ^
          (Fintype.card ι * Fintype.card ι) :=
      Nat.pow_le_pow_left (Nat.mul_le_mul hG hG) _
    _ = (2 * M + 1) ^ (2 * Fintype.card ι ^ 2) := by
      rw [← sq, ← pow_mul, sq]

/-- Every matrix whose entries have norm at most `R` has a representative in the
explicit coordinate grid with entrywise error at most `R/M`. -/
theorem exists_mem_complexMatrixGrid
    {ι : Type*} [Fintype ι] {M : ℕ} (hM : 0 < M) {R : ℝ} (hR : 0 < R)
    (A : Matrix ι ι ℂ) (hA : ∀ i j, ‖A i j‖ ≤ R) :
    ∃ Q ∈ complexMatrixGrid ι M R, ∀ i j, ‖(A - Q) i j‖ ≤ R / M := by
  classical
  choose gre hgre hgreClose using fun i j ↦ exists_mem_scaledRealGrid hM hR
    ((Complex.abs_re_le_norm (A i j)).trans (hA i j))
  choose gim hgim hgimClose using fun i j ↦ exists_mem_scaledRealGrid hM hR
    ((Complex.abs_im_le_norm (A i j)).trans (hA i j))
  let f : ι × ι → ℝ × ℝ := fun ij ↦ (gre ij.1 ij.2, gim ij.1 ij.2)
  let Q : Matrix ι ι ℂ := Matrix.of fun i j ↦ ⟨(f (i, j)).1, (f (i, j)).2⟩
  refine ⟨Q, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨f, Fintype.mem_piFinset.mpr fun ij ↦
      Finset.mem_product.mpr ⟨hgre ij.1 ij.2, hgim ij.1 ij.2⟩, rfl⟩
  · intro i j
    calc
      ‖(A - Q) i j‖ ≤ |(A i j).re - gre i j| + |(A i j).im - gim i j| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ R / (2 * M) + R / (2 * M) :=
        add_le_add (hgreClose i j) (hgimClose i j)
      _ = R / M := by field_simp; ring

/-- The integer coordinate-grid order needed for entrywise tolerance `δ` on matrices
whose entries have norm at most `R`. -/
noncomputable def boundedMatrixGridOrder (R δ : ℝ) : ℕ := ⌈R / δ⌉₊

/-- The concrete coordinate grid for matrices with entry bound `R` and entrywise
approximation tolerance `δ`. -/
noncomputable def boundedMatrixGrid
    (ι : Type*) [Fintype ι] (R δ : ℝ) : Finset (Matrix ι ι ℂ) :=
  complexMatrixGrid ι (boundedMatrixGridOrder R δ) R

/-- The bounded-matrix coordinate-grid order is positive for positive radius and
tolerance. -/
theorem boundedMatrixGridOrder_pos {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    0 < boundedMatrixGridOrder R δ := by
  rw [boundedMatrixGridOrder]
  exact Nat.ceil_pos.mpr (div_pos hR hδ)

/-- The concrete bounded-matrix grid has the expected coordinate-count cardinality. -/
theorem boundedMatrixGrid_card_le
    {ι : Type*} [Fintype ι] (R δ : ℝ) :
    (boundedMatrixGrid ι R δ).card ≤
      (2 * boundedMatrixGridOrder R δ + 1) ^
        (2 * Fintype.card ι ^ 2) :=
  complexMatrixGrid_card_le _ _

/-- Every matrix with entry bound `R` has an entrywise `δ`-approximation in the
concrete bounded-matrix grid. -/
theorem exists_mem_boundedMatrixGrid
    {ι : Type*} [Fintype ι] {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (A : Matrix ι ι ℂ) (hA : ∀ i j, ‖A i j‖ ≤ R) :
    ∃ Q ∈ boundedMatrixGrid ι R δ, ∀ i j, ‖(A - Q) i j‖ ≤ δ := by
  let M := boundedMatrixGridOrder R δ
  have hM : 0 < M := boundedMatrixGridOrder_pos hR hδ
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hratio : R / δ ≤ M := Nat.le_ceil _
  have hround : R / M ≤ δ := by
    rw [div_le_iff₀ hMreal]
    have := (div_le_iff₀ hδ).mp hratio
    nlinarith
  obtain ⟨Q, hQ, hclose⟩ := exists_mem_complexMatrixGrid hM hR A hA
  exact ⟨Q, hQ, fun i j ↦ (hclose i j).trans hround⟩

/-- The concrete Hermitian grid obtained by taking Hermitian parts of the bounded
coordinate grid. -/
noncomputable def hermitianBoundedMatrixGrid
    (ι : Type*) [Fintype ι] (R δ : ℝ) : Finset (Matrix ι ι ℂ) := by
  classical
  exact (boundedMatrixGrid ι R δ).image matrixHermitianPart

/-- Taking Hermitian parts cannot increase the grid cardinality. -/
theorem hermitianBoundedMatrixGrid_card_le
    {ι : Type*} [Fintype ι] (R δ : ℝ) :
    (hermitianBoundedMatrixGrid ι R δ).card ≤
      (2 * boundedMatrixGridOrder R δ + 1) ^
        (2 * Fintype.card ι ^ 2) := by
  classical
  exact Finset.card_image_le.trans (boundedMatrixGrid_card_le R δ)

/-- Every member of the Hermitian bounded-matrix grid is Hermitian. -/
theorem matrixHermitianPart_mem_hermitianBoundedMatrixGrid
    {ι : Type*} [Fintype ι] {R δ : ℝ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ boundedMatrixGrid ι R δ) :
    matrixHermitianPart Q ∈ hermitianBoundedMatrixGrid ι R δ := by
  classical
  exact Finset.mem_image.mpr ⟨Q, hQ, rfl⟩

/-- Hermitian projection preserves an entrywise approximation to a Hermitian target,
without enlarging its tolerance. -/
theorem norm_sub_matrixHermitianPart_apply_le
    {ι : Type*} [Fintype ι] {A Q : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {δ : ℝ} (hclose : ∀ i j, ‖(A - Q) i j‖ ≤ δ) (i j : ι) :
    ‖(A - matrixHermitianPart Q) i j‖ ≤ δ := by
  have hid : A - matrixHermitianPart Q =
      ((2 : ℂ)⁻¹) • ((A - Q) + (A - Q)ᴴ) := by
    rw [matrixHermitianPart, Matrix.conjTranspose_sub, hA.eq]
    module
  rw [hid, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, norm_smul,
    norm_inv]
  have htwo : ‖(2 : ℂ)‖⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [htwo]
  calc
    (2 : ℝ)⁻¹ * ‖(A - Q) i j + star ((A - Q) j i)‖ ≤
        (2 : ℝ)⁻¹ * (‖(A - Q) i j‖ + ‖star ((A - Q) j i)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (2 : ℝ)⁻¹ * (δ + δ) := by
      gcongr
      · exact hclose i j
      · rw [norm_star]
        exact hclose j i
    _ = δ := by ring

/-- Every Hermitian matrix with entry bound `R` has a Hermitian entrywise
`δ`-approximation in the concrete Hermitian grid. -/
theorem exists_mem_hermitianBoundedMatrixGrid
    {ι : Type*} [Fintype ι] {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (A : Matrix ι ι ℂ) (hAHerm : A.IsHermitian)
    (hA : ∀ i j, ‖A i j‖ ≤ R) :
    ∃ Q ∈ hermitianBoundedMatrixGrid ι R δ,
      Q.IsHermitian ∧ ∀ i j, ‖(A - Q) i j‖ ≤ δ := by
  obtain ⟨Q, hQ, hclose⟩ := exists_mem_boundedMatrixGrid hR hδ A hA
  exact ⟨matrixHermitianPart Q, matrixHermitianPart_mem_hermitianBoundedMatrixGrid hQ,
    matrixHermitianPart_isHermitian Q,
    norm_sub_matrixHermitianPart_apply_le hAHerm hclose⟩

/-- The Hermitian projection of the tolerance-driven Gaussian-rational grid. -/
noncomputable def rationalHermitianBoundedMatrixGrid
    (ι : Type*) [Fintype ι] (R δ : ℝ) : Finset (Matrix ι ι ℂ) := by
  classical
  exact (rationalBoundedMatrixGrid ι R δ).image matrixHermitianPart

/-- Representation-preserving tolerance-driven Hermitian grid. -/
noncomputable def rationalHermitianBoundedMatrixCodeGrid
    (ι : Type*) [Fintype ι] [DecidableEq ι] (R δ : ℝ) :
    Finset (RationalMatrixCode ι) :=
  (rationalBoundedMatrixCodeGrid ι R δ).image RationalMatrixCode.hermitianPart

/-- Decoding the representation-preserving Hermitian grid gives exactly the existing
complex-valued Hermitian grid. -/
theorem rationalHermitianBoundedMatrixGrid_eq_image_decode
    (ι : Type*) [Fintype ι] [DecidableEq ι] (R δ : ℝ) :
    rationalHermitianBoundedMatrixGrid ι R δ =
      (rationalHermitianBoundedMatrixCodeGrid ι R δ).image
        RationalMatrixCode.decode := by
  classical
  ext Q
  constructor
  · intro hQ
    rw [rationalHermitianBoundedMatrixGrid, Finset.mem_image] at hQ
    obtain ⟨Q₀, hQ₀, rfl⟩ := hQ
    rw [rationalBoundedMatrixGrid_eq_image_decode, Finset.mem_image] at hQ₀
    obtain ⟨f, hf, rfl⟩ := hQ₀
    rw [rationalHermitianBoundedMatrixCodeGrid, Finset.mem_image]
    have hfHerm : f.hermitianPart ∈
        (rationalBoundedMatrixCodeGrid ι R δ).image
          RationalMatrixCode.hermitianPart :=
      Finset.mem_image.mpr ⟨f, hf, rfl⟩
    refine ⟨f.hermitianPart, hfHerm, ?_⟩
    exact RationalMatrixCode.decode_hermitianPart f
  · intro hQ
    rw [rationalHermitianBoundedMatrixCodeGrid, Finset.mem_image] at hQ
    obtain ⟨g, hg, rfl⟩ := hQ
    rw [Finset.mem_image] at hg
    obtain ⟨f, hf, rfl⟩ := hg
    rw [RationalMatrixCode.decode_hermitianPart,
      rationalHermitianBoundedMatrixGrid, Finset.mem_image]
    refine ⟨f.decode, ?_, rfl⟩
    rw [rationalBoundedMatrixGrid_eq_image_decode, Finset.mem_image]
    exact ⟨f, hf, rfl⟩

theorem RationalMatrixCode.decode_mem_rationalHermitianBoundedMatrixGrid
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R δ : ℝ}
    {f : RationalMatrixCode ι}
    (hf : f ∈ rationalHermitianBoundedMatrixCodeGrid ι R δ) :
    f.decode ∈ rationalHermitianBoundedMatrixGrid ι R δ := by
  rw [rationalHermitianBoundedMatrixGrid_eq_image_decode]
  exact Finset.mem_image.mpr ⟨f, hf, rfl⟩

theorem exists_code_of_mem_rationalHermitianBoundedMatrixGrid
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R δ : ℝ}
    {Q : Matrix ι ι ℂ} (hQ : Q ∈ rationalHermitianBoundedMatrixGrid ι R δ) :
    ∃ f ∈ rationalHermitianBoundedMatrixCodeGrid ι R δ, f.decode = Q := by
  rw [rationalHermitianBoundedMatrixGrid_eq_image_decode, Finset.mem_image] at hQ
  exact hQ

theorem rationalHermitianBoundedMatrixCodeGrid_card_eq
    (ι : Type*) [Fintype ι] [DecidableEq ι] (R δ : ℝ) :
    (rationalHermitianBoundedMatrixCodeGrid ι R δ).card =
      (rationalHermitianBoundedMatrixGrid ι R δ).card := by
  classical
  have h := congrArg Finset.card
    (rationalHermitianBoundedMatrixGrid_eq_image_decode ι R δ)
  rw [Finset.card_image_of_injective _ RationalMatrixCode.decode_injective] at h
  exact h.symm

/-- Uniform coordinate-height bound after Hermitian projection of the rational grid. -/
noncomputable def rationalHermitianBoundedMatrixGridHeight (R δ : ℝ) : ℕ :=
  hermitianPartHeight (rationalBoundedMatrixGridHeight R δ)

theorem rationalHermitianBoundedMatrixGrid_hasRationalEntriesOfHeight
    {ι : Type*} [Fintype ι] {R δ : ℝ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ rationalHermitianBoundedMatrixGrid ι R δ) :
    Matrix.HasRationalEntriesOfHeight
      (rationalHermitianBoundedMatrixGridHeight R δ) Q := by
  classical
  rw [rationalHermitianBoundedMatrixGrid, Finset.mem_image] at hQ
  obtain ⟨Q₀, hQ₀, rfl⟩ := hQ
  exact Matrix.HasRationalEntriesOfHeight.hermitianPart
    (rationalBoundedMatrixGrid_hasRationalEntriesOfHeight hQ₀)

/-- Hermitian projection does not increase the rational grid cardinality. -/
theorem rationalHermitianBoundedMatrixGrid_card_le
    {ι : Type*} [Fintype ι] (R δ : ℝ) :
    (rationalHermitianBoundedMatrixGrid ι R δ).card ≤
      (2 * rationalMatrixGridRadius R * rationalMatrixGridOrder δ + 1) ^
        (2 * Fintype.card ι ^ 2) := by
  classical
  exact Finset.card_image_le.trans (rationalBoundedMatrixGrid_card_le R δ)

/-- Taking the Hermitian part preserves Gaussian-rational coordinates. -/
theorem matrixHermitianPart_hasRationalEntries
    {ι : Type*} [Fintype ι] {Q : Matrix ι ι ℂ}
    (hQ : ∀ i j, ∃ x y : ℚ, Q i j = ⟨(x : ℝ), (y : ℝ)⟩) :
    ∀ i j, ∃ x y : ℚ, matrixHermitianPart Q i j = ⟨(x : ℝ), (y : ℝ)⟩ := by
  intro i j
  obtain ⟨x, y, hxy⟩ := hQ i j
  obtain ⟨u, v, huv⟩ := hQ j i
  refine ⟨(x + u) / 2, (y - v) / 2, ?_⟩
  apply Complex.ext <;>
    simp [matrixHermitianPart, Matrix.conjTranspose_apply, hxy, huv] <;>
    ring

theorem rationalHermitianBoundedMatrixGrid_entry
    {ι : Type*} [Fintype ι] {R δ : ℝ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ rationalHermitianBoundedMatrixGrid ι R δ) :
    ∀ i j, ∃ x y : ℚ, Q i j = ⟨(x : ℝ), (y : ℝ)⟩ := by
  classical
  rw [rationalHermitianBoundedMatrixGrid, Finset.mem_image] at hQ
  obtain ⟨Q₀, hQ₀, rfl⟩ := hQ
  apply matrixHermitianPart_hasRationalEntries
  intro i j
  exact gaussianRationalMatrixGrid_entry hQ₀ i j

/-- Every Hermitian matrix with bounded entries has a Hermitian Gaussian-rational
approximation at the prescribed entrywise tolerance. -/
theorem exists_mem_rationalHermitianBoundedMatrixGrid
    {ι : Type*} [Fintype ι] {R δ : ℝ} (hδ : 0 < δ)
    (A : Matrix ι ι ℂ) (hAHerm : A.IsHermitian)
    (hA : ∀ i j, ‖A i j‖ ≤ R) :
    ∃ Q ∈ rationalHermitianBoundedMatrixGrid ι R δ,
      Q.IsHermitian ∧
      (∀ i j, ∃ x y : ℚ, Q i j = ⟨(x : ℝ), (y : ℝ)⟩) ∧
      ∀ i j, ‖(A - Q) i j‖ ≤ δ := by
  obtain ⟨Q, hQ, hQrat, hclose⟩ := exists_mem_rationalBoundedMatrixGrid hδ A hA
  refine ⟨matrixHermitianPart Q, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩,
    matrixHermitianPart_isHermitian Q, matrixHermitianPart_hasRationalEntries hQrat, ?_⟩
  exact norm_sub_matrixHermitianPart_apply_le hAHerm hclose

/-- Entrywise error controls the trace error with one factor of the matrix order. -/
theorem norm_trace_le_card_mul_of_entry_norm_le
    {ι : Type*} [Fintype ι] (D : Matrix ι ι ℂ) {δ : ℝ}
    (hD : ∀ i j, ‖D i j‖ ≤ δ) :
    ‖D.trace‖ ≤ Fintype.card ι * δ := by
  rw [Matrix.trace]
  calc
    ‖∑ i, D i i‖ ≤ ∑ i, ‖D i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum fun i _ ↦ hD i i
    _ = Fintype.card ι * δ := by simp [Finset.sum_const]

/-- Entrywise error controls the difference of the real parts of two traces. -/
theorem abs_re_trace_sub_le_card_mul_of_entry_norm_le
    {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) {δ : ℝ}
    (hAB : ∀ i j, ‖(A - B) i j‖ ≤ δ) :
    |A.trace.re - B.trace.re| ≤ Fintype.card ι * δ := by
  calc
    |A.trace.re - B.trace.re| = |((A - B).trace).re| := by
      rw [Matrix.trace_sub, Complex.sub_re]
    _ ≤ ‖(A - B).trace‖ := Complex.abs_re_le_norm _
    _ ≤ Fintype.card ι * δ := norm_trace_le_card_mul_of_entry_norm_le (A - B) hAB

/-- Rounding a matrix entrywise enlarges its real trace-defect tolerance by at most
the matrix order times the entry tolerance. -/
theorem abs_one_sub_re_trace_le_of_entry_rounding
    {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) {κ δ : ℝ}
    (htrace : |1 - A.trace.re| ≤ κ)
    (hAB : ∀ i j, ‖(A - B) i j‖ ≤ δ) :
    |1 - B.trace.re| ≤ κ + Fintype.card ι * δ := by
  have hdiff := abs_re_trace_sub_le_card_mul_of_entry_norm_le A B hAB
  calc
    |1 - B.trace.re| = |(1 - A.trace.re) + (A.trace.re - B.trace.re)| := by
      congr 1
      ring
    _ ≤ |1 - A.trace.re| + |A.trace.re - B.trace.re| := abs_add_le _ _
    _ ≤ κ + Fintype.card ι * δ := add_le_add htrace hdiff

/-- Rounding two auxiliary matrices entrywise enlarges their joint real trace budget by
at most twice the matrix order times the entry tolerance. -/
theorem re_trace_add_le_of_entry_rounding
    {ι : Type*} [Fintype ι] (P N P' N' : Matrix ι ι ℂ) {η δ : ℝ}
    (htraces : P.trace.re + N.trace.re ≤ η)
    (hP : ∀ i j, ‖(P - P') i j‖ ≤ δ)
    (hN : ∀ i j, ‖(N - N') i j‖ ≤ δ) :
    P'.trace.re + N'.trace.re ≤ η + 2 * Fintype.card ι * δ := by
  have hPdiff := abs_re_trace_sub_le_card_mul_of_entry_norm_le P P' hP
  have hNdiff := abs_re_trace_sub_le_card_mul_of_entry_norm_le N N' hN
  linarith [(abs_le.mp hPdiff).1, (abs_le.mp hNdiff).1]

/-- Scaling the unit-ball grid gives a finite trace-norm net for a ball of arbitrary
positive radius.  This is the bounded search region needed for the auxiliary variables
of the compressed semidefinite program. -/
theorem exists_finset_rectangularTraceNorm_ball_net
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ N : Finset (Matrix ι ι ℂ),
      N.card ≤
        (2 * ⌈(Fintype.card ι : ℝ) ^ 2 / (δ / R)⌉₊ + 1) ^
          (2 * Fintype.card ι ^ 2) ∧
      ∀ Y : Matrix ι ι ℂ, rectangularTraceNorm Y ≤ R →
        ∃ X ∈ N, rectangularTraceNorm (Y - X) ≤ δ := by
  classical
  have hδR : 0 < δ / R := div_pos hδ hR
  obtain ⟨N, hcard, hcover⟩ :=
    Matrix.exists_finset_rectangularTraceNorm_net (n := ι) (η := δ / R) hδR
  let scale : Matrix ι ι ℂ → Matrix ι ι ℂ := fun X ↦ (R : ℂ) • X
  refine ⟨N.image scale, Finset.card_image_le.trans hcard, ?_⟩
  intro Y hY
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hscaled : rectangularTraceNorm ((R : ℂ)⁻¹ • Y) ≤ 1 := by
    rw [rectangularTraceNorm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    calc
      R⁻¹ * rectangularTraceNorm Y ≤ R⁻¹ * R :=
        mul_le_mul_of_nonneg_left hY (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  obtain ⟨X, hXN, hclose⟩ := hcover ((R : ℂ)⁻¹ • Y) hscaled
  refine ⟨scale X, Finset.mem_image.mpr ⟨X, hXN, rfl⟩, ?_⟩
  have heq : Y - scale X = (R : ℂ) • ((R : ℂ)⁻¹ • Y - X) := by
    dsimp only [scale]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hRne, one_smul]
  rw [heq, rectangularTraceNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  calc
    R * rectangularTraceNorm ((R : ℂ)⁻¹ • Y - X) ≤ R * (δ / R) :=
      mul_le_mul_of_nonneg_left hclose hR.le
    _ = δ := by field_simp

/-- Matrices whose squared entries are bounded by `C` admit an explicit finite net
which is entrywise accurate.  The construction uses the trace-norm ball of radius
`d² √C`, where `d` is the matrix order; trace-norm proximity then controls every
entry.  This is the finite search region for bounded Gram factors. -/
theorem exists_finset_bounded_gram_factor_net
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) :
    ∃ N : Finset (Matrix ι ι ℂ),
      N.card ≤
        (2 * ⌈(Fintype.card ι : ℝ) ^ 2 /
          (δ / ((Fintype.card ι : ℝ) ^ 2 * √C))⌉₊ + 1) ^
            (2 * Fintype.card ι ^ 2) ∧
      ∀ R : Matrix ι ι ℂ, (∀ i j, ‖R i j‖ ^ 2 ≤ C) →
        ∃ Q ∈ N, ∀ i j, ‖(R - Q) i j‖ ≤ δ := by
  classical
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hradius : 0 < (Fintype.card ι : ℝ) ^ 2 * √C :=
    mul_pos (sq_pos_of_pos hcard) (Real.sqrt_pos.2 hC)
  obtain ⟨N, hNcard, hNcover⟩ :=
    exists_finset_rectangularTraceNorm_ball_net (ι := ι)
      (R := (Fintype.card ι : ℝ) ^ 2 * √C) (δ := δ) hradius hδ
  refine ⟨N, hNcard, ?_⟩
  intro R hR
  have hentry : ∀ i j, ‖R i j‖ ≤ √C := by
    intro i j
    nlinarith [hR i j, Real.sq_sqrt hC.le, norm_nonneg (R i j), Real.sqrt_nonneg C]
  have hRnorm : rectangularTraceNorm R ≤ (Fintype.card ι : ℝ) ^ 2 * √C :=
    rectangularTraceNorm_le_card_sq_mul_of_entry_norm_le R hentry
  obtain ⟨Q, hQN, hclose⟩ := hNcover R hRnorm
  exact ⟨Q, hQN, fun i j ↦ (norm_apply_le_rectangularTraceNorm (R - Q) i j).trans hclose⟩

/-- The bounded factor net induces a finite net of approximate Gram certificates.
For a factor with squared entries bounded by `C`, a grid spacing `δ` produces
entrywise Gram error at most `d δ (2 √C + δ)`. -/
theorem exists_finset_bounded_gram_certificate_net
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) :
    ∃ N : Finset (Matrix ι ι ℂ),
      N.card ≤
        (2 * ⌈(Fintype.card ι : ℝ) ^ 2 /
          (δ / ((Fintype.card ι : ℝ) ^ 2 * √C))⌉₊ + 1) ^
            (2 * Fintype.card ι ^ 2) ∧
      ∀ R : Matrix ι ι ℂ, (∀ i j, ‖R i j‖ ^ 2 ≤ C) →
        ∃ Q ∈ N, ∀ i j,
          ‖(R * Rᴴ - Q * Qᴴ) i j‖ ≤
            Fintype.card ι * δ * (2 * √C + δ) := by
  classical
  obtain ⟨N, hNcard, hNcover⟩ :=
    exists_finset_bounded_gram_factor_net (ι := ι) (C := C) (δ := δ) hC hδ
  refine ⟨N, hNcard, ?_⟩
  intro R hR
  obtain ⟨Q, hQN, hclose⟩ := hNcover R hR
  have hentry : ∀ i j, ‖R i j‖ ≤ √C := by
    intro i j
    nlinarith [hR i j, Real.sq_sqrt hC.le, norm_nonneg (R i j), Real.sqrt_nonneg C]
  exact ⟨Q, hQN, norm_gram_sub_apply_le_of_entry_norm_le R Q
    (Real.sqrt_nonneg C) hδ.le hentry hclose⟩

end TNLean.MPS.AreaLaw
