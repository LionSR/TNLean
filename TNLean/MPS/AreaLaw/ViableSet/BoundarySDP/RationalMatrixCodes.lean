/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalCertificateTests
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalMatrixHeights

/-!
# Exact rational matrix representations

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- A real point in `[-B,B]` is within `1/(2M)` of the coercion of a point of the
rational grid. -/
theorem exists_mem_rationalRealGrid {B M : ℕ} (hM : 0 < M) {t : ℝ}
    (ht : |t| ≤ B) :
    ∃ q ∈ rationalRealGrid B M, |t - (q : ℝ)| ≤ 1 / (2 * M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  set y := (t + B) * M + 1 / 2 with hy
  have hy0 : 0 ≤ y := by rw [hy]; nlinarith
  let k := ⌊y⌋₊
  let q : ℚ := -(B : ℚ) + (k : ℚ) / M
  refine ⟨q, ?_, ?_⟩
  · rw [rationalRealGrid, Finset.mem_image]
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hylt : y < 2 * B * M + 1 := by rw [hy]; nlinarith
    have := Nat.floor_lt hy0 |>.mpr (by exact_mod_cast hylt)
    omega
  · have hfl := Nat.floor_le hy0
    have hlt := Nat.lt_floor_add_one y
    have hq : (q : ℝ) = -(B : ℝ) + (k : ℝ) / M := by
      simp only [q, Rat.cast_add, Rat.cast_neg, Rat.cast_natCast, Rat.cast_div]
    rw [hq, abs_le]
    constructor
    · rw [show t - (-(B : ℝ) + (k : ℝ) / M) =
          ((t + B) * M - k) / M by field_simp; ring,
        le_div_iff₀ hM']
      dsimp only [k]
      field_simp
      nlinarith
    · rw [show t - (-(B : ℝ) + (k : ℝ) / M) =
          ((t + B) * M - k) / M by field_simp; ring,
        div_le_iff₀ hM']
      dsimp only [k]
      field_simp
      nlinarith

/-- A square matrix represented by explicit rational real and imaginary coordinates. -/
abbrev RationalMatrixCode (ι : Type*) := ι × ι → ℚ × ℚ

/-- A possibly rectangular matrix represented by rational real and imaginary
coordinates. -/
abbrev RationalRectMatrixCode (m n : Type*) := m → n → ℚ × ℚ

/-- Decode a pair of rational coordinates as a complex number. -/
def decodeRationalComplex (z : ℚ × ℚ) : ℂ :=
  ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

namespace RationalComplexCode

def add (z w : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 + w.1, z.2 + w.2)

def neg (z : ℚ × ℚ) : ℚ × ℚ :=
  (-z.1, -z.2)

def sub (z w : ℚ × ℚ) : ℚ × ℚ :=
  add z (neg w)

def mul (z w : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

def conj (z : ℚ × ℚ) : ℚ × ℚ :=
  (z.1, -z.2)

@[simp] theorem decode_add (z w : ℚ × ℚ) :
    decodeRationalComplex (add z w) =
      decodeRationalComplex z + decodeRationalComplex w := by
  apply Complex.ext <;> simp [decodeRationalComplex, add]

@[simp] theorem decode_neg (z : ℚ × ℚ) :
    decodeRationalComplex (neg z) = -decodeRationalComplex z := by
  apply Complex.ext <;> simp [decodeRationalComplex, neg]

@[simp] theorem decode_sub (z w : ℚ × ℚ) :
    decodeRationalComplex (sub z w) =
      decodeRationalComplex z - decodeRationalComplex w := by
  rw [sub_eq_add_neg]
  simp [sub]

@[simp] theorem decode_mul (z w : ℚ × ℚ) :
    decodeRationalComplex (mul z w) =
      decodeRationalComplex z * decodeRationalComplex w := by
  apply Complex.ext <;> simp [decodeRationalComplex, mul]

@[simp] theorem decode_conj (z : ℚ × ℚ) :
    decodeRationalComplex (conj z) = star (decodeRationalComplex z) := by
  apply Complex.ext <;> simp [decodeRationalComplex, conj]

end RationalComplexCode

@[simp] theorem decodeRationalComplex_ratCast (q : ℚ) :
    decodeRationalComplex (q, 0) = (q : ℂ) := by
  apply Complex.ext <;> simp [decodeRationalComplex]

@[simp] theorem decodeRationalComplex_zero :
    decodeRationalComplex (0 : ℚ × ℚ) = 0 := by
  apply Complex.ext <;> simp [decodeRationalComplex]

@[simp] theorem decodeRationalComplex_add (z w : ℚ × ℚ) :
    decodeRationalComplex (z + w) =
      decodeRationalComplex z + decodeRationalComplex w := by
  apply Complex.ext <;> simp [decodeRationalComplex]

@[simp] theorem decodeRationalComplex_finset_sum
    {α : Type*} (s : Finset α) (f : α → ℚ × ℚ) :
    decodeRationalComplex (∑ x ∈ s, f x) =
      ∑ x ∈ s, decodeRationalComplex (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha => simp [*]

@[simp] theorem decodeRationalComplex_fintype_sum
    {α : Type*} [Fintype α] (f : α → ℚ × ℚ) :
    decodeRationalComplex (∑ x, f x) =
      ∑ x, decodeRationalComplex (f x) := by
  exact decodeRationalComplex_finset_sum Finset.univ f

/-- Real norm bounds on the Gaussian-rational residuals imply exact rational
acceptance.  This is the completeness counterpart to the numerical soundness theorem. -/
theorem RationalApproxCertificateTestValues.accepts_of_norm_bounds
    {ι : Type*} [Fintype ι] {n : ℕ}
    (v : RationalApproxCertificateTestValues ι n)
    {η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN : ℚ}
    (hε : 0 ≤ ε) (hεb : 0 ≤ εb) (hζ : 0 ≤ ζ)
    (hζA : 0 ≤ ζA) (hζP : 0 ≤ ζP) (hζN : 0 ≤ ζN)
    (htrace : |1 - (v.densityTrace : ℝ)| ≤ (κ : ℝ))
    (hAgr : ∀ i j, ‖decodeRationalComplex (v.densityGramResidual i j)‖ ≤ (ζA : ℝ))
    (hAbudget : εA₀ + ((n : ℚ) + 1) * ζA ≤ ε)
    (hPgr : ∀ i j, ‖decodeRationalComplex (v.positiveGramResidual i j)‖ ≤ (ζP : ℝ))
    (hPbudget : εP₀ + ((Fintype.card ι : ℚ) + 1) * ζP ≤ εb)
    (hNgr : ∀ i j, ‖decodeRationalComplex (v.negativeGramResidual i j)‖ ≤ (ζN : ℝ))
    (hNbudget : εN₀ + ((Fintype.card ι : ℚ) + 1) * ζN ≤ εb)
    (hboundary : ∀ i j, ‖decodeRationalComplex (v.boundaryResidual i j)‖ ≤ (ζ : ℝ))
    (hscale : (Fintype.card ι : ℚ) ^ 2 * ζ ≤ δ)
    (htraces : v.positiveTrace + v.negativeTrace ≤ η)
    (henergy : v.objective ≤ E) :
    v.Accepts η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN := by
  refine ⟨hε, hεb, hζ, hζA, hζP, hζN, ?_, ?_, hAbudget,
    ?_, hPbudget, ?_, hNbudget, ?_, hscale, htraces, henergy⟩
  · exact_mod_cast htrace
  · intro i j
    exact (gaussianRational_norm_le_iff _ _ _ hζA).mp (hAgr i j)
  · intro i j
    exact (gaussianRational_norm_le_iff _ _ _ hζP).mp (hPgr i j)
  · intro i j
    exact (gaussianRational_norm_le_iff _ _ _ hζN).mp (hNgr i j)
  · intro i j
    exact (gaussianRational_norm_le_iff _ _ _ hζ).mp (hboundary i j)

namespace RationalRectMatrixCode

/-- Decode a rectangular rational-coordinate matrix. -/
def decode {m n : Type*} (A : RationalRectMatrixCode m n) : Matrix m n ℂ :=
  fun i j ↦ decodeRationalComplex (A i j)

/-- The largest reduced rational-coordinate height occurring in a finite matrix code. -/
def height {m n : Type*} [Fintype m] [Fintype n]
    (A : RationalRectMatrixCode m n) : ℕ :=
  Finset.univ.sup fun i ↦ Finset.univ.sup fun j ↦
    max (rationalHeight (A i j).1) (rationalHeight (A i j).2)

/-- Decoding a finite rational matrix code preserves its canonical coordinate-height
bound. -/
theorem decode_hasRationalEntriesOfHeight {m n : Type*} [Fintype m] [Fintype n]
    (A : RationalRectMatrixCode m n) :
    Matrix.HasRationalEntriesOfHeight A.height A.decode := by
  intro i j
  refine ⟨(A i j).1, (A i j).2, rfl, ?_, ?_⟩
  · apply (le_max_left _ _).trans
    apply (Finset.le_sup (f := fun j ↦
      max (rationalHeight (A i j).1) (rationalHeight (A i j).2))
      (Finset.mem_univ j)).trans
    exact Finset.le_sup (f := fun i ↦ Finset.univ.sup fun j ↦
      max (rationalHeight (A i j).1) (rationalHeight (A i j).2))
      (Finset.mem_univ i)
  · apply (le_max_right _ _).trans
    apply (Finset.le_sup (f := fun j ↦
      max (rationalHeight (A i j).1) (rationalHeight (A i j).2))
      (Finset.mem_univ j)).trans
    exact Finset.le_sup (f := fun i ↦ Finset.univ.sup fun j ↦
      max (rationalHeight (A i j).1) (rationalHeight (A i j).2))
      (Finset.mem_univ i)

/-- A finite matrix with rational coordinates of height at most `H` has a rational
coordinate code of canonical height at most `H`. -/
theorem exists_code_of_hasRationalEntriesOfHeight
    {m n : Type*} [Fintype m] [Fintype n] {H : ℕ} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    ∃ c : RationalRectMatrixCode m n, c.decode = A ∧ c.height ≤ H := by
  choose x y hxy hx hy using hA
  let c : RationalRectMatrixCode m n := fun i j ↦ (x i j, y i j)
  refine ⟨c, ?_, ?_⟩
  · ext i j
    exact (hxy i j).symm
  · unfold height
    apply Finset.sup_le
    intro i _hi
    apply Finset.sup_le
    intro j _hj
    exact max_le (hx i j) (hy i j)

def add {m n : Type*} (A B : RationalRectMatrixCode m n) :
    RationalRectMatrixCode m n :=
  fun i j ↦ RationalComplexCode.add (A i j) (B i j)

def sub {m n : Type*} (A B : RationalRectMatrixCode m n) :
    RationalRectMatrixCode m n :=
  fun i j ↦ RationalComplexCode.sub (A i j) (B i j)

def mul {m n p : Type*} [Fintype n]
    (A : RationalRectMatrixCode m n) (B : RationalRectMatrixCode n p) :
    RationalRectMatrixCode m p :=
  fun i k ↦ ∑ j, RationalComplexCode.mul (A i j) (B j k)

def conjTranspose {m n : Type*} (A : RationalRectMatrixCode m n) :
    RationalRectMatrixCode n m :=
  fun j i ↦ RationalComplexCode.conj (A i j)

def trace {ι : Type*} [Fintype ι] (A : RationalRectMatrixCode ι ι) : ℚ × ℚ :=
  ∑ i, A i i

def addRealDiagonal {ι : Type*} [DecidableEq ι]
    (A : RationalRectMatrixCode ι ι) (q : ℚ) : RationalRectMatrixCode ι ι :=
  fun i j ↦ if i = j then RationalComplexCode.add (A i j) (q, 0) else A i j

def partialTraceFirst {a s b : Type*} [Fintype a]
    (A : RationalRectMatrixCode ((a × s) × b) ((a × s) × b)) :
    RationalRectMatrixCode (s × b) (s × b) :=
  fun i j ↦ ∑ x, A ((x, i.1), i.2) ((x, j.1), j.2)

@[simp] theorem decode_add {m n : Type*} (A B : RationalRectMatrixCode m n) :
    decode (add A B) = decode A + decode B := by
  ext i j
  simp [decode, add, Matrix.add_apply]

@[simp] theorem decode_sub {m n : Type*} (A B : RationalRectMatrixCode m n) :
    decode (sub A B) = decode A - decode B := by
  ext i j
  simp [decode, sub, Matrix.sub_apply]

@[simp] theorem decode_mul {m n p : Type*} [Fintype n]
    (A : RationalRectMatrixCode m n) (B : RationalRectMatrixCode n p) :
    decode (mul A B) = decode A * decode B := by
  ext i k
  simp [decode, mul, Matrix.mul_apply]

@[simp] theorem decode_conjTranspose {m n : Type*}
    (A : RationalRectMatrixCode m n) :
    decode (conjTranspose A) = (decode A)ᴴ := by
  ext j i
  simp [decode, conjTranspose, Matrix.conjTranspose_apply]

@[simp] theorem decode_trace {ι : Type*} [Fintype ι]
    (A : RationalRectMatrixCode ι ι) :
    decodeRationalComplex (trace A) = (decode A).trace := by
  simp [trace, decode, Matrix.trace]

@[simp] theorem decode_addRealDiagonal {ι : Type*} [DecidableEq ι]
    (A : RationalRectMatrixCode ι ι) (q : ℚ) :
    decode (addRealDiagonal A q) =
      decode A + (q : ℂ) • (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [decode, addRealDiagonal, Matrix.add_apply, Matrix.smul_apply]
  · simp [decode, addRealDiagonal, Matrix.add_apply, Matrix.smul_apply, hij]

@[simp] theorem decode_partialTraceFirst {a s b : Type*} [Fintype a]
    (A : RationalRectMatrixCode ((a × s) × b) ((a × s) × b)) :
    decode (partialTraceFirst A) = Matrix.partialTraceFirst (decode A) := by
  ext i j
  simp [decode, partialTraceFirst, Matrix.partialTraceFirst,
    Matrix.partialTraceLeft_apply, Matrix.reindex_apply]

end RationalRectMatrixCode

/-- Decode an explicit rational matrix code as a complex matrix. -/
def RationalMatrixCode.decode {ι : Type*} (f : RationalMatrixCode ι) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j ↦ ⟨((f (i, j)).1 : ℝ), ((f (i, j)).2 : ℝ)⟩

/-- Regard a square code with paired indices as a curried rectangular code. -/
def RationalMatrixCode.toRect {ι : Type*} (f : RationalMatrixCode ι) :
    RationalRectMatrixCode ι ι :=
  fun i j ↦ f (i, j)

@[simp] theorem RationalMatrixCode.decode_toRect {ι : Type*}
    (f : RationalMatrixCode ι) :
    RationalRectMatrixCode.decode f.toRect = f.decode := by
  rfl

theorem RationalMatrixCode.decode_injective {ι : Type*} :
    Function.Injective (RationalMatrixCode.decode : RationalMatrixCode ι → Matrix ι ι ℂ) := by
  intro f g hfg
  funext ij
  apply Prod.ext
  · have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A ij.1 ij.2).re) hfg
    change ((f ij).1 : ℝ) = ((g ij).1 : ℝ) at h
    exact_mod_cast h
  · have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A ij.1 ij.2).im) hfg
    change ((f ij).2 : ℝ) = ((g ij).2 : ℝ) at h
    exact_mod_cast h

/-- The representation-preserving Gaussian-rational matrix grid. -/
def rationalMatrixCodeGrid
    (ι : Type*) [Fintype ι] [DecidableEq ι] (B M : ℕ) :
    Finset (RationalMatrixCode ι) :=
  Fintype.piFinset fun _ : ι × ι ↦
    rationalRealGrid B M ×ˢ rationalRealGrid B M

/-- Rational Hermitian projection, performed before decoding to complex numbers. -/
def RationalMatrixCode.hermitianPart {ι : Type*} (f : RationalMatrixCode ι) :
    RationalMatrixCode ι := fun ij ↦
  ((f ij).1 / 2 + (f (ij.2, ij.1)).1 / 2,
    (f ij).2 / 2 - (f (ij.2, ij.1)).2 / 2)

/-- Decoding commutes with Hermitian projection. -/
theorem RationalMatrixCode.decode_hermitianPart
    {ι : Type*} [Fintype ι] (f : RationalMatrixCode ι) :
    f.hermitianPart.decode = matrixHermitianPart f.decode := by
  apply Matrix.ext
  intro i j
  apply Complex.ext <;>
    simp [RationalMatrixCode.hermitianPart, RationalMatrixCode.decode,
      matrixHermitianPart, Matrix.smul_apply, Matrix.add_apply,
      Matrix.conjTranspose_apply] <;>
    ring

/-- A representation-preserving Hermitian rational grid. -/
def rationalHermitianMatrixCodeGrid
    (ι : Type*) [Fintype ι] [DecidableEq ι] (B M : ℕ) :
    Finset (RationalMatrixCode ι) :=
  (rationalMatrixCodeGrid ι B M).image RationalMatrixCode.hermitianPart

/-- Every decoded member of the rational Hermitian code grid is Hermitian. -/
theorem RationalMatrixCode.decode_isHermitian_of_mem_rationalHermitianMatrixCodeGrid
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B M : ℕ}
    {f : RationalMatrixCode ι} (hf : f ∈ rationalHermitianMatrixCodeGrid ι B M) :
    f.decode.IsHermitian := by
  rw [rationalHermitianMatrixCodeGrid, Finset.mem_image] at hf
  obtain ⟨g, _hg, rfl⟩ := hf
  rw [RationalMatrixCode.decode_hermitianPart]
  exact matrixHermitianPart_isHermitian g.decode

/-- The complex matrix grid with independently chosen rational real and imaginary
coordinates of denominator `M` and magnitude at most `B`. -/
noncomputable def gaussianRationalMatrixGrid
    (ι : Type*) [Fintype ι] (B M : ℕ) : Finset (Matrix ι ι ℂ) := by
  classical
  let toMat : (ι × ι → ℚ × ℚ) → Matrix ι ι ℂ := fun f ↦
    Matrix.of fun i j ↦ ⟨((f (i, j)).1 : ℝ), ((f (i, j)).2 : ℝ)⟩
  exact (Fintype.piFinset fun _ : ι × ι ↦
    rationalRealGrid B M ×ˢ rationalRealGrid B M).image toMat

/-- The older complex Gaussian grid is precisely the decoded image of the rational
code grid. -/
theorem gaussianRationalMatrixGrid_eq_image_decode
    (ι : Type*) [Fintype ι] [DecidableEq ι] (B M : ℕ) :
    gaussianRationalMatrixGrid ι B M =
      (rationalMatrixCodeGrid ι B M).image RationalMatrixCode.decode := by
  unfold gaussianRationalMatrixGrid rationalMatrixCodeGrid
  dsimp only
  congr 1
  ext f
  simp only [Fintype.mem_piFinset]

/-- Every entry of the rational complex matrix grid retains its two scalar-grid
membership witnesses. -/
theorem gaussianRationalMatrixGrid_entry_mem
    {ι : Type*} [Fintype ι] {B M : ℕ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ gaussianRationalMatrixGrid ι B M) (i j : ι) :
    ∃ x ∈ rationalRealGrid B M, ∃ y ∈ rationalRealGrid B M,
      Q i j = ⟨(x : ℝ), (y : ℝ)⟩ := by
  classical
  rw [gaussianRationalMatrixGrid, Finset.mem_image] at hQ
  obtain ⟨f, hf, rfl⟩ := hQ
  have hfij := Fintype.mem_piFinset.mp hf (i, j)
  have hfij' := Finset.mem_product.mp hfij
  exact ⟨(f (i, j)).1, hfij'.1, (f (i, j)).2, hfij'.2, rfl⟩

/-- Every entry of the rational complex matrix grid has rational real and imaginary
parts, with the witnesses retained independently at each coordinate. -/
theorem gaussianRationalMatrixGrid_entry
    {ι : Type*} [Fintype ι] {B M : ℕ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ gaussianRationalMatrixGrid ι B M) (i j : ι) :
    ∃ x y : ℚ, Q i j = ⟨(x : ℝ), (y : ℝ)⟩ := by
  obtain ⟨x, _hx, y, _hy, hxy⟩ := gaussianRationalMatrixGrid_entry_mem hQ i j
  exact ⟨x, y, hxy⟩

/-- Both rational coordinates of every matrix-grid entry have polynomially bounded
reduced numerator and denominator. -/
theorem gaussianRationalMatrixGrid_entry_height_le
    {ι : Type*} [Fintype ι] {B M : ℕ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ gaussianRationalMatrixGrid ι B M) (i j : ι) :
    ∃ x y : ℚ, Q i j = ⟨(x : ℝ), (y : ℝ)⟩ ∧
      rationalHeight x ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) ∧
      rationalHeight y ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := gaussianRationalMatrixGrid_entry_mem hQ i j
  exact ⟨x, y, hxy, rationalHeight_le_of_mem_rationalRealGrid hx,
    rationalHeight_le_of_mem_rationalRealGrid hy⟩

/-- A matrix in the Gaussian-rational grid has a uniform explicit coordinate-height
bound. -/
theorem gaussianRationalMatrixGrid_hasRationalEntriesOfHeight
    {ι : Type*} [Fintype ι] {B M : ℕ} {Q : Matrix ι ι ℂ}
    (hQ : Q ∈ gaussianRationalMatrixGrid ι B M) :
    Matrix.HasRationalEntriesOfHeight
      (2 * (B + 1) * ((2 * B * M + 1) * (M + 1))) Q := by
  intro i j
  exact gaussianRationalMatrixGrid_entry_height_le hQ i j

/-- The rational complex matrix grid has at most
`(2BM+1)^(2d²)` elements. -/
theorem gaussianRationalMatrixGrid_card_le
    {ι : Type*} [Fintype ι] (B M : ℕ) :
    (gaussianRationalMatrixGrid ι B M).card ≤
      (2 * B * M + 1) ^ (2 * Fintype.card ι ^ 2) := by
  classical
  let G := rationalRealGrid B M
  let toMat : (ι × ι → ℚ × ℚ) → Matrix ι ι ℂ := fun f ↦
    Matrix.of fun i j ↦ ⟨((f (i, j)).1 : ℝ), ((f (i, j)).2 : ℝ)⟩
  have hG : G.card ≤ 2 * B * M + 1 :=
    Finset.card_image_le.trans (Finset.card_range _).le
  change ((Fintype.piFinset fun _ : ι × ι ↦ G ×ˢ G).image toMat).card ≤ _
  refine Finset.card_image_le.trans ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Finset.card_product]
  calc
    (G.card * G.card) ^ (Fintype.card ι * Fintype.card ι) ≤
        ((2 * B * M + 1) * (2 * B * M + 1)) ^
          (Fintype.card ι * Fintype.card ι) :=
      Nat.pow_le_pow_left (Nat.mul_le_mul hG hG) _
    _ = (2 * B * M + 1) ^ (2 * Fintype.card ι ^ 2) := by
      rw [← sq, ← pow_mul, sq]

/-- A complex matrix with entries bounded by the natural number `B` has a
Gaussian-rational representative within entrywise error `1/M`. -/
theorem exists_mem_gaussianRationalMatrixGrid
    {ι : Type*} [Fintype ι] {B M : ℕ} (hM : 0 < M)
    (A : Matrix ι ι ℂ) (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ∃ Q ∈ gaussianRationalMatrixGrid ι B M,
      ∀ i j, ‖(A - Q) i j‖ ≤ 1 / M := by
  classical
  choose qre hqre hqreClose using fun i j ↦ exists_mem_rationalRealGrid hM
    ((Complex.abs_re_le_norm (A i j)).trans (hA i j))
  choose qim hqim hqimClose using fun i j ↦ exists_mem_rationalRealGrid hM
    ((Complex.abs_im_le_norm (A i j)).trans (hA i j))
  let f : ι × ι → ℚ × ℚ := fun ij ↦ (qre ij.1 ij.2, qim ij.1 ij.2)
  let Q : Matrix ι ι ℂ := Matrix.of fun i j ↦
    ⟨((f (i, j)).1 : ℝ), ((f (i, j)).2 : ℝ)⟩
  refine ⟨Q, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨f, Fintype.mem_piFinset.mpr fun ij ↦
      Finset.mem_product.mpr ⟨hqre ij.1 ij.2, hqim ij.1 ij.2⟩, rfl⟩
  · intro i j
    calc
      ‖(A - Q) i j‖ ≤
          |(A i j).re - (qre i j : ℝ)| + |(A i j).im - (qim i j : ℝ)| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 / (2 * M) + 1 / (2 * M) :=
        add_le_add (hqreClose i j) (hqimClose i j)
      _ = 1 / M := by field_simp; ring

end TNLean.MPS.AreaLaw
