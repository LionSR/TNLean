/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalCoordinates

/-!
# Rational comparisons and finite certificate selection

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Gaussian-rational complex numbers are norm-dense in the complex numbers.  This
elementary coordinatewise form is the scalar approximation input for rationalizing
finite open-boundary MPS tensor data. -/
theorem exists_rationalComplex_close (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℂ, HasRationalComplexCoordinates w ∧ ‖z - w‖ < ε := by
  let η := ε / 4
  have hη : 0 < η := by positivity
  obtain ⟨x, hx₁, hx₂⟩ := exists_rat_btwn
    (show z.re - η < z.re + η by linarith)
  obtain ⟨y, hy₁, hy₂⟩ := exists_rat_btwn
    (show z.im - η < z.im + η by linarith)
  let w : ℂ := ⟨(x : ℝ), (y : ℝ)⟩
  refine ⟨w, ⟨x, y, rfl⟩, ?_⟩
  apply lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im (z - w))
  have hx : |z.re - (x : ℝ)| < η := by
    rw [abs_lt]
    constructor <;> linarith
  have hy : |z.im - (y : ℝ)| < η := by
    rw [abs_lt]
    constructor <;> linarith
  dsimp only [η] at hx hy
  change |z.re - (x : ℝ)| + |z.im - (y : ℝ)| < ε
  linarith

/-- A complex number with rational real and imaginary parts, retained together with
the arithmetic certificate. -/
abbrev RationalComplex := {z : ℂ // HasRationalComplexCoordinates z}

/-- Gaussian-rational complex numbers form a dense subset of the complex plane. -/
theorem denseRange_rationalComplex_val :
    DenseRange ((↑) : RationalComplex → ℂ) := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  obtain ⟨w, hw, hzw⟩ := exists_rationalComplex_close z hε
  exact ⟨⟨w, hw⟩, by simpa [dist_eq_norm] using hzw⟩

/-- A classically selected rational real coordinate of a complex number known to have
rational coordinates.  Executable search records retain this coordinate directly; this
selector is used only to connect the older complex-valued grids to that representation. -/
noncomputable def rationalComplexRealCoordinate {z : ℂ}
    (hz : HasRationalComplexCoordinates z) : ℚ :=
  hz.choose

/-- The corresponding selected rational imaginary coordinate. -/
noncomputable def rationalComplexImagCoordinate {z : ℂ}
    (hz : HasRationalComplexCoordinates z) : ℚ :=
  hz.choose_spec.choose

theorem eq_complex_of_rationalComplexCoordinates {z : ℂ}
    (hz : HasRationalComplexCoordinates z) :
    z = ⟨(rationalComplexRealCoordinate hz : ℝ),
      (rationalComplexImagCoordinate hz : ℝ)⟩ :=
  hz.choose_spec.choose_spec

theorem real_eq_rationalComplexRealCoordinate {z : ℂ}
    (hz : HasRationalComplexCoordinates z) :
    z.re = (rationalComplexRealCoordinate hz : ℝ) := by
  have h := congrArg Complex.re (eq_complex_of_rationalComplexCoordinates hz)
  simpa using h

/-- An ordered comparison between rational numbers is unchanged after coercion to the
real numbers. -/
theorem rationalCast_le_iff (x q : ℚ) :
    (x : ℝ) ≤ (q : ℝ) ↔ x ≤ q := by
  norm_cast

/-- A trace-defect comparison with rational data is exactly a rational inequality. -/
theorem rationalTraceDefect_le_iff (x κ : ℚ) :
    |1 - (x : ℝ)| ≤ (κ : ℝ) ↔ |1 - x| ≤ κ := by
  norm_cast

/-- A sum-budget comparison with rational data is exactly a rational inequality. -/
theorem rationalTraceSum_le_iff (x y η : ℚ) :
    (x : ℝ) + (y : ℝ) ≤ (η : ℝ) ↔ x + y ≤ η := by
  norm_cast

/-- A rational threshold comparison after coercion to the reals is decidable by
rational arithmetic. -/
def rationalCastLEDecidable (x q : ℚ) : Decidable ((x : ℝ) ≤ (q : ℝ)) :=
  decidable_of_iff (x ≤ q) (rationalCast_le_iff x q).symm

/-- A rational trace-defect comparison is decidable by rational arithmetic. -/
def rationalTraceDefectLEDecidable (x κ : ℚ) :
    Decidable (|1 - (x : ℝ)| ≤ (κ : ℝ)) :=
  decidable_of_iff (|1 - x| ≤ κ) (rationalTraceDefect_le_iff x κ).symm

/-- A rational sum-budget comparison is decidable by rational arithmetic. -/
def rationalTraceSumLEDecidable (x y η : ℚ) :
    Decidable ((x : ℝ) + (y : ℝ) ≤ (η : ℝ)) :=
  decidable_of_iff (x + y ≤ η) (rationalTraceSum_le_iff x y η).symm

/-- Comparing a complex norm with a nonnegative threshold is equivalent to comparing
their squares; no square-root evaluation is needed. -/
theorem complex_norm_le_iff_normSq_le_sq {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    ‖z‖ ≤ t ↔ Complex.normSq z ≤ t ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, pow_two, pow_two,
    ← mul_self_le_mul_self_iff (norm_nonneg z) ht]

/-- For Gaussian-rational coordinates, a complex norm comparison is exactly a rational
polynomial inequality. -/
theorem gaussianRational_norm_le_iff
    (x y q : ℚ) (hq : 0 ≤ q) :
    ‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ ≤ (q : ℝ) ↔ x ^ 2 + y ^ 2 ≤ q ^ 2 := by
  rw [complex_norm_le_iff_normSq_le_sq (by exact_mod_cast hq), Complex.normSq_apply]
  constructor <;> intro h
  · have h' : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by
      simpa [pow_two] using h
    exact_mod_cast h'
  · have h' : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by
      exact_mod_cast h
    simpa [pow_two] using h'

/-- The norm comparison for a Gaussian-rational number is decidable by rational
arithmetic. -/
def gaussianRationalNormLEDecidable (x y q : ℚ) (hq : 0 ≤ q) :
    Decidable (‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ ≤ (q : ℝ)) :=
  decidable_of_iff (x ^ 2 + y ^ 2 ≤ q ^ 2)
    (gaussianRational_norm_le_iff x y q hq).symm

/-- All entrywise norm comparisons for a finite Gaussian-rational matrix are decidable
by finitely many rational polynomial comparisons. -/
def gaussianRationalMatrixEntryNormLEDecidable
    {m n : Type*} [Fintype m] [Fintype n]
    (x y : m → n → ℚ) (q : ℚ) (hq : 0 ≤ q) :
    Decidable (∀ i j,
      ‖(⟨(x i j : ℝ), (y i j : ℝ)⟩ : ℂ)‖ ≤ (q : ℝ)) := by
  letI (i : m) (j : n) : Decidable
      (‖(⟨(x i j : ℝ), (y i j : ℝ)⟩ : ℂ)‖ ≤ (q : ℝ)) :=
    gaussianRationalNormLEDecidable (x i j) (y i j) q hq
  letI (i : m) : Decidable (∀ j,
      ‖(⟨(x i j : ℝ), (y i j : ℝ)⟩ : ℂ)‖ ≤ (q : ℝ)) :=
    Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

/-- Rational values of every scalar and matrix expression inspected by the finite
certificate tester.  Storing real and imaginary coordinates explicitly makes the test
computable over `ℚ`; the accompanying soundness theorem below relates these values to
the corresponding complex matrix expressions. -/
structure RationalApproxCertificateTestValues (ι : Type*) (n : ℕ) where
  densityTrace : ℚ
  positiveTrace : ℚ
  negativeTrace : ℚ
  objective : ℚ
  boundaryResidual : ι → ι → ℚ × ℚ
  densityGramResidual : Fin n → Fin n → ℚ × ℚ
  positiveGramResidual : ι → ι → ℚ × ℚ
  negativeGramResidual : ι → ι → ℚ × ℚ

/-- Exact rational acceptance predicate for an approximate SDP certificate.  Every
condition is a rational polynomial inequality, and all matrix conditions range over
finite index types. -/
def RationalApproxCertificateTestValues.Accepts
    {ι : Type*} [Fintype ι] {n : ℕ}
    (v : RationalApproxCertificateTestValues ι n)
    (η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN : ℚ) : Prop :=
  0 ≤ ε ∧ 0 ≤ εb ∧ 0 ≤ ζ ∧ 0 ≤ ζA ∧ 0 ≤ ζP ∧ 0 ≤ ζN ∧
  |1 - v.densityTrace| ≤ κ ∧
  (∀ i j, (v.densityGramResidual i j).1 ^ 2 +
    (v.densityGramResidual i j).2 ^ 2 ≤ ζA ^ 2) ∧
  εA₀ + ((n : ℚ) + 1) * ζA ≤ ε ∧
  (∀ i j, (v.positiveGramResidual i j).1 ^ 2 +
    (v.positiveGramResidual i j).2 ^ 2 ≤ ζP ^ 2) ∧
  εP₀ + ((Fintype.card ι : ℚ) + 1) * ζP ≤ εb ∧
  (∀ i j, (v.negativeGramResidual i j).1 ^ 2 +
    (v.negativeGramResidual i j).2 ^ 2 ≤ ζN ^ 2) ∧
  εN₀ + ((Fintype.card ι : ℚ) + 1) * ζN ≤ εb ∧
  (∀ i j, (v.boundaryResidual i j).1 ^ 2 +
    (v.boundaryResidual i j).2 ^ 2 ≤ ζ ^ 2) ∧
  (Fintype.card ι : ℚ) ^ 2 * ζ ≤ δ ∧
  v.positiveTrace + v.negativeTrace ≤ η ∧ v.objective ≤ E

/-- The finite certificate acceptance predicate is decidable by rational arithmetic. -/
instance RationalApproxCertificateTestValues.instDecidableAccepts
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (v : RationalApproxCertificateTestValues ι n)
    (η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN : ℚ) :
    Decidable (v.Accepts η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN) := by
  unfold RationalApproxCertificateTestValues.Accepts
  infer_instance

/-- Scan an ordered finite list of candidates and return the first one whose stored
rational test values satisfy the certificate inequalities. -/
def firstAcceptedRationalApproxCertificate
    {α ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (values : α → RationalApproxCertificateTestValues ι n)
    (η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN : ℚ) :
    List α → Option α
  | [] => none
  | c :: candidates =>
      if (values c).Accepts η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN then
        some c
      else
        firstAcceptedRationalApproxCertificate values
          η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN candidates

/-- Any candidate returned by the rational selector belongs to the input list and
passes the exact rational acceptance test. -/
theorem firstAcceptedRationalApproxCertificate_sound
    {α ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (values : α → RationalApproxCertificateTestValues ι n)
    (η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN : ℚ)
    {candidates : List α} {c : α}
    (hfind : firstAcceptedRationalApproxCertificate values
      η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN candidates = some c) :
    c ∈ candidates ∧
      (values c).Accepts η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN := by
  induction candidates with
  | nil => simp [firstAcceptedRationalApproxCertificate] at hfind
  | cons d candidates ih =>
      by_cases hd : (values d).Accepts
          η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN
      · rw [firstAcceptedRationalApproxCertificate, ite_eq_left hd] at hfind
        have hdc : d = c := Option.some.inj hfind
        subst c
        exact ⟨List.mem_cons_self, hd⟩
      · rw [firstAcceptedRationalApproxCertificate, ite_eq_right hd] at hfind
        obtain ⟨hc, haccept⟩ := ih hfind
        exact ⟨List.mem_cons_of_mem d hc, haccept⟩

/-- If the input list contains an accepted candidate, the rational selector returns an
accepted candidate.  Together with the preceding theorem, this is completeness of the
finite scan independently of how the rational test values are evaluated. -/
theorem firstAcceptedRationalApproxCertificate_complete
    {α ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (values : α → RationalApproxCertificateTestValues ι n)
    (η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN : ℚ)
    (candidates : List α)
    (hexists : ∃ c ∈ candidates,
      (values c).Accepts η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN) :
    ∃ c, firstAcceptedRationalApproxCertificate values
        η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN candidates = some c := by
  induction candidates with
  | nil => simp at hexists
  | cons d candidates ih =>
      by_cases hd : (values d).Accepts
          η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN
      · exact ⟨d, by simp [firstAcceptedRationalApproxCertificate, hd]⟩
      · have htail : ∃ c ∈ candidates,
            (values c).Accepts η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN := by
          simpa only [List.mem_cons, exists_eq_or_imp, hd, false_or] using hexists
        obtain ⟨c, hc⟩ := ih htail
        exact ⟨c, by simpa [firstAcceptedRationalApproxCertificate, hd] using hc⟩

/-- Select an accepted member of a finite set by taking the least natural-number
encoding among accepted candidates.  Unlike conversion of a finite set to an
arbitrarily ordered list, this construction is canonical and executable. -/
def encodableDecidableEq {α : Type*} [Encodable α] : DecidableEq α :=
  fun a b ↦ decidable_of_iff (Encodable.encode a = Encodable.encode b)
    Encodable.encode_inj

def firstAcceptedInFinset
    {α : Type*} [Encodable α]
    (candidates : Finset α) (Accepts : α → Prop) [DecidablePred Accepts] : Option α := by
  let _ : DecidableEq α := encodableDecidableEq
  let acceptedCodes := (candidates.filter Accepts).image Encodable.encode
  exact if h : acceptedCodes.Nonempty then Encodable.decode (acceptedCodes.min' h) else none

/-- The canonical finite-set selector returns only members of the original finite set
which satisfy its acceptance predicate. -/
theorem firstAcceptedInFinset_sound
    {α : Type*} [Encodable α]
    (candidates : Finset α) (Accepts : α → Prop) [DecidablePred Accepts]
    {c : α} (hfind : firstAcceptedInFinset candidates Accepts = some c) :
    c ∈ candidates ∧ Accepts c := by
  let _ : DecidableEq α := encodableDecidableEq
  by_cases hnonempty : ((candidates.filter Accepts).image Encodable.encode).Nonempty
  · rw [firstAcceptedInFinset, dite_eq_left hnonempty] at hfind
    have hmin := Finset.min'_mem
      ((candidates.filter Accepts).image Encodable.encode) hnonempty
    obtain ⟨d, hd, hencode⟩ := Finset.mem_image.mp hmin
    have hdecode : Encodable.decode (Encodable.encode d) = some d :=
      Encodable.encodek d
    rw [← hencode, hdecode] at hfind
    cases hfind
    exact Finset.mem_filter.mp hd
  · rw [firstAcceptedInFinset, dite_eq_right hnonempty] at hfind
    simp at hfind

/-- The canonical finite-set selector returns a value whenever an accepted candidate
exists. -/
theorem firstAcceptedInFinset_complete
    {α : Type*} [Encodable α]
    (candidates : Finset α) (Accepts : α → Prop) [DecidablePred Accepts]
    (hexists : ∃ c ∈ candidates, Accepts c) :
    ∃ c, firstAcceptedInFinset candidates Accepts = some c := by
  let _ : DecidableEq α := encodableDecidableEq
  obtain ⟨d, hd, haccept⟩ := hexists
  have hnonempty : ((candidates.filter Accepts).image Encodable.encode).Nonempty := by
    exact ⟨Encodable.encode d, Finset.mem_image.mpr
      ⟨d, Finset.mem_filter.mpr ⟨hd, haccept⟩, rfl⟩⟩
  have hmin := Finset.min'_mem
    ((candidates.filter Accepts).image Encodable.encode) hnonempty
  obtain ⟨c, _hc, hencode⟩ := Finset.mem_image.mp hmin
  refine ⟨c, ?_⟩
  rw [firstAcceptedInFinset, dite_eq_left hnonempty, ← hencode,
    Encodable.encodek]

end TNLean.MPS.AreaLaw
