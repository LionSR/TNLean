/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SemidefiniteRepair

/-!
# Uniform certificate rounding and rational arithmetic

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- A uniform entry mesh which absorbs both primary-variable and Gram-factor rounding
in matrix order `d`. -/
noncomputable def uniformCertificateRoundingMesh (d : ℕ) (ω : ℝ) : ℝ :=
  ω / (2 * ((d : ℝ) + 1) ^ 2)

theorem uniformCertificateRoundingMesh_pos {d : ℕ} {ω : ℝ} (hω : 0 < ω) :
    0 < uniformCertificateRoundingMesh d ω := by
  exact div_pos hω (by positivity)

/-- The uniform mesh controls every dimension factor appearing in the simultaneous
rounding theorem. -/
theorem uniformCertificateRoundingMesh_bounds (d : ℕ) {ω : ℝ} (hω : 0 ≤ ω) :
    (d : ℝ) * uniformCertificateRoundingMesh d ω ≤ ω ∧
      2 * ((d : ℝ) + 1) * uniformCertificateRoundingMesh d ω ≤ ω ∧
      (d : ℝ) ^ 2 * uniformCertificateRoundingMesh d ω ≤ ω ∧
      2 * (d : ℝ) ^ 2 * uniformCertificateRoundingMesh d ω ≤ ω := by
  let q : ℝ := 2 * ((d : ℝ) + 1) ^ 2
  have hq : 0 < q := by positivity
  have hmesh : 0 ≤ uniformCertificateRoundingMesh d ω :=
    div_nonneg hω hq.le
  have hscale : q * uniformCertificateRoundingMesh d ω = ω := by
    simp only [uniformCertificateRoundingMesh, q]
    exact mul_div_cancel₀ ω hq.ne'
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hdq : (d : ℝ) ≤ q := by
    dsimp only [q]
    nlinarith [sq_nonneg ((d : ℝ) + 1)]
  have htwodq : 2 * ((d : ℝ) + 1) ≤ q := by
    dsimp only [q]
    nlinarith [sq_nonneg (d : ℝ)]
  have hdsq : (d : ℝ) ^ 2 ≤ q := by
    dsimp only [q]
    nlinarith [sq_nonneg ((d : ℝ) + 2)]
  have htwodsqq : 2 * (d : ℝ) ^ 2 ≤ q := by
    dsimp only [q]
    nlinarith [sq_nonneg ((d : ℝ) + 1)]
  exact ⟨(mul_le_mul_of_nonneg_right hdq hmesh).trans_eq hscale,
    (mul_le_mul_of_nonneg_right htwodq hmesh).trans_eq hscale,
    (mul_le_mul_of_nonneg_right hdsq hmesh).trans_eq hscale,
    (mul_le_mul_of_nonneg_right htwodsqq hmesh).trans_eq hscale⟩

/-- Indices for all candidate-dependent rational comparisons in the approximate
Gram-factor certificate: three scalar tests, one `n × n` Gram residual, two `r × r`
Gram residuals, and one `r × r` boundary residual. -/
abbrev ApproxCertificateComparisonIndex (n r : ℕ) :=
  Fin 3 ⊕ ((Fin n × Fin n) ⊕
    ((Fin r × Fin r) ⊕ ((Fin r × Fin r) ⊕ (Fin r × Fin r))))

/-- Number of rational comparisons needed to test one six-matrix certificate. -/
def approxCertificateComparisonCount (n r : ℕ) : ℕ :=
  Fintype.card (ApproxCertificateComparisonIndex n r)

theorem approxCertificateComparisonCount_eq (n r : ℕ) :
    approxCertificateComparisonCount n r = n ^ 2 + 3 * r ^ 2 + 3 := by
  simp [approxCertificateComparisonCount, ApproxCertificateComparisonIndex, pow_two]
  omega

/-- Indices of the complex scalar-product terms in a direct dense evaluation of all
matrix products in one certificate: the density Gram product and objective product,
the two auxiliary Gram products, and the two products in `Z * A * Zᴴ`. -/
abbrev ApproxCertificateDenseProductTermIndex (a n r : ℕ) :=
  (Fin 2 × Fin n × Fin n × Fin n) ⊕
    ((Fin 2 × Fin r × Fin r × Fin r) ⊕
      ((Fin (a * r) × Fin n × Fin n) ⊕
        (Fin (a * r) × Fin (a * r) × Fin n)))

/-- Number of complex scalar-product terms in direct dense evaluation of all matrix
products appearing in one certificate. -/
def approxCertificateDenseProductTermCount (a n r : ℕ) : ℕ :=
  Fintype.card (ApproxCertificateDenseProductTermIndex a n r)

theorem approxCertificateDenseProductTermCount_eq (a n r : ℕ) :
    approxCertificateDenseProductTermCount a n r =
      2 * n ^ 3 + 2 * r ^ 3 + (a * r) * n ^ 2 + (a * r) ^ 2 * n := by
  simp [approxCertificateDenseProductTermCount,
    ApproxCertificateDenseProductTermIndex, pow_succ]
  ring

/-- The coordinate-count bound for a square Gaussian-rational matrix grid of order
`d`, integer radius `B`, and denominator `M`. -/
def matrixCoordinateGridCardBound (d B M : ℕ) : ℕ :=
  (2 * B * M + 1) ^ (2 * d ^ 2)

/-- The concrete product search over the three Hermitian primary variables and the
three Gram factors, using the uniform precision allowance `ω`. -/
noncomputable def uniformCertificateSearchGrid
    (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) :
    Finset (Matrix (Fin n) (Fin n) ℂ ×
      (Matrix ι ι ℂ × (Matrix ι ι ℂ ×
        (Matrix (Fin n) (Fin n) ℂ × (Matrix ι ι ℂ × Matrix ι ι ℂ))))) := by
  classical
  let r := Fintype.card ι
  let θA := uniformCertificateRoundingMesh n ω
  let θb := uniformCertificateRoundingMesh r ω
  exact rationalHermitianBoundedMatrixGrid (Fin n)
      (approxSDPDensityEntryBound n κ ε) θA ×ˢ
    (rationalHermitianBoundedMatrixGrid ι (approxSDPAuxEntryBound r η εb) θb ×ˢ
      (rationalHermitianBoundedMatrixGrid ι (approxSDPAuxEntryBound r η εb) θb ×ˢ
        (rationalGramCertificateGrid (Fin n)
            (gramCertificateBound (1 + κ + n * ε)) θA ×ˢ
          (rationalGramCertificateGrid ι
              (gramCertificateBound (η + 2 * r * εb)) θb ×ˢ
            rationalGramCertificateGrid ι
              (gramCertificateBound (η + 2 * r * εb)) θb))))

/-- Six-matrix candidate with every complex coordinate retained as a rational pair. -/
abbrev RationalCertificateCode (ι : Type*) (n : ℕ) :=
  RationalMatrixCode (Fin n) ×
    (RationalMatrixCode ι × (RationalMatrixCode ι ×
      (RationalMatrixCode (Fin n) × (RationalMatrixCode ι × RationalMatrixCode ι))))

/-- Decode all six matrices of a rational certificate candidate. -/
def RationalCertificateCode.decode {ι : Type*} {n : ℕ}
    (c : RationalCertificateCode ι n) :=
  (c.1.decode, c.2.1.decode, c.2.2.1.decode, c.2.2.2.1.decode,
    c.2.2.2.2.1.decode, c.2.2.2.2.2.decode)

theorem RationalCertificateCode.decode_injective {ι : Type*} {n : ℕ} :
    Function.Injective
      (RationalCertificateCode.decode : RationalCertificateCode ι n → _) := by
  intro c d hcd
  apply Prod.ext
  · apply RationalMatrixCode.decode_injective
    exact congrArg (fun x ↦ x.1) hcd
  · apply Prod.ext
    · apply RationalMatrixCode.decode_injective
      exact congrArg (fun x ↦ x.2.1) hcd
    · apply Prod.ext
      · apply RationalMatrixCode.decode_injective
        exact congrArg (fun x ↦ x.2.2.1) hcd
      · apply Prod.ext
        · apply RationalMatrixCode.decode_injective
          exact congrArg (fun x ↦ x.2.2.2.1) hcd
        · apply Prod.ext
          · apply RationalMatrixCode.decode_injective
            exact congrArg (fun x ↦ x.2.2.2.2.1) hcd
          · apply RationalMatrixCode.decode_injective
            exact congrArg (fun x ↦ x.2.2.2.2.2) hcd

/-- Exact rational-coordinate evaluation of the compressed boundary map. -/
def rationalCompressedBoundaryCode
    {a s b : Type*} [Fintype a] {n : ℕ}
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (A : RationalRectMatrixCode (Fin n) (Fin n)) :
    RationalRectMatrixCode (s × b) (s × b) :=
  RationalRectMatrixCode.partialTraceFirst
    (RationalRectMatrixCode.mul
      (RationalRectMatrixCode.mul Z A)
      (RationalRectMatrixCode.conjTranspose Z))

/-- Compute every scalar and residual inspected by the certificate test directly in
rational arithmetic.  The fixed isometry, objective, boundary center, and both shifts
are supplied by rational coordinates, as is the six-matrix candidate. -/
def RationalCertificateCode.testValues
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (ε εb : ℚ) (c : RationalCertificateCode (s × b) n) :
    RationalApproxCertificateTestValues (s × b) n :=
  let A := c.1.toRect
  let P := c.2.1.toRect
  let N := c.2.2.1.toRect
  let QA := c.2.2.2.1.toRect
  let QP := c.2.2.2.2.1.toRect
  let QN := c.2.2.2.2.2.toRect
  { densityTrace := (RationalRectMatrixCode.trace A).1
    positiveTrace := (RationalRectMatrixCode.trace P).1
    negativeTrace := (RationalRectMatrixCode.trace N).1
    objective := (RationalRectMatrixCode.trace
      (RationalRectMatrixCode.mul A K)).1
    boundaryResidual := RationalRectMatrixCode.sub
      (RationalRectMatrixCode.sub (rationalCompressedBoundaryCode Z A) X)
      (RationalRectMatrixCode.sub P N)
    densityGramResidual := RationalRectMatrixCode.sub
      (RationalRectMatrixCode.addRealDiagonal A ε)
      (RationalRectMatrixCode.mul QA (RationalRectMatrixCode.conjTranspose QA))
    positiveGramResidual := RationalRectMatrixCode.sub
      (RationalRectMatrixCode.addRealDiagonal P εb)
      (RationalRectMatrixCode.mul QP (RationalRectMatrixCode.conjTranspose QP))
    negativeGramResidual := RationalRectMatrixCode.sub
      (RationalRectMatrixCode.addRealDiagonal N εb)
      (RationalRectMatrixCode.mul QN (RationalRectMatrixCode.conjTranspose QN)) }

/-- Decoding the directly evaluated rational test record gives exactly the complex
matrix expressions used by certificate soundness. -/
theorem RationalCertificateCode.testValues_correct
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (ε εb : ℚ) (c : RationalCertificateCode (s × b) n) :
    let v := c.testValues Z K X ε εb
    c.1.decode.trace.re = (v.densityTrace : ℝ) ∧
      c.2.1.decode.trace.re = (v.positiveTrace : ℝ) ∧
      c.2.2.1.decode.trace.re = (v.negativeTrace : ℝ) ∧
      (c.1.decode * RationalRectMatrixCode.decode K).trace.re =
        (v.objective : ℝ) ∧
      (∀ i j,
        ((compressedBoundaryLM (RationalRectMatrixCode.decode Z) c.1.decode -
            RationalRectMatrixCode.decode X) -
            (c.2.1.decode - c.2.2.1.decode)) i j =
          decodeRationalComplex (v.boundaryResidual i j)) ∧
      (∀ i j,
        (c.1.decode + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
            c.2.2.2.1.decode * c.2.2.2.1.decodeᴴ) i j =
          decodeRationalComplex (v.densityGramResidual i j)) ∧
      (∀ i j,
        (c.2.1.decode + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
            c.2.2.2.2.1.decode * c.2.2.2.2.1.decodeᴴ) i j =
          decodeRationalComplex (v.positiveGramResidual i j)) ∧
      ∀ i j,
        (c.2.2.1.decode + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
            c.2.2.2.2.2.decode * c.2.2.2.2.2.decodeᴴ) i j =
          decodeRationalComplex (v.negativeGramResidual i j) := by
  dsimp only [RationalCertificateCode.testValues]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg Complex.re
      (RationalRectMatrixCode.decode_trace c.1.toRect)
    simpa [decodeRationalComplex] using h.symm
  · have h := congrArg Complex.re
      (RationalRectMatrixCode.decode_trace c.2.1.toRect)
    simpa [decodeRationalComplex] using h.symm
  · have h := congrArg Complex.re
      (RationalRectMatrixCode.decode_trace c.2.2.1.toRect)
    simpa [decodeRationalComplex] using h.symm
  · have h := congrArg Complex.re
      (RationalRectMatrixCode.decode_trace
        (RationalRectMatrixCode.mul c.1.toRect K))
    simpa [decodeRationalComplex] using h.symm
  · intro i j
    have hdecode : RationalRectMatrixCode.decode
          (RationalRectMatrixCode.sub
            (RationalRectMatrixCode.sub
              (rationalCompressedBoundaryCode Z c.1.toRect) X)
            (RationalRectMatrixCode.sub c.2.1.toRect c.2.2.1.toRect)) =
        (compressedBoundaryLM (RationalRectMatrixCode.decode Z) c.1.decode -
          RationalRectMatrixCode.decode X) -
          (c.2.1.decode - c.2.2.1.decode) := by
      rw [RationalRectMatrixCode.decode_sub, RationalRectMatrixCode.decode_sub,
        RationalRectMatrixCode.decode_sub, compressedBoundaryLM_apply]
      simp [rationalCompressedBoundaryCode]
    exact (congrArg (fun M ↦ M i j) hdecode).symm
  · intro i j
    have hdecode : RationalRectMatrixCode.decode
          (RationalRectMatrixCode.sub
            (RationalRectMatrixCode.addRealDiagonal c.1.toRect ε)
            (RationalRectMatrixCode.mul c.2.2.2.1.toRect
              (RationalRectMatrixCode.conjTranspose c.2.2.2.1.toRect))) =
        c.1.decode + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          c.2.2.2.1.decode * c.2.2.2.1.decodeᴴ := by
      simp
    exact (congrArg (fun M ↦ M i j) hdecode).symm
  · intro i j
    have hdecode : RationalRectMatrixCode.decode
          (RationalRectMatrixCode.sub
            (RationalRectMatrixCode.addRealDiagonal c.2.1.toRect εb)
            (RationalRectMatrixCode.mul c.2.2.2.2.1.toRect
              (RationalRectMatrixCode.conjTranspose c.2.2.2.2.1.toRect))) =
        c.2.1.decode + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
          c.2.2.2.2.1.decode * c.2.2.2.2.1.decodeᴴ := by
      simp
    exact (congrArg (fun M ↦ M i j) hdecode).symm
  · intro i j
    have hdecode : RationalRectMatrixCode.decode
          (RationalRectMatrixCode.sub
            (RationalRectMatrixCode.addRealDiagonal c.2.2.1.toRect εb)
            (RationalRectMatrixCode.mul c.2.2.2.2.2.toRect
              (RationalRectMatrixCode.conjTranspose c.2.2.2.2.2.toRect))) =
        c.2.2.1.decode + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
          c.2.2.2.2.2.decode * c.2.2.2.2.2.decodeᴴ := by
      simp
    exact (congrArg (fun M ↦ M i j) hdecode).symm

/-- Entrywise bounds on a decoded rational certificate imply acceptance of its directly
computed rational test record. -/
theorem RationalCertificateCode.testValues_accepts_of_bounds
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ : ℚ) (c : RationalCertificateCode (s × b) n)
    {η E κ ε εb δ ζ ζA ζP ζN : ℚ}
    (hε : 0 ≤ ε) (hεb : 0 ≤ εb) (hζ : 0 ≤ ζ)
    (hζA : 0 ≤ ζA) (hζP : 0 ≤ ζP) (hζN : 0 ≤ ζN)
    (htrace : |1 - c.1.decode.trace.re| ≤ (κ : ℝ))
    (hAgr : ∀ i j,
      ‖(c.1.decode + (εA₀ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        c.2.2.2.1.decode * c.2.2.2.1.decodeᴴ) i j‖ ≤ (ζA : ℝ))
    (hAbudget : εA₀ + ((n : ℚ) + 1) * ζA ≤ ε)
    (hPgr : ∀ i j,
      ‖(c.2.1.decode + (εb₀ : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
        c.2.2.2.2.1.decode * c.2.2.2.2.1.decodeᴴ) i j‖ ≤ (ζP : ℝ))
    (hPbudget : εb₀ + ((Fintype.card (s × b) : ℚ) + 1) * ζP ≤ εb)
    (hNgr : ∀ i j,
      ‖(c.2.2.1.decode + (εb₀ : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
        c.2.2.2.2.2.decode * c.2.2.2.2.2.decodeᴴ) i j‖ ≤ (ζN : ℝ))
    (hNbudget : εb₀ + ((Fintype.card (s × b) : ℚ) + 1) * ζN ≤ εb)
    (hboundary : ∀ i j,
      ‖((compressedBoundaryLM (RationalRectMatrixCode.decode Z) c.1.decode -
        RationalRectMatrixCode.decode X) -
        (c.2.1.decode - c.2.2.1.decode)) i j‖ ≤ (ζ : ℝ))
    (hscale : (Fintype.card (s × b) : ℚ) ^ 2 * ζ ≤ δ)
    (htraces : c.2.1.decode.trace.re + c.2.2.1.decode.trace.re ≤ (η : ℝ))
    (henergy : (c.1.decode * RationalRectMatrixCode.decode K).trace.re ≤ (E : ℝ)) :
    (c.testValues Z K X εA₀ εb₀).Accepts
      η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN := by
  obtain ⟨htraceA, htraceP, htraceN, hobjective, hboundaryEq,
      hAfactor, hPfactor, hNfactor⟩ := c.testValues_correct Z K X εA₀ εb₀
  apply RationalApproxCertificateTestValues.accepts_of_norm_bounds
  · exact hε
  · exact hεb
  · exact hζ
  · exact hζA
  · exact hζP
  · exact hζN
  · rwa [← htraceA]
  · intro i j
    rw [← hAfactor i j]
    exact hAgr i j
  · exact hAbudget
  · intro i j
    rw [← hPfactor i j]
    exact hPgr i j
  · exact hPbudget
  · intro i j
    rw [← hNfactor i j]
    exact hNgr i j
  · exact hNbudget
  · intro i j
    rw [← hboundaryEq i j]
    exact hboundary i j
  · exact hscale
  · rw [htraceP, htraceN] at htraces
    exact_mod_cast htraces
  · rw [hobjective] at henergy
    exact_mod_cast henergy

/-- Executable exhaustive search on an ordered list of rational certificate codes,
using the direct rational evaluator for the fixed compressed input. -/
def firstAcceptedRationalCertificateCode
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ) :
    List (RationalCertificateCode (s × b) n) →
      Option (RationalCertificateCode (s × b) n) :=
  firstAcceptedRationalApproxCertificate
    (fun c ↦ c.testValues Z K X εA₀ εb₀)
    η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN

/-- Natural ceiling computed in the rational floor ring. -/
def rationalNatCeil (q : ℚ) : ℕ := ⌈q⌉₊

theorem rationalNatCeil_cast_real {q : ℚ} (hq : 0 ≤ q) :
    ⌈(q : ℝ)⌉₊ = rationalNatCeil q := by
  let x : ℚ≥0 := ⟨q, hq⟩
  exact (NNRat.ceil_cast (K := ℝ) x).trans (NNRat.ceil_coe x).symm

/-- Rational versions of the entry and Gram bounds used in the certificate grid. -/
def rationalGramCertificateBound (x : ℚ) : ℚ := 1 + |x|

def rationalApproxSDPDensityEntryBound (n : ℕ) (κ ε : ℚ) : ℚ :=
  n * rationalGramCertificateBound (1 + κ + n * ε) + ε

def rationalApproxSDPAuxEntryBound (r : ℕ) (η εb : ℚ) : ℚ :=
  r * rationalGramCertificateBound (η + 2 * r * εb) + εb

def rationalUniformCertificateRoundingMesh (d : ℕ) (ω : ℚ) : ℚ :=
  ω / (2 * ((d : ℚ) + 1) ^ 2)

def rationalMatrixGridRadiusQ (R : ℚ) : ℕ := rationalNatCeil R

def rationalMatrixGridOrderQ (δ : ℚ) : ℕ := rationalNatCeil (1 / δ)

def rationalGramCertificateRadiusQ (C : ℚ) : ℕ := rationalNatCeil C + 1

def rationalGramCertificateOrderQ (d : ℕ) (C ζ : ℚ) : ℕ :=
  rationalNatCeil
    ((d : ℚ) * (2 * rationalGramCertificateRadiusQ C + 1) / ζ)

@[simp] theorem rationalGramCertificateBound_cast (x : ℚ) :
    (rationalGramCertificateBound x : ℝ) = gramCertificateBound (x : ℝ) := by
  simp [rationalGramCertificateBound, gramCertificateBound]

@[simp] theorem rationalApproxSDPDensityEntryBound_cast
    (n : ℕ) (κ ε : ℚ) :
    (rationalApproxSDPDensityEntryBound n κ ε : ℝ) =
      approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ) := by
  simp [rationalApproxSDPDensityEntryBound, approxSDPDensityEntryBound]

@[simp] theorem rationalApproxSDPAuxEntryBound_cast
    (r : ℕ) (η εb : ℚ) :
    (rationalApproxSDPAuxEntryBound r η εb : ℝ) =
      approxSDPAuxEntryBound r (η : ℝ) (εb : ℝ) := by
  simp [rationalApproxSDPAuxEntryBound, approxSDPAuxEntryBound]

@[simp] theorem rationalUniformCertificateRoundingMesh_cast
    (d : ℕ) (ω : ℚ) :
    (rationalUniformCertificateRoundingMesh d ω : ℝ) =
      uniformCertificateRoundingMesh d (ω : ℝ) := by
  simp [rationalUniformCertificateRoundingMesh, uniformCertificateRoundingMesh]

theorem rationalMatrixGridRadius_ratCast {R : ℚ} (hR : 0 ≤ R) :
    rationalMatrixGridRadius (R : ℝ) = rationalMatrixGridRadiusQ R := by
  exact rationalNatCeil_cast_real hR

theorem rationalMatrixGridOrder_ratCast {δ : ℚ} (hδ : 0 < δ) :
    rationalMatrixGridOrder (δ : ℝ) = rationalMatrixGridOrderQ δ := by
  simpa [rationalMatrixGridOrder, rationalMatrixGridOrderQ] using
    rationalNatCeil_cast_real (one_div_nonneg.mpr hδ.le)

theorem rationalGramCertificateRadius_ratCast {C : ℚ} (hC : 0 ≤ C) :
    rationalGramCertificateRadius (C : ℝ) = rationalGramCertificateRadiusQ C := by
  rw [rationalGramCertificateRadius, rationalGramCertificateRadiusQ,
    rationalNatCeil_cast_real hC]

theorem rationalGramCertificateOrder_ratCast
    (ι : Type*) [Fintype ι] {C ζ : ℚ} (hC : 0 ≤ C) (hζ : 0 < ζ) :
    rationalGramCertificateOrder ι (C : ℝ) (ζ : ℝ) =
      rationalGramCertificateOrderQ (Fintype.card ι) C ζ := by
  rw [rationalGramCertificateOrder, rationalGramCertificateOrderQ,
    rationalGramCertificateRadius_ratCast hC]
  let q : ℚ := (Fintype.card ι : ℚ) *
    (2 * rationalGramCertificateRadiusQ C + 1) / ζ
  have hq : 0 ≤ q := by positivity
  simpa [q] using rationalNatCeil_cast_real hq

/-- The eight natural parameters of the fully discrete rational certificate grid. -/
structure RationalCertificateGridParameters where
  densityRadius : ℕ
  densityOrder : ℕ
  boundaryRadius : ℕ
  boundaryOrder : ℕ
  densityGramRadius : ℕ
  densityGramOrder : ℕ
  boundaryGramRadius : ℕ
  boundaryGramOrder : ℕ

/-- Compute all eight grid parameters using rational arithmetic only. -/
def rationalCertificateGridParameters
    (n r : ℕ) (η κ ε εb ω : ℚ) : RationalCertificateGridParameters :=
  let θA := rationalUniformCertificateRoundingMesh n ω
  let θb := rationalUniformCertificateRoundingMesh r ω
  let CA := rationalGramCertificateBound (1 + κ + n * ε)
  let Cb := rationalGramCertificateBound (η + 2 * r * εb)
  { densityRadius := rationalMatrixGridRadiusQ
      (rationalApproxSDPDensityEntryBound n κ ε)
    densityOrder := rationalMatrixGridOrderQ θA
    boundaryRadius := rationalMatrixGridRadiusQ
      (rationalApproxSDPAuxEntryBound r η εb)
    boundaryOrder := rationalMatrixGridOrderQ θb
    densityGramRadius := rationalGramCertificateRadiusQ CA
    densityGramOrder := rationalGramCertificateOrderQ n CA θA
    boundaryGramRadius := rationalGramCertificateRadiusQ Cb
    boundaryGramOrder := rationalGramCertificateOrderQ r Cb θb }

end TNLean.MPS.AreaLaw
