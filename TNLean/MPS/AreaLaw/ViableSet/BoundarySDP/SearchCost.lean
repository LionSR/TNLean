/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.CertificateSearch
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.InputEncoding

/-!
# Arithmetic heights and cost of finite certificate search

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Every expression tested for a six-grid candidate obeys the single uniform height
bound `uniformCertificateTestExpressionHeight`. -/
theorem uniformCertificateSearchGrid_testExpressions_height_le
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b]
    {n HD : ℕ} {η κ ε εb ω : ℝ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {A QA : Matrix (Fin n) (Fin n) ℂ}
    {P N QP QN : Matrix (s × b) (s × b) ℂ}
    (hsearch : (A, P, N, QA, QP, QN) ∈
      uniformCertificateSearchGrid (s × b) n η κ ε εb ω)
    (hZ : Matrix.HasRationalEntriesOfHeight HD Z)
    (hK : Matrix.HasRationalEntriesOfHeight HD K)
    (hX : Matrix.HasRationalEntriesOfHeight HD X)
    (hε : HasRationalComplexCoordinatesOfHeight HD (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight HD (εb : ℂ)) :
    let HC := uniformCertificateCandidateEntryHeight (s × b) n η κ ε εb ω
    let HT := uniformCertificateTestExpressionHeight
      (Fintype.card a) n (Fintype.card (s × b)) HD HC
    Matrix.HasRationalEntriesOfHeight HT
        ((compressedBoundaryLM Z A - X) - (P - N)) ∧
      HasRationalComplexCoordinatesOfHeight HT (A * K).trace ∧
      HasRationalComplexCoordinatesOfHeight HT A.trace ∧
      HasRationalComplexCoordinatesOfHeight HT P.trace ∧
      HasRationalComplexCoordinatesOfHeight HT N.trace ∧
      Matrix.HasRationalEntriesOfHeight HT
        (A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) ∧
      Matrix.HasRationalEntriesOfHeight HT
        (P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) ∧
      Matrix.HasRationalEntriesOfHeight HT
        (N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) := by
  obtain ⟨hA, hP, hN, hQA, hQP, hQN⟩ :=
    uniformCertificateSearchGrid_entries_height_le hsearch
  let HC := uniformCertificateCandidateEntryHeight (s × b) n η κ ε εb ω
  change Matrix.HasRationalEntriesOfHeight HC A at hA
  change Matrix.HasRationalEntriesOfHeight HC P at hP
  change Matrix.HasRationalEntriesOfHeight HC N at hN
  change Matrix.HasRationalEntriesOfHeight HC QA at hQA
  change Matrix.HasRationalEntriesOfHeight HC QP at hQP
  change Matrix.HasRationalEntriesOfHeight HC QN at hQN
  let Hb := compressedBoundaryResidualHeight (Fintype.card a) n HD HC HD HC HC
  let Ho := matrixTraceProductHeight n HC HD
  let Ht := max (matrixTraceHeight n HC) (matrixTraceHeight (Fintype.card (s × b)) HC)
  let HGA := shiftedGramResidualHeight n HC HD HC
  let HGb := shiftedGramResidualHeight (Fintype.card (s × b)) HC HD HC
  let HT := max Hb (max Ho (max Ht (max HGA HGb)))
  have hb : Matrix.HasRationalEntriesOfHeight Hb
      ((compressedBoundaryLM Z A - X) - (P - N)) := by
    simpa [Hb, compressedBoundaryResidualHeight, compressedBoundaryHeight,
      matrixTraceHeight, matrixProductHeight] using
      compressedBoundaryResidual_hasRationalEntriesOfHeight hZ hA hX hP hN
  have ho : HasRationalComplexCoordinatesOfHeight Ho (A * K).trace := by
    simpa [Ho, matrixTraceProductHeight, matrixTraceHeight, matrixProductHeight] using
      Matrix.HasRationalEntriesOfHeight.trace_mul hA hK
  have htA : HasRationalComplexCoordinatesOfHeight Ht A.trace :=
    (Matrix.HasRationalEntriesOfHeight.trace hA).mono (by simp [Ht, matrixTraceHeight])
  have htP : HasRationalComplexCoordinatesOfHeight Ht P.trace :=
    (Matrix.HasRationalEntriesOfHeight.trace hP).mono (by simp [Ht, matrixTraceHeight])
  have htN : HasRationalComplexCoordinatesOfHeight Ht N.trace :=
    (Matrix.HasRationalEntriesOfHeight.trace hN).mono (by simp [Ht, matrixTraceHeight])
  have hgA : Matrix.HasRationalEntriesOfHeight HGA
      (A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) := by
    simpa [HGA, shiftedGramResidualHeight, matrixProductHeight] using
      Matrix.HasRationalEntriesOfHeight.shiftedGramResidual hA hε hQA
  have hgP : Matrix.HasRationalEntriesOfHeight HGb
      (P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) := by
    simpa [HGb, shiftedGramResidualHeight, matrixProductHeight] using
      Matrix.HasRationalEntriesOfHeight.shiftedGramResidual hP hεb hQP
  have hgN : Matrix.HasRationalEntriesOfHeight HGb
      (N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) := by
    simpa [HGb, shiftedGramResidualHeight, matrixProductHeight] using
      Matrix.HasRationalEntriesOfHeight.shiftedGramResidual hN hεb hQN
  change Matrix.HasRationalEntriesOfHeight HT _ ∧
    HasRationalComplexCoordinatesOfHeight HT _ ∧
    HasRationalComplexCoordinatesOfHeight HT _ ∧
    HasRationalComplexCoordinatesOfHeight HT _ ∧
    HasRationalComplexCoordinatesOfHeight HT _ ∧
    Matrix.HasRationalEntriesOfHeight HT _ ∧
    Matrix.HasRationalEntriesOfHeight HT _ ∧
    Matrix.HasRationalEntriesOfHeight HT _
  exact ⟨hb.mono (by simp [HT]), ho.mono (by simp [HT]),
    htA.mono (by simp [HT]), htP.mono (by simp [HT]), htN.mono (by simp [HT]),
    hgA.mono (by simp [HT]), hgP.mono (by simp [HT]), hgN.mono (by simp [HT])⟩

/-- An encoded fixed input supplies the common height hypothesis needed by the uniform
certificate-expression bound. -/
theorem RationalCompressedSDPInputEncoding.testExpressions_height_le
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b]
    {n : ℕ} {η κ ε εb ω : ℝ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {A QA : Matrix (Fin n) (Fin n) ℂ}
    {P N QP QN : Matrix (s × b) (s × b) ℂ}
    (hinput : RationalCompressedSDPInputEncoding Z K X ε εb)
    (hsearch : (A, P, N, QA, QP, QN) ∈
      uniformCertificateSearchGrid (s × b) n η κ ε εb ω) :
    let HC := uniformCertificateCandidateEntryHeight (s × b) n η κ ε εb ω
    let HT := uniformCertificateTestExpressionHeight
      (Fintype.card a) n (Fintype.card (s × b)) hinput.height HC
    Matrix.HasRationalEntriesOfHeight HT
        ((compressedBoundaryLM Z A - X) - (P - N)) ∧
      HasRationalComplexCoordinatesOfHeight HT (A * K).trace ∧
      HasRationalComplexCoordinatesOfHeight HT A.trace ∧
      HasRationalComplexCoordinatesOfHeight HT P.trace ∧
      HasRationalComplexCoordinatesOfHeight HT N.trace ∧
      Matrix.HasRationalEntriesOfHeight HT
        (A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) ∧
      Matrix.HasRationalEntriesOfHeight HT
        (P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) ∧
      Matrix.HasRationalEntriesOfHeight HT
        (N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) :=
  uniformCertificateSearchGrid_testExpressions_height_le hsearch
    hinput.z_height hinput.objective_height hinput.boundary_height
    hinput.densityShift_height hinput.boundaryShift_height

/-- One bit-length bound for every rational coordinate occurring in certificate tests,
given a common fixed-data height bound `HD`. -/
noncomputable def uniformCertificateOperandBitLength
    (a : ℕ) (ι : Type*) [Fintype ι] (n : ℕ)
    (η κ ε εb ω : ℝ) (HD : ℕ) : ℕ :=
  certificateTestOperandBitLength a n (Fintype.card ι) HD
    (uniformCertificateCandidateEntryHeight ι n η κ ε εb ω)

/-- The uniform executable-test operand bound is monotone in the common height assigned
to the fixed input data. -/
theorem uniformCertificateOperandBitLength_mono_height
    (a : ℕ) (ι : Type*) [Fintype ι] (n : ℕ)
    (η κ ε εb ω : ℝ) {HD HD' : ℕ} (hHD : HD ≤ HD') :
    uniformCertificateOperandBitLength a ι n η κ ε εb ω HD ≤
      uniformCertificateOperandBitLength a ι n η κ ε εb ω HD' := by
  exact certificateTestOperandBitLength_mono_fixedData _ _ _ _ hHD

/-- Common rational height of the twelve scalar thresholds inspected by the direct
certificate acceptance test. -/
def rationalCertificateThresholdHeight
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ) : ℕ :=
  max (rationalHeight εA₀) <| max (rationalHeight εb₀) <|
    max (rationalHeight η) <| max (rationalHeight E) <|
      max (rationalHeight κ) <| max (rationalHeight ε) <|
        max (rationalHeight εb) <| max (rationalHeight δ) <|
          max (rationalHeight ζ) <| max (rationalHeight ζA) <|
            max (rationalHeight ζP) (rationalHeight ζN)

/-- Every scalar inspected by the acceptance test is bounded by the common threshold
height. -/
theorem rationalCertificateThresholdHeight_bounds
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ) :
    rationalHeight εA₀ ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight εb₀ ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight η ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight E ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight κ ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight ε ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight εb ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight δ ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight ζ ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight ζA ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight ζP ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ∧
    rationalHeight ζN ≤ rationalCertificateThresholdHeight
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN := by
  simp [rationalCertificateThresholdHeight]

/-- Operand length for the executable rational test, including both matrix-expression
coordinates and every scalar threshold used in its comparisons. -/
noncomputable def rationalCertificateOperandBitLength
    (a : ℕ) (ι : Type*) [Fintype ι] (n : ℕ)
    (ηgrid κgrid εgrid εbgrid ωgrid : ℝ) (HD : ℕ)
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ) : ℕ :=
  uniformCertificateOperandBitLength a ι n ηgrid κgrid εgrid εbgrid ωgrid <|
    max HD (rationalCertificateThresholdHeight
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN)

/-- The rational certificate-test operand bound is monotone in the common fixed-data
height while all twelve scalar thresholds are held fixed. -/
theorem rationalCertificateOperandBitLength_mono_height
    (a : ℕ) (ι : Type*) [Fintype ι] (n : ℕ)
    (ηgrid κgrid εgrid εbgrid ωgrid : ℝ) {HD HD' : ℕ}
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ) (hHD : HD ≤ HD') :
    rationalCertificateOperandBitLength a ι n
        ηgrid κgrid εgrid εbgrid ωgrid HD
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN ≤
      rationalCertificateOperandBitLength a ι n
        ηgrid κgrid εgrid εbgrid ωgrid HD'
        εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN := by
  unfold rationalCertificateOperandBitLength
  exact uniformCertificateOperandBitLength_mono_height _ _ _ _ _ _ _ _
    (max_le_max_right _ hHD)

/-- Total number of candidate-dependent rational comparisons in exhaustive search of
the six-grid certificate space. -/
noncomputable def uniformCertificateSearchComparisonCount
    (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) : ℕ :=
  (uniformCertificateSearchGrid ι n η κ ε εb ω).card *
    approxCertificateComparisonCount n (Fintype.card ι)

/-- Total number of complex scalar-product terms in direct dense evaluation of every
candidate in the six-grid search. -/
noncomputable def uniformCertificateSearchDenseProductTermCount
    (a : ℕ) (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) : ℕ :=
  (uniformCertificateSearchGrid ι n η κ ε εb ω).card *
    approxCertificateDenseProductTermCount a n (Fintype.card ι)

/-- A conservative schoolbook cost charged to one rational arithmetic operation or
comparison on inputs of at most `L` bits. -/
def rationalSchoolbookOperationCost (L : ℕ) : ℕ :=
  8 * (L + 1) ^ 2

/-- The schoolbook charge for one rational operation is monotone in the certified
operand length. -/
theorem rationalSchoolbookOperationCost_mono {L L' : ℕ} (hL : L ≤ L') :
    rationalSchoolbookOperationCost L ≤ rationalSchoolbookOperationCost L' := by
  unfold rationalSchoolbookOperationCost
  gcongr

/-- Total schoolbook bit-operation charge for the comparisons and dense scalar-product
terms in exhaustive search, under a uniform `L`-bit operand bound. -/
noncomputable def uniformCertificateSearchSchoolbookBitCost
    (a : ℕ) (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) (L : ℕ) : ℕ :=
  (uniformCertificateSearchGrid ι n η κ ε εb ω).card *
    (approxCertificateComparisonCount n (Fintype.card ι) +
      approxCertificateDenseProductTermCount a n (Fintype.card ι)) *
    rationalSchoolbookOperationCost L

/-- Enlarging the certified operand length enlarges the total exhaustive-search
schoolbook charge. -/
theorem uniformCertificateSearchSchoolbookBitCost_mono_operand
    (a : ℕ) (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ)
    {L L' : ℕ} (hL : L ≤ L') :
    uniformCertificateSearchSchoolbookBitCost a ι n η κ ε εb ω L ≤
      uniformCertificateSearchSchoolbookBitCost a ι n η κ ε εb ω L' := by
  unfold uniformCertificateSearchSchoolbookBitCost
  exact Nat.mul_le_mul_left _ (rationalSchoolbookOperationCost_mono hL)

/-- Any cardinality bound for the six-grid search immediately gives the corresponding
total comparison bound. -/
theorem uniformCertificateSearchComparisonCount_le_of_card_le
    {ι : Type*} [Fintype ι] {n C : ℕ} {η κ ε εb ω : ℝ}
    (hcard : (uniformCertificateSearchGrid ι n η κ ε εb ω).card ≤ C) :
    uniformCertificateSearchComparisonCount ι n η κ ε εb ω ≤
      C * (n ^ 2 + 3 * Fintype.card ι ^ 2 + 3) := by
  rw [uniformCertificateSearchComparisonCount, approxCertificateComparisonCount_eq]
  exact Nat.mul_le_mul_right _ hcard

theorem uniformCertificateSearchDenseProductTermCount_le_of_card_le
    {a : ℕ} {ι : Type*} [Fintype ι] {n C : ℕ} {η κ ε εb ω : ℝ}
    (hcard : (uniformCertificateSearchGrid ι n η κ ε εb ω).card ≤ C) :
    uniformCertificateSearchDenseProductTermCount a ι n η κ ε εb ω ≤
      C * (2 * n ^ 3 + 2 * Fintype.card ι ^ 3 +
        (a * Fintype.card ι) * n ^ 2 + (a * Fintype.card ι) ^ 2 * n) := by
  rw [uniformCertificateSearchDenseProductTermCount,
    approxCertificateDenseProductTermCount_eq]
  exact Nat.mul_le_mul_right _ hcard

theorem uniformCertificateSearchSchoolbookBitCost_le_of_card_le
    {a L : ℕ} {ι : Type*} [Fintype ι] {n C : ℕ} {η κ ε εb ω : ℝ}
    (hcard : (uniformCertificateSearchGrid ι n η κ ε εb ω).card ≤ C) :
    uniformCertificateSearchSchoolbookBitCost a ι n η κ ε εb ω L ≤
      C * ((n ^ 2 + 3 * Fintype.card ι ^ 2 + 3) +
        (2 * n ^ 3 + 2 * Fintype.card ι ^ 3 +
          (a * Fintype.card ι) * n ^ 2 + (a * Fintype.card ι) ^ 2 * n)) *
        rationalSchoolbookOperationCost L := by
  rw [uniformCertificateSearchSchoolbookBitCost,
    approxCertificateComparisonCount_eq, approxCertificateDenseProductTermCount_eq]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcard)

/-- The explicit product bound for the cardinality of the six-grid search. -/
noncomputable def uniformCertificateSearchCardBound
    (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) : ℕ :=
  let r := Fintype.card ι
  let θA := uniformCertificateRoundingMesh n ω
  let θb := uniformCertificateRoundingMesh r ω
  matrixCoordinateGridCardBound n
      (rationalMatrixGridRadius (approxSDPDensityEntryBound n κ ε))
      (rationalMatrixGridOrder θA) *
    (matrixCoordinateGridCardBound r
      (rationalMatrixGridRadius (approxSDPAuxEntryBound r η εb))
      (rationalMatrixGridOrder θb) *
    (matrixCoordinateGridCardBound r
      (rationalMatrixGridRadius (approxSDPAuxEntryBound r η εb))
      (rationalMatrixGridOrder θb) *
    (matrixCoordinateGridCardBound n
      (rationalGramCertificateRadius (gramCertificateBound (1 + κ + n * ε)))
      (rationalGramCertificateOrder (Fin n)
        (gramCertificateBound (1 + κ + n * ε)) θA) *
    (matrixCoordinateGridCardBound r
      (rationalGramCertificateRadius (gramCertificateBound (η + 2 * r * εb)))
      (rationalGramCertificateOrder ι
        (gramCertificateBound (η + 2 * r * εb)) θb) *
    matrixCoordinateGridCardBound r
      (rationalGramCertificateRadius (gramCertificateBound (η + 2 * r * εb)))
      (rationalGramCertificateOrder ι
        (gramCertificateBound (η + 2 * r * εb)) θb)))))

/-- The complete six-grid search has the product of the six coordinate-count bounds.
This is the explicit finite search-space estimate used in the LVV runtime analysis. -/
theorem uniformCertificateSearchGrid_card_le
    (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) :
    let r := Fintype.card ι
    let θA := uniformCertificateRoundingMesh n ω
    let θb := uniformCertificateRoundingMesh r ω
    (uniformCertificateSearchGrid ι n η κ ε εb ω).card ≤
      matrixCoordinateGridCardBound n
          (rationalMatrixGridRadius (approxSDPDensityEntryBound n κ ε))
          (rationalMatrixGridOrder θA) *
        (matrixCoordinateGridCardBound r
          (rationalMatrixGridRadius (approxSDPAuxEntryBound r η εb))
          (rationalMatrixGridOrder θb) *
        (matrixCoordinateGridCardBound r
          (rationalMatrixGridRadius (approxSDPAuxEntryBound r η εb))
          (rationalMatrixGridOrder θb) *
        (matrixCoordinateGridCardBound n
          (rationalGramCertificateRadius (gramCertificateBound (1 + κ + n * ε)))
          (rationalGramCertificateOrder (Fin n)
            (gramCertificateBound (1 + κ + n * ε)) θA) *
        (matrixCoordinateGridCardBound r
          (rationalGramCertificateRadius (gramCertificateBound (η + 2 * r * εb)))
          (rationalGramCertificateOrder ι
            (gramCertificateBound (η + 2 * r * εb)) θb) *
        matrixCoordinateGridCardBound r
          (rationalGramCertificateRadius (gramCertificateBound (η + 2 * r * εb)))
          (rationalGramCertificateOrder ι
            (gramCertificateBound (η + 2 * r * εb)) θb))))) := by
  dsimp only
  let r := Fintype.card ι
  let θA := uniformCertificateRoundingMesh n ω
  let θb := uniformCertificateRoundingMesh r ω
  let RA := approxSDPDensityEntryBound n κ ε
  let Rb := approxSDPAuxEntryBound r η εb
  let CA := gramCertificateBound (1 + κ + n * ε)
  let Cb := gramCertificateBound (η + 2 * r * εb)
  rw [show uniformCertificateSearchGrid ι n η κ ε εb ω =
      rationalHermitianBoundedMatrixGrid (Fin n) RA θA ×ˢ
        (rationalHermitianBoundedMatrixGrid ι Rb θb ×ˢ
          (rationalHermitianBoundedMatrixGrid ι Rb θb ×ˢ
            (rationalGramCertificateGrid (Fin n) CA θA ×ˢ
              (rationalGramCertificateGrid ι Cb θb ×ˢ
                rationalGramCertificateGrid ι Cb θb)))) by
    rfl]
  rw [Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.card_product, Finset.card_product]
  have h := Nat.mul_le_mul
    (rationalHermitianBoundedMatrixGrid_card_le (ι := Fin n) RA θA)
    (Nat.mul_le_mul (rationalHermitianBoundedMatrixGrid_card_le (ι := ι) Rb θb)
      (Nat.mul_le_mul (rationalHermitianBoundedMatrixGrid_card_le (ι := ι) Rb θb)
        (Nat.mul_le_mul (rationalGramCertificateGrid_card_le (ι := Fin n) CA θA)
          (Nat.mul_le_mul (rationalGramCertificateGrid_card_le (ι := ι) Cb θb)
            (rationalGramCertificateGrid_card_le (ι := ι) Cb θb)))))
  simpa only [matrixCoordinateGridCardBound, Fintype.card_fin,
    r, θA, θb, RA, Rb, CA, Cb] using h

theorem uniformCertificateSearchGrid_card_le_explicitBound
    (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) :
    (uniformCertificateSearchGrid ι n η κ ε εb ω).card ≤
      uniformCertificateSearchCardBound ι n η κ ε εb ω := by
  simpa [uniformCertificateSearchCardBound] using
    uniformCertificateSearchGrid_card_le ι n η κ ε εb ω

/-- The representation-preserving rational search has the same explicit cardinality
bound as the decoded complex search. -/
theorem uniformCertificateCodeSearchGrid_card_le_explicitBound
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (η κ ε εb ω : ℝ) :
    (uniformCertificateCodeSearchGrid ι n η κ ε εb ω).card ≤
      uniformCertificateSearchCardBound ι n η κ ε εb ω := by
  rw [uniformCertificateCodeSearchGrid_card_eq]
  exact uniformCertificateSearchGrid_card_le_explicitBound ι n η κ ε εb ω

/-- Exhaustive testing of the complete six-grid search uses at most the explicit
search-cardinality bound times `n² + 3r² + 3` rational comparisons. -/
theorem uniformCertificateSearchComparisonCount_le_explicitBound
    (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) :
    uniformCertificateSearchComparisonCount ι n η κ ε εb ω ≤
      uniformCertificateSearchCardBound ι n η κ ε εb ω *
        (n ^ 2 + 3 * Fintype.card ι ^ 2 + 3) :=
  uniformCertificateSearchComparisonCount_le_of_card_le
    (uniformCertificateSearchGrid_card_le_explicitBound ι n η κ ε εb ω)

/-- The dense scalar-product work over the complete search is bounded by the explicit
search cardinality times the displayed polynomial per-candidate count. -/
theorem uniformCertificateSearchDenseProductTermCount_le_explicitBound
    (a : ℕ) (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) :
    uniformCertificateSearchDenseProductTermCount a ι n η κ ε εb ω ≤
      uniformCertificateSearchCardBound ι n η κ ε εb ω *
        (2 * n ^ 3 + 2 * Fintype.card ι ^ 3 +
          (a * Fintype.card ι) * n ^ 2 + (a * Fintype.card ι) ^ 2 * n) :=
  uniformCertificateSearchDenseProductTermCount_le_of_card_le
    (uniformCertificateSearchGrid_card_le_explicitBound ι n η κ ε εb ω)

/-- Under the stated schoolbook rational-arithmetic cost model and a uniform `L`-bit
operand bound, exhaustive certificate testing has the fully explicit bit-cost bound. -/
theorem uniformCertificateSearchSchoolbookBitCost_le_explicitBound
    (a L : ℕ) (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) :
    uniformCertificateSearchSchoolbookBitCost a ι n η κ ε εb ω L ≤
      uniformCertificateSearchCardBound ι n η κ ε εb ω *
        ((n ^ 2 + 3 * Fintype.card ι ^ 2 + 3) +
          (2 * n ^ 3 + 2 * Fintype.card ι ^ 3 +
            (a * Fintype.card ι) * n ^ 2 + (a * Fintype.card ι) ^ 2 * n)) *
          rationalSchoolbookOperationCost L :=
  uniformCertificateSearchSchoolbookBitCost_le_of_card_le
    (uniformCertificateSearchGrid_card_le_explicitBound ι n η κ ε εb ω)

/-- The end-to-end schoolbook bit-cost bound with the uniform operand length obtained
from the fixed-data and six-grid coordinate heights substituted explicitly. -/
theorem uniformCertificateSearchSchoolbookBitCost_le_uniformOperandBound
    (a HD : ℕ) (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) :
    let L := uniformCertificateOperandBitLength a ι n η κ ε εb ω HD
    uniformCertificateSearchSchoolbookBitCost a ι n η κ ε εb ω L ≤
      uniformCertificateSearchCardBound ι n η κ ε εb ω *
        ((n ^ 2 + 3 * Fintype.card ι ^ 2 + 3) +
          (2 * n ^ 3 + 2 * Fintype.card ι ^ 3 +
            (a * Fintype.card ι) * n ^ 2 + (a * Fintype.card ι) ^ 2 * n)) *
          rationalSchoolbookOperationCost L := by
  dsimp only
  exact uniformCertificateSearchSchoolbookBitCost_le_explicitBound
    a (uniformCertificateOperandBitLength a ι n η κ ε εb ω HD)
    ι n η κ ε εb ω

/-- End-to-end search cost specialized to the height stored in an exact rational input
encoding. -/
theorem RationalCompressedSDPInputEncoding.searchSchoolbookBitCost_le
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    {n : ℕ} {η κ ε εb ω : ℝ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    (hinput : RationalCompressedSDPInputEncoding Z K X ε εb) :
    let L := uniformCertificateOperandBitLength (Fintype.card a) (s × b)
      n η κ ε εb ω hinput.height
    uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
        n η κ ε εb ω L ≤
      uniformCertificateSearchCardBound (s × b) n η κ ε εb ω *
        ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
          (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
            (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
              (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
          rationalSchoolbookOperationCost L := by
  dsimp only
  exact uniformCertificateSearchSchoolbookBitCost_le_uniformOperandBound
    (Fintype.card a) hinput.height (s × b) n η κ ε εb ω

end TNLean.MPS.AreaLaw
