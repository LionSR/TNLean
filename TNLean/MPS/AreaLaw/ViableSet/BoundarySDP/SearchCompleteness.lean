/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ApproximateCertificates
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SearchCost

/-!
# Completeness of rational certificate search

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Every candidate in the complete six-grid search has Gaussian-rational entries in
all six matrices. -/
theorem uniformCertificateSearchGrid_entries_rational
    {ι : Type*} [Fintype ι] {n : ℕ} {η κ ε εb ω : ℝ}
    {A QA : Matrix (Fin n) (Fin n) ℂ} {P N QP QN : Matrix ι ι ℂ}
    (h : (A, P, N, QA, QP, QN) ∈
      uniformCertificateSearchGrid ι n η κ ε εb ω) :
    (∀ i j, ∃ x y : ℚ, A i j = ⟨(x : ℝ), (y : ℝ)⟩) ∧
      (∀ i j, ∃ x y : ℚ, P i j = ⟨(x : ℝ), (y : ℝ)⟩) ∧
      (∀ i j, ∃ x y : ℚ, N i j = ⟨(x : ℝ), (y : ℝ)⟩) ∧
      (∀ i j, ∃ x y : ℚ, QA i j = ⟨(x : ℝ), (y : ℝ)⟩) ∧
      (∀ i j, ∃ x y : ℚ, QP i j = ⟨(x : ℝ), (y : ℝ)⟩) ∧
      ∀ i j, ∃ x y : ℚ, QN i j = ⟨(x : ℝ), (y : ℝ)⟩ := by
  simp only [uniformCertificateSearchGrid, Finset.mem_product] at h
  rcases h with ⟨hA, hP, hN, hQA, hQP, hQN⟩
  exact ⟨rationalHermitianBoundedMatrixGrid_entry hA,
    rationalHermitianBoundedMatrixGrid_entry hP,
    rationalHermitianBoundedMatrixGrid_entry hN,
    rationalGramCertificateGrid_entry hQA,
    rationalGramCertificateGrid_entry hQP,
    rationalGramCertificateGrid_entry hQN⟩

/-- For exact-coordinate problem data and rational spectral shifts, every matrix and
scalar expression tested by the rounded SDP certificate has rational coordinates. -/
theorem uniformCertificateSearchGrid_testExpressions_rational
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b]
    {n : ℕ} {η κ ε εb ω : ℝ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {A QA : Matrix (Fin n) (Fin n) ℂ}
    {P N QP QN : Matrix (s × b) (s × b) ℂ}
    (hsearch : (A, P, N, QA, QP, QN) ∈
      uniformCertificateSearchGrid (s × b) n η κ ε εb ω)
    (hZ : Matrix.HasRationalEntries Z) (hK : Matrix.HasRationalEntries K)
    (hX : Matrix.HasRationalEntries X)
    (hε : HasRationalComplexCoordinates (ε : ℂ))
    (hεb : HasRationalComplexCoordinates (εb : ℂ)) :
    Matrix.HasRationalEntries ((compressedBoundaryLM Z A - X) - (P - N)) ∧
      HasRationalComplexCoordinates (A * K).trace ∧
      HasRationalComplexCoordinates A.trace ∧
      HasRationalComplexCoordinates P.trace ∧
      HasRationalComplexCoordinates N.trace ∧
      Matrix.HasRationalEntries
        (A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) ∧
      Matrix.HasRationalEntries
        (P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) ∧
      Matrix.HasRationalEntries
        (N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) := by
  obtain ⟨hA, hP, hN, hQA, hQP, hQN⟩ :=
    uniformCertificateSearchGrid_entries_rational hsearch
  have hAI : Matrix.HasRationalEntries
      ((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
    Matrix.HasRationalEntries.smul hε Matrix.HasRationalEntries.one
  have hBI : Matrix.HasRationalEntries
      ((εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ)) :=
    Matrix.HasRationalEntries.smul hεb Matrix.HasRationalEntries.one
  exact ⟨Matrix.HasRationalEntries.sub
      (Matrix.HasRationalEntries.sub (compressedBoundaryLM_hasRationalEntries hZ hA) hX)
      (Matrix.HasRationalEntries.sub hP hN),
    Matrix.HasRationalEntries.trace (Matrix.HasRationalEntries.mul hA hK),
    Matrix.HasRationalEntries.trace hA, Matrix.HasRationalEntries.trace hP,
    Matrix.HasRationalEntries.trace hN,
    Matrix.HasRationalEntries.sub (Matrix.HasRationalEntries.add hA hAI)
      (Matrix.HasRationalEntries.mul hQA (Matrix.HasRationalEntries.conjTranspose hQA)),
    Matrix.HasRationalEntries.sub (Matrix.HasRationalEntries.add hP hBI)
      (Matrix.HasRationalEntries.mul hQP (Matrix.HasRationalEntries.conjTranspose hQP)),
    Matrix.HasRationalEntries.sub (Matrix.HasRationalEntries.add hN hBI)
      (Matrix.HasRationalEntries.mul hQN (Matrix.HasRationalEntries.conjTranspose hQN))⟩

/-- Every candidate in the complex-valued six-grid search admits an explicit rational
test-value record.  This bridges the existing grid representation to the decidable
acceptance predicate; a representation-preserving implementation may store these
coordinates directly instead of selecting them classically. -/
theorem exists_rationalApproxCertificateTestValues_of_mem_searchGrid
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b]
    {n : ℕ} {η κ ε εb ω : ℝ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {A QA : Matrix (Fin n) (Fin n) ℂ}
    {P N QP QN : Matrix (s × b) (s × b) ℂ}
    (hsearch : (A, P, N, QA, QP, QN) ∈
      uniformCertificateSearchGrid (s × b) n η κ ε εb ω)
    (hZ : Matrix.HasRationalEntries Z) (hK : Matrix.HasRationalEntries K)
    (hX : Matrix.HasRationalEntries X)
    (hε : HasRationalComplexCoordinates (ε : ℂ))
    (hεb : HasRationalComplexCoordinates (εb : ℂ)) :
    ∃ v : RationalApproxCertificateTestValues (s × b) n,
      A.trace.re = (v.densityTrace : ℝ) ∧
      P.trace.re = (v.positiveTrace : ℝ) ∧
      N.trace.re = (v.negativeTrace : ℝ) ∧
      (A * K).trace.re = (v.objective : ℝ) ∧
      (∀ i j, (((compressedBoundaryLM Z A - X) - (P - N)) i j) =
        ⟨((v.boundaryResidual i j).1 : ℝ),
          ((v.boundaryResidual i j).2 : ℝ)⟩) ∧
      (∀ i j,
        (A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) i j =
          ⟨((v.densityGramResidual i j).1 : ℝ),
            ((v.densityGramResidual i j).2 : ℝ)⟩) ∧
      (∀ i j,
        (P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) i j =
          ⟨((v.positiveGramResidual i j).1 : ℝ),
            ((v.positiveGramResidual i j).2 : ℝ)⟩) ∧
      ∀ i j,
        (N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) i j =
          ⟨((v.negativeGramResidual i j).1 : ℝ),
            ((v.negativeGramResidual i j).2 : ℝ)⟩ := by
  obtain ⟨hb, ho, htA, htP, htN, hGA, hGP, hGN⟩ :=
    uniformCertificateSearchGrid_testExpressions_rational
      hsearch hZ hK hX hε hεb
  let v : RationalApproxCertificateTestValues (s × b) n :=
    { densityTrace := rationalComplexRealCoordinate htA
      positiveTrace := rationalComplexRealCoordinate htP
      negativeTrace := rationalComplexRealCoordinate htN
      objective := rationalComplexRealCoordinate ho
      boundaryResidual := fun i j ↦
        (rationalComplexRealCoordinate (hb i j), rationalComplexImagCoordinate (hb i j))
      densityGramResidual := fun i j ↦
        (rationalComplexRealCoordinate (hGA i j), rationalComplexImagCoordinate (hGA i j))
      positiveGramResidual := fun i j ↦
        (rationalComplexRealCoordinate (hGP i j), rationalComplexImagCoordinate (hGP i j))
      negativeGramResidual := fun i j ↦
        (rationalComplexRealCoordinate (hGN i j), rationalComplexImagCoordinate (hGN i j)) }
  refine ⟨v, real_eq_rationalComplexRealCoordinate htA,
    real_eq_rationalComplexRealCoordinate htP,
    real_eq_rationalComplexRealCoordinate htN,
    real_eq_rationalComplexRealCoordinate ho, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact eq_complex_of_rationalComplexCoordinates (hb i j)
  · intro i j
    exact eq_complex_of_rationalComplexCoordinates (hGA i j)
  · intro i j
    exact eq_complex_of_rationalComplexCoordinates (hGP i j)
  · intro i j
    exact eq_complex_of_rationalComplexCoordinates (hGN i j)

/-- Simultaneous concrete rounding of the three primary matrices and their three Gram
factors preserves the unified certificate after explicit enlargement of every affected
tolerance.  This is the finite-search completeness statement for the rounded algebraic
certificate. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_explicit_rounded_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ θA θb ζA ζb : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hZ : Zᴴ * Z = 1) (hθA : 0 < θA) (hθb : 0 < θb)
    (hζA : 0 < ζA) (hζb : 0 < ζb) :
    ∃ A' ∈ rationalHermitianBoundedMatrixGrid (Fin n)
        (approxSDPDensityEntryBound n κ ε) θA,
      ∃ P' ∈ rationalHermitianBoundedMatrixGrid (s × b)
          (approxSDPAuxEntryBound (Fintype.card (s × b)) η εb) θb,
        ∃ N' ∈ rationalHermitianBoundedMatrixGrid (s × b)
            (approxSDPAuxEntryBound (Fintype.card (s × b)) η εb) θb,
          ∃ QA ∈ rationalGramCertificateGrid (Fin n)
              (gramCertificateBound (1 + κ + n * ε)) ζA,
            ∃ QP ∈ rationalGramCertificateGrid (s × b)
                (gramCertificateBound (η + 2 * Fintype.card (s × b) * εb)) ζb,
              ∃ QN ∈ rationalGramCertificateGrid (s × b)
                  (gramCertificateBound (η + 2 * Fintype.card (s × b) * εb)) ζb,
                IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
                  (η + 2 * Fintype.card (s × b) * θb)
                  (E + ‖K‖ * ((n : ℝ) ^ 2 * θA))
                  (κ + n * θA)
                  (ε + ((n : ℝ) + 1) * (θA + ζA))
                  (εb + ((Fintype.card (s × b) : ℝ) + 1) * (θb + ζb))
                  (δ + (n : ℝ) ^ 2 * θA +
                    2 * (Fintype.card (s × b) : ℝ) ^ 2 * θb)
                  A' P' N' ∧
                (∀ i j,
                  ‖(A' + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
                    QA * QAᴴ) i j‖ ≤ θA + ζA) ∧
                (∀ i j,
                  ‖(P' + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
                    QP * QPᴴ) i j‖ ≤ θb + ζb) ∧
                ∀ i j,
                  ‖(N' + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
                    QN * QNᴴ) i j‖ ≤ θb + ζb := by
  obtain ⟨A', hAgrid, hA'Herm, P', hPgrid, hP'Herm, N', hNgrid, hN'Herm,
      hAclose, hPclose, hNclose, htrace, htraces, hresidual, henergy⟩ :=
    h.exists_explicit_primary_search hZ hθA hθb
  obtain ⟨QA, hQAgrid, QP, hQPgrid, QN, hQNgrid, hQAclose, hQPclose, hQNclose⟩ :=
    h.exists_rational_gram_search hζA hζb
  have hAclose' : ∀ i j, ‖(A' - A) i j‖ ≤ θA := by
    intro i j
    rw [Matrix.sub_apply, norm_sub_rev]
    exact hAclose i j
  have hPclose' : ∀ i j, ‖(P' - P) i j‖ ≤ θb := by
    intro i j
    rw [Matrix.sub_apply, norm_sub_rev]
    exact hPclose i j
  have hNclose' : ∀ i j, ‖(N' - N) i j‖ ≤ θb := by
    intro i j
    rw [Matrix.sub_apply, norm_sub_rev]
    exact hNclose i j
  have hAfactor : ∀ i j,
      ‖(A' + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) i j‖ ≤
        θA + ζA := by
    intro i j
    have hid : A' + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ =
        (A' - A) + (A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) := by
      module
    rw [hid, Matrix.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hAclose' i j) (hQAclose i j))
  have hPfactor : ∀ i j,
      ‖(P' + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) i j‖ ≤
        θb + ζb := by
    intro i j
    have hid : P' + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ =
        (P' - P) + (P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) := by
      module
    rw [hid, Matrix.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hPclose' i j) (hQPclose i j))
  have hNfactor : ∀ i j,
      ‖(N' + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) i j‖ ≤
        θb + ζb := by
    intro i j
    have hid : N' + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ =
        (N' - N) + (N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) := by
      module
    rw [hid, Matrix.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hNclose' i j) (hQNclose i j))
  have hAmin := neg_le_minEigenvalue_of_approx_gram_factor
    (ε₀ := ε) (ε := ε + ((n : ℝ) + 1) * (θA + ζA))
    (ζ := θA + ζA) hA'Herm (add_nonneg hθA.le hζA.le) QA hAfactor
    (by simp only [Fintype.card_fin]; exact le_rfl)
  have hPmin := neg_le_minEigenvalue_of_approx_gram_factor
    (ε₀ := εb) (ε := εb + ((Fintype.card (s × b) : ℝ) + 1) * (θb + ζb))
    (ζ := θb + ζb) hP'Herm (add_nonneg hθb.le hζb.le) QP hPfactor le_rfl
  have hNmin := neg_le_minEigenvalue_of_approx_gram_factor
    (ε₀ := εb) (ε := εb + ((Fintype.card (s × b) : ℝ) + 1) * (θb + ζb))
    (ζ := θb + ζb) hN'Herm (add_nonneg hθb.le hζb.le) QN hNfactor le_rfl
  refine ⟨A', hAgrid, P', hPgrid, N', hNgrid, QA, hQAgrid,
    QP, hQPgrid, QN, hQNgrid, ?_⟩
  exact ⟨⟨hA'Herm, hP'Herm, hN'Herm, htrace,
      add_nonneg h.hε (mul_nonneg (by positivity) (add_nonneg hθA.le hζA.le)), hAmin,
      add_nonneg h.hεb (mul_nonneg (by positivity) (add_nonneg hθb.le hζb.le)),
      hPmin, hNmin, hresidual, htraces, henergy⟩,
    hAfactor, hPfactor, hNfactor⟩

/-- A single positive precision allowance determines all four meshes in the concrete
finite search.  Every scalar tolerance except the boundary residual grows by at most
`ω`; the boundary residual grows by at most `2ω`. -/
theorem
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_uniformly_rounded_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ω : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hZ : Zᴴ * Z = 1) (hω : 0 < ω) :
    let r := Fintype.card (s × b)
    let θA := uniformCertificateRoundingMesh n ω
    let θb := uniformCertificateRoundingMesh r ω
    ∃ A' ∈ rationalHermitianBoundedMatrixGrid (Fin n)
        (approxSDPDensityEntryBound n κ ε) θA,
      ∃ P' ∈ rationalHermitianBoundedMatrixGrid (s × b)
          (approxSDPAuxEntryBound r η εb) θb,
        ∃ N' ∈ rationalHermitianBoundedMatrixGrid (s × b)
            (approxSDPAuxEntryBound r η εb) θb,
          ∃ QA ∈ rationalGramCertificateGrid (Fin n)
              (gramCertificateBound (1 + κ + n * ε)) θA,
            ∃ QP ∈ rationalGramCertificateGrid (s × b)
                (gramCertificateBound (η + 2 * r * εb)) θb,
              ∃ QN ∈ rationalGramCertificateGrid (s × b)
                  (gramCertificateBound (η + 2 * r * εb)) θb,
                IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
                  (η + ω) (E + ‖K‖ * ω) (κ + ω) (ε + ω) (εb + ω) (δ + 2 * ω)
                  A' P' N' ∧
                (A', P', N', QA, QP, QN) ∈
                  uniformCertificateSearchGrid (s × b) n η κ ε εb ω ∧
                (∀ i j,
                  ‖(A' + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
                    QA * QAᴴ) i j‖ ≤ 2 * θA) ∧
                (∀ i j,
                  ‖(P' + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
                    QP * QPᴴ) i j‖ ≤ 2 * θb) ∧
                ∀ i j,
                  ‖(N' + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) -
                    QN * QNᴴ) i j‖ ≤ 2 * θb := by
  dsimp only
  let θA := uniformCertificateRoundingMesh n ω
  let r := Fintype.card (s × b)
  let θb := uniformCertificateRoundingMesh r ω
  have hθA : 0 < θA := uniformCertificateRoundingMesh_pos hω
  have hθb : 0 < θb := uniformCertificateRoundingMesh_pos hω
  obtain ⟨A', hA', P', hP', N', hN', QA, hQA, QP, hQP, QN, hQN,
      hcert, hAfactor, hPfactor, hNfactor⟩ :=
    h.exists_explicit_rounded_certificate hZ hθA hθb hθA hθb
  refine ⟨A', hA', P', hP', N', hN', QA, hQA, QP, hQP, QN, hQN, ?_⟩
  obtain ⟨hn₁, hn₂, hn₃, _hn₄⟩ :=
    uniformCertificateRoundingMesh_bounds n hω.le
  obtain ⟨_hr₁, hr₂, _hr₃, hr₄⟩ :=
    uniformCertificateRoundingMesh_bounds r hω.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply hcert.mono
    · dsimp only [θb]
      linarith
    · gcongr
    · dsimp only [θA]
      linarith
    · dsimp only [θA]
      linarith
    · dsimp only [θb]
      linarith
    · dsimp only [θA, θb]
      linarith
  · simp only [uniformCertificateSearchGrid, Finset.mem_product]
    exact ⟨hA', hP', hN', hQA, hQP, hQN⟩
  · simpa only [two_mul] using hAfactor
  · simpa only [two_mul] using hPfactor
  · simpa only [two_mul] using hNfactor

/-- A feasible rational-input certificate yields an accepted code in the executable
rational-tolerance grid.  The boundary tolerance carries the explicit `r²` factor used
to pass from entrywise residual tests to trace norm. -/
theorem
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_accepted_rational_code
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    {η E κ ε εb δ ω Et : ℚ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      (RationalRectMatrixCode.decode Z) (RationalRectMatrixCode.decode K)
      (RationalRectMatrixCode.decode X)
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : (RationalRectMatrixCode.decode Z)ᴴ *
      RationalRectMatrixCode.decode Z = 1)
    (hω : 0 < ω)
    (hEt : (E : ℝ) + ‖RationalRectMatrixCode.decode K‖ * (ω : ℝ) ≤ (Et : ℝ)) :
    let r := Fintype.card (s × b)
    let θA := rationalUniformCertificateRoundingMesh n ω
    let θb := rationalUniformCertificateRoundingMesh r ω
    ∃ c ∈ rationalCertificateCodeGridOfTolerances (s × b) n η κ ε εb ω,
      (c.testValues Z K X ε εb).Accepts
        (η + ω) Et (κ + ω) (ε + ω) (εb + ω)
        ((r : ℚ) ^ 2 * (δ + 2 * ω)) (δ + 2 * ω)
        ε (2 * θA) εb (2 * θb) εb (2 * θb) := by
  dsimp only
  let r := Fintype.card (s × b)
  let θA := rationalUniformCertificateRoundingMesh n ω
  let θb := rationalUniformCertificateRoundingMesh r ω
  have hωreal : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast hω
  obtain ⟨A', hA', P', hP', N', hN', QA, hQA, QP, hQP, QN, hQN,
      hrounded, hgrid, hAfactor, hPfactor, hNfactor⟩ :=
    h.exists_uniformly_rounded_certificate hZ hωreal
  obtain ⟨c, hc, hdecode⟩ := exists_code_of_mem_uniformCertificateSearchGrid hgrid
  have hc' : c ∈ rationalCertificateCodeGridOfTolerances (s × b) n η κ ε εb ω := by
    rw [← uniformCertificateCodeSearchGrid_eq_of_rational_tolerances]
    · exact hc
    · exact_mod_cast h.hε
    · exact_mod_cast h.hεb
    · exact hω
  refine ⟨c, hc', ?_⟩
  have hdecodeA := congrArg (fun x ↦ x.1) hdecode
  have hdecodeP := congrArg (fun x ↦ x.2.1) hdecode
  have hdecodeN := congrArg (fun x ↦ x.2.2.1) hdecode
  have hdecodeQA := congrArg (fun x ↦ x.2.2.2.1) hdecode
  have hdecodeQP := congrArg (fun x ↦ x.2.2.2.2.1) hdecode
  have hdecodeQN := congrArg (fun x ↦ x.2.2.2.2.2) hdecode
  have hcA : c.1.decode = A' := by
    simpa [RationalCertificateCode.decode] using hdecodeA
  have hcP : c.2.1.decode = P' := by
    simpa [RationalCertificateCode.decode] using hdecodeP
  have hcN : c.2.2.1.decode = N' := by
    simpa [RationalCertificateCode.decode] using hdecodeN
  have hcQA : c.2.2.2.1.decode = QA := by
    simpa [RationalCertificateCode.decode] using hdecodeQA
  have hcQP : c.2.2.2.2.1.decode = QP := by
    simpa [RationalCertificateCode.decode] using hdecodeQP
  have hcQN : c.2.2.2.2.2.decode = QN := by
    simpa [RationalCertificateCode.decode] using hdecodeQN
  have hδ : 0 ≤ δ := by
    exact_mod_cast (rectangularTraceNorm_nonneg _).trans h.hresidual
  have hε : 0 ≤ ε := by exact_mod_cast h.hε
  have hεb : 0 ≤ εb := by exact_mod_cast h.hεb
  have hθA : (θA : ℝ) = uniformCertificateRoundingMesh n (ω : ℝ) := by
    exact rationalUniformCertificateRoundingMesh_cast n ω
  have hθb : (θb : ℝ) = uniformCertificateRoundingMesh r (ω : ℝ) := by
    exact rationalUniformCertificateRoundingMesh_cast r ω
  have hnBudget : ε + ((n : ℚ) + 1) * (2 * θA) ≤ ε + ω := by
    have hn := (uniformCertificateRoundingMesh_bounds n hωreal.le).2.1
    rw [← hθA] at hn
    have hnq : (2 * ((n : ℚ) + 1)) * θA ≤ ω := by exact_mod_cast hn
    calc
      ε + ((n : ℚ) + 1) * (2 * θA) = ε + (2 * ((n : ℚ) + 1)) * θA := by ring
      _ ≤ ε + ω := by linarith
  have hrBudget : εb + ((r : ℚ) + 1) * (2 * θb) ≤ εb + ω := by
    have hr := (uniformCertificateRoundingMesh_bounds r hωreal.le).2.1
    rw [← hθb] at hr
    have hrq : (2 * ((r : ℚ) + 1)) * θb ≤ ω := by exact_mod_cast hr
    calc
      εb + ((r : ℚ) + 1) * (2 * θb) = εb + (2 * ((r : ℚ) + 1)) * θb := by ring
      _ ≤ εb + ω := by linarith
  apply c.testValues_accepts_of_bounds Z K X ε εb
  · linarith
  · linarith
  · linarith
  · dsimp only [θA, rationalUniformCertificateRoundingMesh]
    positivity
  · dsimp only [θb, rationalUniformCertificateRoundingMesh]
    positivity
  · dsimp only [θb, rationalUniformCertificateRoundingMesh]
    positivity
  · rw [hcA]
    exact_mod_cast hrounded.htrace
  · intro i j
    rw [hcA, hcQA]
    simpa [hθA] using hAfactor i j
  · exact hnBudget
  · intro i j
    rw [hcP, hcQP]
    simpa [hθb] using hPfactor i j
  · exact hrBudget
  · intro i j
    rw [hcN, hcQN]
    simpa [hθb] using hNfactor i j
  · exact hrBudget
  · intro i j
    rw [hcA, hcP, hcN]
    exact_mod_cast (norm_apply_le_rectangularTraceNorm _ i j).trans hrounded.hresidual
  · exact le_rfl
  · rw [hcP, hcN]
    exact_mod_cast hrounded.htraces
  · rw [hcA]
    exact hrounded.henergy.trans hEt

/-- Any rounded six-grid certificate for rational fixed data gives an accepted code.
This separates rational acceptance from the construction of the rounded certificate and
therefore applies after perturbing the coordinate isometry and the other fixed data. -/
theorem exists_accepted_rational_code_of_grid_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    {gridη gridκ gridε gridεb gridω E δ : ℚ}
    {A QA : Matrix (Fin n) (Fin n) ℂ}
    {P N QP QN : Matrix (s × b) (s × b) ℂ}
    (hgrid : (A, P, N, QA, QP, QN) ∈ uniformCertificateSearchGrid
      (s × b) n (gridη : ℝ) (gridκ : ℝ) (gridε : ℝ) (gridεb : ℝ) (gridω : ℝ))
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z.decode K.decode X.decode ((gridη + gridω : ℚ) : ℝ) (E : ℝ)
      ((gridκ + gridω : ℚ) : ℝ) ((gridε + gridω : ℚ) : ℝ)
      ((gridεb + gridω : ℚ) : ℝ) (δ : ℝ) A P N)
    (hgridε : 0 ≤ gridε) (hgridεb : 0 ≤ gridεb) (hgridω : 0 < gridω)
    (hAfactor : ∀ i j,
      ‖(A + ((gridε : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) i j‖ ≤
        2 * uniformCertificateRoundingMesh n (gridω : ℝ))
    (hPfactor : ∀ i j,
      ‖(P + ((gridεb : ℝ) : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) i j‖ ≤
        2 * uniformCertificateRoundingMesh (Fintype.card (s × b)) (gridω : ℝ))
    (hNfactor : ∀ i j,
      ‖(N + ((gridεb : ℝ) : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) i j‖ ≤
        2 * uniformCertificateRoundingMesh (Fintype.card (s × b)) (gridω : ℝ)) :
    let r := Fintype.card (s × b)
    let θA := rationalUniformCertificateRoundingMesh n gridω
    let θb := rationalUniformCertificateRoundingMesh r gridω
    ∃ c ∈ rationalCertificateCodeGridOfTolerances (s × b) n
        gridη gridκ gridε gridεb gridω,
      (c.testValues Z K X gridε gridεb).Accepts
        (gridη + gridω) E (gridκ + gridω) (gridε + gridω) (gridεb + gridω)
        ((r : ℚ) ^ 2 * δ) δ
        gridε (2 * θA) gridεb (2 * θb) gridεb (2 * θb) := by
  dsimp only
  let r := Fintype.card (s × b)
  let θA := rationalUniformCertificateRoundingMesh n gridω
  let θb := rationalUniformCertificateRoundingMesh r gridω
  obtain ⟨c, hc, hdecode⟩ := exists_code_of_mem_uniformCertificateSearchGrid hgrid
  have hc' : c ∈ rationalCertificateCodeGridOfTolerances (s × b) n
      gridη gridκ gridε gridεb gridω := by
    rw [← uniformCertificateCodeSearchGrid_eq_of_rational_tolerances]
    · exact hc
    · exact hgridε
    · exact hgridεb
    · exact hgridω
  refine ⟨c, hc', ?_⟩
  have hcA : c.1.decode = A := by
    simpa [RationalCertificateCode.decode] using congrArg (fun x ↦ x.1) hdecode
  have hcP : c.2.1.decode = P := by
    simpa [RationalCertificateCode.decode] using congrArg (fun x ↦ x.2.1) hdecode
  have hcN : c.2.2.1.decode = N := by
    simpa [RationalCertificateCode.decode] using congrArg (fun x ↦ x.2.2.1) hdecode
  have hcQA : c.2.2.2.1.decode = QA := by
    simpa [RationalCertificateCode.decode] using congrArg (fun x ↦ x.2.2.2.1) hdecode
  have hcQP : c.2.2.2.2.1.decode = QP := by
    simpa [RationalCertificateCode.decode] using congrArg (fun x ↦ x.2.2.2.2.1) hdecode
  have hcQN : c.2.2.2.2.2.decode = QN := by
    simpa [RationalCertificateCode.decode] using congrArg (fun x ↦ x.2.2.2.2.2) hdecode
  have hωreal : (0 : ℝ) < (gridω : ℝ) := by exact_mod_cast hgridω
  have hθA : (θA : ℝ) = uniformCertificateRoundingMesh n (gridω : ℝ) :=
    rationalUniformCertificateRoundingMesh_cast n gridω
  have hθb : (θb : ℝ) = uniformCertificateRoundingMesh r (gridω : ℝ) :=
    rationalUniformCertificateRoundingMesh_cast r gridω
  have hgridεcast : ((gridε : ℝ) : ℂ) = (gridε : ℂ) := by norm_cast
  have hgridεbcast : ((gridεb : ℝ) : ℂ) = (gridεb : ℂ) := by norm_cast
  have hnBudget : gridε + ((n : ℚ) + 1) * (2 * θA) ≤ gridε + gridω := by
    have hn := (uniformCertificateRoundingMesh_bounds n hωreal.le).2.1
    rw [← hθA] at hn
    have hnq : (2 * ((n : ℚ) + 1)) * θA ≤ gridω := by exact_mod_cast hn
    calc
      gridε + ((n : ℚ) + 1) * (2 * θA) =
          gridε + (2 * ((n : ℚ) + 1)) * θA := by ring
      _ ≤ gridε + gridω := by linarith
  have hrBudget : gridεb + ((r : ℚ) + 1) * (2 * θb) ≤ gridεb + gridω := by
    have hr := (uniformCertificateRoundingMesh_bounds r hωreal.le).2.1
    rw [← hθb] at hr
    have hrq : (2 * ((r : ℚ) + 1)) * θb ≤ gridω := by exact_mod_cast hr
    calc
      gridεb + ((r : ℚ) + 1) * (2 * θb) =
          gridεb + (2 * ((r : ℚ) + 1)) * θb := by ring
      _ ≤ gridεb + gridω := by linarith
  apply c.testValues_accepts_of_bounds Z K X gridε gridεb
  · exact_mod_cast hcert.hε
  · exact_mod_cast hcert.hεb
  · exact_mod_cast (rectangularTraceNorm_nonneg _).trans hcert.hresidual
  · dsimp only [θA, rationalUniformCertificateRoundingMesh]
    positivity
  · dsimp only [θb, rationalUniformCertificateRoundingMesh]
    positivity
  · dsimp only [θb, rationalUniformCertificateRoundingMesh]
    positivity
  · rw [hcA]
    exact_mod_cast hcert.htrace
  · intro i j
    rw [hcA, hcQA, ← hgridεcast]
    simpa [hθA] using hAfactor i j
  · exact hnBudget
  · intro i j
    rw [hcP, hcQP, ← hgridεbcast]
    simpa [hθb] using hPfactor i j
  · exact hrBudget
  · intro i j
    rw [hcN, hcQN, ← hgridεbcast]
    simpa [hθb] using hNfactor i j
  · exact hrBudget
  · intro i j
    rw [hcA, hcP, hcN]
    exact_mod_cast (norm_apply_le_rectangularTraceNorm _ i j).trans hcert.hresidual
  · exact le_rfl
  · rw [hcP, hcN]
    exact_mod_cast hcert.htraces
  · rw [hcA]
    exact_mod_cast hcert.henergy

/-- The executable rational-tolerance search succeeds on every feasible rational-input
instance.  The returned code is tested using the explicit rounding losses appearing in
`exists_accepted_rational_code`. -/
theorem
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_search_result
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    {η E κ ε εb δ ω Et : ℚ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      (RationalRectMatrixCode.decode Z) (RationalRectMatrixCode.decode K)
      (RationalRectMatrixCode.decode X)
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : (RationalRectMatrixCode.decode Z)ᴴ *
      RationalRectMatrixCode.decode Z = 1)
    (hω : 0 < ω)
    (hEt : (E : ℝ) + ‖RationalRectMatrixCode.decode K‖ * (ω : ℝ) ≤ (Et : ℝ)) :
    let r := Fintype.card (s × b)
    let θA := rationalUniformCertificateRoundingMesh n ω
    let θb := rationalUniformCertificateRoundingMesh r ω
    ∃ c, searchRationalCertificateCodeGridOfTolerances
      η κ ε εb ω Z K X ε εb
      (η + ω) Et (κ + ω) (ε + ω) (εb + ω)
      ((r : ℚ) ^ 2 * (δ + 2 * ω)) (δ + 2 * ω)
      (2 * θA) (2 * θb) (2 * θb) = some c := by
  dsimp only
  let r := Fintype.card (s × b)
  let θA := rationalUniformCertificateRoundingMesh n ω
  let θb := rationalUniformCertificateRoundingMesh r ω
  apply searchRationalCertificateCodeGridOfTolerances_complete
  exact h.exists_accepted_rational_code Z K X hZ hω hEt

/-- A feasible rational-input instance has both a successful executable search and the
explicit schoolbook bit-cost bound for that same exhaustive search. -/
theorem
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_search_result_and_cost_le
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    {η E κ ε εb δ ω Et : ℚ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      (RationalRectMatrixCode.decode Z) (RationalRectMatrixCode.decode K)
      (RationalRectMatrixCode.decode X)
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : (RationalRectMatrixCode.decode Z)ᴴ *
      RationalRectMatrixCode.decode Z = 1)
    (hω : 0 < ω)
    (hEt : (E : ℝ) + ‖RationalRectMatrixCode.decode K‖ * (ω : ℝ) ≤ (Et : ℝ)) :
    let r := Fintype.card (s × b)
    let θA := rationalUniformCertificateRoundingMesh n ω
    let θb := rationalUniformCertificateRoundingMesh r ω
    let L := rationalCertificateOperandBitLength (Fintype.card a) (s × b)
      n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ω : ℝ)
        (rationalCompressedSDPInputCodeHeight Z K X ε εb)
        ε εb (η + ω) Et (κ + ω) (ε + ω) (εb + ω)
        ((r : ℚ) ^ 2 * (δ + 2 * ω)) (δ + 2 * ω)
        (2 * θA) (2 * θb) (2 * θb)
    (∃ c, searchRationalCertificateCodeGridOfTolerances
      η κ ε εb ω Z K X ε εb
      (η + ω) Et (κ + ω) (ε + ω) (εb + ω)
      ((r : ℚ) ^ 2 * (δ + 2 * ω)) (δ + 2 * ω)
      (2 * θA) (2 * θb) (2 * θb) = some c) ∧
    uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
        n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ω : ℝ) L ≤
      uniformCertificateSearchCardBound (s × b)
          n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ω : ℝ) *
        ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
          (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
            (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
              (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
          rationalSchoolbookOperationCost L := by
  dsimp only
  constructor
  · exact h.exists_search_result Z K X hZ hω hEt
  · exact uniformCertificateSearchSchoolbookBitCost_le_uniformOperandBound
      (Fintype.card a) _ (s × b) n
      (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ω : ℝ)

/-- Completeness of the concrete six-grid search after rationalizing all fixed matrix
data.  Starting from any feasible certificate for the exact isometry, objective, and
boundary center, the search contains six rational matrices which certify feasibility
for the rational approximations `QZ`, `QK`, and `QX` with the displayed accumulated
losses. -/
theorem
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_rational_data_grid_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z QZ : Matrix ((a × s) × b) (Fin n) ℂ}
    {K QK : Matrix (Fin n) (Fin n) ℂ}
    {X QX : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ θZ θK θX : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ) (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ) i j‖ ≤ θZ)
    (hKclose : ∀ i j, ‖(K - QK) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX) i j‖ ≤ θX) :
    let r := Fintype.card (s × b)
    let κ' := κ + ρ
    let ε' := ε + ρ
    let εb' := εb + ρ
    let C := approxSDPDensityEntryBound n κ' ε'
    let eK := (n : ℝ) ^ 2 * C * θK
    let eX := (r : ℝ) ^ 2 * θX
    let ωZ := (r : ℝ) ^ 2 *
      (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
    ∃ A' P' N' QA QP QN,
      (A', P', N', QA, QP, QN) ∈
        uniformCertificateSearchGrid (s × b) n η κ ε εb ρ ∧
      IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy QZ QK QX
        (η + ρ) ((E + ‖K‖ * ρ) + eK) κ' ε' εb'
        (((δ + 2 * ρ) + eX) + ωZ) A' P' N' := by
  dsimp only
  obtain ⟨A', _hA', P', _hP', N', _hN', QA, _hQA, QP, _hQP, QN, _hQN,
      hrounded, hgrid, _hAfactor, _hPfactor, _hNfactor⟩ :=
    h.exists_uniformly_rounded_certificate hZ hρ
  have hfixed := hrounded.to_fixed_data_approximation hKclose hXclose
  have hrational := hfixed.to_coordinate_approximation hZ hθZ hZclose
  exact ⟨A', P', N', QA, QP, QN, hgrid, hrational⟩

/-- Completeness of the executable rational search after approximating a possibly
irrational coordinate isometry and the other fixed data.  Rational upper bounds `Et`
and `Dt` absorb the objective and boundary perturbations, respectively. -/
theorem
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_accepted_approx_data_code
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (QZ : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode (s × b) (s × b))
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ Et Dt : ℚ} {θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ) (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j, ‖(K - QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (hEt : let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK ≤ (Et : ℝ))
    (hDt : let r := Fintype.card (s × b)
      let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 * (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ)) ≤
          (Dt : ℝ)) :
    let r := Fintype.card (s × b)
    let θA := rationalUniformCertificateRoundingMesh n ρ
    let θb := rationalUniformCertificateRoundingMesh r ρ
    ∃ c ∈ rationalCertificateCodeGridOfTolerances (s × b) n η κ ε εb ρ,
      (c.testValues QZ QK QX ε εb).Accepts
        (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
        ((r : ℚ) ^ 2 * Dt) Dt
        ε (2 * θA) εb (2 * θb) εb (2 * θb) := by
  dsimp only at hEt hDt ⊢
  have hρreal : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  obtain ⟨A', _hA', P', _hP', N', _hN', QA, _hQA, QP, _hQP, QN, _hQN,
      hrounded, hgrid, hAfactor, hPfactor, hNfactor⟩ :=
    h.exists_uniformly_rounded_certificate hZ hρreal
  have hfixed := hrounded.to_fixed_data_approximation hKclose hXclose
  have hrational := hfixed.to_coordinate_approximation hZ hθZ hZclose
  have hEt' : (E : ℝ) + ‖K‖ * (ρ : ℝ) +
      (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
        ((κ : ℝ) + (ρ : ℝ)) ((ε : ℝ) + (ρ : ℝ)) * θK ≤ (Et : ℝ) := by
    simpa only [Rat.cast_add] using hEt
  have hDt' : (δ : ℝ) + 2 * (ρ : ℝ) +
      (Fintype.card (s × b) : ℝ) ^ 2 * θX +
      (Fintype.card (s × b) : ℝ) ^ 2 *
        (Fintype.card a * (n : ℝ) ^ 2 * θZ *
          approxSDPDensityEntryBound n ((κ : ℝ) + (ρ : ℝ))
            ((ε : ℝ) + (ρ : ℝ)) * (2 + θZ)) ≤ (Dt : ℝ) := by
    simpa only [Rat.cast_add] using hDt
  have hcert := hrational.mono le_rfl hEt' le_rfl le_rfl le_rfl hDt'
  apply exists_accepted_rational_code_of_grid_certificate QZ QK QX hgrid
  · simpa only [Rat.cast_add] using hcert
  · exact_mod_cast h.hε
  · exact_mod_cast h.hεb
  · exact hρ
  · simpa only [two_mul] using hAfactor
  · simpa only [two_mul] using hPfactor
  · simpa only [two_mul] using hNfactor

/-- The executable rational-tolerance search succeeds after rational approximation of
the coordinate isometry, objective matrix, and boundary centre. -/
theorem
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_approx_data_search_result
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (QZ : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode (s × b) (s × b))
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ Et Dt : ℚ} {θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ) (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j, ‖(K - QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (hEt : let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK ≤ (Et : ℝ))
    (hDt : let r := Fintype.card (s × b)
      let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 * (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ)) ≤
          (Dt : ℝ)) :
    let r := Fintype.card (s × b)
    let θA := rationalUniformCertificateRoundingMesh n ρ
    let θb := rationalUniformCertificateRoundingMesh r ρ
    ∃ c, searchRationalCertificateCodeGridOfTolerances
      η κ ε εb ρ QZ QK QX ε εb
      (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c := by
  dsimp only
  apply searchRationalCertificateCodeGridOfTolerances_complete
  exact h.exists_accepted_approx_data_code QZ QK QX hZ hρ hθZ
    hZclose hKclose hXclose hEt hDt

end TNLean.MPS.AreaLaw
