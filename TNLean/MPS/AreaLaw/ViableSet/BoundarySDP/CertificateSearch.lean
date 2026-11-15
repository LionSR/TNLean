/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.CertificateRounding

/-!
# Finite rational certificate search

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Fully discrete six-matrix search space.  Its eight natural-number parameters are
the coordinate radii and common denominators for the primary density, the two boundary
variables, and their Gram factors. -/
def rationalCertificateCodeGrid
    (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (BA MA Bb Mb BGA MGA BGb MGb : ℕ) :
    Finset (RationalCertificateCode ι n) :=
  rationalHermitianMatrixCodeGrid (Fin n) BA MA ×ˢ
    (rationalHermitianMatrixCodeGrid ι Bb Mb ×ˢ
      (rationalHermitianMatrixCodeGrid ι Bb Mb ×ˢ
        (rationalMatrixCodeGrid (Fin n) BGA MGA ×ˢ
          (rationalMatrixCodeGrid ι BGb MGb ×ˢ
            rationalMatrixCodeGrid ι BGb MGb))))

/-- Fully discrete certificate grid whose eight parameters are computed from rational
tolerances. -/
def rationalCertificateCodeGridOfTolerances
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (η κ ε εb ω : ℚ) : Finset (RationalCertificateCode ι n) :=
  let p := rationalCertificateGridParameters n (Fintype.card ι) η κ ε εb ω
  rationalCertificateCodeGrid ι n
    p.densityRadius p.densityOrder p.boundaryRadius p.boundaryOrder
    p.densityGramRadius p.densityGramOrder
    p.boundaryGramRadius p.boundaryGramOrder

/-- The three primary matrices in every discrete certificate code are Hermitian after
decoding. -/
theorem RationalCertificateCode.primary_isHermitian_of_mem_grid
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {BA MA Bb Mb BGA MGA BGb MGb : ℕ} {c : RationalCertificateCode ι n}
    (hc : c ∈ rationalCertificateCodeGrid ι n BA MA Bb Mb BGA MGA BGb MGb) :
    c.1.decode.IsHermitian ∧ c.2.1.decode.IsHermitian ∧
      c.2.2.1.decode.IsHermitian := by
  simp only [rationalCertificateCodeGrid, Finset.mem_product] at hc
  exact ⟨RationalMatrixCode.decode_isHermitian_of_mem_rationalHermitianMatrixCodeGrid
      hc.1,
    RationalMatrixCode.decode_isHermitian_of_mem_rationalHermitianMatrixCodeGrid
      hc.2.1,
    RationalMatrixCode.decode_isHermitian_of_mem_rationalHermitianMatrixCodeGrid
      hc.2.2.1⟩

/-- Executable exhaustive search on the fully discrete certificate grid.  All matrix
arithmetic and all acceptance comparisons are rational. -/
def searchRationalCertificateCodeGrid
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)] [Encodable (s × b)]
    (BA MA Bb Mb BGA MGA BGb MGb : ℕ)
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ) :
    Option (RationalCertificateCode (s × b) n) :=
  firstAcceptedInFinset
    (rationalCertificateCodeGrid (s × b) n BA MA Bb Mb BGA MGA BGb MGb)
    (fun c ↦ (c.testValues Z K X εA₀ εb₀).Accepts
      η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN)

/-- Executable rational search with grid parameters computed directly from rational
tolerances. -/
def searchRationalCertificateCodeGridOfTolerances
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)] [Encodable (s × b)]
    (gridη gridκ gridε gridεb gridω : ℚ)
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ) :
    Option (RationalCertificateCode (s × b) n) :=
  firstAcceptedInFinset
    (rationalCertificateCodeGridOfTolerances (s × b) n
      gridη gridκ gridε gridεb gridω)
    (fun c ↦ (c.testValues Z K X εA₀ εb₀).Accepts
      η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN)

/-- The rational-tolerance search is the discrete search instantiated with the eight
parameters computed by `rationalCertificateGridParameters`. -/
theorem searchRationalCertificateCodeGridOfTolerances_eq
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)] [Encodable (s × b)]
    (gridη gridκ gridε gridεb gridω : ℚ)
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ) :
    let p := rationalCertificateGridParameters n (Fintype.card (s × b))
      gridη gridκ gridε gridεb gridω
    searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω Z K X
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN =
    searchRationalCertificateCodeGrid
      p.densityRadius p.densityOrder p.boundaryRadius p.boundaryOrder
      p.densityGramRadius p.densityGramOrder
      p.boundaryGramRadius p.boundaryGramOrder
      Z K X εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN := by
  rfl

/-- The rational-tolerance search returns a code whenever its computed grid contains an
accepted code. -/
theorem searchRationalCertificateCodeGridOfTolerances_complete
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)] [Encodable (s × b)]
    (gridη gridκ gridε gridεb gridω : ℚ)
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    (hexists : ∃ c ∈ rationalCertificateCodeGridOfTolerances (s × b) n
        gridη gridκ gridε gridεb gridω,
      (c.testValues Z K X εA₀ εb₀).Accepts
        η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN) :
    ∃ c, searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω Z K X
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c :=
  firstAcceptedInFinset_complete _ _ hexists

/-- A code returned by the discrete-grid search belongs to that grid and passes its
direct rational acceptance test. -/
theorem searchRationalCertificateCodeGrid_sound
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)] [Encodable (s × b)]
    (BA MA Bb Mb BGA MGA BGb MGb : ℕ)
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (s × b) n}
    (hfind : searchRationalCertificateCodeGrid BA MA Bb Mb BGA MGA BGb MGb
      Z K X εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c) :
    c ∈ rationalCertificateCodeGrid (s × b) n BA MA Bb Mb BGA MGA BGb MGb ∧
      (c.testValues Z K X εA₀ εb₀).Accepts
        η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN :=
  firstAcceptedInFinset_sound _ _ hfind

/-- If the discrete grid contains an accepted code, its executable search returns an
accepted code. -/
theorem searchRationalCertificateCodeGrid_complete
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq (s × b)] [Encodable (s × b)]
    (BA MA Bb Mb BGA MGA BGb MGb : ℕ)
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    (hexists : ∃ c ∈ rationalCertificateCodeGrid (s × b) n
        BA MA Bb Mb BGA MGA BGb MGb,
      (c.testValues Z K X εA₀ εb₀).Accepts
        η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN) :
    ∃ c, searchRationalCertificateCodeGrid BA MA Bb Mb BGA MGA BGb MGb
      Z K X εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c :=
  firstAcceptedInFinset_complete _ _ hexists

/-- Representation-preserving version of the complete six-grid search. -/
noncomputable def uniformCertificateCodeSearchGrid
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (η κ ε εb ω : ℝ) : Finset (RationalCertificateCode ι n) := by
  let r := Fintype.card ι
  let θA := uniformCertificateRoundingMesh n ω
  let θb := uniformCertificateRoundingMesh r ω
  exact rationalHermitianBoundedMatrixCodeGrid (Fin n)
      (approxSDPDensityEntryBound n κ ε) θA ×ˢ
    (rationalHermitianBoundedMatrixCodeGrid ι
      (approxSDPAuxEntryBound r η εb) θb ×ˢ
      (rationalHermitianBoundedMatrixCodeGrid ι
        (approxSDPAuxEntryBound r η εb) θb ×ˢ
        (rationalGramCertificateCodeGrid (Fin n)
          (gramCertificateBound (1 + κ + n * ε)) θA ×ˢ
          (rationalGramCertificateCodeGrid ι
            (gramCertificateBound (η + 2 * r * εb)) θb ×ˢ
            rationalGramCertificateCodeGrid ι
              (gramCertificateBound (η + 2 * r * εb)) θb))))

/-- The tolerance-driven representation-preserving grid is exactly an instance of the
fully discrete grid with the displayed natural radii and denominators. -/
theorem uniformCertificateCodeSearchGrid_eq_rationalCertificateCodeGrid
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (η κ ε εb ω : ℝ) :
    let r := Fintype.card ι
    let θA := uniformCertificateRoundingMesh n ω
    let θb := uniformCertificateRoundingMesh r ω
    uniformCertificateCodeSearchGrid ι n η κ ε εb ω =
      rationalCertificateCodeGrid ι n
        (rationalMatrixGridRadius (approxSDPDensityEntryBound n κ ε))
        (rationalMatrixGridOrder θA)
        (rationalMatrixGridRadius (approxSDPAuxEntryBound r η εb))
        (rationalMatrixGridOrder θb)
        (rationalGramCertificateRadius (gramCertificateBound (1 + κ + n * ε)))
        (rationalGramCertificateOrder (Fin n)
          (gramCertificateBound (1 + κ + n * ε)) θA)
        (rationalGramCertificateRadius
          (gramCertificateBound (η + 2 * r * εb)))
        (rationalGramCertificateOrder ι
          (gramCertificateBound (η + 2 * r * εb)) θb) := by
  rfl

/-- For rational tolerances, the existing tolerance-driven search grid is exactly the
grid obtained by executable rational parameter computation. -/
theorem uniformCertificateCodeSearchGrid_eq_of_rational_tolerances
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (η κ ε εb ω : ℚ)
    (hε : 0 ≤ ε) (hεb : 0 ≤ εb) (hω : 0 < ω) :
    uniformCertificateCodeSearchGrid ι n
      (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ω : ℝ) =
        rationalCertificateCodeGridOfTolerances ι n η κ ε εb ω := by
  rw [uniformCertificateCodeSearchGrid_eq_rationalCertificateCodeGrid]
  let r := Fintype.card ι
  have hDensity : 0 ≤ rationalApproxSDPDensityEntryBound n κ ε := by
    simp only [rationalApproxSDPDensityEntryBound, rationalGramCertificateBound]
    positivity
  have hBoundary : 0 ≤ rationalApproxSDPAuxEntryBound r η εb := by
    simp only [rationalApproxSDPAuxEntryBound, rationalGramCertificateBound]
    positivity
  have hθA : 0 < rationalUniformCertificateRoundingMesh n ω := by
    simp only [rationalUniformCertificateRoundingMesh]
    positivity
  have hθb : 0 < rationalUniformCertificateRoundingMesh r ω := by
    simp only [rationalUniformCertificateRoundingMesh]
    positivity
  have hCA : 0 ≤ rationalGramCertificateBound (1 + κ + n * ε) := by
    exact add_nonneg zero_le_one (abs_nonneg _)
  have hCb : 0 ≤ rationalGramCertificateBound (η + 2 * r * εb) := by
    exact add_nonneg zero_le_one (abs_nonneg _)
  have hCAcast : gramCertificateBound (1 + (κ : ℝ) + n * (ε : ℝ)) =
      (rationalGramCertificateBound (1 + κ + n * ε) : ℝ) := by
    rw [rationalGramCertificateBound_cast]
    norm_num
  have hCbcast : gramCertificateBound ((η : ℝ) + 2 * r * (εb : ℝ)) =
      (rationalGramCertificateBound (η + 2 * r * εb) : ℝ) := by
    rw [rationalGramCertificateBound_cast]
    norm_num
  simp only [rationalCertificateCodeGridOfTolerances,
    rationalCertificateGridParameters]
  rw [← rationalApproxSDPDensityEntryBound_cast,
    rationalMatrixGridRadius_ratCast hDensity,
    ← rationalUniformCertificateRoundingMesh_cast,
    rationalMatrixGridOrder_ratCast hθA,
    ← rationalApproxSDPAuxEntryBound_cast,
    rationalMatrixGridRadius_ratCast hBoundary,
    ← rationalUniformCertificateRoundingMesh_cast,
    rationalMatrixGridOrder_ratCast hθb,
    hCAcast,
    rationalGramCertificateRadius_ratCast hCA,
    rationalGramCertificateOrder_ratCast (Fin n) hCA hθA,
    hCbcast,
    rationalGramCertificateRadius_ratCast hCb,
    rationalGramCertificateOrder_ratCast ι hCb hθb]
  simp [r]

/-- Decoding a representation-preserving candidate places it in the original complex
six-grid search. -/
theorem RationalCertificateCode.decode_mem_uniformCertificateSearchGrid
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} {η κ ε εb ω : ℝ} {c : RationalCertificateCode ι n}
    (hc : c ∈ uniformCertificateCodeSearchGrid ι n η κ ε εb ω) :
    c.decode ∈ uniformCertificateSearchGrid ι n η κ ε εb ω := by
  simp only [uniformCertificateCodeSearchGrid, Finset.mem_product] at hc
  simp only [RationalCertificateCode.decode, uniformCertificateSearchGrid,
    Finset.mem_product]
  exact ⟨c.1.decode_mem_rationalHermitianBoundedMatrixGrid hc.1,
    c.2.1.decode_mem_rationalHermitianBoundedMatrixGrid hc.2.1,
    c.2.2.1.decode_mem_rationalHermitianBoundedMatrixGrid hc.2.2.1,
    c.2.2.2.1.decode_mem_rationalGramCertificateGrid hc.2.2.2.1,
    c.2.2.2.2.1.decode_mem_rationalGramCertificateGrid hc.2.2.2.2.1,
    c.2.2.2.2.2.decode_mem_rationalGramCertificateGrid hc.2.2.2.2.2⟩

/-- Every candidate of the original complex six-grid search has a
representation-preserving rational preimage. -/
theorem exists_code_of_mem_uniformCertificateSearchGrid
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} {η κ ε εb ω : ℝ}
    {A QA : Matrix (Fin n) (Fin n) ℂ} {P N QP QN : Matrix ι ι ℂ}
    (h : (A, P, N, QA, QP, QN) ∈
      uniformCertificateSearchGrid ι n η κ ε εb ω) :
    ∃ c ∈ uniformCertificateCodeSearchGrid ι n η κ ε εb ω,
      c.decode = (A, P, N, QA, QP, QN) := by
  simp only [uniformCertificateSearchGrid, Finset.mem_product] at h
  obtain ⟨cA, hcA, rfl⟩ := exists_code_of_mem_rationalHermitianBoundedMatrixGrid h.1
  obtain ⟨cP, hcP, rfl⟩ := exists_code_of_mem_rationalHermitianBoundedMatrixGrid h.2.1
  obtain ⟨cN, hcN, rfl⟩ :=
    exists_code_of_mem_rationalHermitianBoundedMatrixGrid h.2.2.1
  obtain ⟨cQA, hcQA, rfl⟩ := exists_code_of_mem_rationalGramCertificateGrid h.2.2.2.1
  obtain ⟨cQP, hcQP, rfl⟩ :=
    exists_code_of_mem_rationalGramCertificateGrid h.2.2.2.2.1
  obtain ⟨cQN, hcQN, rfl⟩ :=
    exists_code_of_mem_rationalGramCertificateGrid h.2.2.2.2.2
  refine ⟨(cA, cP, cN, cQA, cQP, cQN), ?_, rfl⟩
  simp only [uniformCertificateCodeSearchGrid, Finset.mem_product]
  exact ⟨hcA, hcP, hcN, hcQA, hcQP, hcQN⟩

/-- Membership in the original complex grid is equivalent to having a rational-code
preimage in the representation-preserving grid. -/
theorem mem_uniformCertificateSearchGrid_iff_exists_code
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} {η κ ε εb ω : ℝ}
    {A QA : Matrix (Fin n) (Fin n) ℂ} {P N QP QN : Matrix ι ι ℂ} :
    (A, P, N, QA, QP, QN) ∈ uniformCertificateSearchGrid ι n η κ ε εb ω ↔
      ∃ c ∈ uniformCertificateCodeSearchGrid ι n η κ ε εb ω,
        c.decode = (A, P, N, QA, QP, QN) := by
  constructor
  · exact exists_code_of_mem_uniformCertificateSearchGrid
  · rintro ⟨c, hc, hdecode⟩
    rw [← hdecode]
    exact c.decode_mem_uniformCertificateSearchGrid hc

/-- Retaining rational coordinate pairs does not enlarge the six-grid search. -/
theorem uniformCertificateCodeSearchGrid_card_eq
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (η κ ε εb ω : ℝ) :
    (uniformCertificateCodeSearchGrid ι n η κ ε εb ω).card =
      (uniformCertificateSearchGrid ι n η κ ε εb ω).card := by
  simp only [uniformCertificateCodeSearchGrid, uniformCertificateSearchGrid,
    Finset.card_product]
  rw [rationalHermitianBoundedMatrixCodeGrid_card_eq (Fin n),
    rationalHermitianBoundedMatrixCodeGrid_card_eq ι,
    rationalGramCertificateCodeGrid_card_eq (Fin n),
    rationalGramCertificateCodeGrid_card_eq ι]

/-- Common coordinate-height bound for all six matrices in the uniform certificate
search. -/
noncomputable def uniformCertificateCandidateEntryHeight
    (ι : Type*) [Fintype ι] (n : ℕ) (η κ ε εb ω : ℝ) : ℕ :=
  let r := Fintype.card ι
  let θA := uniformCertificateRoundingMesh n ω
  let θb := uniformCertificateRoundingMesh r ω
  let HA := rationalHermitianBoundedMatrixGridHeight
    (approxSDPDensityEntryBound n κ ε) θA
  let Hb := rationalHermitianBoundedMatrixGridHeight
    (approxSDPAuxEntryBound r η εb) θb
  let HGA := rationalGramCertificateGridHeight (Fin n)
    (gramCertificateBound (1 + κ + n * ε)) θA
  let HGb := rationalGramCertificateGridHeight ι
    (gramCertificateBound (η + 2 * r * εb)) θb
  max (max HA Hb) (max HGA HGb)

/-- Every matrix in a six-grid candidate obeys the common candidate height bound. -/
theorem uniformCertificateSearchGrid_entries_height_le
    {ι : Type*} [Fintype ι] {n : ℕ} {η κ ε εb ω : ℝ}
    {A QA : Matrix (Fin n) (Fin n) ℂ} {P N QP QN : Matrix ι ι ℂ}
    (h : (A, P, N, QA, QP, QN) ∈
      uniformCertificateSearchGrid ι n η κ ε εb ω) :
    let H := uniformCertificateCandidateEntryHeight ι n η κ ε εb ω
    Matrix.HasRationalEntriesOfHeight H A ∧
      Matrix.HasRationalEntriesOfHeight H P ∧
      Matrix.HasRationalEntriesOfHeight H N ∧
      Matrix.HasRationalEntriesOfHeight H QA ∧
      Matrix.HasRationalEntriesOfHeight H QP ∧
      Matrix.HasRationalEntriesOfHeight H QN := by
  simp only [uniformCertificateSearchGrid, Finset.mem_product] at h
  rcases h with ⟨hA, hP, hN, hQA, hQP, hQN⟩
  dsimp only [uniformCertificateCandidateEntryHeight]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (rationalHermitianBoundedMatrixGrid_hasRationalEntriesOfHeight hA).mono
      ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))
  · exact (rationalHermitianBoundedMatrixGrid_hasRationalEntriesOfHeight hP).mono
      ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  · exact (rationalHermitianBoundedMatrixGrid_hasRationalEntriesOfHeight hN).mono
      ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  · exact (rationalGramCertificateGrid_hasRationalEntriesOfHeight hQA).mono
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  · exact (rationalGramCertificateGrid_hasRationalEntriesOfHeight hQP).mono
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  · exact (rationalGramCertificateGrid_hasRationalEntriesOfHeight hQN).mono
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

/-- One coordinate-height bound covering every matrix and scalar expression tested for
a candidate, given common height bounds `HD` for the fixed problem data and `HC` for
the six candidate matrices. -/
def uniformCertificateTestExpressionHeight (a n r HD HC : ℕ) : ℕ :=
  let Hb := compressedBoundaryResidualHeight a n HD HC HD HC HC
  let Ho := matrixTraceProductHeight n HC HD
  let Ht := max (matrixTraceHeight n HC) (matrixTraceHeight r HC)
  let HGA := shiftedGramResidualHeight n HC HD HC
  let HGb := shiftedGramResidualHeight r HC HD HC
  max Hb (max Ho (max Ht (max HGA HGb)))

/-- The dense-product height bound is monotone in either matrix height. -/
theorem matrixProductHeight_mono (d : ℕ) {H H' K K' : ℕ}
    (hH : H ≤ H') (hK : K ≤ K') :
    matrixProductHeight d H K ≤ matrixProductHeight d H' K' := by
  unfold matrixProductHeight
  exact Nat.pow_le_pow_left (by gcongr) d

/-- The trace height bound is monotone in the matrix height. -/
theorem matrixTraceHeight_mono (d : ℕ) {H H' : ℕ} (hH : H ≤ H') :
    matrixTraceHeight d H ≤ matrixTraceHeight d H' := by
  unfold matrixTraceHeight
  exact Nat.pow_le_pow_left (by gcongr) d

/-- The shifted-Gram residual height is monotone in the shifted matrix height. -/
theorem shiftedGramResidualHeight_mono_shift (d HA HQ : ℕ) {Hε Hε' : ℕ}
    (hε : Hε ≤ Hε') :
    shiftedGramResidualHeight d HA Hε HQ ≤
      shiftedGramResidualHeight d HA Hε' HQ := by
  simp only [shiftedGramResidualHeight]
  gcongr

/-- The compressed-boundary residual height is monotone in the fixed coordinate-map
and boundary-centre heights when they share one common bound. -/
theorem compressedBoundaryResidualHeight_mono_fixedData
    (a n HA HP HN : ℕ) {HD HD' : ℕ} (hHD : HD ≤ HD') :
    compressedBoundaryResidualHeight a n HD HA HD HP HN ≤
      compressedBoundaryResidualHeight a n HD' HA HD' HP HN := by
  simp only [compressedBoundaryResidualHeight, compressedBoundaryHeight]
  gcongr
  · exact matrixTraceHeight_mono _
      (matrixProductHeight_mono _
        (matrixProductHeight_mono _ hHD le_rfl) hHD)

/-- Enlarging the common height bound for the fixed data enlarges the common height
bound for every expression tested on a certificate candidate. -/
theorem uniformCertificateTestExpressionHeight_mono_fixedData
    (a n r HC : ℕ) {HD HD' : ℕ} (hHD : HD ≤ HD') :
    uniformCertificateTestExpressionHeight a n r HD HC ≤
      uniformCertificateTestExpressionHeight a n r HD' HC := by
  simp only [uniformCertificateTestExpressionHeight, matrixTraceProductHeight]
  gcongr
  · exact compressedBoundaryResidualHeight_mono_fixedData _ _ _ _ _ hHD
  · exact matrixTraceHeight_mono _ (matrixProductHeight_mono _ le_rfl hHD)
  · exact shiftedGramResidualHeight_mono_shift _ _ _ hHD
  · exact shiftedGramResidualHeight_mono_shift _ _ _ hHD

/-- Bit length certified by common fixed-data and candidate-expression height bounds. -/
def certificateTestOperandBitLength (a n r HD HC : ℕ) : ℕ :=
  Nat.log2 (uniformCertificateTestExpressionHeight a n r HD HC) + 1

/-- Taking a binary logarithm converts monotonicity of the tested-expression height
into monotonicity of its certified operand length. -/
theorem certificateTestOperandBitLength_mono_fixedData
    (a n r HC : ℕ) {HD HD' : ℕ} (hHD : HD ≤ HD') :
    certificateTestOperandBitLength a n r HD HC ≤
      certificateTestOperandBitLength a n r HD' HC := by
  unfold certificateTestOperandBitLength
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (b := 2)
    (uniformCertificateTestExpressionHeight_mono_fixedData a n r HC hHD)) 1

end TNLean.MPS.AreaLaw
