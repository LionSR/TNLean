/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SearchCompleteness

/-!
# Soundness of rational certificate search

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Entrywise certification of the boundary equation is sufficient for the unified
finite-precision feasibility statement.  If every residual entry has modulus at most
`ζ`, it suffices to budget `r² ζ ≤ δ`, where `r` is the boundary-matrix order. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.of_entrywise_residual
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ζ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (hA : A.IsHermitian) (hP : P.IsHermitian) (hN : N.IsHermitian)
    (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hεb : 0 ≤ εb) (hPmin : -εb ≤ minEigenvalue hP)
    (hNmin : -εb ≤ minEigenvalue hN)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ)
    (hscale : (Fintype.card (s × b) : ℝ) ^ 2 * ζ ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N := by
  exact ⟨hA, hP, hN, htrace, hε, hmin, hεb, hPmin, hNmin,
    rectangularTraceNorm_le_of_entry_norm_le _ hresidual hscale, htraces, henergy⟩

/-- Gershgorin row inequalities for all three cone variables, together with entrywise
control of the boundary residual, certify the complete unified feasibility predicate.
All non-scalar numerical conditions are thereby reduced to finitely many entrywise norm
and real inequalities. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.of_gershgorin
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ζ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (hA : A.IsHermitian) (hP : P.IsHermitian) (hN : N.IsHermitian)
    (htrace : |1 - A.trace.re| ≤ κ) (hε : 0 ≤ ε)
    (hArows : ∀ i, -ε + ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ (A i i).re)
    (hεb : 0 ≤ εb)
    (hProws : ∀ i, -εb + ∑ j ∈ Finset.univ.erase i, ‖P i j‖ ≤ (P i i).re)
    (hNrows : ∀ i, -εb + ∑ j ∈ Finset.univ.erase i, ‖N i j‖ ≤ (N i i).re)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ)
    (hscale : (Fintype.card (s × b) : ℝ) ^ 2 * ζ ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N := by
  exact .of_entrywise_residual hA hP hN htrace hε
    (neg_le_minEigenvalue_of_gershgorin hA hArows) hεb
    (neg_le_minEigenvalue_of_gershgorin hP hProws)
    (neg_le_minEigenvalue_of_gershgorin hN hNrows)
    hresidual hscale htraces henergy

/-- Gram factorizations of the three shifted cone variables and entrywise control of the
boundary residual certify the unified feasibility predicate.  This version imposes no
diagonal-dominance restriction: a shifted Hermitian matrix is positive semidefinite
precisely when it admits such a complex Gram factorization. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.of_gram_factors
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ζ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (hA : A.IsHermitian) (hP : P.IsHermitian) (hN : N.IsHermitian)
    (htrace : |1 - A.trace.re| ≤ κ) (hε : 0 ≤ ε)
    (RA : Matrix (Fin n) (Fin n) ℂ)
    (hAfactor : A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = RA * RAᴴ)
    (hεb : 0 ≤ εb) (RP RN : Matrix (s × b) (s × b) ℂ)
    (hPfactor : P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) = RP * RPᴴ)
    (hNfactor : N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) = RN * RNᴴ)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ)
    (hscale : (Fintype.card (s × b) : ℝ) ^ 2 * ζ ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N := by
  exact .of_entrywise_residual hA hP hN htrace hε
    (neg_le_minEigenvalue_of_add_smul_one_eq_mul_conjTranspose hA RA hAfactor) hεb
    (neg_le_minEigenvalue_of_add_smul_one_eq_mul_conjTranspose hP RP hPfactor)
    (neg_le_minEigenvalue_of_add_smul_one_eq_mul_conjTranspose hN RN hNfactor)
    hresidual hscale htraces henergy

/-- Entrywise approximate Gram factorizations give a stable certificate for all three
cone constraints.  Their dimension-weighted factorization errors are absorbed into the
allowed spectral tolerances `ε` and `εb`; the boundary equation is certified entrywise as
before. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.of_approx_gram_factors
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (hA : A.IsHermitian) (hP : P.IsHermitian) (hN : N.IsHermitian)
    (htrace : |1 - A.trace.re| ≤ κ) (hε : 0 ≤ ε)
    (RA : Matrix (Fin n) (Fin n) ℂ) (hζA : 0 ≤ ζA)
    (hAfactor : ∀ i j,
      ‖(A + (εA₀ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - RA * RAᴴ) i j‖ ≤ ζA)
    (hAbudget : εA₀ + ((n : ℝ) + 1) * ζA ≤ ε)
    (hεb : 0 ≤ εb) (RP RN : Matrix (s × b) (s × b) ℂ)
    (hζP : 0 ≤ ζP) (hζN : 0 ≤ ζN)
    (hPfactor : ∀ i j,
      ‖(P + (εP₀ : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - RP * RPᴴ) i j‖ ≤ ζP)
    (hNfactor : ∀ i j,
      ‖(N + (εN₀ : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - RN * RNᴴ) i j‖ ≤ ζN)
    (hPbudget : εP₀ + ((Fintype.card (s × b) : ℝ) + 1) * ζP ≤ εb)
    (hNbudget : εN₀ + ((Fintype.card (s × b) : ℝ) + 1) * ζN ≤ εb)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ)
    (hscale : (Fintype.card (s × b) : ℝ) ^ 2 * ζ ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N := by
  exact .of_entrywise_residual hA hP hN htrace hε
    (neg_le_minEigenvalue_of_approx_gram_factor hA hζA RA hAfactor
      (by simpa only [Fintype.card_fin] using hAbudget)) hεb
    (neg_le_minEigenvalue_of_approx_gram_factor hP hζP RP hPfactor hPbudget)
    (neg_le_minEigenvalue_of_approx_gram_factor hN hζN RN hNfactor hNbudget)
    hresidual hscale htraces henergy

/-- Soundness of the executable rational acceptance test.  Equality witnesses connect
the stored rational values to the complex matrix expressions; all inequalities used to
construct the approximate SDP certificate then come from the decidable rational test. -/
theorem RationalApproxCertificateTestValues.sound
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {A RA : Matrix (Fin n) (Fin n) ℂ}
    {P N RP RN : Matrix (s × b) (s × b) ℂ}
    (v : RationalApproxCertificateTestValues (s × b) n)
    {η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN : ℚ}
    (haccept : v.Accepts η E κ ε εb δ ζ εA₀ ζA εP₀ ζP εN₀ ζN)
    (hA : A.IsHermitian) (hP : P.IsHermitian) (hN : N.IsHermitian)
    (htraceA : A.trace.re = (v.densityTrace : ℝ))
    (htraceP : P.trace.re = (v.positiveTrace : ℝ))
    (htraceN : N.trace.re = (v.negativeTrace : ℝ))
    (hobjective : (A * K).trace.re = (v.objective : ℝ))
    (hboundary : ∀ i j,
      (((compressedBoundaryLM Z A - X) - (P - N)) i j) =
        ⟨((v.boundaryResidual i j).1 : ℝ),
          ((v.boundaryResidual i j).2 : ℝ)⟩)
    (hAfactor : ∀ i j,
      (A + (εA₀ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - RA * RAᴴ) i j =
        ⟨((v.densityGramResidual i j).1 : ℝ),
          ((v.densityGramResidual i j).2 : ℝ)⟩)
    (hPfactor : ∀ i j,
      (P + (εP₀ : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - RP * RPᴴ) i j =
        ⟨((v.positiveGramResidual i j).1 : ℝ),
          ((v.positiveGramResidual i j).2 : ℝ)⟩)
    (hNfactor : ∀ i j,
      (N + (εN₀ : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - RN * RNᴴ) i j =
        ⟨((v.negativeGramResidual i j).1 : ℝ),
          ((v.negativeGramResidual i j).2 : ℝ)⟩) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N := by
  rcases haccept with ⟨hε, hεb, hζ, hζA, hζP, hζN, htrace, hAgr, hAbudget,
    hPgr, hPbudget, hNgr, hNbudget, hboundaryTest, hscale, htraces, henergy⟩
  have hAfactor' : ∀ i j,
      ‖(A + (εA₀ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - RA * RAᴴ) i j‖ ≤
        (ζA : ℝ) := by
    intro i j
    rw [hAfactor i j]
    exact (gaussianRational_norm_le_iff _ _ _ hζA).2 (hAgr i j)
  have hPfactor' : ∀ i j,
      ‖(P + (εP₀ : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - RP * RPᴴ) i j‖ ≤
        (ζP : ℝ) := by
    intro i j
    rw [hPfactor i j]
    exact (gaussianRational_norm_le_iff _ _ _ hζP).2 (hPgr i j)
  have hNfactor' : ∀ i j,
      ‖(N + (εN₀ : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - RN * RNᴴ) i j‖ ≤
        (ζN : ℝ) := by
    intro i j
    rw [hNfactor i j]
    exact (gaussianRational_norm_le_iff _ _ _ hζN).2 (hNgr i j)
  have hboundary' : ∀ i j,
      ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ (ζ : ℝ) := by
    intro i j
    rw [hboundary i j]
    exact (gaussianRational_norm_le_iff _ _ _ hζ).2 (hboundaryTest i j)
  have htrace' : |1 - A.trace.re| ≤ (κ : ℝ) := by
    rw [htraceA]
    exact_mod_cast htrace
  have hε' : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
  have hζA' : (0 : ℝ) ≤ (ζA : ℝ) := by exact_mod_cast hζA
  have hAbudget' : (εA₀ : ℝ) + ((n : ℝ) + 1) * (ζA : ℝ) ≤ (ε : ℝ) := by
    exact_mod_cast hAbudget
  have hεb' : (0 : ℝ) ≤ (εb : ℝ) := by exact_mod_cast hεb
  have hζP' : (0 : ℝ) ≤ (ζP : ℝ) := by exact_mod_cast hζP
  have hζN' : (0 : ℝ) ≤ (ζN : ℝ) := by exact_mod_cast hζN
  have hPbudget' : (εP₀ : ℝ) + ((Fintype.card (s × b) : ℝ) + 1) * (ζP : ℝ) ≤
      (εb : ℝ) := by
    exact_mod_cast hPbudget
  have hNbudget' : (εN₀ : ℝ) + ((Fintype.card (s × b) : ℝ) + 1) * (ζN : ℝ) ≤
      (εb : ℝ) := by
    exact_mod_cast hNbudget
  have hscale' : (Fintype.card (s × b) : ℝ) ^ 2 * (ζ : ℝ) ≤ (δ : ℝ) := by
    exact_mod_cast hscale
  have htraces' : P.trace.re + N.trace.re ≤ (η : ℝ) := by
    rw [htraceP, htraceN]
    exact_mod_cast htraces
  have henergy' : (A * K).trace.re ≤ (E : ℝ) := by
    rw [hobjective]
    exact_mod_cast henergy
  exact IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.of_approx_gram_factors
    hA hP hN htrace' hε' RA hζA' hAfactor' hAbudget' hεb' RP RN hζP' hζN'
      hPfactor' hNfactor' hPbudget' hNbudget' hboundary' hscale' htraces' henergy'

/-- Acceptance of the directly evaluated rational record certifies the decoded
six-matrix candidate for the complete approximate compressed SDP. -/
theorem RationalCertificateCode.testValues_sound
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)] [Nonempty (Fin n)]
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ : ℚ) (c : RationalCertificateCode (s × b) n)
    {η E κ ε εb δ ζ ζA ζP ζN : ℚ}
    (haccept : (c.testValues Z K X εA₀ εb₀).Accepts
      η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN)
    (hA : c.1.decode.IsHermitian)
    (hP : c.2.1.decode.IsHermitian)
    (hN : c.2.2.1.decode.IsHermitian) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      (RationalRectMatrixCode.decode Z) (RationalRectMatrixCode.decode K)
      (RationalRectMatrixCode.decode X)
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ)
      c.1.decode c.2.1.decode c.2.2.1.decode := by
  obtain ⟨htraceA, htraceP, htraceN, hobjective, hboundary,
      hAfactor, hPfactor, hNfactor⟩ := c.testValues_correct Z K X εA₀ εb₀
  exact RationalApproxCertificateTestValues.sound
    (c.testValues Z K X εA₀ εb₀) haccept hA hP hN
    htraceA htraceP htraceN hobjective
    (by simpa [decodeRationalComplex] using hboundary)
    (by simpa [decodeRationalComplex] using hAfactor)
    (by simpa [decodeRationalComplex] using hPfactor)
    (by simpa [decodeRationalComplex] using hNfactor)

/-- Any code returned by the executable discrete-grid search certifies approximate SDP
feasibility for the decoded rational input. -/
theorem searchRationalCertificateCodeGrid_sdp_sound
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)]
    [Nonempty (s × b)] [Nonempty (Fin n)]
    (BA MA Bb Mb BGA MGA BGb MGb : ℕ)
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (s × b) n}
    (hfind : searchRationalCertificateCodeGrid BA MA Bb Mb BGA MGA BGb MGb
      Z K X εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      (RationalRectMatrixCode.decode Z) (RationalRectMatrixCode.decode K)
      (RationalRectMatrixCode.decode X)
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ)
      c.1.decode c.2.1.decode c.2.2.1.decode := by
  obtain ⟨hgrid, haccept⟩ := searchRationalCertificateCodeGrid_sound
    BA MA Bb Mb BGA MGA BGb MGb Z K X
    εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN hfind
  obtain ⟨hA, hP, hN⟩ := c.primary_isHermitian_of_mem_grid hgrid
  exact c.testValues_sound Z K X εA₀ εb₀ haccept hA hP hN

/-- Any code returned by the rational-tolerance search certifies approximate SDP
feasibility for the decoded rational input. -/
theorem searchRationalCertificateCodeGridOfTolerances_sdp_sound
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)]
    [Nonempty (s × b)] [Nonempty (Fin n)]
    (gridη gridκ gridε gridεb gridω : ℚ)
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (s × b) n}
    (hfind : searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω Z K X
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      (RationalRectMatrixCode.decode Z) (RationalRectMatrixCode.decode K)
      (RationalRectMatrixCode.decode X)
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ)
      c.1.decode c.2.1.decode c.2.2.1.decode := by
  let p := rationalCertificateGridParameters n (Fintype.card (s × b))
    gridη gridκ gridε gridεb gridω
  obtain ⟨hgrid, haccept⟩ := firstAcceptedInFinset_sound
    (rationalCertificateCodeGridOfTolerances (s × b) n
      gridη gridκ gridε gridεb gridω)
    (fun d ↦ (d.testValues Z K X εA₀ εb₀).Accepts
      η E κ ε εb δ ζ εA₀ ζA εb₀ ζP εb₀ ζN) hfind
  change c ∈ rationalCertificateCodeGrid (s × b) n
    p.densityRadius p.densityOrder p.boundaryRadius p.boundaryOrder
    p.densityGramRadius p.densityGramOrder
    p.boundaryGramRadius p.boundaryGramOrder at hgrid
  obtain ⟨hA, hP, hN⟩ := c.primary_isHermitian_of_mem_grid hgrid
  exact c.testValues_sound Z K X εA₀ εb₀ haccept hA hP hN

/-- A code returned using rational approximations of all fixed data certifies the exact
problem after the explicit objective, boundary-centre, and coordinate-map losses are
added.  The rational coordinate code is not required to be an isometry. -/
theorem searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    {a s b : Type*} {n : ℕ} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)]
    [Nonempty (s × b)] [Nonempty (Fin n)]
    (gridη gridκ gridε gridεb gridω : ℚ)
    (QZ : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode (s × b) (s × b))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (s × b) n}
    (hfind : searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω QZ QK QX
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c)
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hZ : Zᴴ * Z = 1) {θZ θK θX : ℝ} (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j, ‖(K - QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) :
    let r := Fintype.card (s × b)
    let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) ((E : ℝ) + (n : ℝ) ^ 2 * C * θK)
      (κ : ℝ) (ε : ℝ) (εb : ℝ)
      ((δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ)))
      c.1.decode c.2.1.decode c.2.2.1.decode := by
  dsimp only
  have hQ := searchRationalCertificateCodeGridOfTolerances_sdp_sound
    gridη gridκ gridε gridεb gridω QZ QK QX
    εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN hfind
  have hfixed := hQ.of_fixed_data_approximation hKclose hXclose
  exact hfixed.of_coordinate_approximation hZ hθZ hZclose

namespace IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy

/-- End-to-end numerical completeness and exact-data soundness.  From one feasible
exact-data certificate, the executable search returns a rational code whose decoded
primary matrices certify the exact problem with all forward and reverse approximation
losses displayed. -/
theorem exists_approx_data_search_result_and_exact_certificate
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
    let C := approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
    ∃ c,
      searchRationalCertificateCodeGridOfTolerances
        η κ ε εb ρ QZ QK QX ε εb
        (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
        ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c ∧
      IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
        (((η + ρ : ℚ) : ℝ))
        ((Et : ℝ) + (n : ℝ) ^ 2 * C * θK)
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) (((εb + ρ : ℚ) : ℝ))
        ((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ) + (r : ℝ) ^ 2 * θX +
          (r : ℝ) ^ 2 *
            (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ)))
        c.1.decode c.2.1.decode c.2.2.1.decode := by
  dsimp only
  obtain ⟨c, hfind⟩ := h.exists_approx_data_search_result QZ QK QX hZ hρ hθZ
    hZclose hKclose hXclose hEt hDt
  refine ⟨c, hfind, ?_⟩
  exact searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    η κ ε εb ρ QZ QK QX ε εb
    (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((Fintype.card (s × b) : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh (Fintype.card (s × b)) ρ)
    (2 * rationalUniformCertificateRoundingMesh (Fintype.card (s × b)) ρ)
    hfind Z K X hZ hθZ hZclose hKclose hXclose

end IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy

end TNLean.MPS.AreaLaw
