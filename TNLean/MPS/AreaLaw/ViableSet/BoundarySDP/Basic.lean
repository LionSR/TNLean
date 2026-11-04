/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.FiniteBoundarySelection
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNet
import TNLean.MPS.AreaLaw.ViableSet.Span
import TNLean.MPS.AreaLaw.ViableSet.LeftCoordinates
import TNLean.MPS.AreaLaw.ViableSet.Endpoints
import TNLean.MPS.Preparation.IsometricChain
import TNLean.Algebra.FinsetNormSumCauchySchwarz
import QICLean.Analysis.TraceNormContractivity
import QICLean.Analysis.TraceNormNet
import QICLean.Analysis.RectangularTraceNormTopology
import QICLean.Algebra.MatrixIsometryEntries
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Data.NNRat.Floor
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Data.Nat.Log


/-!
# Semidefinite boundary constraints and matrix perturbation bounds

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A uniform entrywise error bound gives a trace-norm error bound with the square of
the matrix order as dimension factor.  This is the elementary certification step for
turning entrywise numerical residual estimates into the trace-norm residual required by
the compressed LVV semidefinite program. -/
theorem rectangularTraceNorm_le_card_sq_mul_of_entry_norm_le
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {ε : ℝ}
    (hentry : ∀ i j, ‖A i j‖ ≤ ε) :
    rectangularTraceNorm A ≤ (Fintype.card n : ℝ) ^ 2 * ε := by
  calc
    rectangularTraceNorm A ≤ ∑ i, ∑ j, ‖A i j‖ :=
      rectangularTraceNorm_le_sum_norm_apply A
    _ ≤ ∑ _i : n, ∑ _j : n, ε := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hentry i j
    _ = (Fintype.card n : ℝ) ^ 2 * ε := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- An entrywise residual tolerance certifies any prescribed trace-norm tolerance once
the square-order scaling inequality is checked. -/
theorem rectangularTraceNorm_le_of_entry_norm_le
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {ε δ : ℝ}
    (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (hscale : (Fintype.card n : ℝ) ^ 2 * ε ≤ δ) :
    rectangularTraceNorm A ≤ δ :=
  (rectangularTraceNorm_le_card_sq_mul_of_entry_norm_le A hentry).trans hscale

/-- Each squared entry of a Gram factor is bounded by the real trace of its Gram
matrix.  This supplies bounded search regions for factor certificates. -/
theorem norm_sq_apply_le_re_trace_mul_conjTranspose
    {n : Type*} [Fintype n] (R : Matrix n n ℂ) (i j : n) :
    ‖R i j‖ ^ 2 ≤ (R * Rᴴ).trace.re := by
  rw [Matrix.trace_mul_comm, Matrix.trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
  exact (Finset.single_le_sum (f := fun i' ↦ ‖R i' j‖ ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun j' ↦ ∑ i', ‖R i' j'‖ ^ 2)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j))

/-- Entrywise bounds on two square matrices give the corresponding elementary bound
on every entry of their product. -/
theorem norm_mul_apply_le_card_mul_of_entry_norm_le
    {n : Type*} [Fintype n] (A B : Matrix n n ℂ) {α β : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ α) (hB : ∀ i j, ‖B i j‖ ≤ β)
    (hα : 0 ≤ α) (i j : n) :
    ‖(A * B) i j‖ ≤ Fintype.card n * α * β := by
  rw [Matrix.mul_apply]
  calc
    ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : n, α * β := by
      exact Finset.sum_le_sum fun k _ ↦ by
        rw [norm_mul]
        exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hα
    _ = Fintype.card n * α * β := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Entrywise bounds on rectangular matrices give the elementary bound on every
entry of their product. -/
theorem norm_rectangular_mul_apply_le_card_mul_of_entry_norm_le
    {m n p : Type*} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) {α β : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ α) (hB : ∀ i j, ‖B i j‖ ≤ β)
    (hα : 0 ≤ α) (i : m) (j : p) :
    ‖(A * B) i j‖ ≤ Fintype.card n * α * β := by
  rw [Matrix.mul_apply]
  calc
    ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : n, α * β := by
      exact Finset.sum_le_sum fun k _ ↦ by
        rw [norm_mul]
        exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hα
    _ = Fintype.card n * α * β := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Entrywise bounds give a quadratic-dimension bound on the trace pairing of two
square matrices. -/
theorem norm_trace_mul_le_card_sq_mul_of_entry_norm_le
    {n : Type*} [Fintype n] (A B : Matrix n n ℂ) {C θ : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ C) (hB : ∀ i j, ‖B i j‖ ≤ θ)
    (hC : 0 ≤ C) :
    ‖(A * B).trace‖ ≤ (Fintype.card n : ℝ) ^ 2 * C * θ := by
  rw [Matrix.trace]
  calc
    ‖∑ i, (A * B) i i‖ ≤ ∑ i, ‖(A * B) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, Fintype.card n * C * θ := by
      exact Finset.sum_le_sum fun i _ ↦
        norm_rectangular_mul_apply_le_card_mul_of_entry_norm_le A B hA hB hC i i
    _ = (Fintype.card n : ℝ) ^ 2 * C * θ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Entrywise approximation of an objective matrix changes every bounded matrix trace
pairing by at most the quadratic-dimension entrywise estimate. -/
theorem abs_re_trace_mul_sub_le_of_entry_norm_le
    {n : Type*} [Fintype n] (A K Q : Matrix n n ℂ) {C θ : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ C) (hclose : ∀ i j, ‖(K - Q) i j‖ ≤ θ)
    (hC : 0 ≤ C) :
    |(A * K).trace.re - (A * Q).trace.re| ≤
      (Fintype.card n : ℝ) ^ 2 * C * θ := by
  calc
    |(A * K).trace.re - (A * Q).trace.re| =
        |((A * K).trace - (A * Q).trace).re| := by rw [Complex.sub_re]
    _ = |(A * (K - Q)).trace.re| := by rw [Matrix.mul_sub, Matrix.trace_sub]
    _ ≤ ‖(A * (K - Q)).trace‖ := Complex.abs_re_le_norm _
    _ ≤ (Fintype.card n : ℝ) ^ 2 * C * θ :=
      norm_trace_mul_le_card_sq_mul_of_entry_norm_le A (K - Q) hA hclose hC

/-- A squared-entry bound on a matrix gives an entrywise bound on its Gram matrix. -/
theorem norm_mul_conjTranspose_apply_le_card_mul_of_sq_entry_norm_le
    {n : Type*} [Fintype n] (R : Matrix n n ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ i j, ‖R i j‖ ^ 2 ≤ C) (i j : n) :
    ‖(R * Rᴴ) i j‖ ≤ Fintype.card n * C := by
  have hentry : ∀ i j, ‖R i j‖ ≤ √C := by
    intro i j
    nlinarith [hR i j, Real.sq_sqrt hC, norm_nonneg (R i j), Real.sqrt_nonneg C]
  have hstar : ∀ i j, ‖Rᴴ i j‖ ≤ √C := by
    intro i j
    rw [Matrix.conjTranspose_apply, norm_star]
    exact hentry j i
  calc
    ‖(R * Rᴴ) i j‖ ≤ Fintype.card n * √C * √C :=
      norm_mul_apply_le_card_mul_of_entry_norm_le R Rᴴ hentry hstar
        (Real.sqrt_nonneg C) i j
    _ = Fintype.card n * (√C * √C) := by ring
    _ = Fintype.card n * C := by rw [Real.mul_self_sqrt hC]

/-- Entrywise approximation of a bounded matrix controls its Gram matrix entrywise.
If `R` has entries of norm at most `M` and `Q` is entrywise `δ`-close to `R`, then
the Gram error is at most `d δ (2M + δ)` in every entry. -/
theorem norm_gram_sub_apply_le_of_entry_norm_le
    {n : Type*} [Fintype n] (R Q : Matrix n n ℂ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hR : ∀ i j, ‖R i j‖ ≤ M)
    (hclose : ∀ i j, ‖(R - Q) i j‖ ≤ δ) (i j : n) :
    ‖(R * Rᴴ - Q * Qᴴ) i j‖ ≤ Fintype.card n * δ * (2 * M + δ) := by
  have hQ : ∀ i j, ‖Q i j‖ ≤ M + δ := by
    intro i j
    calc
      ‖Q i j‖ = ‖R i j - (R - Q) i j‖ := by congr 2; simp
      _ ≤ ‖R i j‖ + ‖(R - Q) i j‖ := norm_sub_le _ _
      _ ≤ M + δ := add_le_add (hR i j) (hclose i j)
  have hstarR : ∀ i j, ‖Rᴴ i j‖ ≤ M := by
    intro i j
    rw [Matrix.conjTranspose_apply, norm_star]
    exact hR j i
  have hstarDiff : ∀ i j, ‖(R - Q)ᴴ i j‖ ≤ δ := by
    intro i j
    rw [Matrix.conjTranspose_apply, norm_star]
    exact hclose j i
  have hid : R * Rᴴ - Q * Qᴴ = (R - Q) * Rᴴ + Q * (R - Q)ᴴ := by
    rw [Matrix.conjTranspose_sub, sub_mul, mul_sub]
    abel
  rw [hid, Matrix.add_apply]
  calc
    ‖((R - Q) * Rᴴ) i j + (Q * (R - Q)ᴴ) i j‖ ≤
        ‖((R - Q) * Rᴴ) i j‖ + ‖(Q * (R - Q)ᴴ) i j‖ := norm_add_le _ _
    _ ≤ Fintype.card n * δ * M + Fintype.card n * (M + δ) * δ :=
      add_le_add
        (norm_mul_apply_le_card_mul_of_entry_norm_le (R - Q) Rᴴ hclose hstarR hδ i j)
        (norm_mul_apply_le_card_mul_of_entry_norm_le Q (R - Q)ᴴ hQ hstarDiff
          (add_nonneg hM hδ) i j)
    _ = Fintype.card n * δ * (2 * M + δ) := by ring

/-- A Hermitian matrix whose Gershgorin row intervals lie to the right of `-ε` has
least eigenvalue at least `-ε`.  This gives an entrywise certificate for the approximate
positive-semidefiniteness conditions in the numerical LVV semidefinite program. -/
theorem neg_le_minEigenvalue_of_gershgorin
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ}
    (hrows : ∀ i, -ε + ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ (A i i).re) :
    -ε ≤ minEigenvalue hA := by
  obtain ⟨i, hi⟩ := minEigenvalue_achieved hA
  let ψ : n → ℂ := ⇑(hA.eigenvectorBasis i)
  have hψne : ψ ≠ 0 := by
    intro hψ
    have hnorm := hA.eigenvectorBasis.orthonormal.1 i
    rw [show hA.eigenvectorBasis i = 0 by ext j; exact congrFun hψ j, norm_zero] at hnorm
    norm_num at hnorm
  have hψ : A *ᵥ ψ = (hA.eigenvalues i : ℂ) • ψ := by
    simpa only [ψ, RCLike.real_smul_eq_coe_smul] using! hA.mulVec_eigenvectorBasis i
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector <| Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hψ), hψne⟩
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  have hk' : ‖(hA.eigenvalues i : ℂ) - A k k‖ ≤
      ∑ j ∈ Finset.univ.erase k, ‖A k j‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hk
  have hre : |hA.eigenvalues i - (A k k).re| ≤
      ∑ j ∈ Finset.univ.erase k, ‖A k j‖ := by
    exact (Complex.abs_re_le_norm ((hA.eigenvalues i : ℂ) - A k k)).trans hk'
  rw [hi] at hre
  linarith [hrows k, neg_abs_le (minEigenvalue hA - (A k k).re)]

/-- Uniform entrywise control of a Hermitian matrix gives a least-eigenvalue lower bound.
The factor `r + 1` is a convenient dimension bound for one diagonal entry and at most
`r` off-diagonal entries in a Gershgorin row. -/
theorem neg_card_add_one_mul_le_minEigenvalue_of_entry_norm_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (hentry : ∀ i j, ‖A i j‖ ≤ ζ) :
    -((Fintype.card n : ℝ) + 1) * ζ ≤ minEigenvalue hA := by
  have h := neg_le_minEigenvalue_of_gershgorin
    (ε := ((Fintype.card n : ℝ) + 1) * ζ) hA
    (show ∀ i, -(((Fintype.card n : ℝ) + 1) * ζ) +
        ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ (A i i).re by
      intro i
      have hsum : ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤
          (Fintype.card n : ℝ) * ζ := by
        calc
          ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ∑ _j ∈ Finset.univ.erase i, ζ :=
            Finset.sum_le_sum fun j _ ↦ hentry i j
          _ = (Finset.card (Finset.univ.erase i) : ℝ) * ζ := by
            simp only [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Fintype.card n : ℝ) * ζ := by
            gcongr
            exact_mod_cast (Finset.card_erase_le :
              (Finset.univ.erase i).card ≤ (Finset.univ : Finset n).card)
      have hdiagAbs : |(A i i).re| ≤ ζ :=
        (Complex.abs_re_le_norm (A i i)).trans (hentry i i)
      linarith [neg_abs_le (A i i).re])
  simpa only [neg_mul] using h

/-- Positivity after a scalar shift is also a certificate for a lower bound on the
least eigenvalue. -/
theorem neg_le_minEigenvalue_of_add_smul_one_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ}
    (hshift : (A + (ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    -ε ≤ minEigenvalue hA := by
  obtain ⟨i, hi⟩ := minEigenvalue_achieved hA
  let ψ : n → ℂ := ⇑(hA.eigenvectorBasis i)
  have hnonneg := hshift.re_dotProduct_nonneg ψ
  have hnorm : star ψ ⬝ᵥ ψ = 1 := by
    simpa only [ψ] using hA.star_eigenvectorBasis_dotProduct_self i
  have heig : A *ᵥ ψ = (hA.eigenvalues i : ℂ) • ψ := by
    simpa only [ψ, RCLike.real_smul_eq_coe_smul] using! hA.mulVec_eigenvectorBasis i
  rw [Matrix.add_mulVec, heig, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul, hnorm] at hnonneg
  simp only [smul_eq_mul, mul_one] at hnonneg
  rw [hi] at hnonneg
  change 0 ≤ minEigenvalue hA + ε at hnonneg
  linarith

/-- A Gram factorization of the shifted matrix certifies its spectral lower bound.  Unlike
diagonal dominance, this certificate is complete over the complex numbers: every positive
semidefinite shifted matrix has a square-root factorization. -/
theorem neg_le_minEigenvalue_of_add_smul_one_eq_mul_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ} (R : Matrix n n ℂ)
    (hfactor : A + (ε : ℂ) • (1 : Matrix n n ℂ) = R * Rᴴ) :
    -ε ≤ minEigenvalue hA := by
  apply neg_le_minEigenvalue_of_add_smul_one_posSemidef hA
  rw [hfactor]
  simpa only [Matrix.mul_one] using
    (Matrix.PosSemidef.one.mul_mul_conjTranspose_same R)

/-- The trace norm of a Hermitian matrix is the sum of the traces of its positive and
negative spectral parts. -/
theorem Matrix.IsHermitian.rectangularTraceNorm_eq_re_trace_posPart_add_negPart
    {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    rectangularTraceNorm H = ((H⁺).trace).re + ((H⁻).trace).re := by
  rw [rectangularTraceNorm_eq_re_trace_abs,
    ← CFC.posPart_add_negPart H (isSelfAdjoint_iff.mpr hH), trace_add,
    Complex.add_re]

/-- A Hermitian trace-norm bound is exactly a semidefinite feasibility condition with
positive and negative matrix variables.  This is the matrix form of the boundary
constraint in LVV13, equation `eq:conv`, `algo53.tex`, lines 472--476. -/
theorem hermitian_rectangularTraceNorm_le_iff_exists_posSemidef_sub
    {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (η : ℝ) :
    rectangularTraceNorm H ≤ η ↔
      ∃ P N : Matrix n n ℂ,
        P.PosSemidef ∧ N.PosSemidef ∧ H = P - N ∧ P.trace.re + N.trace.re ≤ η := by
  constructor
  · intro hnorm
    refine ⟨H⁺, H⁻, Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H),
      Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H), ?_, ?_⟩
    · exact (CFC.posPart_sub_negPart H (isSelfAdjoint_iff.mpr hH)).symm
    · rwa [← Matrix.IsHermitian.rectangularTraceNorm_eq_re_trace_posPart_add_negPart hH]
  · rintro ⟨P, N, hP, hN, rfl, htrace⟩
    calc
      rectangularTraceNorm (P - N) ≤
          rectangularTraceNorm P + rectangularTraceNorm (-N) := by
        simpa only [sub_eq_add_neg] using rectangularTraceNorm_add_le P (-N)
      _ = P.trace.re + N.trace.re := by
        rw [show -N = (-1 : ℂ) • N by module, rectangularTraceNorm_smul,
          rectangularTraceNorm_eq_re_trace_abs,
          CFC.abs_of_nonneg _ hP.nonneg,
          rectangularTraceNorm_eq_re_trace_abs,
          CFC.abs_of_nonneg _ hN.nonneg]
        norm_num
      _ ≤ η := htrace

/-- The compressed boundary marginal of a Hermitian matrix is Hermitian. -/
theorem compressedBoundaryLM_isHermitian {a s b : Type*} [Fintype a] [Finite s]
    [Finite b] {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.IsHermitian) :
    (compressedBoundaryLM Z σ).IsHermitian := by
  classical
  rw [compressedBoundaryLM_apply]
  unfold Matrix.partialTraceFirst
  exact Matrix.partialTraceLeft_isHermitian
    ((Matrix.isHermitian_mul_mul_conjTranspose Z hσ).submatrix _)

/-- Entrywise approximation of the coordinate map controls the compressed boundary
marginal entrywise.  This is the perturbative substitute for requiring the coordinate
isometry in the LVV boundary test to have exactly rational entries.  The boundary map
is the support-compressed form of LVV13, `algo53.tex`, lines 472--476. -/
theorem norm_compressedBoundaryLM_sub_apply_le_of_entry_norm_le
    {a s b : Type*} [Fintype a] [Finite s] [Finite b] {n : ℕ}
    (Z Q : Matrix ((a × s) × b) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    {M C θ : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hZ : ∀ i j, ‖Z i j‖ ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ C)
    (hclose : ∀ i j, ‖(Z - Q) i j‖ ≤ θ) (i j : s × b) :
    ‖(compressedBoundaryLM Z A - compressedBoundaryLM Q A) i j‖ ≤
      Fintype.card a * (n * (n * θ * C) * M + n * (n * (M + θ) * C) * θ) := by
  have hQ : ∀ i j, ‖Q i j‖ ≤ M + θ := by
    intro i j
    calc
      ‖Q i j‖ = ‖Z i j - (Z - Q) i j‖ := by congr 2; simp
      _ ≤ ‖Z i j‖ + ‖(Z - Q) i j‖ := norm_sub_le _ _
      _ ≤ M + θ := add_le_add (hZ i j) (hclose i j)
  have hstarZ : ∀ i j, ‖Zᴴ i j‖ ≤ M := by
    intro i j
    rw [Matrix.conjTranspose_apply, norm_star]
    exact hZ j i
  have hstarDiff : ∀ i j, ‖(Z - Q)ᴴ i j‖ ≤ θ := by
    intro i j
    rw [Matrix.conjTranspose_apply, norm_star]
    exact hclose j i
  have hprod : ∀ i j,
      ‖(Z * A * Zᴴ - Q * A * Qᴴ) i j‖ ≤
        n * (n * θ * C) * M + n * (n * (M + θ) * C) * θ := by
    intro i j
    have hid : Z * A * Zᴴ - Q * A * Qᴴ =
        (Z - Q) * A * Zᴴ + Q * A * (Z - Q)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [hid, Matrix.add_apply]
    calc
      ‖(((Z - Q) * A * Zᴴ) i j + (Q * A * (Z - Q)ᴴ) i j)‖ ≤
          ‖((Z - Q) * A * Zᴴ) i j‖ + ‖(Q * A * (Z - Q)ᴴ) i j‖ := norm_add_le _ _
      _ ≤ n * (n * θ * C) * M + n * (n * (M + θ) * C) * θ := by
        apply add_le_add
        · have hleft : ∀ k l, ‖((Z - Q) * A) k l‖ ≤ n * θ * C := by
            intro k l
            simpa only [Fintype.card_fin] using
              norm_rectangular_mul_apply_le_card_mul_of_entry_norm_le
                (Z - Q) A hclose hA hθ k l
          simpa only [Fintype.card_fin] using
            norm_rectangular_mul_apply_le_card_mul_of_entry_norm_le
              ((Z - Q) * A) Zᴴ hleft hstarZ
                (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hθ) hC) i j
        · have hleft : ∀ k l, ‖(Q * A) k l‖ ≤ n * (M + θ) * C := by
            intro k l
            simpa only [Fintype.card_fin] using
              norm_rectangular_mul_apply_le_card_mul_of_entry_norm_le
                Q A hQ hA (add_nonneg hM hθ) k l
          simpa only [Fintype.card_fin] using
            norm_rectangular_mul_apply_le_card_mul_of_entry_norm_le
              (Q * A) (Z - Q)ᴴ hleft hstarDiff
                (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (add_nonneg hM hθ)) hC) i j
  rw [compressedBoundaryLM_apply, compressedBoundaryLM_apply]
  unfold Matrix.partialTraceFirst
  rw [Matrix.sub_apply, Matrix.partialTraceLeft_apply, Matrix.partialTraceLeft_apply,
    ← Finset.sum_sub_distrib]
  calc
    ‖∑ k, (Matrix.reindex (Equiv.prodAssoc a s b) (Equiv.prodAssoc a s b)
        (Z * A * Zᴴ - Q * A * Qᴴ)) (k, i) (k, j)‖ ≤
        ∑ _k : a, (n * (n * θ * C) * M + n * (n * (M + θ) * C) * θ) := by
      apply norm_sum_le_of_le
      intro k _hk
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply] using
        hprod ((Equiv.prodAssoc a s b).symm (k, i))
          ((Equiv.prodAssoc a s b).symm (k, j))
    _ = Fintype.card a *
        (n * (n * θ * C) * M + n * (n * (M + θ) * C) * θ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Symmetric form of the coordinate-map perturbation estimate for the boundary map
of LVV13, `algo53.tex`, lines 472--476. -/
theorem norm_compressedBoundaryLM_sub_apply_le_of_entry_norm_le'
    {a s b : Type*} [Fintype a] [Finite s] [Finite b] {n : ℕ}
    (Z Q : Matrix ((a × s) × b) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    {M C θ : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hZ : ∀ i j, ‖Z i j‖ ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ C)
    (hclose : ∀ i j, ‖(Z - Q) i j‖ ≤ θ) (i j : s × b) :
    ‖(compressedBoundaryLM Z A - compressedBoundaryLM Q A) i j‖ ≤
      Fintype.card a * (n : ℝ) ^ 2 * θ * C * (2 * M + θ) := by
  convert norm_compressedBoundaryLM_sub_apply_le_of_entry_norm_le
    Z Q A hM hC hθ hZ hA hclose i j using 1
  ring

/-- Replacing the coordinate map by an entrywise approximation only enlarges the
entrywise boundary-residual tolerance by the explicit perturbation bound.  This applies
to the support-compressed boundary constraint of LVV13, `algo53.tex`, lines 472--476. -/
theorem compressedBoundaryResidual_entry_norm_le_of_coordinate_approximation
    {a s b : Type*} [Fintype a] [Finite s] [Finite b] {n : ℕ}
    (Z Q : Matrix ((a × s) × b) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (X P N : Matrix (s × b) (s × b) ℂ) {M C θ ζ : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hZ : ∀ i j, ‖Z i j‖ ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ C)
    (hclose : ∀ i j, ‖(Z - Q) i j‖ ≤ θ)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ)
    (i j : s × b) :
    ‖((compressedBoundaryLM Q A - X) - (P - N)) i j‖ ≤
      ζ + Fintype.card a * (n : ℝ) ^ 2 * θ * C * (2 * M + θ) := by
  have hperturb := norm_compressedBoundaryLM_sub_apply_le_of_entry_norm_le'
    Z Q A hM hC hθ hZ hA hclose i j
  calc
    ‖((compressedBoundaryLM Q A - X) - (P - N)) i j‖ =
        ‖((compressedBoundaryLM Z A - X) - (P - N)) i j -
          (compressedBoundaryLM Z A - compressedBoundaryLM Q A) i j‖ := by
      congr 2
      simp only [Matrix.sub_apply]
      ring
    _ ≤ ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ +
        ‖(compressedBoundaryLM Z A - compressedBoundaryLM Q A) i j‖ := norm_sub_le _ _
    _ ≤ ζ + Fintype.card a * (n : ℝ) ^ 2 * θ * C * (2 * M + θ) :=
      add_le_add (hresidual i j) hperturb

/-- The entrywise coordinate-map estimate gives a trace-norm estimate on the
compressed boundary marginal. -/
theorem rectangularTraceNorm_compressedBoundaryLM_sub_le_of_entry_norm_le
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z Q : Matrix ((a × s) × b) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    {M C θ : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hZ : ∀ i j, ‖Z i j‖ ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ C)
    (hclose : ∀ i j, ‖(Z - Q) i j‖ ≤ θ) :
    rectangularTraceNorm (compressedBoundaryLM Z A - compressedBoundaryLM Q A) ≤
      (Fintype.card (s × b) : ℝ) ^ 2 *
        (Fintype.card a * (n : ℝ) ^ 2 * θ * C * (2 * M + θ)) := by
  exact rectangularTraceNorm_le_card_sq_mul_of_entry_norm_le _
    (norm_compressedBoundaryLM_sub_apply_le_of_entry_norm_le'
      Z Q A hM hC hθ hZ hA hclose)

/-- Replacing the coordinate map enlarges a trace-norm boundary residual by at most
the trace-norm perturbation of the compressed boundary marginal. -/
theorem compressedBoundaryResidual_rectangularTraceNorm_le_of_coordinate_approximation
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z Q : Matrix ((a × s) × b) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (X P N : Matrix (s × b) (s × b) ℂ) {M C θ ζ : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hZ : ∀ i j, ‖Z i j‖ ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ C)
    (hclose : ∀ i j, ‖(Z - Q) i j‖ ≤ θ)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ ζ) :
    rectangularTraceNorm ((compressedBoundaryLM Q A - X) - (P - N)) ≤
      ζ + (Fintype.card (s × b) : ℝ) ^ 2 *
        (Fintype.card a * (n : ℝ) ^ 2 * θ * C * (2 * M + θ)) := by
  have hperturb := rectangularTraceNorm_compressedBoundaryLM_sub_le_of_entry_norm_le
    Z Q A hM hC hθ hZ hA hclose
  have hid : (compressedBoundaryLM Q A - X) - (P - N) =
      ((compressedBoundaryLM Z A - X) - (P - N)) -
        (compressedBoundaryLM Z A - compressedBoundaryLM Q A) := by
    module
  rw [hid, sub_eq_add_neg]
  calc
    rectangularTraceNorm
        (((compressedBoundaryLM Z A - X) - (P - N)) +
          -(compressedBoundaryLM Z A - compressedBoundaryLM Q A)) ≤
        rectangularTraceNorm ((compressedBoundaryLM Z A - X) - (P - N)) +
          rectangularTraceNorm (-(compressedBoundaryLM Z A - compressedBoundaryLM Q A)) :=
      rectangularTraceNorm_add_le _ _
    _ = rectangularTraceNorm ((compressedBoundaryLM Z A - X) - (P - N)) +
        rectangularTraceNorm (compressedBoundaryLM Z A - compressedBoundaryLM Q A) := by
      rw [show -(compressedBoundaryLM Z A - compressedBoundaryLM Q A) =
        (-1 : ℂ) • (compressedBoundaryLM Z A - compressedBoundaryLM Q A) by module,
        rectangularTraceNorm_smul]
      norm_num
    _ ≤ ζ + (Fintype.card (s × b) : ℝ) ^ 2 *
        (Fintype.card a * (n : ℝ) ^ 2 * θ * C * (2 * M + θ)) :=
      add_le_add hresidual hperturb

/-- The reverse residual transfer has the same cost: a certificate tested with the
approximating coordinate map is sound for the exact isometry after adding the same
trace-norm perturbation. -/
theorem compressedBoundaryResidual_rectangularTraceNorm_le_of_coordinate_approximation_rev
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z Q : Matrix ((a × s) × b) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (X P N : Matrix (s × b) (s × b) ℂ) {M C θ ζ : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hZ : ∀ i j, ‖Z i j‖ ≤ M) (hA : ∀ i j, ‖A i j‖ ≤ C)
    (hclose : ∀ i j, ‖(Z - Q) i j‖ ≤ θ)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Q A - X) - (P - N)) ≤ ζ) :
    rectangularTraceNorm ((compressedBoundaryLM Z A - X) - (P - N)) ≤
      ζ + (Fintype.card (s × b) : ℝ) ^ 2 *
        (Fintype.card a * (n : ℝ) ^ 2 * θ * C * (2 * M + θ)) := by
  have hperturb := rectangularTraceNorm_compressedBoundaryLM_sub_le_of_entry_norm_le
    Z Q A hM hC hθ hZ hA hclose
  have hid : (compressedBoundaryLM Z A - X) - (P - N) =
      ((compressedBoundaryLM Q A - X) - (P - N)) +
        (compressedBoundaryLM Z A - compressedBoundaryLM Q A) := by
    module
  rw [hid]
  exact (rectangularTraceNorm_add_le _ _).trans (add_le_add hresidual hperturb)

/-- A certificate tested with an approximate boundary center is sound for the exact
center after adding the trace norm of the center perturbation. -/
theorem compressedBoundaryResidual_rectangularTraceNorm_le_of_boundary_center_approximation
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (X Q P N : Matrix (s × b) (s × b) ℂ) {θ ζ : ℝ}
    (hclose : ∀ i j, ‖(X - Q) i j‖ ≤ θ)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - Q) - (P - N)) ≤ ζ) :
    rectangularTraceNorm ((compressedBoundaryLM Z A - X) - (P - N)) ≤
      ζ + (Fintype.card (s × b) : ℝ) ^ 2 * θ := by
  have hcenter : rectangularTraceNorm (X - Q) ≤
      (Fintype.card (s × b) : ℝ) ^ 2 * θ :=
    rectangularTraceNorm_le_card_sq_mul_of_entry_norm_le (X - Q) hclose
  have hid : (compressedBoundaryLM Z A - X) - (P - N) =
      ((compressedBoundaryLM Z A - Q) - (P - N)) - (X - Q) := by
    module
  rw [hid, sub_eq_add_neg]
  calc
    rectangularTraceNorm
        (((compressedBoundaryLM Z A - Q) - (P - N)) + -(X - Q)) ≤
      rectangularTraceNorm ((compressedBoundaryLM Z A - Q) - (P - N)) +
        rectangularTraceNorm (-(X - Q)) := rectangularTraceNorm_add_le _ _
    _ = rectangularTraceNorm ((compressedBoundaryLM Z A - Q) - (P - N)) +
        rectangularTraceNorm (X - Q) := by
      rw [show -(X - Q) = (-1 : ℂ) • (X - Q) by module, rectangularTraceNorm_smul]
      norm_num
    _ ≤ ζ + (Fintype.card (s × b) : ℝ) ^ 2 * θ :=
      add_le_add hresidual hcenter

/-- With a Hermitian boundary-net center, the compressed LVV boundary constraint is
equivalent to an explicit semidefinite feasibility condition.  This is the constraint in
LVV13, equation `eq:conv`, `algo53.tex`, lines 472--476, after support compression. -/
theorem compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : σ.IsHermitian) (X : Matrix (s × b) (s × b) ℂ) (hX : X.IsHermitian)
    (η : ℝ) :
    rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η ↔
      ∃ P N : Matrix (s × b) (s × b) ℂ,
        P.PosSemidef ∧ N.PosSemidef ∧ compressedBoundaryLM Z σ - X = P - N ∧
          P.trace.re + N.trace.re ≤ η :=
  hermitian_rectangularTraceNorm_le_iff_exists_posSemidef_sub
    ((compressedBoundaryLM_isHermitian Z hσ).sub hX) η

/-- The explicit semidefinite system for the compressed LVV boundary problem at an
energy threshold `E`.  Its variables are the compressed density `σ` and the positive
and negative parts `P`, `N` of its boundary residual. -/
def IsCompressedBoundarySDPFeasibleAtEnergy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (η E : ℝ) (σ : Matrix (Fin n) (Fin n) ℂ)
    (P N : Matrix (s × b) (s × b) ℂ) : Prop :=
  σ.PosSemidef ∧ σ.trace = 1 ∧
    P.PosSemidef ∧ N.PosSemidef ∧
    compressedBoundaryLM Z σ - X = P - N ∧
    P.trace.re + N.trace.re ≤ η ∧
    (σ * K).trace.re ≤ E

/-- Every feasible compressed boundary certificate lies in an explicit trace-norm ball.
The density variable has trace norm one, while each auxiliary positive-semidefinite
variable has trace norm at most the boundary budget.  Feasibility itself forces this
budget to be nonnegative. -/
theorem IsCompressedBoundarySDPFeasibleAtEnergy.rectangularTraceNorm_bounds
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E : ℝ} {σ : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E σ P N) :
    0 ≤ η ∧ rectangularTraceNorm σ = 1 ∧
      rectangularTraceNorm P ≤ η ∧ rectangularTraceNorm N ≤ η := by
  rcases h with ⟨hσ, hσtrace, hP, hN, _hresidual, hbudget, _henergy⟩
  have hPtrace : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp hP.trace_nonneg).1
  have hNtrace : 0 ≤ N.trace.re := (Complex.nonneg_iff.mp hN.trace_nonneg).1
  rw [rectangularTraceNorm_eq_re_trace_of_posSemidef hσ,
    rectangularTraceNorm_eq_re_trace_of_posSemidef hP,
    rectangularTraceNorm_eq_re_trace_of_posSemidef hN, hσtrace]
  norm_num
  constructor
  · linarith
  exact ⟨by linarith, by linarith⟩

/-- Entrywise form of the feasible-set bounds.  Thus the three matrix variables lie in
an explicit finite product of closed disks: radius one for the density and radius `η`
for each auxiliary matrix. -/
theorem IsCompressedBoundarySDPFeasibleAtEnergy.entry_norm_bounds
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    {n : ℕ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E : ℝ} {σ : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E σ P N) :
    (∀ i j, ‖σ i j‖ ≤ 1) ∧
      (∀ i j, ‖P i j‖ ≤ η) ∧ ∀ i j, ‖N i j‖ ≤ η := by
  classical
  obtain ⟨_hη, hσ, hP, hN⟩ := h.rectangularTraceNorm_bounds
  exact ⟨fun i j ↦ (norm_apply_le_rectangularTraceNorm σ i j).trans_eq hσ,
    fun i j ↦ (norm_apply_le_rectangularTraceNorm P i j).trans hP,
    fun i j ↦ (norm_apply_le_rectangularTraceNorm N i j).trans hN⟩

end TNLean.MPS.AreaLaw
