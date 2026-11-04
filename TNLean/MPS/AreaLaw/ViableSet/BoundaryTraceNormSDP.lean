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

/-!
# Semidefinite representation of a Hermitian boundary trace-norm constraint

For a Hermitian matrix `H`, the constraint `rectangularTraceNorm H ≤ η` is equivalent
to the existence of positive-semidefinite matrices `P` and `N` such that
`H = P - N` and `P.trace.re + N.trace.re ≤ η`.  Thus, once the boundary-net center
is chosen Hermitian, the trace-norm constraint in the size-trimming program is a finite
system of linear equalities, one linear inequality, and positive-semidefinite constraints.

This is the semidefinite representation used implicitly in Landau, Vazirani and Vidick,
arXiv:1307.5143v1, equation `eq:conv`, `algo53.tex`, lines 472--476.
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

/-- The uniform real grid of order `M` on `[-1,1]`. -/
noncomputable def unitRealGrid (M : ℕ) : Finset ℝ := by
  classical
  exact (Finset.range (2 * M + 1)).image fun k : ℕ ↦ -1 + (k : ℝ) / M

/-- The uniform real grid of order `M` scaled to `[-R,R]`. -/
noncomputable def scaledRealGrid (M : ℕ) (R : ℝ) : Finset ℝ := by
  classical
  exact (unitRealGrid M).image fun x ↦ R * x

/-- The rational grid of denominator `M` on the interval `[-B,B]`.  Unlike the
real-scaled grids below, its elements carry an exact rational representation. -/
def rationalRealGrid (B M : ℕ) : Finset ℚ := by
  exact (Finset.range (2 * B * M + 1)).image fun k : ℕ ↦
    -(B : ℚ) + (k : ℚ) / M

/-- Membership in the rational grid is witnessed by a bounded natural-number
coordinate.  This is the discrete representation used in the eventual encoding bound. -/
theorem mem_rationalRealGrid_iff {B M : ℕ} {q : ℚ} :
    q ∈ rationalRealGrid B M ↔
      ∃ k < 2 * B * M + 1, q = -(B : ℚ) + (k : ℚ) / M := by
  simp [rationalRealGrid, eq_comm]

/-- The arithmetic height of a rational number: the larger of the absolute reduced
numerator and the reduced positive denominator. -/
def rationalHeight (q : ℚ) : ℕ :=
  max q.num.natAbs q.den

/-- One plus the base-two logarithm of rational height, a uniform bit-length bound
for the reduced numerator and denominator. -/
def rationalBitLength (q : ℚ) : ℕ :=
  Nat.log2 (rationalHeight q) + 1

theorem num_natAbs_le_rationalHeight (q : ℚ) : q.num.natAbs ≤ rationalHeight q :=
  le_max_left _ _

theorem den_le_rationalHeight (q : ℚ) : q.den ≤ rationalHeight q :=
  le_max_right _ _

theorem rationalBitLength_le {q : ℚ} {H : ℕ} (hq : rationalHeight q ≤ H) :
    rationalBitLength q ≤ Nat.log2 H + 1 := by
  apply Nat.add_le_add_right
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right hq

/-- The rational height is Mathlib's multiplicative Weil height specialized to
`ℚ`, expressed as a natural number. -/
theorem rationalHeight_cast (q : ℚ) :
    (rationalHeight q : ℝ) = Height.mulHeight₁ q := by
  rw [Rat.mulHeight₁_eq_max]
  rfl

/-- Negation does not change rational height. -/
theorem rationalHeight_neg (q : ℚ) : rationalHeight (-q) = rationalHeight q := by
  simp [rationalHeight]

/-- Multiplication increases rational height by at most the product of the two
input heights. -/
theorem rationalHeight_mul_le (x y : ℚ) :
    rationalHeight (x * y) ≤ rationalHeight x * rationalHeight y := by
  have h := Height.mulHeight₁_mul_le x y
  rw [← rationalHeight_cast, ← rationalHeight_cast, ← rationalHeight_cast] at h
  exact_mod_cast h

/-- Addition increases rational height by at most twice the product of the two
input heights. -/
theorem rationalHeight_add_le (x y : ℚ) :
    rationalHeight (x + y) ≤ 2 * rationalHeight x * rationalHeight y := by
  have h := Height.mulHeight₁_add_le x y
  rw [NumberField.totalWeight_eq_finrank] at h
  norm_num only [Module.finrank_self, pow_one, Nat.cast_ofNat] at h
  rw [← rationalHeight_cast, ← rationalHeight_cast, ← rationalHeight_cast] at h
  exact_mod_cast h

/-- Subtraction obeys the same rational-height bound as addition. -/
theorem rationalHeight_sub_le (x y : ℚ) :
    rationalHeight (x - y) ≤ 2 * rationalHeight x * rationalHeight y := by
  simpa [sub_eq_add_neg, rationalHeight_neg] using rationalHeight_add_le x (-y)

/-- Casting a natural number to the rationals has height at most one more than
that natural number; the extra one uniformly covers zero. -/
theorem rationalHeight_natCast_le (n : ℕ) :
    rationalHeight (n : ℚ) ≤ n + 1 := by
  simp [rationalHeight]

/-- Inversion preserves rational height. -/
theorem rationalHeight_inv (q : ℚ) : rationalHeight q⁻¹ = rationalHeight q := by
  have h := Height.mulHeight₁_inv q
  rw [← rationalHeight_cast, ← rationalHeight_cast] at h
  exact_mod_cast h

/-- Division increases rational height by at most the product of the two input
heights. -/
theorem rationalHeight_div_le (x y : ℚ) :
    rationalHeight (x / y) ≤ rationalHeight x * rationalHeight y := by
  simpa [div_eq_mul_inv, rationalHeight_inv] using rationalHeight_mul_le x y⁻¹

/-- The height of a nonempty finite rational sum is bounded by the number of
summands times the product of their heights. -/
theorem rationalHeight_finset_sum_le {α : Type*} {s : Finset α} (hs : s.Nonempty)
    (x : α → ℚ) :
    rationalHeight (∑ a ∈ s, x a) ≤ s.card * ∏ a ∈ s, rationalHeight (x a) := by
  have h := Height.mulHeight₁_sum_le hs x
  rw [NumberField.totalWeight_eq_finrank] at h
  norm_num only [Module.finrank_self, pow_one] at h
  rw [← rationalHeight_cast] at h
  simp_rw [← rationalHeight_cast] at h
  exact_mod_cast h

/-- A coordinate in the explicit presentation of the rational grid has polynomially
bounded reduced numerator and denominator. -/
theorem rationalGridCoordinate_height_le (B M k : ℕ) (hk : k < 2 * B * M + 1) :
    rationalHeight (-(B : ℚ) + (k : ℚ) / M) ≤
      2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
  calc
    rationalHeight (-(B : ℚ) + (k : ℚ) / M) ≤
        2 * rationalHeight (-(B : ℚ)) * rationalHeight ((k : ℚ) / M) :=
      rationalHeight_add_le _ _
    _ ≤ 2 * (B + 1) * ((k + 1) * (M + 1)) := by
      gcongr
      · simpa [rationalHeight_neg] using rationalHeight_natCast_le B
      · exact (rationalHeight_div_le _ _).trans <|
          Nat.mul_le_mul (rationalHeight_natCast_le k) (rationalHeight_natCast_le M)
    _ ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
      gcongr
      omega

/-- Every member of `rationalRealGrid B M` has polynomially bounded reduced
numerator and denominator. -/
theorem rationalHeight_le_of_mem_rationalRealGrid {B M : ℕ} {q : ℚ}
    (hq : q ∈ rationalRealGrid B M) :
    rationalHeight q ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
  obtain ⟨k, hk, rfl⟩ := mem_rationalRealGrid_iff.mp hq
  exact rationalGridCoordinate_height_le B M k hk

/-- Every rational-grid coordinate has logarithmic binary encoding length in the
explicit polynomial height bound. -/
theorem rationalBitLength_le_of_mem_rationalRealGrid {B M : ℕ} {q : ℚ}
    (hq : q ∈ rationalRealGrid B M) :
    rationalBitLength q ≤
      Nat.log2 (2 * (B + 1) * ((2 * B * M + 1) * (M + 1))) + 1 :=
  rationalBitLength_le (rationalHeight_le_of_mem_rationalRealGrid hq)

/-- The reduced numerator and denominator of every rational-grid coordinate obey the
same explicit polynomial bound. -/
theorem numerator_denominator_le_of_mem_rationalRealGrid {B M : ℕ} {q : ℚ}
    (hq : q ∈ rationalRealGrid B M) :
    q.num.natAbs ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) ∧
      q.den ≤ 2 * (B + 1) * ((2 * B * M + 1) * (M + 1)) := by
  have hheight := rationalHeight_le_of_mem_rationalRealGrid hq
  exact ⟨(num_natAbs_le_rationalHeight q).trans hheight,
    (den_le_rationalHeight q).trans hheight⟩

/-- A canonical positive integer denominator for choosing a rational precision below
a prescribed positive real target. -/
noncomputable def rationalPositiveToleranceOrder (t : ℝ) : ℕ :=
  ⌈1 / t⌉₊ + 1

/-- A canonical positive rational precision below `t`: the reciprocal of one more than
the ceiling of `1/t`. -/
noncomputable def rationalPositiveTolerance (t : ℝ) : ℝ :=
  ((1 / (rationalPositiveToleranceOrder t : ℚ) : ℚ) : ℝ)

theorem rationalPositiveToleranceOrder_pos (t : ℝ) :
    0 < rationalPositiveToleranceOrder t := by
  unfold rationalPositiveToleranceOrder
  omega

theorem rationalPositiveTolerance_pos (t : ℝ) : 0 < rationalPositiveTolerance t := by
  have hM : (0 : ℚ) < rationalPositiveToleranceOrder t := by
    exact_mod_cast rationalPositiveToleranceOrder_pos t
  unfold rationalPositiveTolerance
  exact_mod_cast div_pos (by norm_num : (0 : ℚ) < 1) hM

theorem rationalPositiveTolerance_le {t : ℝ} (ht : 0 < t) :
    rationalPositiveTolerance t ≤ t := by
  let M := rationalPositiveToleranceOrder t
  have hM : (0 : ℝ) < M := by exact_mod_cast rationalPositiveToleranceOrder_pos t
  have hceil : 1 / t ≤ (⌈1 / t⌉₊ : ℝ) := Nat.le_ceil _
  have hMt : 1 / t ≤ (M : ℝ) := by
    dsimp only [M, rationalPositiveToleranceOrder]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hrecip : 1 / (M : ℝ) ≤ t := by
    rw [div_le_iff₀ hM]
    have := (div_le_iff₀ ht).mp hMt
    nlinarith
  simpa only [rationalPositiveTolerance, M, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast] using hrecip

/-- A canonical nonnegative rational upper bound for an arbitrary real number. -/
noncomputable def rationalNonnegativeUpperBound (x : ℝ) : ℚ :=
  (⌈max x 0⌉₊ : ℚ)

theorem le_rationalNonnegativeUpperBound (x : ℝ) :
    x ≤ (rationalNonnegativeUpperBound x : ℝ) := by
  calc
    x ≤ max x 0 := le_max_left _ _
    _ ≤ (⌈max x 0⌉₊ : ℕ) := Nat.le_ceil _
    _ = (rationalNonnegativeUpperBound x : ℝ) := by
      simp [rationalNonnegativeUpperBound]

theorem rationalNonnegativeUpperBound_height_le (x : ℝ) :
    rationalHeight (rationalNonnegativeUpperBound x) ≤ ⌈max x 0⌉₊ + 1 := by
  simpa only [rationalNonnegativeUpperBound] using
    rationalHeight_natCast_le ⌈max x 0⌉₊

/-- Rational upper rounding of `x` on the mesh determined by a positive target `t`.
Unlike the integer ceiling, its overshoot is at most `t`. -/
noncomputable def rationalNonnegativeUpperApproximation (x t : ℝ) : ℚ :=
  let M := rationalPositiveToleranceOrder t
  (⌈max x 0 * M⌉₊ : ℚ) / M

theorem le_rationalNonnegativeUpperApproximation (x t : ℝ) :
    x ≤ (rationalNonnegativeUpperApproximation x t : ℝ) := by
  let M := rationalPositiveToleranceOrder t
  have hM : (0 : ℝ) < M := by exact_mod_cast rationalPositiveToleranceOrder_pos t
  have hceil : max x 0 * M ≤ (⌈max x 0 * M⌉₊ : ℕ) := Nat.le_ceil _
  calc
    x ≤ max x 0 := le_max_left _ _
    _ ≤ (⌈max x 0 * M⌉₊ : ℝ) / M := by
      rw [le_div_iff₀ hM]
      exact_mod_cast hceil
    _ = (rationalNonnegativeUpperApproximation x t : ℝ) := by
      simp [rationalNonnegativeUpperApproximation, M]

theorem rationalNonnegativeUpperApproximation_le
    {x t : ℝ} (ht : 0 < t) :
    (rationalNonnegativeUpperApproximation x t : ℝ) ≤ max x 0 + t := by
  let M := rationalPositiveToleranceOrder t
  have hM : (0 : ℝ) < M := by exact_mod_cast rationalPositiveToleranceOrder_pos t
  have hceil : (⌈max x 0 * (M : ℝ)⌉₊ : ℝ) < max x 0 * M + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (le_max_right x 0) hM.le)
  have hround : (1 : ℝ) / M ≤ t := by
    simpa only [M, rationalPositiveTolerance, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast] using rationalPositiveTolerance_le ht
  have hstrict : (⌈max x 0 * M⌉₊ : ℝ) / M < max x 0 + 1 / M := by
    calc
      (⌈max x 0 * M⌉₊ : ℝ) / M < (max x 0 * M + 1) / M :=
        div_lt_div_of_pos_right hceil hM
      _ = max x 0 + 1 / M := by field_simp
  calc
    (rationalNonnegativeUpperApproximation x t : ℝ) =
        (⌈max x 0 * M⌉₊ : ℝ) / M := by
      simp [rationalNonnegativeUpperApproximation, M]
    _ ≤ max x 0 + 1 / M := hstrict.le
    _ ≤ max x 0 + t := by
      simpa only [add_comm] using add_le_add_right hround (max x 0)

theorem rationalNonnegativeUpperApproximation_height_le (x t : ℝ) :
    rationalHeight (rationalNonnegativeUpperApproximation x t) ≤
      (⌈max x 0 * rationalPositiveToleranceOrder t⌉₊ + 1) *
        (rationalPositiveToleranceOrder t + 1) := by
  unfold rationalNonnegativeUpperApproximation
  apply (rationalHeight_div_le _ _).trans
  exact Nat.mul_le_mul (rationalHeight_natCast_le _)
    (rationalHeight_natCast_le _)

/-- A complex number whose real and imaginary parts are rational. -/
def HasRationalComplexCoordinates (z : ℂ) : Prop :=
  ∃ x y : ℚ, z = ⟨(x : ℝ), (y : ℝ)⟩

/-- A complex number with rational coordinates whose reduced numerators and
denominators are uniformly bounded by `H`. -/
def HasRationalComplexCoordinatesOfHeight (H : ℕ) (z : ℂ) : Prop :=
  ∃ x y : ℚ, z = ⟨(x : ℝ), (y : ℝ)⟩ ∧ rationalHeight x ≤ H ∧ rationalHeight y ≤ H

theorem rationalPositiveTolerance_hasRationalCoordinatesOfHeight (t : ℝ) :
    HasRationalComplexCoordinatesOfHeight (rationalPositiveToleranceOrder t + 1)
      (rationalPositiveTolerance t : ℂ) := by
  let M := rationalPositiveToleranceOrder t
  let q : ℚ := 1 / M
  refine ⟨q, 0, ?_, ?_, ?_⟩
  · apply Complex.ext
    · simp [q, M, rationalPositiveTolerance]
    · simp
  · exact (rationalHeight_div_le 1 M).trans <| by
      have h1 : rationalHeight (1 : ℚ) = 1 := by norm_num [rationalHeight]
      rw [h1, one_mul]
      exact rationalHeight_natCast_le M
  · simp [rationalHeight]

namespace HasRationalComplexCoordinatesOfHeight

theorem forget {H : ℕ} {z : ℂ} (hz : HasRationalComplexCoordinatesOfHeight H z) :
    HasRationalComplexCoordinates z := by
  obtain ⟨x, y, hxy, _hx, _hy⟩ := hz
  exact ⟨x, y, hxy⟩

theorem mono {H K : ℕ} {z : ℂ} (hHK : H ≤ K)
    (hz : HasRationalComplexCoordinatesOfHeight H z) :
    HasRationalComplexCoordinatesOfHeight K z := by
  obtain ⟨x, y, hxy, hx, hy⟩ := hz
  exact ⟨x, y, hxy, hx.trans hHK, hy.trans hHK⟩

theorem exists_bitLength_le {H : ℕ} {z : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z) :
    ∃ x y : ℚ, z = ⟨(x : ℝ), (y : ℝ)⟩ ∧
      rationalBitLength x ≤ Nat.log2 H + 1 ∧
      rationalBitLength y ≤ Nat.log2 H + 1 := by
  obtain ⟨x, y, hxy, hx, hy⟩ := hz
  exact ⟨x, y, hxy, rationalBitLength_le hx, rationalBitLength_le hy⟩

theorem zero : HasRationalComplexCoordinatesOfHeight 1 0 := by
  exact ⟨0, 0, by apply Complex.ext <;> simp, by simp [rationalHeight], by simp [rationalHeight]⟩

theorem one : HasRationalComplexCoordinatesOfHeight 1 1 := by
  exact ⟨1, 0, by apply Complex.ext <;> simp, by simp [rationalHeight], by simp [rationalHeight]⟩

theorem half : HasRationalComplexCoordinatesOfHeight 2 ((2 : ℂ)⁻¹) := by
  refine ⟨1 / 2, 0, ?_, ?_, ?_⟩
  · apply Complex.ext <;> norm_num
  · norm_num [rationalHeight]
  · norm_num [rationalHeight]

theorem neg {H : ℕ} {z : ℂ} (hz : HasRationalComplexCoordinatesOfHeight H z) :
    HasRationalComplexCoordinatesOfHeight H (-z) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  exact ⟨-x, -y, by apply Complex.ext <;> simp, by simpa [rationalHeight_neg],
    by simpa [rationalHeight_neg]⟩

theorem star {H : ℕ} {z : ℂ} (hz : HasRationalComplexCoordinatesOfHeight H z) :
    HasRationalComplexCoordinatesOfHeight H (star z) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  exact ⟨x, -y, by apply Complex.ext <;> simp, hx, by simpa [rationalHeight_neg]⟩

theorem add {H K : ℕ} {z w : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z)
    (hw : HasRationalComplexCoordinatesOfHeight K w) :
    HasRationalComplexCoordinatesOfHeight (2 * H * K) (z + w) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  obtain ⟨u, v, rfl, hu, hv⟩ := hw
  exact ⟨x + u, y + v, by apply Complex.ext <;> simp,
    (rationalHeight_add_le x u).trans (by gcongr),
    (rationalHeight_add_le y v).trans (by gcongr)⟩

theorem sub {H K : ℕ} {z w : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z)
    (hw : HasRationalComplexCoordinatesOfHeight K w) :
    HasRationalComplexCoordinatesOfHeight (2 * H * K) (z - w) := by
  simpa [sub_eq_add_neg] using add hz hw.neg

theorem mul {H K : ℕ} {z w : ℂ}
    (hz : HasRationalComplexCoordinatesOfHeight H z)
    (hw : HasRationalComplexCoordinatesOfHeight K w) :
    HasRationalComplexCoordinatesOfHeight (2 * (H * K) * (H * K)) (z * w) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := hz
  obtain ⟨u, v, rfl, hu, hv⟩ := hw
  have hxu : rationalHeight (x * u) ≤ H * K :=
    (rationalHeight_mul_le x u).trans (by gcongr)
  have hyv : rationalHeight (y * v) ≤ H * K :=
    (rationalHeight_mul_le y v).trans (by gcongr)
  have hxv : rationalHeight (x * v) ≤ H * K :=
    (rationalHeight_mul_le x v).trans (by gcongr)
  have hyu : rationalHeight (y * u) ≤ H * K :=
    (rationalHeight_mul_le y u).trans (by gcongr)
  exact ⟨x * u - y * v, x * v + y * u, by apply Complex.ext <;> simp,
    (rationalHeight_sub_le _ _).trans (by gcongr),
    (rationalHeight_add_le _ _).trans (by gcongr)⟩

/-- A sum of `n` complex numbers of coordinate height at most `H` has coordinate
height at most `(2H)^n`.  The bound is deliberately multiplicative, since its
binary encoding length is linear in `n`. -/
theorem finset_sum {ι : Type*} {s : Finset ι} {H : ℕ} {f : ι → ℂ}
    (hf : ∀ i ∈ s, HasRationalComplexCoordinatesOfHeight H (f i)) :
    HasRationalComplexCoordinatesOfHeight ((2 * H) ^ s.card) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        add (hf a (Finset.mem_insert_self a s))
          (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- Coordinate-height bound for a product of `n` complex numbers, each of height at
most `H`.  The recurrence records exactly the elementary multiplication bound above. -/
def productHeight (H : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * (H * productHeight H n) * (H * productHeight H n)

/-- Products of positive-height coordinates retain a positive height bound. -/
theorem productHeight_pos {H : ℕ} (hH : 0 < H) :
    ∀ n, 0 < productHeight H n := by
  intro n
  induction n with
  | zero => simp [productHeight]
  | succ n ih =>
      simp only [productHeight]
      positivity

/-- A product of `n` complex numbers of coordinate height at most `H` has coordinate
height at most `productHeight H n`. -/
theorem finset_prod {ι : Type*} {s : Finset ι} {H : ℕ} {f : ι → ℂ}
    (hf : ∀ i ∈ s, HasRationalComplexCoordinatesOfHeight H (f i)) :
    HasRationalComplexCoordinatesOfHeight (productHeight H s.card) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [productHeight] using one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

end HasRationalComplexCoordinatesOfHeight

namespace HasRationalComplexCoordinates

/-- The real part of a complex number with rational coordinates is the coercion of a
rational number. -/
theorem exists_realPart {z : ℂ} (hz : HasRationalComplexCoordinates z) :
    ∃ x : ℚ, z.re = (x : ℝ) := by
  obtain ⟨x, y, rfl⟩ := hz
  exact ⟨x, rfl⟩

theorem zero : HasRationalComplexCoordinates 0 := ⟨0, 0, by apply Complex.ext <;> simp⟩

theorem one : HasRationalComplexCoordinates 1 := ⟨1, 0, by apply Complex.ext <;> simp⟩

theorem add {z w : ℂ} (hz : HasRationalComplexCoordinates z)
    (hw : HasRationalComplexCoordinates w) : HasRationalComplexCoordinates (z + w) := by
  obtain ⟨x, y, rfl⟩ := hz
  obtain ⟨u, v, rfl⟩ := hw
  exact ⟨x + u, y + v, by apply Complex.ext <;> simp⟩

theorem neg {z : ℂ} (hz : HasRationalComplexCoordinates z) :
    HasRationalComplexCoordinates (-z) := by
  obtain ⟨x, y, rfl⟩ := hz
  exact ⟨-x, -y, by apply Complex.ext <;> simp⟩

theorem sub {z w : ℂ} (hz : HasRationalComplexCoordinates z)
    (hw : HasRationalComplexCoordinates w) : HasRationalComplexCoordinates (z - w) :=
  hz.add hw.neg

theorem mul {z w : ℂ} (hz : HasRationalComplexCoordinates z)
    (hw : HasRationalComplexCoordinates w) : HasRationalComplexCoordinates (z * w) := by
  obtain ⟨x, y, rfl⟩ := hz
  obtain ⟨u, v, rfl⟩ := hw
  refine ⟨x * u - y * v, x * v + y * u, ?_⟩
  apply Complex.ext <;> simp

theorem star {z : ℂ} (hz : HasRationalComplexCoordinates z) :
    HasRationalComplexCoordinates (star z) := by
  obtain ⟨x, y, rfl⟩ := hz
  exact ⟨x, -y, by apply Complex.ext <;> simp⟩

theorem finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ}
    (hf : ∀ i ∈ s, HasRationalComplexCoordinates (f i)) :
    HasRationalComplexCoordinates (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem finset_prod {ι : Type*} {s : Finset ι} {f : ι → ℂ}
    (hf : ∀ i ∈ s, HasRationalComplexCoordinates (f i)) :
    HasRationalComplexCoordinates (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem fintype_sum {ι : Type*} [Fintype ι] {f : ι → ℂ}
    (hf : ∀ i, HasRationalComplexCoordinates (f i)) :
    HasRationalComplexCoordinates (∑ i, f i) :=
  finset_sum fun i _ ↦ hf i

theorem fintype_prod {ι : Type*} [Fintype ι] {f : ι → ℂ}
    (hf : ∀ i, HasRationalComplexCoordinates (f i)) :
    HasRationalComplexCoordinates (∏ i, f i) :=
  finset_prod fun i _ ↦ hf i

end HasRationalComplexCoordinates

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

/-- Every entry of a matrix has rational real and imaginary parts. -/
def Matrix.HasRationalEntries {m n : Type*} (A : Matrix m n ℂ) : Prop :=
  ∀ i j, HasRationalComplexCoordinates (A i j)

/-- Every matrix entry has rational coordinates of height at most `H`. -/
def Matrix.HasRationalEntriesOfHeight {m n : Type*} (H : ℕ)
    (A : Matrix m n ℂ) : Prop :=
  ∀ i j, HasRationalComplexCoordinatesOfHeight H (A i j)

/-- Height bound obtained after taking the Hermitian part of a matrix whose entries
have coordinate height at most `H`. -/
def hermitianPartHeight (H : ℕ) : ℕ :=
  2 * (2 * (2 * H * H)) * (2 * (2 * H * H))

namespace Matrix.HasRationalEntriesOfHeight

theorem forget {m n : Type*} {H : ℕ} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) : Matrix.HasRationalEntries A :=
  fun i j ↦ (hA i j).forget

theorem entry_exists_bitLength_le {m n : Type*} {H : ℕ} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) (i : m) (j : n) :
    ∃ x y : ℚ, A i j = ⟨(x : ℝ), (y : ℝ)⟩ ∧
      rationalBitLength x ≤ Nat.log2 H + 1 ∧
      rationalBitLength y ≤ Nat.log2 H + 1 :=
  (hA i j).exists_bitLength_le

theorem mono {m n : Type*} {H K : ℕ} {A : Matrix m n ℂ} (hHK : H ≤ K)
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight K A :=
  fun i j ↦ (hA i j).mono hHK

theorem one {n : Type*} [DecidableEq n] :
    Matrix.HasRationalEntriesOfHeight 1 (1 : Matrix n n ℂ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using HasRationalComplexCoordinatesOfHeight.one
  · simp only [Matrix.one_apply_ne hij]
    exact HasRationalComplexCoordinatesOfHeight.zero

theorem smul {m n : Type*} {H K : ℕ} {c : ℂ} {A : Matrix m n ℂ}
    (hc : HasRationalComplexCoordinatesOfHeight H c)
    (hA : Matrix.HasRationalEntriesOfHeight K A) :
    Matrix.HasRationalEntriesOfHeight (2 * (H * K) * (H * K)) (c • A) :=
  fun i j ↦ hc.mul (hA i j)

theorem conjTranspose {m n : Type*} {H : ℕ} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight H Aᴴ :=
  fun i j ↦ (hA j i).star

theorem add {m n : Type*} {H K : ℕ} {A B : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A)
    (hB : Matrix.HasRationalEntriesOfHeight K B) :
    Matrix.HasRationalEntriesOfHeight (2 * H * K) (A + B) :=
  fun i j ↦ (hA i j).add (hB i j)

theorem hermitianPart {n : Type*} [Fintype n] {H : ℕ} {A : Matrix n n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight (hermitianPartHeight H)
      (matrixHermitianPart A) := by
  rw [matrixHermitianPart]
  have hhalf : HasRationalComplexCoordinatesOfHeight 2 (1 / 2 : ℂ) := by
    simpa [one_div] using HasRationalComplexCoordinatesOfHeight.half
  exact smul hhalf (add hA hA.conjTranspose)

theorem sub {m n : Type*} {H K : ℕ} {A B : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A)
    (hB : Matrix.HasRationalEntriesOfHeight K B) :
    Matrix.HasRationalEntriesOfHeight (2 * H * K) (A - B) :=
  fun i j ↦ (hA i j).sub (hB i j)

/-- Matrix multiplication has an explicit coordinate-height bound.  Its binary
length is linear in the contracted dimension. -/
theorem mul {m n p : Type*} [Fintype n] {H K : ℕ}
    {A : Matrix m n ℂ} {B : Matrix n p ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A)
    (hB : Matrix.HasRationalEntriesOfHeight K B) :
    Matrix.HasRationalEntriesOfHeight
      ((2 * (2 * (H * K) * (H * K))) ^ Fintype.card n) (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact HasRationalComplexCoordinatesOfHeight.finset_sum fun k _hk ↦
    (hA i k).mul (hB k j)

/-- The trace has an explicit coordinate-height bound linear in the matrix order
after taking binary logarithms. -/
theorem trace {n : Type*} [Fintype n] {H : ℕ} {A : Matrix n n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    HasRationalComplexCoordinatesOfHeight ((2 * H) ^ Fintype.card n) A.trace := by
  rw [Matrix.trace]
  exact HasRationalComplexCoordinatesOfHeight.finset_sum fun i _hi ↦ hA i i

/-- The Gram matrix of a height-bounded rational matrix has an explicit
coordinate-height bound. -/
theorem gram {n : Type*} [Fintype n] {H : ℕ} {Q : Matrix n n ℂ}
    (hQ : Matrix.HasRationalEntriesOfHeight H Q) :
    Matrix.HasRationalEntriesOfHeight
      ((2 * (2 * (H * H) * (H * H))) ^ Fintype.card n) (Q * Qᴴ) :=
  mul hQ hQ.conjTranspose

/-- The shifted Gram residual occurring in each approximate semidefinite
certificate has an explicit coordinate-height bound. -/
theorem shiftedGramResidual {n : Type*} [Fintype n] [DecidableEq n]
    {HA Hε HQ : ℕ} {A Q : Matrix n n ℂ} {ε : ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight HA A)
    (hε : HasRationalComplexCoordinatesOfHeight Hε ε)
    (hQ : Matrix.HasRationalEntriesOfHeight HQ Q) :
    let Hshift := 2 * (Hε * 1) * (Hε * 1)
    let Hleft := 2 * HA * Hshift
    let Hgram := (2 * (2 * (HQ * HQ) * (HQ * HQ))) ^ Fintype.card n
    Matrix.HasRationalEntriesOfHeight (2 * Hleft * Hgram)
      ((A + ε • (1 : Matrix n n ℂ)) - Q * Qᴴ) := by
  dsimp only
  exact sub (add hA (smul hε one)) (gram hQ)

theorem reindex {m n m' n' : Type*} (em : m ≃ m') (en : n ≃ n')
    {H : ℕ} {A : Matrix m n ℂ} (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight H (Matrix.reindex em en A) := by
  intro i j
  exact hA (em.symm i) (en.symm j)

theorem partialTraceLeft {α β : Type*} [Fintype α] {H : ℕ}
    {A : Matrix (α × β) (α × β) ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A) :
    Matrix.HasRationalEntriesOfHeight ((2 * H) ^ Fintype.card α)
      (Matrix.partialTraceLeft A) := by
  intro i j
  rw [Matrix.partialTraceLeft_apply]
  exact HasRationalComplexCoordinatesOfHeight.finset_sum fun k _hk ↦ hA (k, i) (k, j)

/-- The trace of a matrix product has an explicit coordinate-height bound. -/
theorem trace_mul {n : Type*} [Fintype n] {H K : ℕ}
    {A B : Matrix n n ℂ}
    (hA : Matrix.HasRationalEntriesOfHeight H A)
    (hB : Matrix.HasRationalEntriesOfHeight K B) :
    let Hmul := (2 * (2 * (H * K) * (H * K))) ^ Fintype.card n
    HasRationalComplexCoordinatesOfHeight ((2 * Hmul) ^ Fintype.card n)
      (A * B).trace := by
  dsimp only
  exact trace (mul hA hB)

end Matrix.HasRationalEntriesOfHeight

namespace Matrix.HasRationalEntries

theorem one {n : Type*} [DecidableEq n] :
    Matrix.HasRationalEntries (1 : Matrix n n ℂ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using HasRationalComplexCoordinates.one
  · simp only [Matrix.one_apply_ne hij]
    exact HasRationalComplexCoordinates.zero

theorem smul {m n : Type*} {c : ℂ} {A : Matrix m n ℂ}
    (hc : HasRationalComplexCoordinates c) (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (c • A) := fun i j ↦ hc.mul (hA i j)

theorem add {m n : Type*} {A B : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntries A) (hB : Matrix.HasRationalEntries B) :
    Matrix.HasRationalEntries (A + B) := fun i j ↦ (hA i j).add (hB i j)

theorem neg {m n : Type*} {A : Matrix m n ℂ} (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (-A) := fun i j ↦ (hA i j).neg

theorem sub {m n : Type*} {A B : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntries A) (hB : Matrix.HasRationalEntries B) :
    Matrix.HasRationalEntries (A - B) := fun i j ↦ (hA i j).sub (hB i j)

theorem conjTranspose {m n : Type*} {A : Matrix m n ℂ}
    (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries Aᴴ := fun i j ↦ (hA j i).star

theorem mul {m n p : Type*} [Fintype n] {A : Matrix m n ℂ} {B : Matrix n p ℂ}
    (hA : Matrix.HasRationalEntries A) (hB : Matrix.HasRationalEntries B) :
    Matrix.HasRationalEntries (A * B) := by
  intro i k
  rw [Matrix.mul_apply]
  exact HasRationalComplexCoordinates.finset_sum fun j _ ↦ (hA i j).mul (hB j k)

theorem trace {n : Type*} [Fintype n] {A : Matrix n n ℂ}
    (hA : Matrix.HasRationalEntries A) :
    HasRationalComplexCoordinates A.trace := by
  rw [Matrix.trace]
  exact HasRationalComplexCoordinates.finset_sum fun i _ ↦ hA i i

theorem reindex {m n m' n' : Type*} (em : m ≃ m') (en : n ≃ n')
    {A : Matrix m n ℂ} (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (Matrix.reindex em en A) := by
  intro i j
  exact hA (em.symm i) (en.symm j)

theorem partialTraceLeft {α β : Type*} [Fintype α]
    {A : Matrix (α × β) (α × β) ℂ} (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (Matrix.partialTraceLeft A) := by
  intro i j
  rw [Matrix.partialTraceLeft_apply]
  exact HasRationalComplexCoordinates.finset_sum fun k _ ↦ hA (k, i) (k, j)

end Matrix.HasRationalEntries

/-- Rational coordinates are preserved by the compressed boundary marginal whenever
the coordinate isometry itself has rational entries. -/
theorem compressedBoundaryLM_hasRationalEntries
    {a s b : Type*} [Fintype a]
    {n : ℕ} {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Matrix.HasRationalEntries Z) (hA : Matrix.HasRationalEntries A) :
    Matrix.HasRationalEntries (compressedBoundaryLM Z A) := by
  rw [compressedBoundaryLM_apply]
  unfold Matrix.partialTraceFirst
  exact ((hZ.mul hA).mul hZ.conjTranspose).reindex
    (Equiv.prodAssoc a s b) (Equiv.prodAssoc a s b) |>.partialTraceLeft

/-- The compressed boundary marginal has an explicit coordinate-height bound in
terms of the input heights and the two contracted dimensions. -/
theorem compressedBoundaryLM_hasRationalEntriesOfHeight
    {a s b : Type*} [Fintype a]
    {n : ℕ} {HZ HA : ℕ} {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Matrix.HasRationalEntriesOfHeight HZ Z)
    (hA : Matrix.HasRationalEntriesOfHeight HA A) :
    let HZA := (2 * (2 * (HZ * HA) * (HZ * HA))) ^ n
    let HZAZ := (2 * (2 * (HZA * HZ) * (HZA * HZ))) ^ n
    Matrix.HasRationalEntriesOfHeight ((2 * HZAZ) ^ Fintype.card a)
      (compressedBoundaryLM Z A) := by
  dsimp only
  rw [compressedBoundaryLM_apply]
  unfold Matrix.partialTraceFirst
  have hprod := Matrix.HasRationalEntriesOfHeight.mul
    (Matrix.HasRationalEntriesOfHeight.mul hZ hA) hZ.conjTranspose
  simp only [Fintype.card_fin] at hprod
  exact Matrix.HasRationalEntriesOfHeight.partialTraceLeft
    (Matrix.HasRationalEntriesOfHeight.reindex
      (Equiv.prodAssoc a s b) (Equiv.prodAssoc a s b)
      hprod)

/-- The complete boundary equality residual in the approximate SDP certificate has
an explicit coordinate-height bound. -/
theorem compressedBoundaryResidual_hasRationalEntriesOfHeight
    {a s b : Type*} [Fintype a]
    {n : ℕ} {HZ HA HX HP HN : ℕ}
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {X P N : Matrix (s × b) (s × b) ℂ}
    (hZ : Matrix.HasRationalEntriesOfHeight HZ Z)
    (hA : Matrix.HasRationalEntriesOfHeight HA A)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hP : Matrix.HasRationalEntriesOfHeight HP P)
    (hN : Matrix.HasRationalEntriesOfHeight HN N) :
    let HZA := (2 * (2 * (HZ * HA) * (HZ * HA))) ^ n
    let HZAZ := (2 * (2 * (HZA * HZ) * (HZA * HZ))) ^ n
    let Hboundary := (2 * HZAZ) ^ Fintype.card a
    let Hleft := 2 * Hboundary * HX
    let Hright := 2 * HP * HN
    Matrix.HasRationalEntriesOfHeight (2 * Hleft * Hright)
      ((compressedBoundaryLM Z A - X) - (P - N)) := by
  dsimp only
  exact Matrix.HasRationalEntriesOfHeight.sub
    (Matrix.HasRationalEntriesOfHeight.sub
      (compressedBoundaryLM_hasRationalEntriesOfHeight hZ hA) hX)
    (Matrix.HasRationalEntriesOfHeight.sub hP hN)

/-- Coordinate-height bound for a dense matrix product across dimension `d`. -/
def matrixProductHeight (d H K : ℕ) : ℕ :=
  (2 * (2 * (H * K) * (H * K))) ^ d

/-- Coordinate-height bound for the trace of a height-`H` square matrix of order `d`. -/
def matrixTraceHeight (d H : ℕ) : ℕ :=
  (2 * H) ^ d

/-- Coordinate-height bound for a trace of a product of two order-`d` matrices. -/
def matrixTraceProductHeight (d H K : ℕ) : ℕ :=
  matrixTraceHeight d (matrixProductHeight d H K)

/-- Coordinate-height bound for a shifted Gram residual. -/
def shiftedGramResidualHeight (d HA Hε HQ : ℕ) : ℕ :=
  let Hshift := 2 * (Hε * 1) * (Hε * 1)
  let Hleft := 2 * HA * Hshift
  let Hgram := matrixProductHeight d HQ HQ
  2 * Hleft * Hgram

/-- Coordinate-height bound for the compressed boundary marginal. -/
def compressedBoundaryHeight (a n HZ HA : ℕ) : ℕ :=
  let HZA := matrixProductHeight n HZ HA
  let HZAZ := matrixProductHeight n HZA HZ
  matrixTraceHeight a HZAZ

/-- Coordinate-height bound for the full compressed-boundary equality residual. -/
def compressedBoundaryResidualHeight (a n HZ HA HX HP HN : ℕ) : ℕ :=
  let Hboundary := compressedBoundaryHeight a n HZ HA
  let Hleft := 2 * Hboundary * HX
  let Hright := 2 * HP * HN
  2 * Hleft * Hright

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

/-- A canonical factor-grid spacing for a prescribed entrywise Gram error `ζ`.
The denominator includes `ζ` itself so that the spacing is at most one without
requiring an upper bound on the requested error. -/
noncomputable def gramCertificateMesh
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : ℝ :=
  ζ / ((Fintype.card ι : ℝ) * (2 * √C + 1) + ζ)

/-- A strictly positive relaxation of any real entry-square bound. -/
noncomputable def gramCertificateBound (x : ℝ) : ℝ := 1 + |x|

/-- An explicit entry bound for the approximate density variable, obtained from its
bounded shifted Gram factor. -/
noncomputable def approxSDPDensityEntryBound (n : ℕ) (κ ε : ℝ) : ℝ :=
  n * gramCertificateBound (1 + κ + n * ε) + ε

/-- An explicit entry bound for either approximate auxiliary variable. -/
noncomputable def approxSDPAuxEntryBound (r : ℕ) (η εb : ℝ) : ℝ :=
  r * gramCertificateBound (η + 2 * r * εb) + εb

/-- The cardinality bound for the canonical finite Gram-certificate grid. -/
noncomputable def gramCertificateNetCard
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : ℕ :=
  (2 * ⌈(Fintype.card ι : ℝ) ^ 2 /
    (gramCertificateMesh ι C ζ / ((Fintype.card ι : ℝ) ^ 2 * √C))⌉₊ + 1) ^
      (2 * Fintype.card ι ^ 2)

/-- The integer coordinate-grid order needed to attain the canonical Gram mesh. -/
noncomputable def gramCertificateGridOrder
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : ℕ :=
  ⌈√C / gramCertificateMesh ι C ζ⌉₊

/-- The concrete coordinate grid used for bounded Gram certificates. -/
noncomputable def gramCertificateGrid
    (ι : Type*) [Fintype ι] (C ζ : ℝ) : Finset (Matrix ι ι ℂ) :=
  complexMatrixGrid ι (gramCertificateGridOrder ι C ζ) √C

/-- The relaxed Gram-factor bound is strictly positive. -/
theorem gramCertificateBound_pos (x : ℝ) : 0 < gramCertificateBound x := by
  rw [gramCertificateBound]
  positivity

/-- Every real number is at most its relaxed Gram-factor bound. -/
theorem le_gramCertificateBound (x : ℝ) : x ≤ gramCertificateBound x := by
  rw [gramCertificateBound]
  linarith [le_abs_self x]

/-- The density-variable entry bound is positive in positive dimension for a
nonnegative spectral tolerance. -/
theorem approxSDPDensityEntryBound_pos {n : ℕ} (hn : 0 < n) {κ ε : ℝ}
    (hε : 0 ≤ ε) : 0 < approxSDPDensityEntryBound n κ ε := by
  rw [approxSDPDensityEntryBound]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := mul_pos hn' (gramCertificateBound_pos (1 + κ + n * ε))
  linarith

/-- The auxiliary-variable entry bound is positive in positive dimension for a
nonnegative spectral tolerance. -/
theorem approxSDPAuxEntryBound_pos {r : ℕ} (hr : 0 < r) {η εb : ℝ}
    (hεb : 0 ≤ εb) : 0 < approxSDPAuxEntryBound r η εb := by
  rw [approxSDPAuxEntryBound]
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hp := mul_pos hr' (gramCertificateBound_pos (η + 2 * r * εb))
  linarith

/-- The canonical Gram-certificate mesh is positive. -/
theorem gramCertificateMesh_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ} (hζ : 0 < ζ) :
    0 < gramCertificateMesh ι C ζ := by
  apply div_pos hζ
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  positivity

/-- The canonical factor mesh makes the induced Gram error no larger than the
prescribed tolerance. -/
theorem gramCertificateMesh_error_le
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ} (hζ : 0 < ζ) :
    Fintype.card ι * gramCertificateMesh ι C ζ *
        (2 * √C + gramCertificateMesh ι C ζ) ≤ ζ := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hbase : 0 < (Fintype.card ι : ℝ) * (2 * √C + 1) := by positivity
  have hden : 0 < (Fintype.card ι : ℝ) * (2 * √C + 1) + ζ := add_pos hbase hζ
  have hmesh : 0 ≤ gramCertificateMesh ι C ζ :=
    (gramCertificateMesh_pos hζ).le
  have hmeshOne : gramCertificateMesh ι C ζ ≤ 1 := by
    rw [gramCertificateMesh, div_le_one hden]
    linarith [hbase]
  have hidentity : gramCertificateMesh ι C ζ *
      ((Fintype.card ι : ℝ) * (2 * √C + 1) + ζ) = ζ := by
    rw [gramCertificateMesh]
    exact div_mul_cancel₀ ζ hden.ne'
  calc
    Fintype.card ι * gramCertificateMesh ι C ζ *
        (2 * √C + gramCertificateMesh ι C ζ) ≤
        Fintype.card ι * gramCertificateMesh ι C ζ * (2 * √C + 1) := by
      gcongr
    _ = gramCertificateMesh ι C ζ *
        ((Fintype.card ι : ℝ) * (2 * √C + 1)) := by ring
    _ ≤ ζ := by nlinarith

/-- The canonical Gram coordinate-grid order is positive. -/
theorem gramCertificateGridOrder_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ}
    (hC : 0 < C) (hζ : 0 < ζ) :
    0 < gramCertificateGridOrder ι C ζ := by
  rw [gramCertificateGridOrder]
  exact Nat.ceil_pos.mpr (div_pos (Real.sqrt_pos.2 hC) (gramCertificateMesh_pos hζ))

/-- The concrete Gram grid has the expected coordinate-count cardinality. -/
theorem gramCertificateGrid_card_le
    {ι : Type*} [Fintype ι] (C ζ : ℝ) :
    (gramCertificateGrid ι C ζ).card ≤
      (2 * gramCertificateGridOrder ι C ζ + 1) ^
        (2 * Fintype.card ι ^ 2) := by
  exact complexMatrixGrid_card_le _ _

/-- Every factor with squared entries bounded by `C` has a representative in the
concrete Gram grid whose Gram matrix is entrywise `ζ`-close. -/
theorem exists_mem_gramCertificateGrid
    {ι : Type*} [Fintype ι] [Nonempty ι] {C ζ : ℝ}
    (hC : 0 < C) (hζ : 0 < ζ) (R : Matrix ι ι ℂ)
    (hR : ∀ i j, ‖R i j‖ ^ 2 ≤ C) :
    ∃ Q ∈ gramCertificateGrid ι C ζ,
      ∀ i j, ‖(R * Rᴴ - Q * Qᴴ) i j‖ ≤ ζ := by
  let M := gramCertificateGridOrder ι C ζ
  have hM : 0 < M := gramCertificateGridOrder_pos hC hζ
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hmesh : 0 < gramCertificateMesh ι C ζ := gramCertificateMesh_pos hζ
  have hentry : ∀ i j, ‖R i j‖ ≤ √C := by
    intro i j
    nlinarith [hR i j, Real.sq_sqrt hC.le, norm_nonneg (R i j), Real.sqrt_nonneg C]
  have hratio : √C / gramCertificateMesh ι C ζ ≤ M := by
    exact Nat.le_ceil _
  have hround : √C / M ≤ gramCertificateMesh ι C ζ := by
    rw [div_le_iff₀ hMreal]
    have := (div_le_iff₀ hmesh).mp hratio
    nlinarith
  obtain ⟨Q, hQ, hclose⟩ :=
    exists_mem_complexMatrixGrid hM (Real.sqrt_pos.2 hC) R hentry
  refine ⟨Q, hQ, fun i j ↦ ?_⟩
  exact (norm_gram_sub_apply_le_of_entry_norm_le R Q (Real.sqrt_nonneg C)
    hmesh.le hentry (fun i j ↦ (hclose i j).trans hround) i j).trans
      (gramCertificateMesh_error_le hζ)

/-- Bounded Gram factors admit an explicit finite certificate net at any prescribed
positive entrywise Gram tolerance.  The canonical mesh absorbs the quadratic rounding
error, so the statement has no additional grid parameter. -/
theorem exists_finset_bounded_gram_certificate_net_at_error
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C ζ : ℝ} (hC : 0 < C) (hζ : 0 < ζ) :
    ∃ N : Finset (Matrix ι ι ℂ),
      N.card ≤ gramCertificateNetCard ι C ζ ∧
      ∀ R : Matrix ι ι ℂ, (∀ i j, ‖R i j‖ ^ 2 ≤ C) →
        ∃ Q ∈ N, ∀ i j, ‖(R * Rᴴ - Q * Qᴴ) i j‖ ≤ ζ := by
  classical
  obtain ⟨N, hNcard, hNcover⟩ :=
    exists_finset_bounded_gram_certificate_net (ι := ι) (C := C)
      (δ := gramCertificateMesh ι C ζ) hC (gramCertificateMesh_pos hζ)
  refine ⟨N, ?_, ?_⟩
  · simpa only [gramCertificateNetCard] using hNcard
  intro R hR
  obtain ⟨Q, hQN, hclose⟩ := hNcover R hR
  exact ⟨Q, hQN, fun i j ↦ (hclose i j).trans (gramCertificateMesh_error_le hζ)⟩

/-- The density matrices have a finite trace-norm net whose centers are themselves exact
density matrices.  It is obtained by retaining the unit-ball grid cells which meet the
density matrices and choosing one density representative in each retained cell.  The
covering radius is doubled, while the ambient grid cardinality is unchanged. -/
theorem exists_finset_density_rectangularTraceNorm_net
    {ι : Type*} [Fintype ι] [DecidableEq ι] {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : Finset (Matrix ι ι ℂ),
      N.card ≤
        (2 * ⌈(Fintype.card ι : ℝ) ^ 2 / δ⌉₊ + 1) ^
          (2 * Fintype.card ι ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∀ σ : Matrix ι ι ℂ, σ.PosSemidef → σ.trace = 1 →
        ∃ ρ ∈ N, rectangularTraceNorm (σ - ρ) ≤ 2 * δ := by
  classical
  obtain ⟨G, hGcard, hGcover⟩ :=
    Matrix.exists_finset_rectangularTraceNorm_net (n := ι) (η := δ) hδ
  let Good : Matrix ι ι ℂ → Prop := fun X ↦
    ∃ ρ : Matrix ι ι ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ rectangularTraceNorm (ρ - X) ≤ δ
  let rep : Matrix ι ι ℂ → Matrix ι ι ℂ := fun X ↦
    if h : Good X then Classical.choose h else 0
  let N := (G.filter Good).image rep
  have hNcard : N.card ≤ G.card := by
    exact Finset.card_image_le.trans (Finset.card_filter_le _ _)
  refine ⟨N, hNcard.trans hGcard, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hρ
    have hgood : Good X := (Finset.mem_filter.mp hX).2
    dsimp only [rep]
    rw [dite_eq_left hgood]
    exact ⟨(Classical.choose_spec hgood).1, (Classical.choose_spec hgood).2.1⟩
  · intro σ hσ hσtrace
    have hσnorm : rectangularTraceNorm σ ≤ 1 := by
      rw [rectangularTraceNorm_eq_re_trace_of_posSemidef hσ, hσtrace]
      norm_num
    obtain ⟨X, hXG, hσX⟩ := hGcover σ hσnorm
    have hgood : Good X := ⟨σ, hσ, hσtrace, hσX⟩
    refine ⟨rep X, Finset.mem_image.mpr
      ⟨X, Finset.mem_filter.mpr ⟨hXG, hgood⟩, rfl⟩, ?_⟩
    have hrep := (Classical.choose_spec hgood).2.2
    have hrepdef : rep X = Classical.choose hgood := by
      dsimp only [rep]
      rw [dite_eq_left hgood]
    have hrev : rectangularTraceNorm (X - rep X) ≤ δ := by
      rw [hrepdef]
      have heq : X - Classical.choose hgood =
          (-1 : ℂ) • (Classical.choose hgood - X) := by module
      rw [heq, rectangularTraceNorm_smul]
      norm_num
      exact hrep
    calc
      rectangularTraceNorm (σ - rep X) =
          rectangularTraceNorm ((σ - X) + (X - rep X)) := by congr 1; abel
      _ ≤ rectangularTraceNorm (σ - X) + rectangularTraceNorm (X - rep X) :=
        rectangularTraceNorm_add_le _ _
      _ ≤ 2 * δ := by linarith

/-- The number of real scalar coordinates needed to specify the three Hermitian matrix
variables in the compressed boundary semidefinite program.  A Hermitian matrix of order
`d` has `d ^ 2` real coordinates; the variables have orders `n`, `r`, and `r`.

This is the finite-dimensional size count implicit in LVV13, equation `eq:conv`,
`algo53.tex`, lines 472--476.  It does not assert a running-time bound for a particular
semidefinite-program solver. -/
def compressedBoundarySDPRealCoordinateCount (n r : ℕ) : ℕ :=
  n ^ 2 + 2 * r ^ 2

/-- The sum of the orders of the three positive-semidefinite cones in the compressed
boundary program. -/
def compressedBoundarySDPTotalConeOrder (n r : ℕ) : ℕ :=
  n + 2 * r

/-- The scalar-coordinate count is monotone in the density and boundary orders. -/
theorem compressedBoundarySDPRealCoordinateCount_le
    {n r nMax rMax : ℕ} (hn : n ≤ nMax) (hr : r ≤ rMax) :
    compressedBoundarySDPRealCoordinateCount n r ≤
      compressedBoundarySDPRealCoordinateCount nMax rMax := by
  exact Nat.add_le_add (Nat.pow_le_pow_left hn 2)
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hr 2))

/-- The total positive-semidefinite cone order is monotone in the two matrix orders. -/
theorem compressedBoundarySDPTotalConeOrder_le
    {n r nMax rMax : ℕ} (hn : n ≤ nMax) (hr : r ≤ rMax) :
    compressedBoundarySDPTotalConeOrder n r ≤
      compressedBoundarySDPTotalConeOrder nMax rMax := by
  exact Nat.add_le_add hn (Nat.mul_le_mul_left 2 hr)

/-- For the LVV support compression at a chain cut, the semidefinite program has at most
`(|S| m)² + 2 (q m)²` real scalar coordinates and total cone order at most
`|S| m + 2 q m`.  Thus its matrix dimensions are polynomial in the retained support size,
the local dimension, and the actual bond dimension. -/
theorem chain_compressedBoundarySDP_size_le
    {L q k m n : ℕ} (S : Finset (LeftBlockVector L q k)) (hq : 1 ≤ q)
    (hn : n ≤ S.card * m) :
    let r := Fintype.card (CutSite L q k × Fin m)
    compressedBoundarySDPRealCoordinateCount n r ≤
        compressedBoundarySDPRealCoordinateCount (S.card * m) (q * m) ∧
      compressedBoundarySDPTotalConeOrder n r ≤
        compressedBoundarySDPTotalConeOrder (S.card * m) (q * m) := by
  classical
  intro r
  have hr : r ≤ q * m := by
    simpa only [r, Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_le_mul (card_cutSite_le (L := L) (k := k) hq) (Nat.le_refl m)
  exact ⟨compressedBoundarySDPRealCoordinateCount_le hn hr,
    compressedBoundarySDPTotalConeOrder_le hn hr⟩

/-- The compressed LVV density problem at energy threshold `E` is feasible if and only
if its explicit semidefinite system is feasible.  Thus all nonlinear-looking content of
the trace-norm boundary condition has been replaced by two auxiliary positive-semidefinite
variables.  This is LVV13, equation `eq:conv`, `algo53.tex`, lines 472--476, after support
compression. -/
theorem exists_compressed_boundary_density_iff_exists_sdp_feasible_at_energy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) (η E : ℝ) :
    (∃ σ : Matrix (Fin n) (Fin n) ℂ,
      σ.PosSemidef ∧ σ.trace = 1 ∧
      rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η ∧
      (σ * K).trace.re ≤ E) ↔
    ∃ σ : Matrix (Fin n) (Fin n) ℂ,
      ∃ P N : Matrix (s × b) (s × b) ℂ,
        IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E σ P N := by
  constructor
  · rintro ⟨σ, hσ, htrace, hboundary, henergy⟩
    obtain ⟨P, N, hP, hN, hsub, htraces⟩ :=
      (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
        Z hσ.isHermitian X hX η).mp hboundary
    exact ⟨σ, P, N, hσ, htrace, hP, hN, hsub, htraces, henergy⟩
  · rintro ⟨σ, P, N, hσ, htrace, hP, hN, hsub, htraces, henergy⟩
    refine ⟨σ, hσ, htrace, ?_, henergy⟩
    exact (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
      Z hσ.isHermitian X hX η).mpr ⟨P, N, hP, hN, hsub, htraces⟩

/-- A nonempty compressed LVV boundary problem attains its minimum energy, and the
minimizer admits an explicit semidefinite certificate.  This is the attained-minimum
part of LVV13, equation `eq:conv`, `algo53.tex`, lines 472--476, after support
compression. -/
theorem exists_compressed_boundary_sdp_minimizer_of_nonempty
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) (η : ℝ)
    (hne : ∃ τ : Matrix (Fin n) (Fin n) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
        rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η) :
    ∃ σ : Matrix (Fin n) (Fin n) ℂ,
      ∃ P N : Matrix (s × b) (s × b) ℂ,
        IsCompressedBoundarySDPFeasibleAtEnergy Z K X η
          (σ * K).trace.re σ P N ∧
        ∀ τ : Matrix (Fin n) (Fin n) ℂ,
          τ.PosSemidef → τ.trace = 1 →
          rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η →
          (σ * K).trace.re ≤ (τ * K).trace.re := by
  classical
  let F := {τ : Matrix (Fin n) (Fin n) ℂ |
    τ.PosSemidef ∧ τ.trace = 1 ∧
      rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η}
  have hboundary : IsClosed {τ : Matrix (Fin n) (Fin n) ℂ |
      rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η} :=
    (Matrix.isClosed_setOf_rectangularTraceNorm_le η).preimage
      ((compressedBoundaryLM Z).continuous_of_finiteDimensional.sub continuous_const)
  have hcompact : IsCompact F := by
    simpa only [F, Set.ofPred_and, Set.inter_assoc] using
      Matrix.isCompact_setOf_posSemidef_trace_eq_one.inter_right hboundary
  have henergy : Continuous fun τ : Matrix (Fin n) (Fin n) ℂ ↦ (τ * K).trace.re :=
    Complex.continuous_re.comp ((continuous_id.mul continuous_const).matrix_trace)
  obtain ⟨σ, hσ, hmin⟩ := hcompact.exists_isMinOn hne henergy.continuousOn
  obtain ⟨P, N, hP, hN, hsub, htraces⟩ :=
    (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
      Z hσ.1.isHermitian X hX η).mp hσ.2.2
  refine ⟨σ, P, N, ⟨hσ.1, hσ.2.1, hP, hN, hsub, htraces, le_rfl⟩, ?_⟩
  intro τ hτ hτtrace hτboundary
  exact hmin ⟨hτ, hτtrace, hτboundary⟩

/-- A finite exact-density net contains an approximate solution of every nonempty
compressed LVV boundary problem.  Its boundary tolerance is enlarged by `2 δ`, and its
energy is within `‖K‖ (2 δ)` of the global optimum.  This is a finite-search existence
statement; it does not claim that the density representatives are effectively enumerable. -/
theorem exists_finset_approx_compressed_boundary_minimizer
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) (η : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hne : ∃ τ : Matrix (Fin n) (Fin n) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
        rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η) :
    ∃ N : Finset (Matrix (Fin n) (Fin n) ℂ),
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ ρ ∈ N,
        rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤ η + 2 * δ ∧
        ∀ τ : Matrix (Fin n) (Fin n) ℂ,
          τ.PosSemidef → τ.trace = 1 →
          rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η →
          (ρ * K).trace.re ≤ (τ * K).trace.re + ‖K‖ * (2 * δ) := by
  classical
  obtain ⟨N, hNcard, hNdensity, hNcover⟩ :=
    exists_finset_density_rectangularTraceNorm_net (ι := Fin n) hδ
  obtain ⟨σ, _P, _Q, hσ, hmin⟩ :=
    exists_compressed_boundary_sdp_minimizer_of_nonempty Z K X hX η hne
  have hσboundary : rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η :=
    (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
      Z hσ.1.isHermitian X hX η).mpr
        ⟨_P, _Q, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1, hσ.2.2.2.2.2.1⟩
  obtain ⟨ρ, hρN, hσρ⟩ := hNcover σ hσ.1 hσ.2.1
  have hρσ : rectangularTraceNorm (ρ - σ) ≤ 2 * δ := by
    have heq : ρ - σ = (-1 : ℂ) • (σ - ρ) := by module
    rw [heq, rectangularTraceNorm_smul]
    norm_num
    exact hσρ
  have hmap : rectangularTraceNorm
      (compressedBoundaryLM Z ρ - compressedBoundaryLM Z σ) ≤ 2 * δ :=
    (compressedBoundaryLM_distance_le Z hZ σ ρ).trans hρσ
  have hρboundary : rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤
      η + 2 * δ := by
    calc
      rectangularTraceNorm (compressedBoundaryLM Z ρ - X) = rectangularTraceNorm
          ((compressedBoundaryLM Z ρ - compressedBoundaryLM Z σ) +
            (compressedBoundaryLM Z σ - X)) := by congr 1; abel
      _ ≤ rectangularTraceNorm
          (compressedBoundaryLM Z ρ - compressedBoundaryLM Z σ) +
            rectangularTraceNorm (compressedBoundaryLM Z σ - X) :=
        rectangularTraceNorm_add_le _ _
      _ ≤ η + 2 * δ := by linarith
  have henergy := (compressedDensity_trace_energy_perturbation σ ρ K (2 * δ) hρσ).2
  refine ⟨N, ?_, hNdensity, ρ, hρN, hρboundary, ?_⟩
  · simpa only [Fintype.card_fin] using hNcard
  · intro τ hτ hτtrace hτboundary
    have hopt := hmin τ hτ hτtrace hτboundary
    have henergyUpper := (abs_le.mp henergy).2
    linarith

/-- Threshold form of the finite-search approximation theorem.  A single feasible density
below energy `E` guarantees a member of the finite exact-density family with boundary
tolerance `η + 2 δ` and energy at most `E + ‖K‖ (2 δ)`. -/
theorem exists_finset_approx_compressed_boundary_solution_at_energy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) {η E : ℝ} {δ : ℝ} (hδ : 0 < δ)
    {τ₀ : Matrix (Fin n) (Fin n) ℂ} (hτ₀ : τ₀.PosSemidef)
    (hτ₀trace : τ₀.trace = 1)
    (hτ₀boundary : rectangularTraceNorm (compressedBoundaryLM Z τ₀ - X) ≤ η)
    (hτ₀energy : (τ₀ * K).trace.re ≤ E) :
    ∃ N : Finset (Matrix (Fin n) (Fin n) ℂ),
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ ρ ∈ N,
        rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤ η + 2 * δ ∧
        (ρ * K).trace.re ≤ E + ‖K‖ * (2 * δ) := by
  obtain ⟨N, hNcard, hNdensity, ρ, hρN, hρboundary, hρenergy⟩ :=
    exists_finset_approx_compressed_boundary_minimizer Z hZ K X hX η hδ
      ⟨τ₀, hτ₀, hτ₀trace, hτ₀boundary⟩
  have hthreshold : (τ₀ * K).trace.re + ‖K‖ * (2 * δ) ≤
      E + ‖K‖ * (2 * δ) := by
    simpa only [add_comm] using add_le_add_right hτ₀energy (‖K‖ * (2 * δ))
  exact ⟨N, hNcard, hNdensity, ρ, hρN, hρboundary,
    (hρenergy τ₀ hτ₀ hτ₀trace hτ₀boundary).trans hthreshold⟩

/-- The finite exact-density family may be searched by retaining its members satisfying
the enlarged boundary constraint and choosing one of least compressed energy.  The
retained family is nonempty, and its finite minimizer obeys the same approximation bound
as the candidate supplied by the covering argument. -/
theorem exists_finset_minimizing_approx_compressed_boundary_solution_at_energy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) {η E : ℝ} {δ : ℝ} (hδ : 0 < δ)
    {τ₀ : Matrix (Fin n) (Fin n) ℂ} (hτ₀ : τ₀.PosSemidef)
    (hτ₀trace : τ₀.trace = 1)
    (hτ₀boundary : rectangularTraceNorm (compressedBoundaryLM Z τ₀ - X) ≤ η)
    (hτ₀energy : (τ₀ * K).trace.re ≤ E) :
    ∃ N : Finset (Matrix (Fin n) (Fin n) ℂ),
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ ρ ∈ N,
        rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤ η + 2 * δ ∧
        (ρ * K).trace.re ≤ E + ‖K‖ * (2 * δ) ∧
        ∀ σ ∈ N,
          rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η + 2 * δ →
          (ρ * K).trace.re ≤ (σ * K).trace.re := by
  classical
  obtain ⟨N, hNcard, hNdensity, ρ, hρN, hρboundary, hρenergy⟩ :=
    exists_finset_approx_compressed_boundary_solution_at_energy
      Z hZ K X hX hδ hτ₀ hτ₀trace hτ₀boundary hτ₀energy
  let F := N.filter fun σ ↦
    rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η + 2 * δ
  have hρF : ρ ∈ F := Finset.mem_filter.mpr ⟨hρN, hρboundary⟩
  obtain ⟨σ, hσF, hσmin⟩ := Finset.exists_min_image F
    (fun ω ↦ (ω * K).trace.re) ⟨ρ, hρF⟩
  have hσenergy : (σ * K).trace.re ≤ E + ‖K‖ * (2 * δ) :=
    (hσmin ρ hρF).trans hρenergy
  refine ⟨N, hNcard, hNdensity, σ, (Finset.mem_filter.mp hσF).1,
    (Finset.mem_filter.mp hσF).2, hσenergy, ?_⟩
  intro ω hωN hωboundary
  exact hσmin ω (Finset.mem_filter.mpr ⟨hωN, hωboundary⟩)

/-- Any feasible compressed semidefinite certificate may be replaced by a globally
energy-minimizing certificate which remains below the same energy threshold. -/
theorem exists_compressed_boundary_sdp_minimizer_of_feasible
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) {η E : ℝ}
    {τ₀ : Matrix (Fin n) (Fin n) ℂ} {P₀ N₀ : Matrix (s × b) (s × b) ℂ}
    (h₀ : IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E τ₀ P₀ N₀) :
    ∃ σ : Matrix (Fin n) (Fin n) ℂ,
      ∃ P N : Matrix (s × b) (s × b) ℂ,
        IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E σ P N ∧
        ∀ τ : Matrix (Fin n) (Fin n) ℂ,
          τ.PosSemidef → τ.trace = 1 →
          rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η →
          (σ * K).trace.re ≤ (τ * K).trace.re := by
  obtain ⟨τ₁, hτ₁, hτ₁trace, hτ₁boundary, hτ₁energy⟩ :=
    (exists_compressed_boundary_density_iff_exists_sdp_feasible_at_energy
      Z K X hX η E).mpr ⟨τ₀, P₀, N₀, h₀⟩
  obtain ⟨σ, P, N, hσ, hmin⟩ :=
    exists_compressed_boundary_sdp_minimizer_of_nonempty Z K X hX η
      ⟨τ₁, hτ₁, hτ₁trace, hτ₁boundary⟩
  have hσE : (σ * K).trace.re ≤ E :=
    (hmin τ₁ hτ₁ hτ₁trace hτ₁boundary).trans hτ₁energy
  exact ⟨σ, P, N, ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1,
    hσ.2.2.2.2.1, hσ.2.2.2.2.2.1, hσE⟩, hmin⟩

/-- The trace norm of a difference of positive-semidefinite matrices is at most the sum
of their traces. -/
theorem rectangularTraceNorm_sub_le_re_trace_add_of_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n] {P N : Matrix n n ℂ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) :
    rectangularTraceNorm (P - N) ≤ P.trace.re + N.trace.re :=
  (hermitian_rectangularTraceNorm_le_iff_exists_posSemidef_sub
    (hP.isHermitian.sub hN.isHermitian) (P.trace.re + N.trace.re)).mpr
      ⟨P, N, hP, hN, rfl, le_rfl⟩

/-- If a matrix is within trace-norm distance `δ` of `P - N`, for positive
semidefinite `P`, `N` of total trace at most `η`, then its trace norm is at most
`η + δ`. -/
theorem rectangularTraceNorm_le_add_of_approx_posSemidef_sub
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) {P N : Matrix n n ℂ} {η δ : ℝ}
    (hP : P.PosSemidef) (hN : N.PosSemidef)
    (hresidual : rectangularTraceNorm (H - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η) :
    rectangularTraceNorm H ≤ η + δ := by
  have hsub := rectangularTraceNorm_sub_le_re_trace_add_of_posSemidef hP hN
  calc
    rectangularTraceNorm H = rectangularTraceNorm ((H - (P - N)) + (P - N)) := by
      congr 1
      abel
    _ ≤ rectangularTraceNorm (H - (P - N)) + rectangularTraceNorm (P - N) :=
      rectangularTraceNorm_add_le _ _
    _ ≤ η + δ := by linarith

/-- An approximate semidefinite certificate for the compressed LVV boundary problem.
Only the linear matrix equation identifying the boundary residual with `P - N` is allowed
an error `δ`; positivity, normalization, the trace budget, and the energy bound remain
exact. -/
def IsApproxCompressedBoundarySDPFeasibleAtEnergy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b]
    {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (η E δ : ℝ) (σ : Matrix (Fin n) (Fin n) ℂ)
    (P N : Matrix (s × b) (s × b) ℂ) : Prop :=
  σ.PosSemidef ∧ σ.trace = 1 ∧
    P.PosSemidef ∧ N.PosSemidef ∧
    rectangularTraceNorm ((compressedBoundaryLM Z σ - X) - (P - N)) ≤ δ ∧
    P.trace.re + N.trace.re ≤ η ∧
    (σ * K).trace.re ≤ E

/-- An error `δ` in the linear boundary-residual equation enlarges the original LVV
trace-norm tolerance by at most `δ`, without a dimension factor. -/
theorem compressed_boundary_density_of_approx_sdp_feasible_at_energy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {η E δ : ℝ} {σ : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsApproxCompressedBoundarySDPFeasibleAtEnergy Z K X η E δ σ P N) :
    σ.PosSemidef ∧ σ.trace = 1 ∧
      rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η + δ ∧
      (σ * K).trace.re ≤ E := by
  rcases h with ⟨hσ, htrace, hP, hN, hresidual, htraces, henergy⟩
  exact ⟨hσ, htrace,
    rectangularTraceNorm_le_add_of_approx_posSemidef_sub
      (compressedBoundaryLM Z σ - X) hP hN hresidual htraces,
    henergy⟩

/-- A Hermitian matrix whose least eigenvalue is at least `-ε` becomes positive
semidefinite after adding `ε` times the identity. -/
theorem Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ}
    (hmin : -ε ≤ minEigenvalue hA) :
    (A + (ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hnonneg : 0 ≤ ε + minEigenvalue hA := by linarith
  have hscalar :
      (((ε + minEigenvalue hA : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hnonneg)
  have hshift := sub_minEigenvalue_smul_one_posSemidef hA
  rw [show A + (ε : ℂ) • (1 : Matrix n n ℂ) =
      (A - (minEigenvalue hA : ℂ) • 1) +
        ((ε + minEigenvalue hA : ℝ) : ℂ) • 1 by module]
  exact hshift.add hscalar

/-- An entrywise approximate Gram factorization certifies a least-eigenvalue lower bound.
If `A + ε₀ I` differs entrywise from `R Rᴴ` by at most `ζ`, the additional spectral
loss is at most `(r + 1) ζ` in matrix order `r`. -/
theorem neg_le_minEigenvalue_of_approx_gram_factor
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε₀ ε ζ : ℝ} (hζ : 0 ≤ ζ)
    (R : Matrix n n ℂ)
    (hentry : ∀ i j,
      ‖(A + (ε₀ : ℂ) • (1 : Matrix n n ℂ) - R * Rᴴ) i j‖ ≤ ζ)
    (hbudget : ε₀ + ((Fintype.card n : ℝ) + 1) * ζ ≤ ε) :
    -ε ≤ minEigenvalue hA := by
  let D := A + (ε₀ : ℂ) • (1 : Matrix n n ℂ) - R * Rᴴ
  have hD : D.IsHermitian := by
    dsimp only [D]
    exact (hA.add (Matrix.isHermitian_one.smul (by simp [isSelfAdjoint_iff]))).sub
      (Matrix.isHermitian_mul_conjTranspose_self R)
  have hDmin : -((Fintype.card n : ℝ) + 1) * ζ ≤ minEigenvalue hD :=
    neg_card_add_one_mul_le_minEigenvalue_of_entry_norm_le hD hζ hentry
  have hDshift :
      (D + ((((Fintype.card n : ℝ) + 1) * ζ : ℝ) : ℂ) •
        (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hD
      (by simpa only [neg_mul] using hDmin)
  have hgram : (R * Rᴴ).PosSemidef := by
    simpa only [Matrix.mul_one] using
      (Matrix.PosSemidef.one.mul_mul_conjTranspose_same R)
  have hshift :
      (A + ((ε₀ + ((Fintype.card n : ℝ) + 1) * ζ : ℝ) : ℂ) •
        (1 : Matrix n n ℂ)).PosSemidef := by
    rw [show A + ((ε₀ + ((Fintype.card n : ℝ) + 1) * ζ : ℝ) : ℂ) •
        (1 : Matrix n n ℂ) = R * Rᴴ +
          (D + ((((Fintype.card n : ℝ) + 1) * ζ : ℝ) : ℂ) • 1) by
      dsimp only [D]
      module]
    exact hgram.add hDshift
  have hmin := neg_le_minEigenvalue_of_add_smul_one_posSemidef hA hshift
  linarith

/-- The shifted Gram-factor certificate is complete: every Hermitian matrix satisfying
the spectral lower bound admits such a factor, obtained from its positive square root. -/
theorem Matrix.IsHermitian.exists_add_smul_one_eq_mul_conjTranspose_of_neg_le_minEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ}
    (hmin : -ε ≤ minEigenvalue hA) :
    ∃ R : Matrix n n ℂ, A + (ε : ℂ) • (1 : Matrix n n ℂ) = R * Rᴴ := by
  let B := A + (ε : ℂ) • (1 : Matrix n n ℂ)
  have hB : B.PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hA hmin
  refine ⟨CFC.sqrt B, ?_⟩
  rw [Matrix.conjTranspose_cfc_sqrt, CFC.sqrt_mul_sqrt_self B hB.nonneg]

/-- The least-eigenvalue lower bound is equivalent to existence of a Gram factor for the
shifted matrix. -/
theorem Matrix.IsHermitian.neg_le_minEigenvalue_iff_exists_gram_factor
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {ε : ℝ} :
    -ε ≤ minEigenvalue hA ↔
      ∃ R : Matrix n n ℂ, A + (ε : ℂ) • (1 : Matrix n n ℂ) = R * Rᴴ := by
  constructor
  · exact
      Matrix.IsHermitian.exists_add_smul_one_eq_mul_conjTranspose_of_neg_le_minEigenvalue hA
  · rintro ⟨R, hR⟩
    exact neg_le_minEigenvalue_of_add_smul_one_eq_mul_conjTranspose hA R hR

/-- Repairing a Hermitian trace-one matrix whose least eigenvalue is at least `-ε`
produces an exact density matrix within trace-norm distance `2 n ε`.  The dimension
factor is the trace cost of shifting every eigenvalue by `ε`. -/
theorem exists_density_rectangularTraceNorm_sub_le_of_neg_le_minEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htrace : A.trace = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA) :
    ∃ A₀ : Matrix n n ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ 2 * Fintype.card n * ε := by
  classical
  let x₀ : n := Classical.choice (Matrix.nonempty_of_trace_eq_one A htrace)
  let B := A + (ε : ℂ) • (1 : Matrix n n ℂ)
  have hB : B.PosSemidef := by
    exact Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hA hmin
  let A₀ := Matrix.normalizePosSemidef x₀ B
  have hA₀ : A₀.PosSemidef := Matrix.normalizePosSemidef_posSemidef x₀ hB
  have hA₀trace : A₀.trace = 1 := Matrix.normalizePosSemidef_trace x₀ hB
  have hBtrace : B.trace.re = 1 + Fintype.card n * ε := by
    simp [B, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, htrace]
    ring
  have hshift : ((ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hε)
  have hBA : rectangularTraceNorm (B - A) = Fintype.card n * ε := by
    rw [show B - A = (ε : ℂ) • (1 : Matrix n n ℂ) by simp [B]]
    rw [rectangularTraceNorm_eq_re_trace_of_posSemidef hshift,
      Matrix.trace_smul, Matrix.trace_one]
    norm_num
    ring
  have hA₀B : rectangularTraceNorm (A₀ - B) = Fintype.card n * ε := by
    rw [show A₀ = Matrix.normalizePosSemidef x₀ B by rfl,
      rectangularTraceNorm_normalizePosSemidef_sub x₀ hB, hBtrace]
    rw [abs_of_nonpos]
    · ring
    · apply sub_nonpos.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card n)) hε]
  refine ⟨A₀, hA₀, hA₀trace, ?_⟩
  calc
    rectangularTraceNorm (A₀ - A) =
        rectangularTraceNorm ((A₀ - B) + (B - A)) := by congr 1; abel
    _ ≤ rectangularTraceNorm (A₀ - B) + rectangularTraceNorm (B - A) :=
      rectangularTraceNorm_add_le _ _
    _ ≤ 2 * Fintype.card n * ε := by rw [hA₀B, hBA]; nlinarith

/-- A Hermitian matrix with trace defect at most `κ` and least eigenvalue at least
`-ε` can be repaired to an exact density within trace-norm distance
`κ + 2 n ε`. -/
theorem exists_density_rectangularTraceNorm_sub_le_of_trace_defect_of_minEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {κ ε : ℝ}
    (htrace : |1 - A.trace.re| ≤ κ) (hε : 0 ≤ ε)
    (hmin : -ε ≤ minEigenvalue hA) :
    ∃ A₀ : Matrix n n ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * Fintype.card n * ε := by
  classical
  let x₀ : n := Classical.choice (inferInstance : Nonempty n)
  let B := A + (ε : ℂ) • (1 : Matrix n n ℂ)
  have hB : B.PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hA hmin
  let A₀ := Matrix.normalizePosSemidef x₀ B
  have hA₀ : A₀.PosSemidef := Matrix.normalizePosSemidef_posSemidef x₀ hB
  have hA₀trace : A₀.trace = 1 := Matrix.normalizePosSemidef_trace x₀ hB
  have hBtrace : B.trace.re = A.trace.re + Fintype.card n * ε := by
    simp [B, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    ring
  have hshift : ((ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hε)
  have hBA : rectangularTraceNorm (B - A) = Fintype.card n * ε := by
    rw [show B - A = (ε : ℂ) • (1 : Matrix n n ℂ) by simp [B]]
    rw [rectangularTraceNorm_eq_re_trace_of_posSemidef hshift,
      Matrix.trace_smul, Matrix.trace_one]
    norm_num
    ring
  have habs : |1 - B.trace.re| ≤ κ + Fintype.card n * ε := by
    rw [hBtrace]
    calc
      |1 - (A.trace.re + Fintype.card n * ε)| =
          |(1 - A.trace.re) - Fintype.card n * ε| := by congr 1; ring
      _ ≤ |1 - A.trace.re| + |Fintype.card n * ε| := abs_sub _ _
      _ ≤ κ + Fintype.card n * ε := by
        rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)]
        simpa only [add_comm] using
          add_le_add_right htrace (Fintype.card n * ε)
  have hA₀B : rectangularTraceNorm (A₀ - B) ≤ κ + Fintype.card n * ε := by
    rw [show A₀ = Matrix.normalizePosSemidef x₀ B by rfl,
      rectangularTraceNorm_normalizePosSemidef_sub x₀ hB]
    exact habs
  refine ⟨A₀, hA₀, hA₀trace, ?_⟩
  calc
    rectangularTraceNorm (A₀ - A) =
        rectangularTraceNorm ((A₀ - B) + (B - A)) := by congr 1; abel
    _ ≤ rectangularTraceNorm (A₀ - B) + rectangularTraceNorm (B - A) :=
      rectangularTraceNorm_add_le _ _
    _ ≤ κ + 2 * Fintype.card n * ε := by rw [hBA]; linarith

/-- Approximate positivity can be repaired inside the compressed LVV program.  If a
Hermitian trace-one matrix has least eigenvalue at least `-ε`, its repaired density has
boundary error at most `2 n ε` larger and objective value at most
`2 ‖K‖ n ε` larger. -/
theorem exists_density_program_of_neg_le_minEigenvalue
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (htrace : A.trace = 1)
    {η E ε : ℝ} (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤ η + 2 * n * ε ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (2 * n * ε) := by
  obtain ⟨A₀, hA₀, hA₀trace, hclose⟩ :=
    exists_density_rectangularTraceNorm_sub_le_of_neg_le_minEigenvalue
      hA htrace hε hmin
  have hclose' : rectangularTraceNorm (A₀ - A) ≤ 2 * n * ε := by
    simpa using hclose
  obtain ⟨_htraceClose, henergyClose, hboundaryClose⟩ :=
    compressedDensity_program_perturbation Z hZ A A₀ K X η (2 * n * ε) hclose' hboundary
  refine ⟨A₀, hA₀, hA₀trace, hclose', hboundaryClose, ?_⟩
  have hupper : (A₀ * K).trace.re - (A * K).trace.re ≤ ‖K‖ * (2 * n * ε) :=
    le_trans (le_abs_self _) henergyClose
  linarith

/-- Trace defect and approximate positivity can be repaired simultaneously inside the
compressed LVV program.  The common trace-norm repair radius is `κ + 2 n ε`. -/
theorem exists_density_program_of_trace_defect_of_minEigenvalue
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {η E κ ε : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        η + (κ + 2 * n * ε) ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (κ + 2 * n * ε) := by
  obtain ⟨A₀, hA₀, hA₀trace, hclose⟩ :=
    exists_density_rectangularTraceNorm_sub_le_of_trace_defect_of_minEigenvalue
      hA htrace hε hmin
  have hclose' : rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε := by
    simpa using hclose
  obtain ⟨_htraceClose, henergyClose, hboundaryClose⟩ :=
    compressedDensity_program_perturbation Z hZ A A₀ K X η
      (κ + 2 * n * ε) hclose' hboundary
  refine ⟨A₀, hA₀, hA₀trace, hclose', hboundaryClose, ?_⟩
  have hupper : (A₀ * K).trace.re - (A * K).trace.re ≤
      ‖K‖ * (κ + 2 * n * ε) := le_trans (le_abs_self _) henergyClose
  linarith

/-- A solver certificate with spectral positivity error `ε` and boundary-equation error
`δ` yields a genuine compressed density.  The repaired boundary tolerance is
`η + δ + 2 n ε`, and the energy threshold increases by `2 ‖K‖ n ε`. -/
theorem exists_density_of_spectral_approx_sdp_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (htrace : A.trace = 1)
    {P N : Matrix (s × b) (s × b) ℂ} (hP : P.PosSemidef) (hN : N.PosSemidef)
    {η E δ ε : ℝ} (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        η + δ + 2 * n * ε ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (2 * n * ε) := by
  have hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η + δ :=
    rectangularTraceNorm_le_add_of_approx_posSemidef_sub
      (compressedBoundaryLM Z A - X) hP hN hresidual htraces
  exact exists_density_program_of_neg_le_minEigenvalue
    Z hZ K X hA htrace hε hmin hboundary henergy

/-- A numerical semidefinite certificate with trace defect `κ`, spectral positivity
error `ε`, and boundary-equation error `δ` yields an exact compressed density.  All
three errors are displayed in the resulting boundary and energy bounds. -/
theorem exists_density_of_fully_approx_sdp_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {P N : Matrix (s × b) (s × b) ℂ} (hP : P.PosSemidef) (hN : N.PosSemidef)
    {η E δ κ ε : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        η + δ + (κ + 2 * n * ε) ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (κ + 2 * n * ε) := by
  have hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η + δ :=
    rectangularTraceNorm_le_add_of_approx_posSemidef_sub
      (compressedBoundaryLM Z A - X) hP hN hresidual htraces
  exact exists_density_program_of_trace_defect_of_minEigenvalue
    Z hZ K X hA htrace hε hmin hboundary henergy

/-- Two approximately positive Hermitian matrices can be repaired by the same scalar
shift.  Their difference is unchanged, while their total trace grows by exactly
`2 r ε` in dimension `r`. -/
theorem exists_posSemidef_pair_same_sub_of_neg_le_minEigenvalue
    {r : Type*} [Fintype r] [DecidableEq r] [Nonempty r]
    {P N : Matrix r r ℂ} (hP : P.IsHermitian) (hN : N.IsHermitian)
    {ε : ℝ}
    (hPmin : -ε ≤ minEigenvalue hP) (hNmin : -ε ≤ minEigenvalue hN) :
    ∃ P₀ N₀ : Matrix r r ℂ,
      P₀.PosSemidef ∧ N₀.PosSemidef ∧ P₀ - N₀ = P - N ∧
      P₀.trace.re + N₀.trace.re =
        P.trace.re + N.trace.re + 2 * Fintype.card r * ε := by
  let P₀ := P + (ε : ℂ) • (1 : Matrix r r ℂ)
  let N₀ := N + (ε : ℂ) • (1 : Matrix r r ℂ)
  have hP₀ : P₀.PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hP hPmin
  have hN₀ : N₀.PosSemidef :=
    Matrix.IsHermitian.add_smul_one_posSemidef_of_neg_le_minEigenvalue hN hNmin
  refine ⟨P₀, N₀, hP₀, hN₀, ?_, ?_⟩
  · simp only [P₀, N₀]
    module
  · simp [P₀, N₀, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    ring

/-- The complete finite-precision feasibility conditions for the compressed LVV
semidefinite program.  The density and both auxiliary cone variables may have controlled
negative spectra, the density trace and boundary equation may be inexact, and the trace
budget and energy threshold remain one-sided inequalities. -/
structure IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (η E κ ε εb δ : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (P N : Matrix (s × b) (s × b) ℂ) : Prop where
  hA : A.IsHermitian
  hP : P.IsHermitian
  hN : N.IsHermitian
  htrace : |1 - A.trace.re| ≤ κ
  hε : 0 ≤ ε
  hmin : -ε ≤ minEigenvalue hA
  hεb : 0 ≤ εb
  hPmin : -εb ≤ minEigenvalue hP
  hNmin : -εb ≤ minEigenvalue hN
  hresidual : rectangularTraceNorm ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ
  htraces : P.trace.re + N.trace.re ≤ η
  henergy : (A * K).trace.re ≤ E

/-- Enlarging any of the six scalar tolerances preserves a unified approximate
compressed-boundary certificate. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.mono
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ η' E' κ' ε' εb' δ' : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hη : η ≤ η') (hE : E ≤ E') (hκ : κ ≤ κ')
    (hε : ε ≤ ε') (hεb : εb ≤ εb') (hδ : δ ≤ δ') :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η' E' κ' ε' εb' δ' A P N := by
  exact ⟨h.hA, h.hP, h.hN, h.htrace.trans hκ, h.hε.trans hε,
    (neg_le_neg hε).trans h.hmin, h.hεb.trans hεb,
    (neg_le_neg hεb).trans h.hPmin, (neg_le_neg hεb).trans h.hNmin,
    h.hresidual.trans hδ, h.htraces.trans hη, h.henergy.trans hE⟩

/-- Every unified approximate feasible certificate admits Gram witnesses for all three
shifted cone variables.  Their entries have explicit bounds determined by the trace and
spectral-error budgets.  Hence Gram certification covers the full spectral specification
inside a bounded factor region, not merely a diagonally dominant subclass. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_gram_factors
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N) :
    ∃ (RA : Matrix (Fin n) (Fin n) ℂ)
      (RP RN : Matrix (s × b) (s × b) ℂ),
      A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = RA * RAᴴ ∧
      P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) = RP * RPᴴ ∧
      N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) = RN * RNᴴ ∧
      (∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ δ) ∧
      (∀ i j, ‖RA i j‖ ^ 2 ≤ 1 + κ + n * ε) ∧
      (∀ i j, ‖RP i j‖ ^ 2 ≤ η + 2 * Fintype.card (s × b) * εb) ∧
      ∀ i j, ‖RN i j‖ ^ 2 ≤ η + 2 * Fintype.card (s × b) * εb := by
  obtain ⟨RA, hRA⟩ :=
    Matrix.IsHermitian.exists_add_smul_one_eq_mul_conjTranspose_of_neg_le_minEigenvalue
      h.hA h.hmin
  obtain ⟨RP, hRP⟩ :=
    Matrix.IsHermitian.exists_add_smul_one_eq_mul_conjTranspose_of_neg_le_minEigenvalue
      h.hP h.hPmin
  obtain ⟨RN, hRN⟩ :=
    Matrix.IsHermitian.exists_add_smul_one_eq_mul_conjTranspose_of_neg_le_minEigenvalue
      h.hN h.hNmin
  have hRAtrace : (RA * RAᴴ).trace.re = A.trace.re + n * ε := by
    rw [← hRA, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    simp
    ring
  have hRPtrace : (RP * RPᴴ).trace.re = P.trace.re + Fintype.card (s × b) * εb := by
    rw [← hRP, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    simp
    ring
  have hRNtrace : (RN * RNᴴ).trace.re = N.trace.re + Fintype.card (s × b) * εb := by
    rw [← hRN, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    simp
    ring
  have hAtrace : A.trace.re ≤ 1 + κ := by
    linarith [(abs_le.mp h.htrace).1]
  have hRPnonneg : 0 ≤ (RP * RPᴴ).trace.re := by
    rw [Matrix.trace_mul_comm, Matrix.trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
    positivity
  have hRNnonneg : 0 ≤ (RN * RNᴴ).trace.re := by
    rw [Matrix.trace_mul_comm, Matrix.trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
    positivity
  have hPlower : 0 ≤ P.trace.re + Fintype.card (s × b) * εb := by
    rw [← hRPtrace]
    exact hRPnonneg
  have hNlower : 0 ≤ N.trace.re + Fintype.card (s × b) * εb := by
    rw [← hRNtrace]
    exact hRNnonneg
  refine ⟨RA, RP, RN, hRA, hRP, hRN, fun i j ↦
    (norm_apply_le_rectangularTraceNorm _ i j).trans h.hresidual, ?_, ?_, ?_⟩
  · intro i j
    calc
      ‖RA i j‖ ^ 2 ≤ (RA * RAᴴ).trace.re :=
        norm_sq_apply_le_re_trace_mul_conjTranspose RA i j
      _ = A.trace.re + n * ε := hRAtrace
      _ ≤ 1 + κ + n * ε := by linarith
  · intro i j
    calc
      ‖RP i j‖ ^ 2 ≤ (RP * RPᴴ).trace.re :=
        norm_sq_apply_le_re_trace_mul_conjTranspose RP i j
      _ = P.trace.re + Fintype.card (s × b) * εb := hRPtrace
      _ ≤ η + 2 * Fintype.card (s × b) * εb := by linarith [h.htraces, hNlower]
  · intro i j
    calc
      ‖RN i j‖ ^ 2 ≤ (RN * RNᴴ).trace.re :=
        norm_sq_apply_le_re_trace_mul_conjTranspose RN i j
      _ = N.trace.re + Fintype.card (s × b) * εb := hRNtrace
      _ ≤ η + 2 * Fintype.card (s × b) * εb := by linarith [h.htraces, hPlower]

/-- Every matrix variable in a unified approximate certificate lies in an explicit
entrywise bounded region.  The bounds follow from the bounded exact Gram factors of the
three shifted matrices. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.entry_norm_bounds
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N) :
    (∀ i j, ‖A i j‖ ≤ approxSDPDensityEntryBound n κ ε) ∧
      (∀ i j, ‖P i j‖ ≤ approxSDPAuxEntryBound (Fintype.card (s × b)) η εb) ∧
      ∀ i j, ‖N i j‖ ≤ approxSDPAuxEntryBound (Fintype.card (s × b)) η εb := by
  obtain ⟨RA, RP, RN, hRA, hRP, hRN, _hresidual, hRAbound, hRPbound, hRNbound⟩ :=
    h.exists_gram_factors
  have hgramA : ∀ i j, ‖(RA * RAᴴ) i j‖ ≤
      n * gramCertificateBound (1 + κ + n * ε) :=
    fun i j ↦ by
      simpa only [Fintype.card_fin] using
        norm_mul_conjTranspose_apply_le_card_mul_of_sq_entry_norm_le RA
          (gramCertificateBound_pos _).le
          (fun i j ↦ (hRAbound i j).trans (le_gramCertificateBound _)) i j
  have hgramP : ∀ i j, ‖(RP * RPᴴ) i j‖ ≤
      Fintype.card (s × b) *
        gramCertificateBound (η + 2 * Fintype.card (s × b) * εb) :=
    fun i j ↦ norm_mul_conjTranspose_apply_le_card_mul_of_sq_entry_norm_le RP
      (gramCertificateBound_pos _).le
      (fun i j ↦ (hRPbound i j).trans (le_gramCertificateBound _)) i j
  have hgramN : ∀ i j, ‖(RN * RNᴴ) i j‖ ≤
      Fintype.card (s × b) *
        gramCertificateBound (η + 2 * Fintype.card (s × b) * εb) :=
    fun i j ↦ norm_mul_conjTranspose_apply_le_card_mul_of_sq_entry_norm_le RN
      (gramCertificateBound_pos _).le
      (fun i j ↦ (hRNbound i j).trans (le_gramCertificateBound _)) i j
  have hshiftA : ∀ i j, ‖((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ≤ ε := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.hε]
      exact le_rfl
    · simp [Matrix.smul_apply, hij, h.hε]
  have hshiftB : ∀ i j,
      ‖((εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ)) i j‖ ≤ εb := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.hεb]
      exact le_rfl
    · simp [Matrix.smul_apply, hij, h.hεb]
  have heqA : A = RA * RAᴴ - (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hRA]
    abel
  have heqP : P = RP * RPᴴ - (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) := by
    rw [← hRP]
    abel
  have heqN : N = RN * RNᴴ - (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) := by
    rw [← hRN]
    abel
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [heqA, Matrix.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hgramA i j) (hshiftA i j))
  · intro i j
    rw [heqP, Matrix.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hgramP i j) (hshiftB i j))
  · intro i j
    rw [heqN, Matrix.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hgramN i j) (hshiftB i j))

/-- A unified certificate tested with rational approximations of the objective and
boundary center is sound for the exact fixed data after the explicit objective and
boundary-tolerance enlargements. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.of_fixed_data_approximation
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K QK : Matrix (Fin n) (Fin n) ℂ}
    {X QX : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ θK θX : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z QK QX η E κ ε εb δ A P N)
    (hKclose : ∀ i j, ‖(K - QK) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX) i j‖ ≤ θX) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X η
      (E + (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK)
      κ ε εb (δ + (Fintype.card (s × b) : ℝ) ^ 2 * θX) A P N := by
  have hC : 0 ≤ approxSDPDensityEntryBound n κ ε := by
    unfold approxSDPDensityEntryBound
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (gramCertificateBound_pos _).le) h.hε
  have hentry := h.entry_norm_bounds |>.1
  have hobjective : |(A * K).trace.re - (A * QK).trace.re| ≤
      (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK := by
    simpa only [Fintype.card_fin] using
      abs_re_trace_mul_sub_le_of_entry_norm_le A K QK hentry hKclose hC
  have henergy : (A * K).trace.re ≤
      E + (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK := by
    have hdiff : (A * K).trace.re - (A * QK).trace.re ≤
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK :=
      (le_abs_self _).trans hobjective
    linarith [h.henergy]
  refine { h with hresidual := ?_, henergy := henergy }
  exact compressedBoundaryResidual_rectangularTraceNorm_le_of_boundary_center_approximation
    Z A X QX P N hXclose h.hresidual

/-- Conversely, an exact-data certificate remains feasible when tested against
entrywise approximations of the objective and boundary center, after the same explicit
enlargements.  Together with `of_fixed_data_approximation`, this gives two-sided
stability of the fixed-data rationalization. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.to_fixed_data_approximation
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K QK : Matrix (Fin n) (Fin n) ℂ}
    {X QX : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ θK θX : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hKclose : ∀ i j, ‖(K - QK) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX) i j‖ ≤ θX) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z QK QX η
      (E + (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK)
      κ ε εb (δ + (Fintype.card (s × b) : ℝ) ^ 2 * θX) A P N := by
  have hC : 0 ≤ approxSDPDensityEntryBound n κ ε := by
    unfold approxSDPDensityEntryBound
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (gramCertificateBound_pos _).le) h.hε
  have hentry := h.entry_norm_bounds |>.1
  have hobjective : |(A * K).trace.re - (A * QK).trace.re| ≤
      (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK := by
    simpa only [Fintype.card_fin] using
      abs_re_trace_mul_sub_le_of_entry_norm_le A K QK hentry hKclose hC
  have henergy : (A * QK).trace.re ≤
      E + (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK := by
    have hdiff : (A * QK).trace.re - (A * K).trace.re ≤
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK := by
      rw [abs_sub_comm] at hobjective
      exact (le_abs_self _).trans hobjective
    linarith [h.henergy]
  have hXclose' : ∀ i j, ‖(QX - X) i j‖ ≤ θX := by
    intro i j
    rw [Matrix.sub_apply, norm_sub_rev]
    exact hXclose i j
  refine { h with hresidual := ?_, henergy := henergy }
  exact compressedBoundaryResidual_rectangularTraceNorm_le_of_boundary_center_approximation
    Z A QX X P N hXclose' h.hresidual

/-- Bounded objective and boundary-center matrices admit rational fixed-data
approximations that are uniformly sound for every candidate in the approximate SDP
search. -/
theorem exists_rational_fixed_matrices_for_approximate_sdp
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {RK RX θK θX : ℝ} (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    ∃ QK : Matrix (Fin n) (Fin n) ℂ,
      Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight RK θK) QK ∧
      ∃ QX : Matrix (s × b) (s × b) ℂ,
        Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight RX θX) QX ∧
        ∀ (η E κ ε εb δ : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
          (P N : Matrix (s × b) (s × b) ℂ),
          IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
            Z QK QX η E κ ε εb δ A P N →
          IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X η
            (E + (n : ℝ) ^ 2 * approxSDPDensityEntryBound n κ ε * θK)
            κ ε εb (δ + (Fintype.card (s × b) : ℝ) ^ 2 * θX) A P N := by
  obtain ⟨QK, hQKrat, hQKclose⟩ :=
    exists_rational_rectangular_approximation hRK hθK K hK
  obtain ⟨QX, hQXrat, hQXclose⟩ :=
    exists_rational_rectangular_approximation hRX hθX X hX
  refine ⟨QK, hQKrat, QX, hQXrat, ?_⟩
  intro η E κ ε εb δ A P N h
  exact h.of_fixed_data_approximation hQKclose hQXclose

/-- A unified certificate tested with an approximate rational coordinate map is sound
for the exact coordinate isometry after adding the explicit trace-norm perturbation to
the boundary-equation tolerance. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.of_coordinate_approximation
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z Q : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ θ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Q K X η E κ ε εb δ A P N)
    (hZ : Zᴴ * Z = 1) (hθ : 0 ≤ θ)
    (hclose : ∀ i j, ‖(Z - Q) i j‖ ≤ θ) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X η E κ ε εb
      (δ + (Fintype.card (s × b) : ℝ) ^ 2 *
        (Fintype.card a * (n : ℝ) ^ 2 * θ *
          approxSDPDensityEntryBound n κ ε * (2 + θ))) A P N := by
  have hC : 0 ≤ approxSDPDensityEntryBound n κ ε := by
    unfold approxSDPDensityEntryBound
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (gramCertificateBound_pos _).le) h.hε
  have hentry := h.entry_norm_bounds |>.1
  refine { h with hresidual := ?_ }
  simpa only [one_mul, mul_one] using
    compressedBoundaryResidual_rectangularTraceNorm_le_of_coordinate_approximation_rev
      Z Q A X P N zero_le_one hC hθ
        (norm_apply_le_one_of_conjTranspose_mul_self_eq_one Z hZ)
        hentry hclose h.hresidual

/-- An exact-isometry certificate remains feasible when the boundary equation is tested
with an entrywise rational approximation of that isometry.  The perturbation allowance
is identical to the reverse soundness transfer. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.to_coordinate_approximation
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z Q : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ θ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hZ : Zᴴ * Z = 1) (hθ : 0 ≤ θ)
    (hclose : ∀ i j, ‖(Z - Q) i j‖ ≤ θ) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Q K X η E κ ε εb
      (δ + (Fintype.card (s × b) : ℝ) ^ 2 *
        (Fintype.card a * (n : ℝ) ^ 2 * θ *
          approxSDPDensityEntryBound n κ ε * (2 + θ))) A P N := by
  have hC : 0 ≤ approxSDPDensityEntryBound n κ ε := by
    unfold approxSDPDensityEntryBound
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (gramCertificateBound_pos _).le) h.hε
  have hentry := h.entry_norm_bounds |>.1
  refine { h with hresidual := ?_ }
  simpa only [one_mul, mul_one] using
    compressedBoundaryResidual_rectangularTraceNorm_le_of_coordinate_approximation
      Z Q A X P N zero_le_one hC hθ
        (norm_apply_le_one_of_conjTranspose_mul_self_eq_one Z hZ)
        hentry hclose h.hresidual

/-- One rational approximation of the exact coordinate isometry is uniformly sound for
every candidate in the approximate SDP search.  The mesh uses the common candidate
entry bound, and every accepted certificate transfers back to the exact isometry with
boundary tolerance enlarged by at most `ω`. -/
theorem exists_rational_coordinate_map_for_approximate_sdp
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    {κ ε ω : ℝ} (hε : 0 ≤ ε) (hω : 0 < ω) :
    let C := approxSDPDensityEntryBound n κ ε
    let r := Fintype.card (s × b)
    let θ := rationalCoordinateMapTraceToleranceOfBound (Fintype.card a) n r C ω
    ∃ Q : Matrix ((a × s) × b) (Fin n) ℂ,
      Matrix.HasRationalEntriesOfHeight (rationalBoundedMatrixGridHeight 1 θ) Q ∧
      (∀ i j, ‖(Z - Q) i j‖ ≤ θ) ∧
      ∀ (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
        (η E εb δ : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
        (P N : Matrix (s × b) (s × b) ℂ),
        IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
          Q K X η E κ ε εb δ A P N →
        IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
          Z K X η E κ ε εb (δ + ω) A P N := by
  dsimp only
  let C := approxSDPDensityEntryBound n κ ε
  let r := Fintype.card (s × b)
  let θ := rationalCoordinateMapTraceToleranceOfBound (Fintype.card a) n r C ω
  have hC : 0 ≤ C := by
    dsimp only [C, approxSDPDensityEntryBound]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (gramCertificateBound_pos _).le) hε
  have hθ : 0 < θ :=
    rationalCoordinateMapTraceToleranceOfBound_pos _ _ _ hC hω
  obtain ⟨Q, hQrat, hclose⟩ := exists_rational_isometry_approximation hθ Z hZ
  refine ⟨Q, hQrat, hclose, ?_⟩
  intro K X η E εb δ A P N h
  have hsound := h.of_coordinate_approximation hZ hθ.le hclose
  apply hsound.mono le_rfl le_rfl le_rfl le_rfl le_rfl
  have hbound := rationalCoordinateMapTraceToleranceOfBound_boundary_error_le
    (Fintype.card a) n (Fintype.card (s × b)) hC hω
  simpa only [C, r, θ, add_comm] using add_le_add_left hbound δ

/-- Every unified feasible certificate has entrywise approximations of all three primary
matrix variables in concrete coordinate grids.  Thus the primary-variable search region,
as well as the Gram-factor search region, is an explicitly named finite set. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_explicit_primary_search
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ θA θb : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hZ : Zᴴ * Z = 1)
    (hθA : 0 < θA) (hθb : 0 < θb) :
    ∃ A' ∈ rationalHermitianBoundedMatrixGrid (Fin n)
        (approxSDPDensityEntryBound n κ ε) θA,
      A'.IsHermitian ∧
      ∃ P' ∈ rationalHermitianBoundedMatrixGrid (s × b)
          (approxSDPAuxEntryBound (Fintype.card (s × b)) η εb) θb,
        P'.IsHermitian ∧
        ∃ N' ∈ rationalHermitianBoundedMatrixGrid (s × b)
            (approxSDPAuxEntryBound (Fintype.card (s × b)) η εb) θb,
          N'.IsHermitian ∧
          (∀ i j, ‖(A - A') i j‖ ≤ θA) ∧
          (∀ i j, ‖(P - P') i j‖ ≤ θb) ∧
          (∀ i j, ‖(N - N') i j‖ ≤ θb) ∧
          |1 - A'.trace.re| ≤ κ + n * θA ∧
          P'.trace.re + N'.trace.re ≤
            η + 2 * Fintype.card (s × b) * θb ∧
          rectangularTraceNorm
              ((compressedBoundaryLM Z A' - X) - (P' - N')) ≤
            δ + (n : ℝ) ^ 2 * θA +
              2 * (Fintype.card (s × b) : ℝ) ^ 2 * θb ∧
          (A' * K).trace.re ≤ E + ‖K‖ * ((n : ℝ) ^ 2 * θA) := by
  obtain ⟨hA, hP, hN⟩ := h.entry_norm_bounds
  have hn : 0 < n := Fintype.card_fin n ▸ Fintype.card_pos
  have hr : 0 < Fintype.card (s × b) := Fintype.card_pos
  obtain ⟨A', hAgrid, hA'Herm, _hA'rat, hAclose⟩ :=
    exists_mem_rationalHermitianBoundedMatrixGrid hθA A h.hA hA
  obtain ⟨P', hPgrid, hP'Herm, _hP'rat, hPclose⟩ :=
    exists_mem_rationalHermitianBoundedMatrixGrid hθb P h.hP hP
  obtain ⟨N', hNgrid, hN'Herm, _hN'rat, hNclose⟩ :=
    exists_mem_rationalHermitianBoundedMatrixGrid hθb N h.hN hN
  have hAA' : rectangularTraceNorm (A - A') ≤ (n : ℝ) ^ 2 * θA := by
    simpa only [Fintype.card_fin] using
      rectangularTraceNorm_le_card_sq_mul_of_entry_norm_le (A - A') hAclose
  have hA'A : rectangularTraceNorm (A' - A) ≤ (n : ℝ) ^ 2 * θA := by
    have heq : A' - A = (-1 : ℂ) • (A - A') := by module
    rw [heq, rectangularTraceNorm_smul]
    norm_num
    exact hAA'
  have hPP' : rectangularTraceNorm (P - P') ≤
      (Fintype.card (s × b) : ℝ) ^ 2 * θb :=
    rectangularTraceNorm_le_card_sq_mul_of_entry_norm_le (P - P') hPclose
  have hP'P : rectangularTraceNorm (P' - P) ≤
      (Fintype.card (s × b) : ℝ) ^ 2 * θb := by
    have heq : P' - P = (-1 : ℂ) • (P - P') := by module
    rw [heq, rectangularTraceNorm_smul]
    norm_num
    simpa only [Fintype.card_prod, Nat.cast_mul] using hPP'
  have hNN' : rectangularTraceNorm (N - N') ≤
      (Fintype.card (s × b) : ℝ) ^ 2 * θb :=
    rectangularTraceNorm_le_card_sq_mul_of_entry_norm_le (N - N') hNclose
  have hN'N : rectangularTraceNorm (N' - N) ≤
      (Fintype.card (s × b) : ℝ) ^ 2 * θb := by
    have heq : N' - N = (-1 : ℂ) • (N - N') := by module
    rw [heq, rectangularTraceNorm_smul]
    norm_num
    simpa only [Fintype.card_prod, Nat.cast_mul] using hNN'
  have hmap := (compressedBoundaryLM_distance_le Z hZ A A').trans hA'A
  have hresidualIdentity :
      (compressedBoundaryLM Z A' - X) - (P' - N') =
        ((compressedBoundaryLM Z A - X) - (P - N)) +
          (compressedBoundaryLM Z A' - compressedBoundaryLM Z A) -
          (P' - P) + (N' - N) := by
    module
  have hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A' - X) - (P' - N')) ≤
        δ + (n : ℝ) ^ 2 * θA +
          2 * (Fintype.card (s × b) : ℝ) ^ 2 * θb := by
    rw [hresidualIdentity]
    calc
      rectangularTraceNorm
          ((((compressedBoundaryLM Z A - X) - (P - N)) +
            (compressedBoundaryLM Z A' - compressedBoundaryLM Z A) -
            (P' - P)) + (N' - N)) ≤
          rectangularTraceNorm
              (((compressedBoundaryLM Z A - X) - (P - N)) +
                (compressedBoundaryLM Z A' - compressedBoundaryLM Z A) -
                (P' - P)) + rectangularTraceNorm (N' - N) :=
        rectangularTraceNorm_add_le _ _
      _ ≤ (rectangularTraceNorm
              (((compressedBoundaryLM Z A - X) - (P - N)) +
                (compressedBoundaryLM Z A' - compressedBoundaryLM Z A)) +
              rectangularTraceNorm (-(P' - P))) + rectangularTraceNorm (N' - N) := by
        gcongr
        simpa only [sub_eq_add_neg] using rectangularTraceNorm_add_le
          (((compressedBoundaryLM Z A - X) - (P - N)) +
            (compressedBoundaryLM Z A' - compressedBoundaryLM Z A)) (-(P' - P))
      _ ≤ ((rectangularTraceNorm ((compressedBoundaryLM Z A - X) - (P - N)) +
              rectangularTraceNorm
                (compressedBoundaryLM Z A' - compressedBoundaryLM Z A)) +
              rectangularTraceNorm (-(P' - P))) + rectangularTraceNorm (N' - N) := by
        gcongr
        exact rectangularTraceNorm_add_le _ _
      _ ≤ δ + (n : ℝ) ^ 2 * θA +
          2 * (Fintype.card (s × b) : ℝ) ^ 2 * θb := by
        rw [show -(P' - P) = (-1 : ℂ) • (P' - P) by module,
          rectangularTraceNorm_smul]
        norm_num
        rw [Fintype.card_prod] at hP'P hN'N
        push_cast at hP'P hN'N
        linarith [h.hresidual, hmap, hP'P, hN'N]
  have henergy :=
    (compressedDensity_trace_energy_perturbation A A' K ((n : ℝ) ^ 2 * θA) hA'A).2
  refine ⟨A', hAgrid, hA'Herm, P', hPgrid, hP'Herm,
    N', hNgrid, hN'Herm, hAclose, hPclose, hNclose, ?_, ?_, hresidual, ?_⟩
  · simpa only [Fintype.card_fin] using
      abs_one_sub_re_trace_le_of_entry_rounding A A' h.htrace hAclose
  · exact re_trace_add_le_of_entry_rounding P N P' N' h.htraces hPclose hNclose
  · linarith [(abs_le.mp henergy).2, h.henergy]

/-- Every unified feasible certificate has approximate Gram witnesses in three explicit
finite grids.  The density-factor grid and the two auxiliary-factor grids depend only on
the displayed scalar budgets and requested Gram errors, not on the particular feasible
matrices. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_finite_gram_search
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ζA ζb : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hζA : 0 < ζA) (hζb : 0 < ζb) :
    ∃ (NA : Finset (Matrix (Fin n) (Fin n) ℂ))
      (NP NN : Finset (Matrix (s × b) (s × b) ℂ)),
      NA.card ≤ gramCertificateNetCard (Fin n)
        (gramCertificateBound (1 + κ + n * ε)) ζA ∧
      NP.card ≤ gramCertificateNetCard (s × b)
        (gramCertificateBound (η + 2 * Fintype.card (s × b) * εb)) ζb ∧
      NN.card ≤ gramCertificateNetCard (s × b)
        (gramCertificateBound (η + 2 * Fintype.card (s × b) * εb)) ζb ∧
      ∃ QA ∈ NA, ∃ QP ∈ NP, ∃ QN ∈ NN,
        (∀ i j, ‖(A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) i j‖ ≤ ζA) ∧
        (∀ i j, ‖(P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) i j‖ ≤ ζb) ∧
        ∀ i j, ‖(N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) i j‖ ≤ ζb := by
  classical
  obtain ⟨RA, RP, RN, hRA, hRP, hRN, _hresidual, hRAbound, hRPbound, hRNbound⟩ :=
    h.exists_gram_factors
  obtain ⟨NA, hNAcard, hNAcover⟩ :=
    exists_finset_bounded_gram_certificate_net_at_error
      (ι := Fin n) (C := gramCertificateBound (1 + κ + n * ε))
      (ζ := ζA) (gramCertificateBound_pos _) hζA
  obtain ⟨NP, hNPcard, hNPcover⟩ :=
    exists_finset_bounded_gram_certificate_net_at_error
      (ι := s × b) (C := gramCertificateBound
        (η + 2 * Fintype.card (s × b) * εb))
      (ζ := ζb) (gramCertificateBound_pos _) hζb
  obtain ⟨QA, hQANA, hQAclose⟩ := hNAcover RA fun i j ↦
    (hRAbound i j).trans (le_gramCertificateBound _)
  obtain ⟨QP, hQPNP, hQPclose⟩ := hNPcover RP fun i j ↦
    (hRPbound i j).trans (le_gramCertificateBound _)
  obtain ⟨QN, hQNNP, hQNclose⟩ := hNPcover RN fun i j ↦
    (hRNbound i j).trans (le_gramCertificateBound _)
  refine ⟨NA, NP, NP, hNAcard, hNPcard, hNPcard, QA, hQANA,
    QP, hQPNP, QN, hQNNP, ?_, ?_, ?_⟩
  · intro i j
    rw [hRA]
    exact hQAclose i j
  · intro i j
    rw [hRP]
    exact hQPclose i j
  · intro i j
    rw [hRN]
    exact hQNclose i j

/-- Every unified feasible certificate has approximate Gram witnesses in the concrete
coordinate grids `gramCertificateGrid`.  Unlike the preceding existential-net theorem,
the three searched finite sets are named explicitly and can be evaluated from their
orders, radii and requested tolerances. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_explicit_gram_search
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ζA ζb : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hζA : 0 < ζA) (hζb : 0 < ζb) :
    ∃ QA ∈ gramCertificateGrid (Fin n)
        (gramCertificateBound (1 + κ + n * ε)) ζA,
      ∃ QP ∈ gramCertificateGrid (s × b)
          (gramCertificateBound (η + 2 * Fintype.card (s × b) * εb)) ζb,
        ∃ QN ∈ gramCertificateGrid (s × b)
            (gramCertificateBound (η + 2 * Fintype.card (s × b) * εb)) ζb,
          (∀ i j,
            ‖(A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) i j‖ ≤ ζA) ∧
          (∀ i j,
            ‖(P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) i j‖ ≤ ζb) ∧
          ∀ i j,
            ‖(N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) i j‖ ≤ ζb := by
  obtain ⟨RA, RP, RN, hRA, hRP, hRN, _hresidual, hRAbound, hRPbound, hRNbound⟩ :=
    h.exists_gram_factors
  obtain ⟨QA, hQA, hQAclose⟩ := exists_mem_gramCertificateGrid
    (gramCertificateBound_pos _) hζA RA fun i j ↦
      (hRAbound i j).trans (le_gramCertificateBound _)
  obtain ⟨QP, hQP, hQPclose⟩ := exists_mem_gramCertificateGrid
    (gramCertificateBound_pos _) hζb RP fun i j ↦
      (hRPbound i j).trans (le_gramCertificateBound _)
  obtain ⟨QN, hQN, hQNclose⟩ := exists_mem_gramCertificateGrid
    (gramCertificateBound_pos _) hζb RN fun i j ↦
      (hRNbound i j).trans (le_gramCertificateBound _)
  refine ⟨QA, hQA, QP, hQP, QN, hQN, ?_, ?_, ?_⟩
  · intro i j
    rw [hRA]
    exact hQAclose i j
  · intro i j
    rw [hRP]
    exact hQPclose i j
  · intro i j
    rw [hRN]
    exact hQNclose i j

/-- Every unified feasible certificate has Gram witnesses in exact Gaussian-rational
coordinate grids.  This removes the square roots and arbitrary real scalings from the
factor search. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_rational_gram_search
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ζA ζb : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N)
    (hζA : 0 < ζA) (hζb : 0 < ζb) :
    ∃ QA ∈ rationalGramCertificateGrid (Fin n)
        (gramCertificateBound (1 + κ + n * ε)) ζA,
      ∃ QP ∈ rationalGramCertificateGrid (s × b)
          (gramCertificateBound (η + 2 * Fintype.card (s × b) * εb)) ζb,
        ∃ QN ∈ rationalGramCertificateGrid (s × b)
            (gramCertificateBound (η + 2 * Fintype.card (s × b) * εb)) ζb,
          (∀ i j,
            ‖(A + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - QA * QAᴴ) i j‖ ≤ ζA) ∧
          (∀ i j,
            ‖(P + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QP * QPᴴ) i j‖ ≤ ζb) ∧
          ∀ i j,
            ‖(N + (εb : ℂ) • (1 : Matrix (s × b) (s × b) ℂ) - QN * QNᴴ) i j‖ ≤ ζb := by
  obtain ⟨RA, RP, RN, hRA, hRP, hRN, _hresidual, hRAbound, hRPbound, hRNbound⟩ :=
    h.exists_gram_factors
  obtain ⟨QA, hQA, _hQArat, hQAclose⟩ := exists_mem_rationalGramCertificateGrid
    hζA RA fun i j ↦ (hRAbound i j).trans (le_gramCertificateBound _)
  obtain ⟨QP, hQP, _hQPrat, hQPclose⟩ := exists_mem_rationalGramCertificateGrid
    hζb RP fun i j ↦ (hRPbound i j).trans (le_gramCertificateBound _)
  obtain ⟨QN, hQN, _hQNrat, hQNclose⟩ := exists_mem_rationalGramCertificateGrid
    hζb RN fun i j ↦ (hRNbound i j).trans (le_gramCertificateBound _)
  refine ⟨QA, hQA, QP, hQP, QN, hQN, ?_, ?_, ?_⟩
  · intro i j
    rw [hRA]
    exact hQAclose i j
  · intro i j
    rw [hRP]
    exact hQPclose i j
  · intro i j
    rw [hRN]
    exact hQNclose i j

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

/-- Exact rational input representation required by the finite arithmetic certificate
tester.  This structure deliberately separates the numerical input assumption from the
classical construction of the coordinate isometry in the LVV existence argument. -/
structure RationalCompressedSDPInputEncoding
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (ε εb : ℝ) where
  /-- Common height bound for every rational coordinate in the fixed input. -/
  height : ℕ
  z_height : Matrix.HasRationalEntriesOfHeight height Z
  objective_height : Matrix.HasRationalEntriesOfHeight height K
  boundary_height : Matrix.HasRationalEntriesOfHeight height X
  densityShift_height : HasRationalComplexCoordinatesOfHeight height (ε : ℂ)
  boundaryShift_height : HasRationalComplexCoordinatesOfHeight height (εb : ℂ)

/-- A rational scalar, regarded as complex, has coordinate height bounded by the
maximum of its rational height and one. -/
theorem ratCast_hasRationalComplexCoordinatesOfHeight (q : ℚ) :
    HasRationalComplexCoordinatesOfHeight (max (rationalHeight q) 1) (q : ℂ) := by
  refine ⟨q, 0, ?_, le_max_left _ _, ?_⟩
  · apply Complex.ext <;> simp
  · simp [rationalHeight]

/-- Canonical common coordinate height of three rational fixed-data codes and two
rational spectral shifts. -/
def rationalCompressedSDPInputCodeHeight
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b)) (ε εb : ℚ) : ℕ :=
  max Z.height <| max K.height <| max X.height <|
    max (max (rationalHeight ε) 1) (max (rationalHeight εb) 1)

/-- Explicit rational codes canonically provide the common fixed-data height required
by the bit-cost analysis. -/
def rationalCompressedSDPInputEncodingOfCodes
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b)) (ε εb : ℚ) :
    RationalCompressedSDPInputEncoding Z.decode K.decode X.decode (ε : ℝ) (εb : ℝ) where
  height := rationalCompressedSDPInputCodeHeight Z K X ε εb
  z_height := Z.decode_hasRationalEntriesOfHeight.mono <| le_max_left _ _
  objective_height := K.decode_hasRationalEntriesOfHeight.mono <|
    (le_max_left _ _).trans (le_max_right _ _)
  boundary_height := X.decode_hasRationalEntriesOfHeight.mono <|
    (le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  densityShift_height := (ratCast_hasRationalComplexCoordinatesOfHeight ε).mono <|
    (le_max_left _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _)
  boundaryShift_height := (ratCast_hasRationalComplexCoordinatesOfHeight εb).mono <|
    (le_max_right _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _)

/-- Bounded physical fixed data have rational coordinate codes at prescribed positive
entrywise meshes, with explicit canonical height bounds for all three codes. -/
theorem exists_rational_fixed_data_codes_with_height
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {RK RX θZ θK θX : ℝ} (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          QZ.height ≤ rationalBoundedMatrixGridHeight 1 θZ ∧
          QK.height ≤ rationalBoundedMatrixGridHeight RK θK ∧
          QX.height ≤ rationalBoundedMatrixGridHeight RX θX ∧
          (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
          (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
          ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX := by
  obtain ⟨Z', hZ'rat, hZ'close⟩ :=
    exists_rational_isometry_approximation hθZ Z hZ
  obtain ⟨K', hK'rat, hK'close⟩ :=
    exists_rational_rectangular_approximation hRK hθK K hK
  obtain ⟨X', hX'rat, hX'close⟩ :=
    exists_rational_rectangular_approximation hRX hθX X hX
  obtain ⟨QZ, hQZdecode, hQZheight⟩ :=
    RationalRectMatrixCode.exists_code_of_hasRationalEntriesOfHeight hZ'rat
  obtain ⟨QK, hQKdecode, hQKheight⟩ :=
    RationalRectMatrixCode.exists_code_of_hasRationalEntriesOfHeight hK'rat
  obtain ⟨QX, hQXdecode, hQXheight⟩ :=
    RationalRectMatrixCode.exists_code_of_hasRationalEntriesOfHeight hX'rat
  refine ⟨QZ, QK, QX, hQZheight, hQKheight, hQXheight, ?_, ?_, ?_⟩
  · simpa only [hQZdecode] using hZ'close
  · simpa only [hQKdecode] using hK'close
  · simpa only [hQXdecode] using hX'close

/-- Common input-code height obtained from the three explicit approximation grids and
the two rational cone shifts. -/
noncomputable def rationalCompressedSDPApproximationCodeHeight
    (RK RX θZ θK θX : ℝ) (ε εb : ℚ) : ℕ :=
  max (rationalBoundedMatrixGridHeight 1 θZ) <|
    max (rationalBoundedMatrixGridHeight RK θK) <|
      max (rationalBoundedMatrixGridHeight RX θX) <|
        max (max (rationalHeight ε) 1) (max (rationalHeight εb) 1)

/-- Canonical rational objective threshold absorbing fixed-data approximation losses. -/
noncomputable def rationalApproxDataEnergyThreshold
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK : ℝ) : ℚ :=
  rationalNonnegativeUpperApproximation
    ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
      approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK)
    (ρ : ℝ)

/-- Canonical rational boundary threshold absorbing all fixed-data approximation
losses, including the coordinate-map perturbation. -/
noncomputable def rationalApproxDataBoundaryThreshold
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) : ℚ :=
  rationalNonnegativeUpperApproximation
    ((δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
      (a * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) *
          (2 + θZ))) (ρ : ℝ)

theorem le_rationalApproxDataEnergyThreshold
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK : ℝ) :
    (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK ≤
      (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) := by
  exact le_rationalNonnegativeUpperApproximation _ _

theorem le_rationalApproxDataBoundaryThreshold
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) :
    (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
        (a * (n : ℝ) ^ 2 * θZ *
          approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) *
            (2 + θZ)) ≤
      (rationalApproxDataBoundaryThreshold a n r δ κ ε ρ θZ θX : ℝ) := by
  exact le_rationalNonnegativeUpperApproximation _ _

theorem rationalApproxDataEnergyThreshold_le
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK : ℝ)
    (hρ : 0 < (ρ : ℝ)) :
    (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) ≤
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * θK) 0 + (ρ : ℝ) := by
  exact rationalNonnegativeUpperApproximation_le hρ

theorem rationalApproxDataBoundaryThreshold_le
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) (hρ : 0 < (ρ : ℝ)) :
    (rationalApproxDataBoundaryThreshold a n r δ κ ε ρ θZ θX : ℝ) ≤
      max ((δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
        (a * (n : ℝ) ^ 2 * θZ *
          approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
            ((ε + ρ : ℚ) : ℝ) * (2 + θZ))) 0 + (ρ : ℝ) := by
  exact rationalNonnegativeUpperApproximation_le hρ

theorem rationalApproxDataEnergyThreshold_le_add_mesh
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK : ℝ)
    (hρ : 0 < (ρ : ℝ))
    (hnonneg : 0 ≤ (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
      approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ) * θK) :
    (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) ≤
      (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * θK + (ρ : ℝ) := by
  simpa only [max_eq_left hnonneg] using
    rationalApproxDataEnergyThreshold_le n E κ ε ρ K θK hρ

theorem rationalApproxDataBoundaryThreshold_le_add_mesh
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) (hρ : 0 < (ρ : ℝ))
    (hnonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
      (a * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * (2 + θZ))) :
    (rationalApproxDataBoundaryThreshold a n r δ κ ε ρ θZ θX : ℝ) ≤
      (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
        (a * (n : ℝ) ^ 2 * θZ *
          approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
            ((ε + ρ : ℚ) : ℝ) * (2 + θZ)) + (ρ : ℝ) := by
  simpa only [max_eq_left hnonneg] using
    rationalApproxDataBoundaryThreshold_le a n r δ κ ε ρ θZ θX hρ

/-- After canonical upper rounding, the objective contribution is controlled by the
unrounded energy discrepancy, the fixed-matrix error, and one additional mesh unit. -/
theorem rationalApproxDataEnergyThreshold_sub_add_error_le
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK Ephys : ℝ)
    (hρ : 0 < (ρ : ℝ))
    (hnonneg : 0 ≤ (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
      approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ) * θK) :
    (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) - Ephys +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK ≤
      (E : ℝ) - Ephys + ‖K‖ * (ρ : ℝ) +
        2 * ((n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK) + (ρ : ℝ) := by
  have hthreshold := rationalApproxDataEnergyThreshold_le_add_mesh
    n E κ ε ρ K θK hρ hnonneg
  linarith

/-- Without a sign assumption on the unrounded objective threshold, the same estimate
holds with its nonnegative part.  This is the form used for Hamiltonians whose energy
origin has not been fixed. -/
theorem rationalApproxDataEnergyThreshold_sub_add_error_le_max
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK Ephys : ℝ)
    (hρ : 0 < (ρ : ℝ)) :
    (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) - Ephys +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK ≤
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * θK) 0 + (ρ : ℝ) - Ephys +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK := by
  have hthreshold := rationalApproxDataEnergyThreshold_le n E κ ε ρ K θK hρ
  linarith

/-- The boundary error produced by the canonical rational threshold is bounded solely
in terms of the unrounded residual, the rational mesh, and the two fixed-data errors. -/
theorem rationalApproxDataBoundaryTotalError_le
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) (hρ : 0 < (ρ : ℝ))
    (hnonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (a * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * (2 + θZ))) :
    ((((r : ℚ) ^ 2 * rationalApproxDataBoundaryThreshold
          a n r δ κ ε ρ θZ θX : ℚ) : ℝ)) +
        (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
          (a * (n : ℝ) ^ 2 * θZ * approxSDPDensityEntryBound n
            ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * (2 + θZ)) ≤
      (r : ℝ) ^ 2 * ((δ : ℝ) + 3 * (ρ : ℝ) +
        (((r : ℝ) ^ 2 + 1) * θX) + ((r : ℝ) ^ 2 + 1) *
          (a * (n : ℝ) ^ 2 * θZ * approxSDPDensityEntryBound n
            ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * (2 + θZ))) := by
  have hthreshold := rationalApproxDataBoundaryThreshold_le_add_mesh
    a n r δ κ ε ρ θZ θX hρ hnonneg
  norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at *
  nlinarith [sq_nonneg (r : ℝ)]

/-- The canonical input height of approximation codes is bounded by the corresponding
three grid heights and the exact heights of the two rational shifts. -/
theorem rationalCompressedSDPInputCodeHeight_le_approximationCodeHeight
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (QZ : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode (s × b) (s × b))
    (RK RX θZ θK θX : ℝ) (ε εb : ℚ)
    (hZ : QZ.height ≤ rationalBoundedMatrixGridHeight 1 θZ)
    (hK : QK.height ≤ rationalBoundedMatrixGridHeight RK θK)
    (hX : QX.height ≤ rationalBoundedMatrixGridHeight RX θX) :
    rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
      rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb := by
  unfold rationalCompressedSDPInputCodeHeight
  unfold rationalCompressedSDPApproximationCodeHeight
  omega

/-- Simultaneous rational approximation of the three physical fixed matrices, stated
directly in the code representation used by the executable search.  Besides the three
entrywise error bounds, the conclusion controls the canonical common input height. -/
theorem exists_rational_fixed_data_codes_with_common_height
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {RK RX θZ θK θX : ℝ} (ε εb : ℚ) (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
            rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb ∧
          (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
          (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
          ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX := by
  obtain ⟨QZ, QK, QX, hQZheight, hQKheight, hQXheight,
      hQZclose, hQKclose, hQXclose⟩ :=
    exists_rational_fixed_data_codes_with_height Z hZ K X hRK hRX
      hθZ hθK hθX hK hX
  refine ⟨QZ, QK, QX, ?_, hQZclose, hQKclose, hQXclose⟩
  exact rationalCompressedSDPInputCodeHeight_le_approximationCodeHeight
    QZ QK QX RK RX θZ θK θX ε εb hQZheight hQKheight hQXheight

/-- Arbitrary bounded physical fixed data admit a complete rational encoding.  The
coordinate map, objective, and boundary center retain explicit entrywise approximation
witnesses, while the two spectral shifts are chosen as positive rational numbers below
their prescribed targets. -/
theorem exists_rational_compressedSDPInputEncoding
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {RK RX θZ θK θX tε tεb : ℝ} (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (htε : 0 < tε) (htεb : 0 < tεb)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    ∃ ε εb : ℝ, 0 < ε ∧ ε ≤ tε ∧ 0 < εb ∧ εb ≤ tεb ∧
      ∃ QZ : Matrix ((a × s) × b) (Fin n) ℂ,
        (∀ i j, ‖(Z - QZ) i j‖ ≤ θZ) ∧
        ∃ QK : Matrix (Fin n) (Fin n) ℂ,
          (∀ i j, ‖(K - QK) i j‖ ≤ θK) ∧
          ∃ QX : Matrix (s × b) (s × b) ℂ,
            (∀ i j, ‖(X - QX) i j‖ ≤ θX) ∧
            Nonempty (RationalCompressedSDPInputEncoding QZ QK QX ε εb) := by
  let ε := rationalPositiveTolerance tε
  let εb := rationalPositiveTolerance tεb
  obtain ⟨QZ, hQZ, hQZclose⟩ := exists_rational_isometry_approximation hθZ Z hZ
  obtain ⟨QK, hQK, hQKclose⟩ :=
    exists_rational_rectangular_approximation hRK hθK K hK
  obtain ⟨QX, hQX, hQXclose⟩ :=
    exists_rational_rectangular_approximation hRX hθX X hX
  let HZ := rationalBoundedMatrixGridHeight 1 θZ
  let HK := rationalBoundedMatrixGridHeight RK θK
  let HX := rationalBoundedMatrixGridHeight RX θX
  let Hε := rationalPositiveToleranceOrder tε + 1
  let Hεb := rationalPositiveToleranceOrder tεb + 1
  let HD := max HZ (max HK (max HX (max Hε Hεb)))
  have hZHD : HZ ≤ HD := le_max_left _ _
  have hKHD : HK ≤ HD := (le_max_left _ _).trans (le_max_right _ _)
  have hXHD : HX ≤ HD :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hεHD : Hε ≤ HD :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hεbHD : Hεb ≤ HD :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨ε, εb, rationalPositiveTolerance_pos tε,
    rationalPositiveTolerance_le htε, rationalPositiveTolerance_pos tεb,
    rationalPositiveTolerance_le htεb, QZ, hQZclose, QK, hQKclose, QX, hQXclose,
    ⟨{
      height := HD
      z_height := hQZ.mono hZHD
      objective_height := hQK.mono hKHD
      boundary_height := hQX.mono hXHD
      densityShift_height :=
        (rationalPositiveTolerance_hasRationalCoordinatesOfHeight tε).mono hεHD
      boundaryShift_height :=
        (rationalPositiveTolerance_hasRationalCoordinatesOfHeight tεb).mono hεbHD }⟩⟩

/-- Rational approximation of a classically selected coordinate isometry extends any
rational objective, boundary target, and spectral shifts to a complete exact input
encoding for the finite tester.  The boundary residual grows by at most `ω`. -/
theorem exists_rational_coordinate_inputEncoding
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (A K : Matrix (Fin n) (Fin n) ℂ) (X P N : Matrix (s × b) (s × b) ℂ)
    (ε εb : ℝ) {HK HX Hε Hεb : ℕ} {ω ζ : ℝ} (hω : 0 < ω)
    (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ)
    (hK : Matrix.HasRationalEntriesOfHeight HK K)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ)) :
    ∃ Q : Matrix ((a × s) × b) (Fin n) ℂ,
      Nonempty (RationalCompressedSDPInputEncoding Q K X ε εb) ∧
      ∀ i j, ‖((compressedBoundaryLM Q A - X) - (P - N)) i j‖ ≤ ζ + ω := by
  obtain ⟨Q, hQ, hQresidual⟩ :=
    exists_rational_coordinate_map_with_boundary_allowance Z hZ A X P N hω hA hresidual
  let HQ := rationalBoundedMatrixGridHeight 1
    (rationalCoordinateMapTolerance (Fintype.card a) n ω)
  let HD := max HQ (max HK (max HX (max Hε Hεb)))
  have hQHD : HQ ≤ HD := le_max_left _ _
  have hKHD : HK ≤ HD := (le_max_left _ _).trans (le_max_right _ _)
  have hXHD : HX ≤ HD :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hεHD : Hε ≤ HD :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hεbHD : Hεb ≤ HD :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨Q, ⟨{
    height := HD
    z_height := hQ.mono hQHD
    objective_height := hK.mono hKHD
    boundary_height := hX.mono hXHD
    densityShift_height := hε.mono hεHD
    boundaryShift_height := hεb.mono hεbHD }⟩, hQresidual⟩

/-- Number of rational scalar coordinates in the fixed compressed input: two per
complex entry of `Z`, `K`, and `X`, and two for each spectral shift. -/
def compressedSDPInputRationalCoordinateCount (a n r : ℕ) : ℕ :=
  2 * ((a * r) * n + n ^ 2 + r ^ 2 + 2)

/-- The explicit coordinate map alone contributes two rational scalar coordinates for
each of its `a r n` complex entries. -/
theorem coordinateMapRationalCoordinateCount_le_compressedSDPInput
    (a n r : ℕ) :
    2 * ((a * r) * n) ≤ compressedSDPInputRationalCoordinateCount a n r := by
  unfold compressedSDPInputRationalCoordinateCount
  omega

/-- The compressed-input coordinate count is monotone in all three matrix orders. -/
theorem compressedSDPInputRationalCoordinateCount_mono
    {a a' n n' r r' : ℕ} (ha : a ≤ a') (hn : n ≤ n') (hr : r ≤ r') :
    compressedSDPInputRationalCoordinateCount a n r ≤
      compressedSDPInputRationalCoordinateCount a' n' r' := by
  unfold compressedSDPInputRationalCoordinateCount
  gcongr

/-- Bit-size bound for a compressed input whose rational coordinates have height at
most `H`. -/
def compressedSDPInputBitSizeBound (a n r H : ℕ) : ℕ :=
  compressedSDPInputRationalCoordinateCount a n r * (Nat.log2 H + 1)

/-- The bit-size bound dominates the number of rational scalar coordinates even at the
smallest possible height. -/
theorem compressedSDPInputRationalCoordinateCount_le_bitSizeBound
    (a n r H : ℕ) :
    compressedSDPInputRationalCoordinateCount a n r ≤
      compressedSDPInputBitSizeBound a n r H := by
  unfold compressedSDPInputBitSizeBound
  nth_rewrite 1 [← Nat.mul_one (compressedSDPInputRationalCoordinateCount a n r)]
  exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))

/-- Any explicit encoding covered by this model has bit-size at least the number of
rational scalar coordinates in the coordinate map. -/
theorem coordinateMapRationalCoordinateCount_le_compressedSDPInputBitSizeBound
    (a n r H : ℕ) :
    2 * ((a * r) * n) ≤ compressedSDPInputBitSizeBound a n r H :=
  (coordinateMapRationalCoordinateCount_le_compressedSDPInput a n r).trans
    (compressedSDPInputRationalCoordinateCount_le_bitSizeBound a n r H)

/-- The compressed rational input-size bound is monotone in its common coordinate
height. -/
theorem compressedSDPInputBitSizeBound_mono_height
    (a n r : ℕ) {H H' : ℕ} (hH : H ≤ H') :
    compressedSDPInputBitSizeBound a n r H ≤
      compressedSDPInputBitSizeBound a n r H' := by
  unfold compressedSDPInputBitSizeBound
  apply Nat.mul_le_mul_left
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (b := 2) hH) 1

/-- An exponential bound on rational-coordinate height gives a linear bound on the
number of bits per rational coordinate. -/
theorem compressedSDPInputBitSizeBound_le_of_height_le_two_pow
    (a n r H p : ℕ) (hH : H ≤ 2 ^ p) :
    compressedSDPInputBitSizeBound a n r H ≤
      compressedSDPInputRationalCoordinateCount a n r * (p + 1) := by
  unfold compressedSDPInputBitSizeBound
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  rw [Nat.log2_eq_log_two]
  calc
    Nat.log 2 H ≤ Nat.log 2 (2 ^ p) := Nat.log_mono_right hH
    _ = p := Nat.log_pow (by omega) p

/-- If all three matrix orders are at most `M`, the compressed input has at most
`2(M³ + 2M² + 2)` rational scalar coordinates. -/
theorem compressedSDPInputRationalCoordinateCount_le_of_order_bounds
    {a n r M : ℕ} (ha : a ≤ M) (hn : n ≤ M) (hr : r ≤ M) :
    compressedSDPInputRationalCoordinateCount a n r ≤
      2 * (M ^ 3 + 2 * M ^ 2 + 2) := by
  have harn : (a * r) * n ≤ M ^ 3 := by
    calc
      (a * r) * n ≤ (M * M) * M := Nat.mul_le_mul (Nat.mul_le_mul ha hr) hn
      _ = M ^ 3 := by ring
  have hn2 : n ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hn 2
  have hr2 : r ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hr 2
  unfold compressedSDPInputRationalCoordinateCount
  omega

/-- Polynomial matrix orders and exponentially bounded coordinate height give the
corresponding explicit polynomial compressed-input bit-size bound. -/
theorem compressedSDPInputBitSizeBound_le_of_order_and_height_bounds
    {a n r H M p : ℕ} (ha : a ≤ M) (hn : n ≤ M) (hr : r ≤ M)
    (hH : H ≤ 2 ^ p) :
    compressedSDPInputBitSizeBound a n r H ≤
      2 * (M ^ 3 + 2 * M ^ 2 + 2) * (p + 1) := by
  exact (compressedSDPInputBitSizeBound_le_of_height_le_two_pow a n r H p hH).trans
    (Nat.mul_le_mul_right (p + 1)
      (compressedSDPInputRationalCoordinateCount_le_of_order_bounds ha hn hr))

/-- Rational scalar-coordinate count for the structured compressed input.  The support
isometry is encoded by its `n m |S|` expansion coefficients rather than by all of its
ambient matrix entries. -/
def structuredCompressedSDPInputRationalCoordinateCount
    (S : Finset (LeftBlockVector L q k)) (m n r : ℕ) : ℕ :=
  2 * (boundarySupportCoordinateCoefficientCount S m n + n ^ 2 + r ^ 2 + 2)

/-- Bit-size bound for a structured compressed input whose rational coordinates have
common height at most `H`. -/
def structuredCompressedSDPInputBitSizeBound
    (S : Finset (LeftBlockVector L q k)) (m n r H : ℕ) : ℕ :=
  structuredCompressedSDPInputRationalCoordinateCount S m n r * (Nat.log2 H + 1)

/-- A rational encoding of the compressed input in support coordinates.  The ambient
isometry is represented by the coefficients of its bond slices in the retained family
`S`; the remaining data are the objective, boundary center, and two spectral shifts.

This is the arithmetic datum implicit in LVV13, `algo53.tex`, equation `eq:conv`,
lines 472--476.  Its height is kept explicit because a finite spanning family alone does
not control the conditioning of its coordinate map. -/
structure RationalStructuredCompressedSDPInputEncoding
    (S : Finset (LeftBlockVector L q k)) (m n r : ℕ)
    (c : Fin n → Fin m → S → ℂ) (K : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin r) (Fin r) ℂ) (ε εb : ℝ) where
  height : ℕ
  coefficient_height : ∀ j a s, HasRationalComplexCoordinatesOfHeight height (c j a s)
  objective_height : Matrix.HasRationalEntriesOfHeight height K
  boundary_height : Matrix.HasRationalEntriesOfHeight height X
  densityShift_height : HasRationalComplexCoordinatesOfHeight height (ε : ℂ)
  boundaryShift_height : HasRationalComplexCoordinatesOfHeight height (εb : ℂ)

/-- Canonical common height obtained from separate bounds on the five parts of a
structured compressed input. -/
def rationalStructuredCompressedSDPInputHeight
    (Hc HK HX Hε Hεb : ℕ) : ℕ :=
  max Hc (max HK (max HX (max Hε Hεb)))

/-- A common exponential bound on the five component heights bounds their canonical
maximum by the same exponential. -/
theorem rationalStructuredCompressedSDPInputHeight_le_two_pow
    {Hc HK HX Hε Hεb p : ℕ} (hc : Hc ≤ 2 ^ p) (hK : HK ≤ 2 ^ p)
    (hX : HX ≤ 2 ^ p) (hε : Hε ≤ 2 ^ p) (hεb : Hεb ≤ 2 ^ p) :
    rationalStructuredCompressedSDPInputHeight Hc HK HX Hε Hεb ≤ 2 ^ p := by
  simp only [rationalStructuredCompressedSDPInputHeight, max_le_iff]
  exact ⟨hc, hK, hX, hε, hεb⟩

/-- Separate rational-height bounds assemble into a structured compressed-input
encoding at their canonical common maximum. -/
def rationalStructuredCompressedSDPInputEncodingOfHeightBounds
    (S : Finset (LeftBlockVector L q k)) {m n r : ℕ}
    (c : Fin n → Fin m → S → ℂ) (K : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin r) (Fin r) ℂ) (ε εb : ℝ)
    {Hc HK HX Hε Hεb : ℕ}
    (hc : ∀ j a s, HasRationalComplexCoordinatesOfHeight Hc (c j a s))
    (hK : Matrix.HasRationalEntriesOfHeight HK K)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ)) :
    RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb where
  height := rationalStructuredCompressedSDPInputHeight Hc HK HX Hε Hεb
  coefficient_height j a s := (hc j a s).mono (le_max_left _ _)
  objective_height := hK.mono <| (le_max_left _ _).trans (le_max_right _ _)
  boundary_height := hX.mono <|
    (le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  densityShift_height := hε.mono <|
    (le_max_left _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _)
  boundaryShift_height := hεb.mono <|
    (le_max_right _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _)

/-- A bounded finite array of support coefficients admits an entrywise
Gaussian-rational approximation with the same explicit height bound as a rectangular
matrix.  This supplies rational structured coordinates without expanding the ambient
left Hilbert space. -/
theorem exists_rational_boundarySupportCoordinateCoefficientApproximation
    (S : Finset (LeftBlockVector L q k)) {m n : ℕ}
    (c : Fin n → Fin m → S → ℂ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hc : ∀ j a s, ‖c j a s‖ ≤ R) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a s, HasRationalComplexCoordinatesOfHeight
        (rationalBoundedMatrixGridHeight R δ) (qc j a s)) ∧
      ∀ j a s, ‖c j a s - qc j a s‖ ≤ δ := by
  let C : Matrix (Fin n) (Fin m × S) ℂ := fun j as ↦ c j as.1 as.2
  obtain ⟨Q, hQ, hclose⟩ :=
    exists_rational_rectangular_approximation hR hδ C fun j as ↦ hc j as.1 as.2
  let qc : Fin n → Fin m → S → ℂ := fun j a s ↦ Q j (a, s)
  refine ⟨qc, ?_, ?_⟩
  · intro j a s
    exact hQ j (a, s)
  · intro j a s
    change ‖(C - Q) j (a, s)‖ ≤ δ
    exact hclose j (a, s)

/-- Entrywise approximation of support coefficients changes each reconstructed vector
by at most the support cardinality times the coefficient error and the uniform norm
bound on the retained vectors. -/
theorem norm_boundarySupportCoordinate_sum_sub_le
    (S : Finset (LeftBlockVector L q k)) (c qc : S → ℂ) {R δ : ℝ}
    (hδ : 0 ≤ δ) (hS : ∀ s : S, ‖s.1‖ ≤ R)
    (hclose : ∀ s : S, ‖c s - qc s‖ ≤ δ) :
    ‖(∑ s : S, c s • s.1) - ∑ s : S, qc s • s.1‖ ≤ S.card * δ * R := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ s : S, (c s • s.1 - qc s • s.1)‖ ≤
        ∑ s : S, ‖c s • s.1 - qc s • s.1‖ := norm_sum_le _ _
    _ ≤ ∑ _s : S, δ * R := by
      apply Finset.sum_le_sum
      intro s _hs
      rw [← sub_smul, norm_smul]
      exact mul_le_mul (hclose s) (hS s) (norm_nonneg _) hδ
    _ = S.card * δ * R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

/-- Rational approximation of a bounded support-coordinate array changes every bond
slice by at most `|S| δ R`, where `R` bounds both the coefficient array and the norms
of the retained vectors. -/
theorem exists_rational_boundarySupportCoordinateApproximation
    (S : Finset (LeftBlockVector L q k)) {m n : ℕ}
    (c : Fin n → Fin m → S → ℂ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hc : ∀ j a s, ‖c j a s‖ ≤ R) (hS : ∀ s : S, ‖s.1‖ ≤ R) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a s, HasRationalComplexCoordinatesOfHeight
        (rationalBoundedMatrixGridHeight R δ) (qc j a s)) ∧
      ∀ j a,
        ‖(∑ s : S, c j a s • s.1) - ∑ s : S, qc j a s • s.1‖ ≤
          S.card * δ * R := by
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinateCoefficientApproximation S c hR hδ hc
  refine ⟨qc, hqc, ?_⟩
  intro j a
  exact norm_boundarySupportCoordinate_sum_sub_le S (c j a) (qc j a) hδ.le hS
    (hclose j a)

/-- Every support isometry admits rational support coordinates at any positive mesh.
The finite bound `R` controls both the chosen exact coefficients and the retained
vectors; the reconstructed bond slices therefore have error at most `|S| δ R`.

This is the unconditional rational-approximation step behind the structured LVV input.
A polynomial runtime statement additionally requires a polynomial bound on `R`. -/
theorem exists_rational_boundarySupportCoordinates
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a s, HasRationalComplexCoordinatesOfHeight
        (rationalBoundedMatrixGridHeight R δ) (qc j a s)) ∧
      ∀ j a,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
          ∑ s : S, qc j a s • s.1‖ ≤ S.card * δ * R := by
  classical
  obtain ⟨c, hc⟩ := exists_boundarySupportCoordinateCoefficients S m Z hZ hZZ
  obtain ⟨Rc, hRc⟩ :=
    Finite.exists_le (fun x : Fin n × Fin m × S ↦ ‖c x.1 x.2.1 x.2.2‖)
  obtain ⟨Rs, hRs⟩ := Finite.exists_le (fun s : S ↦ ‖s.1‖)
  let R := max 0 (max Rc Rs)
  have hR : 0 ≤ R := le_max_left _ _
  have hcR : ∀ j a s, ‖c j a s‖ ≤ R := by
    intro j a s
    exact (hRc (j, a, s)).trans <| (le_max_left _ _).trans (le_max_right _ _)
  have hSR : ∀ s : S, ‖s.1‖ ≤ R := by
    intro s
    exact (hRs s).trans <| (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinateApproximation S c hR hδ hcR hSR
  refine ⟨R, hR, qc, hqc, ?_⟩
  intro j a
  rw [← hc j a]
  exact hclose j a

/-- The coordinate radius for a support isometry may be chosen before the rational
mesh.  Thus one fixed finite number `R` controls rational approximations at every
positive precision.  Polynomial control of this `R`, rather than its dependence on the
mesh, is the remaining conditioning issue in the iterative LVV algorithm. -/
theorem exists_boundarySupportCoordinateRadius
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {mesh : ℝ}, 0 < mesh →
      ∃ qc : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (qc j a s)) ∧
        ∀ j a,
          ‖WithLp.toLp 2 (fun x ↦
              gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
            ∑ s : S, qc j a s • s.1‖ ≤ S.card * mesh * R := by
  classical
  obtain ⟨c, hc⟩ := exists_boundarySupportCoordinateCoefficients S m Z hZ hZZ
  obtain ⟨Rc, hRc⟩ :=
    Finite.exists_le (fun x : Fin n × Fin m × S ↦ ‖c x.1 x.2.1 x.2.2‖)
  obtain ⟨Rs, hRs⟩ := Finite.exists_le (fun s : S ↦ ‖s.1‖)
  let R := max 0 (max Rc Rs)
  have hR : 0 ≤ R := le_max_left _ _
  have hcR : ∀ j a s, ‖c j a s‖ ≤ R := by
    intro j a s
    exact (hRc (j, a, s)).trans <| (le_max_left _ _).trans (le_max_right _ _)
  have hSR : ∀ s : S, ‖s.1‖ ≤ R := by
    intro s
    exact (hRs s).trans <| (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R, hR, ?_⟩
  intro mesh hmesh
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinateApproximation S c hR hmesh hcR hSR
  refine ⟨qc, hqc, ?_⟩
  intro j a
  rw [← hc j a]
  exact hclose j a

/-- Fixing one coordinate in a Euclidean vector on a finite product cannot increase its
norm. -/
theorem norm_euclidean_prod_slice_le
    {α β : Type*} [Fintype α] [Fintype β]
    (u : EuclideanSpace ℂ (α × β)) (b : β) :
    ‖(WithLp.toLp 2 (fun a ↦ u (a, b)) : EuclideanSpace ℂ α)‖ ≤ ‖u‖ := by
  have hsingle := Finset.single_le_sum
    (fun b _ ↦ sq_nonneg
      ‖(WithLp.toLp 2 (fun a ↦ u (a, b)) : EuclideanSpace ℂ α)‖)
    (Finset.mem_univ b)
  have hsum :
      ∑ b : β, ‖(WithLp.toLp 2 (fun a ↦ u (a, b)) : EuclideanSpace ℂ α)‖ ^ 2 =
        ‖u‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑ b, ∑ a, ‖u (a, b)‖ ^ 2) = ∑ p, ‖u p‖ ^ 2
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hsum] at hsingle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
    (by norm_num : 2 ≠ 0)).mp hsingle

/-- Decode support coefficients into the ambient matrix whose bond slices are the
corresponding linear combinations of retained left vectors. -/
noncomputable def boundarySupportMatrixOfCoordinates
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) :
    Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ :=
  fun p j ↦ ∑ s : S, c j p.2 s * s.1
    ((Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
      (leftBlock_mono (Nat.sub_le k 1))).symm p.1)

/-- A uniform norm error on every reconstructed bond slice gives the same entrywise
error for the decoded ambient support matrix. -/
theorem norm_boundarySupportMatrixOfCoordinates_sub_apply_le
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (c : Fin n → Fin m → S → ℂ) {θ : ℝ}
    (h : ∀ j a,
      ‖WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
        ∑ s : S, c j a s • s.1‖ ≤ θ) :
    ∀ p j, ‖(Z - boundarySupportMatrixOfCoordinates S m c) p j‖ ≤ θ := by
  intro p j
  let x := (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
    (leftBlock_mono (Nat.sub_le k 1))).symm p.1
  let e : LeftBlockVector L q k :=
    WithLp.toLp 2 (fun y ↦
        gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (y, p.2)) -
      ∑ s : S, c j p.2 s • s.1
  calc
    ‖(Z - boundarySupportMatrixOfCoordinates S m c) p j‖ = ‖e x‖ := by
      simp [e, x, boundarySupportMatrixOfCoordinates, gluingLeftCoordinates,
        Matrix.sub_apply, Matrix.col, Finset.sum_apply]
    _ ≤ ‖e‖ := PiLp.norm_apply_le e x
    _ ≤ θ := h j p.2

/-! ### Finite parameter spaces for rational MPS approximation -/

namespace OBCChainTensor

/-- The finite index of all local tensor entries of one open-boundary chain with fixed
virtual dimensions. -/
abbrev ParameterIndex {D n : ℕ} (A : OBCChainTensor q D n) :=
  Σ p : Fin n,
    Fin q × Fin (A.bondDim p.castSucc) × Fin (A.bondDim p.succ)

/-- The finite complex parameter space of local tensor entries. -/
abbrev Parameters {D n : ℕ} (A : OBCChainTensor q D n) :=
  ParameterIndex A → ℂ

/-- A scalar and fixed-bond local tensor entries, all with rational real and imaginary
parts. -/
abbrev RationalParameters {D n : ℕ} (A : OBCChainTensor q D n) :=
  RationalComplex × (ParameterIndex A → RationalComplex)

/-- Forget the rationality certificates on a fixed-bond parameter point. -/
def rationalParametersVal {D n : ℕ} (A : OBCChainTensor q D n)
    (P : RationalParameters A) : ℂ × Parameters A :=
  Prod.map Subtype.val (Pi.map fun _ ↦ Subtype.val) P

/-- Rational fixed-bond parameter points are dense in the full complex parameter
space. -/
theorem denseRange_rationalParametersVal {D n : ℕ} (A : OBCChainTensor q D n) :
    DenseRange (rationalParametersVal A) := by
  have hpi : DenseRange
      (Pi.map fun _ : ParameterIndex A ↦ ((↑) : RationalComplex → ℂ)) :=
    DenseRange.piMap fun _ ↦ denseRange_rationalComplex_val
  have hprod := denseRange_rationalComplex_val.prodMap hpi
  exact hprod

/-- A uniformly bounded scalar and fixed-bond tensor parameter point has a
simultaneous dyadic approximation with one explicit coordinate-height bound. -/
theorem exists_dyadic_parameters_approximation {D n : ℕ}
    (A : OBCChainTensor q D n) {R : ℝ} {u t : ℕ}
    (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (P : ℂ × Parameters A) (hscalar : ‖P.1‖ ≤ R)
    (htensor : ∀ e, ‖P.2 e‖ ≤ R) :
    ∃ Q : ℂ × Parameters A,
      HasRationalComplexCoordinatesOfHeight (2 ^ (2 * u + 2 * t + 5)) Q.1 ∧
      (∀ e, HasRationalComplexCoordinatesOfHeight
        (2 ^ (2 * u + 2 * t + 5)) (Q.2 e)) ∧
      ‖P.1 - Q.1‖ ≤ (2 ^ t : ℝ)⁻¹ ∧
      ∀ e, ‖P.2 e - Q.2 e‖ ≤ (2 ^ t : ℝ)⁻¹ := by
  let f : Unit ⊕ ParameterIndex A → ℂ := fun e ↦
    match e with
    | Sum.inl _ => P.1
    | Sum.inr e => P.2 e
  have hf : ∀ e, ‖f e‖ ≤ R := by
    intro e
    cases e with
    | inl e => exact hscalar
    | inr e => exact htensor e
  obtain ⟨g, hgheight, hgclose⟩ :=
    exists_dyadic_rational_pi_approximation hR0 hR f hf
  let Q : ℂ × Parameters A := (g (Sum.inl ()), fun e ↦ g (Sum.inr e))
  refine ⟨Q, hgheight (Sum.inl ()), fun e ↦ hgheight (Sum.inr e), ?_, fun e ↦ ?_⟩
  · exact hgclose (Sum.inl ())
  · exact hgclose (Sum.inr e)

/-- Rebuild an open-boundary chain with the same virtual dimensions from its local
tensor-entry parameters. -/
def ofParameters {D n : ℕ} (A : OBCChainTensor q D n) (P : Parameters A) :
    OBCChainTensor q D n where
  bondDim := A.bondDim
  bondDim_le := A.bondDim_le
  left_dim := A.left_dim
  right_dim := A.right_dim
  tensor p i a c := P ⟨p, i, a, c⟩

/-- The local-entry parameters of an open-boundary chain. -/
def parameters {D n : ℕ} (A : OBCChainTensor q D n) : Parameters A :=
  fun e ↦ A.tensor e.1 e.2.1 e.2.2.1 e.2.2.2

@[simp]
theorem ofParameters_parameters {D n : ℕ} (A : OBCChainTensor q D n) :
    ofParameters A (parameters A) = A := by
  cases A
  rfl

/-- Entrywise perturbation of fixed-bond tensor parameters changes each contracted
physical coefficient by at most the number of virtual paths times the elementary
product perturbation bound. -/
theorem norm_coeff_ofParameters_sub_le_one {D n : ℕ}
    (A : OBCChainTensor q D n) (P Q : Parameters A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : ∀ e, ‖Q e‖ ≤ 1) (hclose : ∀ e, ‖P e - Q e‖ ≤ δ)
    (σ : Fin n → Fin q) :
    ‖(ofParameters A P).coeff σ - (ofParameters A Q).coeff σ‖ ≤
      Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
        ((1 + δ) ^ n - 1) := by
  classical
  unfold OBCChainTensor.coeff
  change ‖(∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
      ∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩) -
    ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
      ∏ p : Fin n, Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
        ((∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩) -
          ∏ p : Fin n, Q ⟨p, σ p, α p.castSucc, α p.succ⟩)‖ ≤
        ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
          ‖(∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩) -
            ∏ p : Fin n, Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _α : (p : Fin (n + 1)) → Fin (A.bondDim p),
          ((1 + δ) ^ n - 1) := by
      apply Finset.sum_le_sum
      intro α _hα
      simpa using norm_finset_prod_sub_prod_le_one Finset.univ
        (fun p : Fin n ↦ P ⟨p, σ p, α p.castSucc, α p.succ⟩)
        (fun p : Fin n ↦ Q ⟨p, σ p, α p.castSucc, α p.succ⟩)
        hδ (fun p _hp ↦ hQ ⟨p, σ p, α p.castSucc, α p.succ⟩)
        (fun p _hp ↦ hclose ⟨p, σ p, α p.castSucc, α p.succ⟩)
    _ = Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
          ((1 + δ) ^ n - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- If reference tensor entries have norm at most one and the perturbed entries
are `δ`-close, then every perturbed contraction is bounded by the number of
virtual paths times `(1 + δ)^n`. -/
theorem norm_coeff_ofParameters_le_one_add {D n : ℕ}
    (A : OBCChainTensor q D n) (P Q : Parameters A) {δ : ℝ}
    (hQ : ∀ e, ‖Q e‖ ≤ 1) (hclose : ∀ e, ‖P e - Q e‖ ≤ δ)
    (σ : Fin n → Fin q) :
    ‖(ofParameters A P).coeff σ‖ ≤
      Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) * (1 + δ) ^ n := by
  classical
  unfold OBCChainTensor.coeff
  change ‖∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
      ∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ ≤ _
  calc
    ‖∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
        ∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ ≤
      ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
        ‖∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ := norm_sum_le _ _
    _ ≤ ∑ _α : (p : Fin (n + 1)) → Fin (A.bondDim p), (1 + δ) ^ n := by
      apply Finset.sum_le_sum
      intro α _hα
      calc
        ‖∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ ≤
            ∏ p : Fin n, ‖P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ := Finset.norm_prod_le _ _
        _ ≤ ∏ _p : Fin n, (1 + δ) := by
          apply Finset.prod_le_prod₀ (fun p _hp ↦ norm_nonneg _)
          intro p _hp
          calc
            ‖P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ =
                ‖(P ⟨p, σ p, α p.castSucc, α p.succ⟩ -
                    Q ⟨p, σ p, α p.castSucc, α p.succ⟩) +
                  Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ := by ring_nf
            _ ≤ ‖P ⟨p, σ p, α p.castSucc, α p.succ⟩ -
                    Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ +
                  ‖Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ := norm_add_le _ _
            _ ≤ δ + 1 := add_le_add (hclose _) (hQ _)
            _ = 1 + δ := by ring
        _ = (1 + δ) ^ n := by simp
    _ = Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) * (1 + δ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Simultaneously perturbing a unit-bounded scalar cap and unit-bounded tensor
entries changes each represented physical coefficient by the path count times
`(1 + δ)^(n+1) - 1`. -/
theorem norm_scalar_mul_coeff_ofParameters_sub_le_one {D n : ℕ}
    (A : OBCChainTensor q D n) (P Q : ℂ × Parameters A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQscalar : ‖Q.1‖ ≤ 1) (hQ : ∀ e, ‖Q.2 e‖ ≤ 1)
    (hscalarclose : ‖P.1 - Q.1‖ ≤ δ) (hclose : ∀ e, ‖P.2 e - Q.2 e‖ ≤ δ)
    (σ : Fin n → Fin q) :
    ‖P.1 * (ofParameters A P.2).coeff σ - Q.1 * (ofParameters A Q.2).coeff σ‖ ≤
      Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
        ((1 + δ) ^ (n + 1) - 1) := by
  have hcoeffP := norm_coeff_ofParameters_le_one_add A P.2 Q.2 hQ hclose σ
  have hcoeffdiff := norm_coeff_ofParameters_sub_le_one A P.2 Q.2 hδ hQ hclose σ
  have hpow : 0 ≤ (1 + δ) ^ n - 1 := by
    have : 1 ≤ (1 + δ) ^ n := one_le_pow₀ (by linarith)
    linarith
  calc
    ‖P.1 * (ofParameters A P.2).coeff σ - Q.1 * (ofParameters A Q.2).coeff σ‖ =
        ‖(P.1 - Q.1) * (ofParameters A P.2).coeff σ +
          Q.1 * ((ofParameters A P.2).coeff σ - (ofParameters A Q.2).coeff σ)‖ := by
      congr 1
      ring
    _ ≤ ‖P.1 - Q.1‖ * ‖(ofParameters A P.2).coeff σ‖ +
        ‖Q.1‖ * ‖(ofParameters A P.2).coeff σ - (ofParameters A Q.2).coeff σ‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ δ * (Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) * (1 + δ) ^ n) +
        1 * (Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
          ((1 + δ) ^ n - 1)) := by gcongr
    _ = Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
        ((1 + δ) ^ (n + 1) - 1) := by rw [pow_succ]; ring

/-- At a fixed physical configuration, contraction is continuous in all local tensor
entries. -/
theorem continuous_coeff_ofParameters {D n : ℕ} (A : OBCChainTensor q D n)
    (σ : Fin n → Fin q) :
    Continuous (fun P : Parameters A ↦ (ofParameters A P).coeff σ) := by
  unfold OBCChainTensor.coeff
  change Continuous (fun P : Parameters A ↦
    ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
      ∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩)
  refine continuous_finsetSum
    (Finset.univ : Finset ((p : Fin (n + 1)) → Fin (A.bondDim p))) fun α _hα ↦ ?_
  refine continuous_finsetProd (Finset.univ : Finset (Fin n)) fun p _hp ↦ ?_
  exact continuous_apply _

/-- Contraction with an additional scalar is continuous in the scalar and all local
tensor entries. -/
theorem continuous_scalar_mul_coeff_ofParameters {D n : ℕ} (A : OBCChainTensor q D n)
    (σ : Fin n → Fin q) :
    Continuous (fun P : ℂ × Parameters A ↦ P.1 * (ofParameters A P.2).coeff σ) :=
  continuous_fst.mul ((continuous_coeff_ofParameters A σ).comp continuous_snd)

/-- Contract scalar and local-tensor parameters to a vector on the first `n` sites.
The hypothesis `n ≤ L` identifies physical configurations with `Fin n` words. -/
noncomputable def vectorOfParameters {D n : ℕ} (A : OBCChainTensor q D n)
    (hn : n ≤ L) (P : ℂ × Parameters A) : LeftBlockVector L q n :=
  WithLp.toLp 2 fun x ↦
    P.1 * (ofParameters A P.2).coeff ((leftConfigOfFinEquiv hn).symm x)

/-- A simultaneous `δ`-perturbation of unit-bounded fixed-bond parameters changes
the represented left-block vector by at most the number of physical configurations
times the virtual-path and product perturbation bounds. -/
theorem norm_vectorOfParameters_sub_le_one {D n : ℕ}
    (A : OBCChainTensor q D n) (hn : n ≤ L)
    (P Q : ℂ × Parameters A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQscalar : ‖Q.1‖ ≤ 1) (hQ : ∀ e, ‖Q.2 e‖ ≤ 1)
    (hscalarclose : ‖P.1 - Q.1‖ ≤ δ) (hclose : ∀ e, ‖P.2 e - Q.2 e‖ ≤ δ) :
    ‖vectorOfParameters (L := L) A hn P - vectorOfParameters (L := L) A hn Q‖ ≤
      (q ^ n : ℝ) * Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
        ((1 + δ) ^ (n + 1) - 1) := by
  let C : ℝ := Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
    ((1 + δ) ^ (n + 1) - 1)
  have hpow : 0 ≤ (1 + δ) ^ (n + 1) - 1 := by
    have : 1 ≤ (1 + δ) ^ (n + 1) := one_le_pow₀ (by linarith)
    linarith
  have hC : 0 ≤ C := mul_nonneg (by positivity) hpow
  have hbound := PiLp.norm_le_card_mul_of_forall_norm_le
    (vectorOfParameters (L := L) A hn P - vectorOfParameters (L := L) A hn Q)
    hC
    (fun x ↦ by
      change ‖P.1 * (ofParameters A P.2).coeff ((leftConfigOfFinEquiv hn).symm x) -
        Q.1 * (ofParameters A Q.2).coeff ((leftConfigOfFinEquiv hn).symm x)‖ ≤ C
      exact norm_scalar_mul_coeff_ofParameters_sub_le_one A P Q hδ hQscalar hQ
        hscalarclose hclose ((leftConfigOfFinEquiv hn).symm x))
  simpa only [C, Entropy.RegionConfig, Fintype.card_pi, Fintype.card_fin,
    Fintype.card_coe, card_leftBlock, min_eq_right hn, Finset.prod_const, Finset.card_univ,
    Nat.cast_mul, Nat.cast_pow, mul_assoc] using hbound

/-- Finite open-boundary tensor contraction is continuous as a map into the complete
Euclidean left-block vector, not merely coordinatewise. -/
theorem continuous_vectorOfParameters {D n : ℕ} (A : OBCChainTensor q D n)
    (hn : n ≤ L) :
    Continuous (vectorOfParameters (L := L) A hn) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro x
  exact continuous_scalar_mul_coeff_ofParameters A ((leftConfigOfFinEquiv hn).symm x)

/-- On fixed virtual spaces, rational scalar and local-tensor entries approximate the
contracted left-block vector arbitrarily well. -/
theorem exists_rational_parameters_close {D n : ℕ} (A : OBCChainTensor q D n)
    (hn : n ≤ L) (P : ℂ × Parameters A) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℂ × Parameters A,
      HasRationalComplexCoordinates Q.1 ∧
      (∀ e, HasRationalComplexCoordinates (Q.2 e)) ∧
      ‖vectorOfParameters (L := L) A hn P - vectorOfParameters (L := L) A hn Q‖ < ε := by
  have hpre :
      vectorOfParameters (L := L) A hn ⁻¹'
          Metric.ball (vectorOfParameters (L := L) A hn P) ε ∈ nhds P :=
    (continuous_vectorOfParameters A hn).continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds _ hε)
  obtain ⟨R, hR⟩ := (denseRange_rationalParametersVal A).mem_nhds hpre
  let Q : ℂ × Parameters A := rationalParametersVal A R
  refine ⟨Q, R.1.2, fun e ↦ (R.2 e).2, ?_⟩
  have hdist :
      dist (vectorOfParameters (L := L) A hn Q)
        (vectorOfParameters (L := L) A hn P) < ε := by
    simpa [Q] using hR
  rw [dist_comm] at hdist
  simpa [dist_eq_norm] using hdist

end OBCChainTensor

/-- Evaluating the scalar and local-entry parameters of an explicit left-open MPS
representation recovers its represented vector. -/
theorem LeftOpenMPSRepresentation.vectorOfParameters_eq {b k : ℕ}
    {v : LeftBlockVector L q k} (R : LeftOpenMPSRepresentation b v) (hk : k ≤ L) :
    OBCChainTensor.vectorOfParameters (L := L) R.tensor hk
      (R.scalar, OBCChainTensor.parameters R.tensor) = v := by
  ext x
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  change R.scalar * R.tensor.coeff y = v x
  calc
    R.scalar * R.tensor.coeff y = v (leftConfigOfFin y) := (R.coeff_eq y).symm
    _ = v x := congrArg v ((leftConfigOfFinEquiv hk).apply_symm_apply x)

/-- A normalized positive-length left-open MPS has an equivalent representation
with scalar cap one and every local tensor entry of norm at most one, without
increasing any virtual bond dimension. -/
theorem LeftOpenMPSRepresentation.exists_unitBounded_of_norm_eq_one
    {b n : ℕ} {v : LeftBlockVector L q (n + 1)}
    (R : LeftOpenMPSRepresentation b v) (hk : n + 1 ≤ L) (hv : ‖v‖ = 1) :
    ∃ R' : LeftOpenMPSRepresentation b v,
      R'.scalar = 1 ∧ ∀ p i a c, ‖R'.tensor.tensor p i a c‖ ≤ 1 := by
  let B := R.tensor.smulSite (0 : Fin (n + 1)) R.scalar
  have hBcoeff : B.coeff = fun x ↦ v (leftConfigOfFin x) := by
    funext x
    change (R.tensor.smulSite (0 : Fin (n + 1)) R.scalar).coeff x = _
    rw [congrFun (OBCChainTensor.coeff_smulSite
      R.tensor (0 : Fin (n + 1)) R.scalar) x]
    change R.scalar * R.tensor.coeff x = v (leftConfigOfFin x)
    exact (R.coeff_eq x).symm
  have hBnorm : star B.coeff ⬝ᵥ B.coeff = 1 := by
    let w : EuclideanSpace ℂ (Fin (n + 1) → Fin q) := WithLp.toLp 2 B.coeff
    have hw : ‖w‖ = 1 := by
      have hiso := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (leftConfigOfFinEquiv hk).symm).norm_map v
      have hw_eq : w =
          LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (leftConfigOfFinEquiv hk).symm v := by
        ext x
        change B.coeff x = v (leftConfigOfFin x)
        exact congrFun hBcoeff x
      rw [hw_eq, hiso, hv]
    calc
      star B.coeff ⬝ᵥ B.coeff = B.coeff ⬝ᵥ star B.coeff := dotProduct_comm _ _
      _ = inner ℂ w w := by
        simpa only [w, WithLp.ofLp_toLp] using
          (EuclideanSpace.inner_eq_star_dotProduct w w).symm
      _ = (‖w‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K w
      _ = 1 := by rw [hw]; norm_num
  obtain ⟨B', hcoeff, hbond, hiso⟩ := B.exists_isometric_coeff_eq_of_norm hBnorm
  let R' : LeftOpenMPSRepresentation b v :=
    { tensor := B'
      scalar := 1
      internal_bondDim_le := fun k hk0 hkn ↦
        (hbond k).trans (R.internal_bondDim_le k hk0 hkn)
      coeff_eq := fun x ↦ by
        rw [one_mul]
        calc
          v (leftConfigOfFin x) = B.coeff x := (congrFun hBcoeff x).symm
          _ = B'.coeff x := (congrFun hcoeff x).symm }
  refine ⟨R', rfl, ?_⟩
  intro p i a c
  exact norm_apply_le_one_of_sum_conjTranspose_mul_eq_one
    (fun i ↦ B'.tensor p i) (hiso p) i a c

/-- Explicit left-open MPS data whose scalar and every local tensor entry have rational
real and imaginary parts.  This is the arithmetic information about retained vectors
that is not contained in `IsLeftOpenMPS`. -/
structure RationalLeftOpenMPSRepresentation (b : ℕ) {k : ℕ}
    (v : LeftBlockVector L q k) where
  tensor : OBCChainTensor q (max 1 (max 1 b)) k
  scalar : ℂ
  internal_bondDim_le : ∀ p, 0 < p.val → p.val < k → tensor.bondDim p ≤ max 1 b
  coeff_eq : ∀ x, v (leftConfigOfFin x) = scalar * tensor.coeff x
  scalar_rational : HasRationalComplexCoordinates scalar
  tensor_rational : ∀ p i a c,
    HasRationalComplexCoordinates (tensor.tensor p i a c)

namespace RationalLeftOpenMPSRepresentation

/-- Evaluating the canonical scalar and local-entry parameters of a rational MPS
representation recovers its represented left-block vector. -/
theorem vectorOfParameters_eq {b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) (hk : k ≤ L) :
    OBCChainTensor.vectorOfParameters (L := L) R.tensor hk
      (R.scalar, OBCChainTensor.parameters R.tensor) = v := by
  ext x
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  change R.scalar * R.tensor.coeff y = v x
  calc
    R.scalar * R.tensor.coeff y = v (leftConfigOfFin y) := (R.coeff_eq y).symm
    _ = v x := congrArg v ((leftConfigOfFinEquiv hk).apply_symm_apply x)

/-- Forgetting rationality retains the explicit left-open MPS representation. -/
def representation {b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) : LeftOpenMPSRepresentation b v where
  tensor := R.tensor
  scalar := R.scalar
  internal_bondDim_le := R.internal_bondDim_le
  coeff_eq := R.coeff_eq

/-- Rational scalar and local-entry parameters on fixed virtual spaces give an explicit
rational left-open MPS representation. -/
noncomputable def ofParameters {b k : ℕ} {v : LeftBlockVector L q k}
    (R : LeftOpenMPSRepresentation b v) (hk : k ≤ L)
    (P : ℂ × OBCChainTensor.Parameters R.tensor)
    (hscalar : HasRationalComplexCoordinates P.1)
    (htensor : ∀ e, HasRationalComplexCoordinates (P.2 e)) :
    RationalLeftOpenMPSRepresentation b
      (OBCChainTensor.vectorOfParameters (L := L) R.tensor hk P) where
  tensor := OBCChainTensor.ofParameters R.tensor P.2
  scalar := P.1
  internal_bondDim_le := R.internal_bondDim_le
  coeff_eq := by
    intro x
    change P.1 * (OBCChainTensor.ofParameters R.tensor P.2).coeff
      ((leftConfigOfFinEquiv hk).symm (leftConfigOfFin x)) =
        P.1 * (OBCChainTensor.ofParameters R.tensor P.2).coeff x
    have hx : (leftConfigOfFinEquiv (q := q) hk).symm (leftConfigOfFin x) = x :=
      (leftConfigOfFinEquiv hk).symm_apply_apply x
    rw [hx]
  scalar_rational := hscalar
  tensor_rational := by
    intro p i a c
    exact htensor ⟨p, i, a, c⟩

/-- Appending one site preserves rationality of every local tensor entry. -/
theorem tensor_snoc_rational {D n : ℕ} (A : OBCChainTensor q D n) (f : Fin q → ℂ)
    (hA : ∀ p i a c, HasRationalComplexCoordinates (A.tensor p i a c))
    (hf : ∀ i, HasRationalComplexCoordinates (f i)) :
    ∀ p i a c, HasRationalComplexCoordinates ((A.snoc f).tensor p i a c) := by
  intro p
  refine Fin.lastCases ?_ (fun p' ↦ ?_) p
  · intro i a c
    simp only [OBCChainTensor.snoc, Fin.lastCases_last]
    change HasRationalComplexCoordinates (f i)
    exact hf i
  · intro i a c
    simp only [OBCChainTensor.snoc, Fin.lastCases_castSucc]
    change HasRationalComplexCoordinates (A.tensor p' i _ _)
    exact hA p' i _ _

/-- Every physical coefficient represented by rational open-chain tensor data is a
Gaussian rational complex number. -/
theorem coordinate_rational {b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) (hk : k ≤ L)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinates (v x) := by
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  have hxy : leftConfigOfFin y = x := (leftConfigOfFinEquiv hk).apply_symm_apply x
  rw [← hxy]
  rw [R.coeff_eq]
  apply R.scalar_rational.mul
  unfold OBCChainTensor.coeff
  apply HasRationalComplexCoordinates.fintype_sum
  intro path
  apply HasRationalComplexCoordinates.fintype_prod
  intro p
  exact R.tensor_rational p
    (y p)
    (path p.castSucc) (path p.succ)

/-- Forgetting arithmetic information recovers the mathematical MPS predicate. -/
theorem isLeftOpenMPS {b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) : IsLeftOpenMPS b v :=
  R.representation.isLeftOpenMPS

/-- Appending a computational-basis site preserves rational open-chain tensor data. -/
noncomputable def extendSite {i b : ℕ} (hi0 : 0 < i) (hiL : i ≤ L)
    {v : LeftBlockVector L q (i - 1)}
    (R : RationalLeftOpenMPSRepresentation b v) (k : Fin q) :
    RationalLeftOpenMPSRepresentation b (AreaLaw.extendSite i k v) := by
  cases i with
  | zero => omega
  | succ n =>
      simp only [Nat.succ_sub_one] at v R ⊢
      let f : Fin q → ℂ := fun y ↦ if y = k then 1 else 0
      let rep := R.representation.snoc
        (lt_of_lt_of_le Nat.one_pos (le_max_left 1 b)) f
      refine
        { tensor := R.tensor.snoc f
          scalar := R.scalar
          internal_bondDim_le := rep.internal_bondDim_le
          coeff_eq := fun x ↦ ?_
          scalar_rational := R.scalar_rational
          tensor_rational := tensor_snoc_rational R.tensor f R.tensor_rational (fun y ↦ ?_) }
      · have heq : (fun x ↦ AreaLaw.extendSite (n + 1) k v (leftConfigOfFin x)) =
            (fun x ↦ v (leftConfigOfFin (Fin.init x)) * f (x (Fin.last n))) := by
          funext y
          rw [extendSite_apply hi0 hiL, mul_ite, mul_one, mul_zero]
          rfl
        rw [congrFun heq x]
        exact rep.coeff_eq x
      · dsimp only [f]
        split_ifs
        · exact HasRationalComplexCoordinates.one
        · exact HasRationalComplexCoordinates.zero

end RationalLeftOpenMPSRepresentation

/-- Every left-open matrix product state admits arbitrarily accurate rational tensor
data on the same virtual spaces, and hence with the same bond bound. -/
theorem IsLeftOpenMPS.exists_rational_approximation {b k : ℕ}
    {v : LeftBlockVector L q k} (hv : IsLeftOpenMPS b v) (hk : k ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : LeftBlockVector L q k,
      Nonempty (RationalLeftOpenMPSRepresentation b w) ∧ ‖v - w‖ ≤ ε := by
  obtain ⟨R⟩ := (isLeftOpenMPS_iff_nonempty_representation b v).mp hv
  let P : ℂ × OBCChainTensor.Parameters R.tensor :=
    (R.scalar, OBCChainTensor.parameters R.tensor)
  obtain ⟨Q, hQscalar, hQtensor, hclose⟩ :=
    OBCChainTensor.exists_rational_parameters_close R.tensor hk P hε
  let w := OBCChainTensor.vectorOfParameters (L := L) R.tensor hk Q
  refine ⟨w, ⟨RationalLeftOpenMPSRepresentation.ofParameters R hk Q hQscalar hQtensor⟩, ?_⟩
  rw [← R.vectorOfParameters_eq hk]
  exact le_of_lt hclose

/-- The number of dependent virtual paths of an open chain of length `n` and bond
budget `D` is at most `D^(n+1)`. -/
theorem OBCChainTensor.virtualPath_card_le {D n : ℕ} (A : OBCChainTensor q D n) :
    Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) ≤ D ^ (n + 1) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    ∏ p : Fin (n + 1), A.bondDim p ≤ ∏ _p : Fin (n + 1), D := by
      exact Finset.prod_le_prod fun p _hp ↦ A.bondDim_le p
    _ = D ^ (n + 1) := by simp

/-- Rational open-chain tensor data with one common coordinate-height bound. -/
structure RationalLeftOpenMPSRepresentationOfHeight (H b : ℕ) {k : ℕ}
    (v : LeftBlockVector L q k) where
  data : RationalLeftOpenMPSRepresentation b v
  scalar_height : HasRationalComplexCoordinatesOfHeight H data.scalar
  tensor_height : ∀ p i a c,
    HasRationalComplexCoordinatesOfHeight H (data.tensor.tensor p i a c)

namespace RationalLeftOpenMPSRepresentationOfHeight

/-- Height-bounded scalar and local-entry parameters on fixed virtual spaces give a
height-bounded rational left-open MPS representation. -/
noncomputable def ofParameters {H b k : ℕ} {v : LeftBlockVector L q k}
    (R : LeftOpenMPSRepresentation b v) (hk : k ≤ L)
    (P : ℂ × OBCChainTensor.Parameters R.tensor)
    (hscalar : HasRationalComplexCoordinatesOfHeight H P.1)
    (htensor : ∀ e, HasRationalComplexCoordinatesOfHeight H (P.2 e)) :
    RationalLeftOpenMPSRepresentationOfHeight H b
      (OBCChainTensor.vectorOfParameters (L := L) R.tensor hk P) where
  data := RationalLeftOpenMPSRepresentation.ofParameters R hk P hscalar.forget
    (fun e ↦ (htensor e).forget)
  scalar_height := hscalar
  tensor_height := by
    intro p i a c
    exact htensor ⟨p, i, a, c⟩

end RationalLeftOpenMPSRepresentationOfHeight

/-- A normalized positive-length left-open MPS admits a dyadic rational
approximation of the same bond bound, with explicit common parameter height and
an explicit full-vector error bound. -/
theorem IsLeftOpenMPS.exists_dyadic_rational_approximation_of_norm_eq_one
    {b n : ℕ} {v : LeftBlockVector L q (n + 1)}
    (hv : IsLeftOpenMPS b v) (hk : n + 1 ≤ L) (hvnorm : ‖v‖ = 1) (t : ℕ) :
    ∃ w : LeftBlockVector L q (n + 1),
      Nonempty (RationalLeftOpenMPSRepresentationOfHeight
        (2 ^ (2 * t + 5)) b w) ∧
      ‖v - w‖ ≤ (q ^ (n + 1) : ℝ) *
        (max 1 (max 1 b) : ℝ) ^ (n + 2) *
          ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) := by
  obtain ⟨R⟩ := (isLeftOpenMPS_iff_nonempty_representation b v).mp hv
  obtain ⟨R', hR'scalar, hR'tensor⟩ :=
    R.exists_unitBounded_of_norm_eq_one hk hvnorm
  let P₀ : ℂ × OBCChainTensor.Parameters R'.tensor :=
    (R'.scalar, OBCChainTensor.parameters R'.tensor)
  have hP₀scalar : ‖P₀.1‖ ≤ (1 : ℝ) := by simp [P₀, hR'scalar]
  have hP₀tensor : ∀ e, ‖P₀.2 e‖ ≤ (1 : ℝ) := by
    intro e
    exact hR'tensor e.1 e.2.1 e.2.2.1 e.2.2.2
  obtain ⟨P, hPscalar, hPtensor, hPscalarClose, hPtensorClose⟩ :=
    OBCChainTensor.exists_dyadic_parameters_approximation R'.tensor
      (u := 0) (t := t) zero_le_one (by norm_num) P₀ hP₀scalar hP₀tensor
  let w := OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P
  have hscalarClose : ‖P.1 - P₀.1‖ ≤ (2 ^ t : ℝ)⁻¹ := by
    simpa only [norm_sub_rev] using hPscalarClose
  have htensorClose : ∀ e, ‖P.2 e - P₀.2 e‖ ≤ (2 ^ t : ℝ)⁻¹ := by
    intro e
    simpa only [norm_sub_rev] using hPtensorClose e
  have hδ : 0 ≤ (2 ^ t : ℝ)⁻¹ := by positivity
  have herr := OBCChainTensor.norm_vectorOfParameters_sub_le_one R'.tensor hk P P₀
    hδ hP₀scalar hP₀tensor hscalarClose htensorClose
  have hfactor : 0 ≤ (q ^ (n + 1) : ℝ) *
      ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) := by
    have hone : 1 ≤ (1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) :=
      one_le_pow₀ (by linarith)
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hone)
  refine ⟨w, ⟨?_⟩, ?_⟩
  · simpa [w] using
      RationalLeftOpenMPSRepresentationOfHeight.ofParameters R' hk P hPscalar hPtensor
  · have hpath := OBCChainTensor.virtualPath_card_le R'.tensor
    have hscaled := mul_le_mul_of_nonneg_left (show
      (Fintype.card ((p : Fin (n + 1 + 1)) → Fin (R'.tensor.bondDim p)) : ℝ) ≤
        (max 1 (max 1 b) : ℝ) ^ (n + 2) by exact_mod_cast hpath) hfactor
    have hfinal := herr.trans (by
      calc
        (q ^ (n + 1) : ℝ) *
            Fintype.card ((p : Fin (n + 1 + 1)) → Fin (R'.tensor.bondDim p)) *
              ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) =
            ((q ^ (n + 1) : ℝ) *
              ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1)) *
                Fintype.card ((p : Fin (n + 1 + 1)) → Fin (R'.tensor.bondDim p)) := by ring
        _ ≤ ((q ^ (n + 1) : ℝ) *
              ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1)) *
                (max 1 (max 1 b) : ℝ) ^ (n + 2) := hscaled
        _ = (q ^ (n + 1) : ℝ) * (max 1 (max 1 b) : ℝ) ^ (n + 2) *
              ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) := by ring)
    calc
      ‖v - w‖ =
          ‖OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P₀ -
            OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P‖ := by
              rw [R'.vectorOfParameters_eq hk]
      _ = ‖OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P -
            OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P₀‖ := norm_sub_rev _ _
      _ ≤ _ := hfinal

/-- Contracting a height-bounded rational open chain gives an explicit height bound.
The outer exponent is the number of dependent virtual paths, while `productHeight`
accounts for the product of the `n` local tensor entries along each path. -/
theorem OBCChainTensor.coeff_height {D n H : ℕ} (A : OBCChainTensor q D n)
    (hA : ∀ p i a c,
      HasRationalComplexCoordinatesOfHeight H (A.tensor p i a c))
    (σ : Fin n → Fin q) :
    HasRationalComplexCoordinatesOfHeight
      ((2 * HasRationalComplexCoordinatesOfHeight.productHeight H n) ^
        Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)))
      (A.coeff σ) := by
  rw [OBCChainTensor.coeff]
  apply HasRationalComplexCoordinatesOfHeight.finset_sum
  intro α _hα
  simpa using HasRationalComplexCoordinatesOfHeight.finset_prod
    (s := Finset.univ) (fun p _hp ↦ hA p (σ p) (α p.castSucc) (α p.succ))

namespace RationalLeftOpenMPSRepresentationOfHeight

/-- Uniform physical-coordinate height bound obtained from a local height `H`, a bond
budget `b`, and a chain length `k`. -/
def coordinateHeightBound (H b k : ℕ) : ℕ :=
  let HP := HasRationalComplexCoordinatesOfHeight.productHeight H k
  let HC := (2 * HP) ^ ((max 1 (max 1 b)) ^ (k + 1))
  2 * (H * HC) * (H * HC)

/-- Every physical coefficient represented by height-bounded rational open-chain data
has an explicit coordinate-height bound. -/
theorem coordinate_height {H b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    let HC :=
      (2 * HasRationalComplexCoordinatesOfHeight.productHeight H k) ^
        Fintype.card ((p : Fin (k + 1)) → Fin (R.data.tensor.bondDim p))
    HasRationalComplexCoordinatesOfHeight (2 * (H * HC) * (H * HC)) (v x) := by
  dsimp only
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  have hxy : leftConfigOfFin y = x := (leftConfigOfFinEquiv hk).apply_symm_apply x
  rw [← hxy, R.data.coeff_eq]
  exact R.scalar_height.mul
    (OBCChainTensor.coeff_height R.data.tensor R.tensor_height y)

/-- The preceding coefficient bound depends only on the advertised local height, bond
budget, and chain length, rather than on the varying internal bond dimensions. -/
theorem coordinate_height_le {H b k : ℕ} (hH : 0 < H)
    {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight (coordinateHeightBound H b k) (v x) := by
  let HP := HasRationalComplexCoordinatesOfHeight.productHeight H k
  let HC := (2 * HP) ^
    Fintype.card ((p : Fin (k + 1)) → Fin (R.data.tensor.bondDim p))
  have hx : HasRationalComplexCoordinatesOfHeight (2 * (H * HC) * (H * HC)) (v x) :=
    R.coordinate_height hk x
  apply hx.mono
  dsimp only [coordinateHeightBound, HC, HP]
  have hbase : 0 < 2 * HasRationalComplexCoordinatesOfHeight.productHeight H k := by
    exact Nat.mul_pos (by omega)
      (HasRationalComplexCoordinatesOfHeight.productHeight_pos hH k)
  have hpow := Nat.pow_le_pow_right hbase
    (OBCChainTensor.virtualPath_card_le R.data.tensor)
  have hterm := Nat.mul_le_mul_left H hpow
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul hterm hterm)

/-- Height-one rational tensor data for the scalar basis vector at the empty cut. -/
noncomputable def emptyLeftVector (L q : ℕ) :
    RationalLeftOpenMPSRepresentationOfHeight 1 1 (AreaLaw.emptyLeftVector L q) := by
  let A : OBCChainTensor q 1 0 :=
    { bondDim := fun _ ↦ 1
      bondDim_le := fun _ ↦ le_rfl
      left_dim := rfl
      right_dim := rfl
      tensor := fun p ↦ p.elim0 }
  let R : RationalLeftOpenMPSRepresentation 1 (AreaLaw.emptyLeftVector L q) :=
    { tensor := A
      scalar := 1
      internal_bondDim_le := fun p hp hp' ↦ by omega
      coeff_eq := fun x ↦ by simp [AreaLaw.emptyLeftVector, A]
      scalar_rational := HasRationalComplexCoordinates.one
      tensor_rational := fun p ↦ p.elim0 }
  exact
    { data := R
      scalar_height := HasRationalComplexCoordinatesOfHeight.one
      tensor_height := fun p ↦ p.elim0 }

/-- Appending one site whose entries have height at most `H` preserves the same tensor
entry height bound. -/
theorem tensor_snoc_height {D n H : ℕ} (A : OBCChainTensor q D n) (f : Fin q → ℂ)
    (hA : ∀ p i a c, HasRationalComplexCoordinatesOfHeight H (A.tensor p i a c))
    (hf : ∀ i, HasRationalComplexCoordinatesOfHeight H (f i)) :
    ∀ p i a c, HasRationalComplexCoordinatesOfHeight H ((A.snoc f).tensor p i a c) := by
  intro p
  refine Fin.lastCases ?_ (fun p' ↦ ?_) p
  · intro i a c
    simp only [OBCChainTensor.snoc, Fin.lastCases_last]
    change HasRationalComplexCoordinatesOfHeight H (f i)
    exact hf i
  · intro i a c
    simp only [OBCChainTensor.snoc, Fin.lastCases_castSucc]
    change HasRationalComplexCoordinatesOfHeight H (A.tensor p' i _ _)
    exact hA p' i _ _

/-- Computational-basis extension preserves a common height bound `H ≥ 1`. -/
noncomputable def extendSite {H i b : ℕ} (hH : 1 ≤ H) (hi0 : 0 < i) (hiL : i ≤ L)
    {v : LeftBlockVector L q (i - 1)}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (k : Fin q) :
    RationalLeftOpenMPSRepresentationOfHeight H b (AreaLaw.extendSite i k v) := by
  cases i with
  | zero => omega
  | succ n =>
      simp only [Nat.succ_sub_one] at v R ⊢
      let f : Fin q → ℂ := fun y ↦ if y = k then 1 else 0
      let data := R.data.extendSite hi0 hiL k
      refine ⟨data, ?_, ?_⟩
      · change HasRationalComplexCoordinatesOfHeight H R.data.scalar
        exact R.scalar_height
      · change ∀ p i a c,
          HasRationalComplexCoordinatesOfHeight H ((R.data.tensor.snoc f).tensor p i a c)
        apply tensor_snoc_height R.data.tensor f R.tensor_height
        intro y
        dsimp only [f]
        split_ifs
        · exact HasRationalComplexCoordinatesOfHeight.one.mono hH
        · exact HasRationalComplexCoordinatesOfHeight.zero.mono hH

end RationalLeftOpenMPSRepresentationOfHeight

/-- A viable family carrying rational open-chain tensor data for every retained vector. -/
structure RationalViableMPSData
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ)
    {i : ℕ} (S : Finset (LeftBlockVector L q i)) where
  card_le : S.card ≤ s
  representation : ∀ v : S, RationalLeftOpenMPSRepresentation b v.1
  viable : IsViable Γ δ (S : Set (LeftBlockVector L q i))

namespace RationalViableMPSData

/-- Forgetting rationality gives the ordinary data-bearing viable-family invariant. -/
def viableMPSData
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalViableMPSData Γ s b δ S) : ViableMPSData Γ s b δ S where
  card_le := D.card_le
  representation v := (D.representation v).representation
  viable := D.viable

/-- The one-site LVV extension preserves rational tensor data for the whole viable
family.  As in `ViableMPSData.extend`, choice is used only to select a finite preimage
pair of an already constructed image member. -/
noncomputable def extend
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q (i - 1))}
    (D : RationalViableMPSData Γ s b δ S) (hi0 : 0 < i) (hiL : i ≤ L) :
    RationalViableMPSData Γ (q * s) b δ (AreaLaw.extend i S) where
  card_le := (card_extend_le i S).trans (Nat.mul_le_mul_left q D.card_le)
  representation w := by
    classical
    have hp : ∃ p : S × Fin q, AreaLaw.extendSite i p.2 p.1.1 = w.1 := by
      unfold AreaLaw.extend at w
      obtain ⟨v, hv, k, -, hvk⟩ := Finset.mem_image₂.mp w.2
      exact ⟨⟨⟨v, hv⟩, k⟩, hvk⟩
    let p := Classical.choose hp
    have hp_eq := Classical.choose_spec hp
    rw [← hp_eq]
    exact (D.representation p.1).extendSite hi0 hiL p.2
  viable := D.viable.extend hi0 hiL

end RationalViableMPSData

/-- A viable family whose retained tensors and endpoint scalars share the coordinate
height bound `H`. -/
structure RationalViableMPSDataOfHeight (H : ℕ)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ)
    {i : ℕ} (S : Finset (LeftBlockVector L q i)) where
  card_le : S.card ≤ s
  representation : ∀ v : S, RationalLeftOpenMPSRepresentationOfHeight H b v.1
  viable : IsViable Γ δ (S : Set (LeftBlockVector L q i))

namespace RationalViableMPSDataOfHeight

/-- The scalar singleton at the empty cut carries height-one rational data and is
`δ`-viable for every unit target whenever `δ ≥ 0`. -/
noncomputable def emptyLeftVector
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (hΓ : ‖Γ‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    RationalViableMPSDataOfHeight 1 Γ 1 1 δ
      ({AreaLaw.emptyLeftVector L q} : Finset (LeftBlockVector L q 0)) where
  card_le := by simp
  representation v := by
    convert RationalLeftOpenMPSRepresentationOfHeight.emptyLeftVector L q using 1
    exact Finset.mem_singleton.mp v.2
  viable := by
    obtain ⟨w, hw, hoverlap, hsupport⟩ := (isViableMPS_emptyLeftVector hΓ).2.2
    exact ⟨w, hw, by linarith, hsupport⟩

/-- Forgetting heights retains the rational viable-family invariant. -/
def rationalViableMPSData
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalViableMPSDataOfHeight H Γ s b δ S) :
    RationalViableMPSData Γ s b δ S where
  card_le := D.card_le
  representation v := (D.representation v).data
  viable := D.viable

/-- The one-site LVV extension preserves a common rational coordinate height bound
`H ≥ 1` for the entire viable family. -/
noncomputable def extend
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q (i - 1))}
    (D : RationalViableMPSDataOfHeight H Γ s b δ S) (hH : 1 ≤ H)
    (hi0 : 0 < i) (hiL : i ≤ L) :
    RationalViableMPSDataOfHeight H Γ (q * s) b δ (AreaLaw.extend i S) where
  card_le := (card_extend_le i S).trans (Nat.mul_le_mul_left q D.card_le)
  representation w := by
    classical
    have hp : ∃ p : S × Fin q, AreaLaw.extendSite i p.2 p.1.1 = w.1 := by
      unfold AreaLaw.extend at w
      obtain ⟨v, hv, k, -, hvk⟩ := Finset.mem_image₂.mp w.2
      exact ⟨⟨⟨v, hv⟩, k⟩, hvk⟩
    let p := Classical.choose hp
    have hp_eq := Classical.choose_spec hp
    rw [← hp_eq]
    exact (D.representation p.1).extendSite hH hi0 hiL p.2
  viable := D.viable.extend hi0 hiL

end RationalViableMPSDataOfHeight

/-- A viable MPS family whose physical coefficients are rational with one uniform
height bound.  Unlike `RationalViableMPSDataOfHeight`, this invariant does not require
an expanded open-boundary tensor for every retained vector.  It is therefore stable
under the compact rational linear-combination encoding used by LVV size trimming.

This is the representation invariant needed between successive iterations of
LVV13, `algo53.tex`, lines 379--400 and 472--527. -/
structure RationalCoordinateViableMPSDataOfHeight (H : ℕ)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ)
    {i : ℕ} (S : Finset (LeftBlockVector L q i)) where
  card_le : S.card ≤ s
  isLeftOpenMPS : ∀ v : S, IsLeftOpenMPS b v.1
  coordinate_height : ∀ v : S,
    ∀ x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i),
      HasRationalComplexCoordinatesOfHeight H (v.1 x)
  viable : IsViable Γ δ (S : Set (LeftBlockVector L q i))

namespace RationalCoordinateViableMPSDataOfHeight

/-- Forgetting coordinate rationality gives the ordinary viable-MPS predicate. -/
theorem isViableMPS
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalCoordinateViableMPSDataOfHeight H Γ s b δ S) :
    IsViableMPS Γ s b δ S :=
  ⟨D.card_le, fun v hv ↦ D.isLeftOpenMPS ⟨v, hv⟩, D.viable⟩

/-- Explicit height-bounded rational tensor data yield the coordinate form of the
iteration invariant. -/
theorem ofRationalViableMPSData
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)} (hH : 0 < H) (hiL : i ≤ L)
    (D : RationalViableMPSDataOfHeight H Γ s b δ S) :
    RationalCoordinateViableMPSDataOfHeight
      (RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound H b i)
      Γ s b δ S where
  card_le := D.card_le
  isLeftOpenMPS v := (D.representation v).data.isLeftOpenMPS
  coordinate_height v x := (D.representation v).coordinate_height_le hH hiL x
  viable := D.viable

/-- The one-site LVV extension preserves a uniform rational physical-coordinate
height bound.  The appended computational-basis coordinate is either the old
coefficient or zero. -/
theorem extend
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q (i - 1))}
    (D : RationalCoordinateViableMPSDataOfHeight H Γ s b δ S)
    (hH : 1 ≤ H) (hi0 : 0 < i) (hiL : i ≤ L) :
    RationalCoordinateViableMPSDataOfHeight H Γ (q * s) b δ (AreaLaw.extend i S) where
  card_le := (card_extend_le i S).trans (Nat.mul_le_mul_left q D.card_le)
  isLeftOpenMPS w := by
    classical
    obtain ⟨v, hv, k, _hk, hw⟩ := Finset.mem_image₂.mp w.2
    rw [← hw]
    exact (D.isLeftOpenMPS ⟨v, hv⟩).extendSite hi0 hiL k
  coordinate_height w x := by
    classical
    obtain ⟨v, hv, k, _hk, hw⟩ := Finset.mem_image₂.mp w.2
    rw [← hw]
    rw [extendSite_apply hi0 hiL]
    split_ifs
    · exact D.coordinate_height ⟨v, hv⟩ (restrictLeft (Nat.sub_le i 1) x)
    · exact HasRationalComplexCoordinatesOfHeight.zero.mono hH
  viable := D.viable.extend hi0 hiL

/-- Enlarging the permitted overlap error preserves the coordinate-rational
viable-MPS invariant. -/
theorem mono_error
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ δ' : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalCoordinateViableMPSDataOfHeight H Γ s b δ S) (hδ : δ ≤ δ') :
    RationalCoordinateViableMPSDataOfHeight H Γ s b δ' S where
  card_le := D.card_le
  isLeftOpenMPS := D.isLeftOpenMPS
  coordinate_height := D.coordinate_height
  viable := by
    obtain ⟨φ, hφ, hoverlap, hsupport⟩ := D.viable
    exact ⟨φ, hφ, hoverlap.trans' (by linarith), hsupport⟩

/-- Enlarging the advertised coordinate-height bound preserves the viable-MPS
invariant. -/
theorem mono_height
    {H H' : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalCoordinateViableMPSDataOfHeight H Γ s b δ S) (hH : H ≤ H') :
    RationalCoordinateViableMPSDataOfHeight H' Γ s b δ S where
  card_le := D.card_le
  isLeftOpenMPS := D.isLeftOpenMPS
  coordinate_height v x := (D.coordinate_height v x).mono hH
  viable := D.viable

end RationalCoordinateViableMPSDataOfHeight

/-- A compact rational description of one finite output family in the span of a retained
MPS family.  It stores the linear-combination coefficients rather than expanding the
vectors into exponentially many physical coordinates.

This is the data required by the size-trimming step of LVV13, `algo53.tex`, lines
472--478 and 520--527. -/
structure RationalSpanFamilyEncodingOfHeight
    (H : ℕ) (S : Finset (LeftBlockVector L q k))
    (T : Finset (LeftBlockVector L q k)) where
  coefficient : T → S → ℂ
  coefficient_height : ∀ t s,
    HasRationalComplexCoordinatesOfHeight H (coefficient t s)
  linearCombination_eq : ∀ t : T,
    t.1 = ∑ s : S, coefficient t s • s.1

/-- The finite family of all left columns decoded from a structured coefficient array. -/
noncomputable def spanColumnFamily
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) : Finset (LeftBlockVector L q k) :=
  Finset.image₂ (fun j a ↦ ∑ s : S, c j a s • s.1) Finset.univ Finset.univ

/-- A decoded span-column family contains at most `n m` vectors. -/
theorem spanColumnFamily_card_le
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) :
    (spanColumnFamily S m c).card ≤ n * m := by
  unfold spanColumnFamily
  simpa using Finset.card_image₂_le
    (fun j : Fin n ↦ fun a : Fin m ↦ ∑ s : S, c j a s • s.1)
      Finset.univ Finset.univ

/-- Every coefficient slice is represented by its decoded vector in the finite column
family. -/
theorem sum_mem_spanColumnFamily
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) (j : Fin n) (a : Fin m) :
    (∑ s : S, c j a s • s.1) ∈ spanColumnFamily S m c := by
  unfold spanColumnFamily
  exact Finset.mem_image₂.mpr
    ⟨j, Finset.mem_univ j, a, Finset.mem_univ a, rfl⟩

/-- A uniform approximation of coefficient slices becomes an approximation by explicit
members of the decoded finite column family. -/
theorem exists_mem_spanColumnFamily_close
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) (v : Fin n → Fin m → LeftBlockVector L q k)
    {θ : ℝ} (hclose : ∀ j a, ‖v j a - ∑ s : S, c j a s • s.1‖ ≤ θ) :
    ∀ j a, ∃ w ∈ spanColumnFamily S m c, ‖v j a - w‖ ≤ θ := by
  intro j a
  exact ⟨∑ s : S, c j a s • s.1, sum_mem_spanColumnFamily S m c j a,
    hclose j a⟩

/-- Every member of the decoded column family has a coefficient-index preimage. -/
theorem exists_spanColumnFamily_index
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) (t : spanColumnFamily S m c) :
    ∃ p : Fin n × Fin m, ∑ s : S, c p.1 p.2 s • s.1 = t.1 := by
  obtain ⟨j, _hj, a, _ha, hja⟩ := Finset.mem_image₂.mp t.2
  exact ⟨(j, a), hja⟩

/-- Rational structured coefficients canonically equip their decoded column family
with a compact rational span encoding.  A preimage is selected only to resolve duplicate
columns in the finite image. -/
noncomputable def rationalSpanFamilyEncodingOfCoefficients
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n H : ℕ}
    (c : Fin n → Fin m → S → ℂ)
    (hc : ∀ j a s, HasRationalComplexCoordinatesOfHeight H (c j a s)) :
    RationalSpanFamilyEncodingOfHeight H S (spanColumnFamily S m c) where
  coefficient t s :=
    let p := Classical.choose (exists_spanColumnFamily_index S m c t)
    c p.1 p.2 s
  coefficient_height t s := by
    dsimp only
    exact hc _ _ s
  linearCombination_eq t := by
    dsimp only
    exact (Classical.choose_spec (exists_spanColumnFamily_index S m c t)).symm

namespace RationalSpanFamilyEncodingOfHeight

/-- Uniform physical-coordinate height for a rational linear combination of at most
`s` inputs whose physical coordinates have height at most `Hv`. -/
def linearCombinationCoordinateHeight (H Hv s : ℕ) : ℕ :=
  let HM := 2 * (H * Hv) * (H * Hv)
  (2 * HM) ^ s

/-- If coefficient and input-coordinate heights have binary exponents `p` and `v`,
then the physical-coordinate height of a linear combination of at most `s` inputs has
the displayed explicit binary exponent.  This is the one-step height recurrence for a
fully expanded coordinate representation. -/
theorem linearCombinationCoordinateHeight_le_two_pow
    {H Hv p v : ℕ} (hH : H ≤ 2 ^ p) (hHv : Hv ≤ 2 ^ v) (s : ℕ) :
    linearCombinationCoordinateHeight H Hv s ≤
      2 ^ ((2 * p + 2 * v + 2) * s) := by
  unfold linearCombinationCoordinateHeight
  have hprod : H * Hv ≤ (2 ^ p) * (2 ^ v) := Nat.mul_le_mul hH hHv
  have hbase : 2 * (2 * (H * Hv) * (H * Hv)) ≤ 2 ^ (2 * p + 2 * v + 2) := by
    calc
      2 * (2 * (H * Hv) * (H * Hv)) = 4 * (H * Hv) ^ 2 := by ring
      _ ≤ 4 * ((2 ^ p) * (2 ^ v)) ^ 2 := by gcongr
      _ = 2 ^ (2 * p + 2 * v + 2) := by
        rw [← pow_add]
        ring_nf
  calc
    (2 * (2 * (H * Hv) * (H * Hv))) ^ s ≤
        (2 ^ (2 * p + 2 * v + 2)) ^ s := Nat.pow_le_pow_left hbase s
    _ = 2 ^ ((2 * p + 2 * v + 2) * s) := by rw [pow_mul]

/-- Uniform physical-coordinate height of a rational linear combination of a retained
height-bounded MPS family.  This bound is used only when a physical coordinate is
queried; the stored representation remains the compact coefficient array. -/
def outputCoordinateHeight (H Hv b k s : ℕ) : ℕ :=
  linearCombinationCoordinateHeight H
    (RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound Hv b k) s

/-- Number of rational scalar coordinates stored by a compact span-family encoding. -/
def rationalCoordinateCount (S T : Finset (LeftBlockVector L q k)) : ℕ :=
  2 * T.card * S.card

/-- Bit-size bound for the stored rational coefficient array. -/
def coefficientBitSizeBound (H : ℕ)
    (S T : Finset (LeftBlockVector L q k)) : ℕ :=
  rationalCoordinateCount S T * (Nat.log2 H + 1)

/-- Each stored complex coefficient is represented by two rationals of bit length at
most `log₂ H + 1`. -/
theorem coefficient_exists_bitLength_le
    {H : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) (t : T) (s : S) :
    ∃ x y : ℚ, E.coefficient t s = ⟨(x : ℝ), (y : ℝ)⟩ ∧
      rationalBitLength x ≤ Nat.log2 H + 1 ∧
      rationalBitLength y ≤ Nat.log2 H + 1 :=
  (E.coefficient_height t s).exists_bitLength_le

/-- Polynomial cardinality bounds on the input and output families give the expected
quadratic bound on the number of stored rational coordinates. -/
theorem rationalCoordinateCount_le {H s t : ℕ}
    {S T : Finset (LeftBlockVector L q k)}
    (_E : RationalSpanFamilyEncodingOfHeight H S T)
    (hS : S.card ≤ s) (hT : T.card ≤ t) :
    rationalCoordinateCount S T ≤ 2 * t * s := by
  unfold rationalCoordinateCount
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hT) hS

/-- The same family-cardinality bounds control the complete coefficient bit-size. -/
theorem coefficientBitSizeBound_le {H s t : ℕ}
    {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (hS : S.card ≤ s) (hT : T.card ≤ t) :
    coefficientBitSizeBound H S T ≤ 2 * t * s * (Nat.log2 H + 1) := by
  unfold coefficientBitSizeBound
  exact Nat.mul_le_mul_right _ (E.rationalCoordinateCount_le hS hT)

/-- Every encoded output vector belongs to the span of the retained input family. -/
theorem mem_span {H : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) (t : T) :
    t.1 ∈ Submodule.span ℂ (S : Set (LeftBlockVector L q k)) := by
  rw [E.linearCombination_eq t]
  apply Submodule.sum_mem
  intro s _hs
  exact Submodule.smul_mem _ _ (Submodule.subset_span s.2)

/-- The compact span encoding carries the usual finite-span MPS bond bound. -/
theorem isLeftOpenMPS {H b : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (hS : ∀ s ∈ S, IsLeftOpenMPS b s) (t : T) :
    IsLeftOpenMPS (S.card * max 1 b) t.1 :=
  isLeftOpenMPS_of_mem_span S hS (E.mem_span t)

/-- Querying any physical coordinate of an encoded output vector gives a rational
number with a uniform explicit height bound. -/
theorem coordinate_height_of_input
    {H Hv : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (hS : ∀ s : S,
      ∀ x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k),
        HasRationalComplexCoordinatesOfHeight Hv (s.1 x))
    (t : T) (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (linearCombinationCoordinateHeight H Hv S.card) (t.1 x) := by
  rw [E.linearCombination_eq t]
  unfold linearCombinationCoordinateHeight
  simpa using HasRationalComplexCoordinatesOfHeight.finset_sum
    (s := Finset.univ) (fun s _hs ↦ (E.coefficient_height t s).mul (hS s x))

/-- Querying any physical coordinate of an encoded output vector gives a rational
number with a uniform explicit height bound. -/
theorem coordinate_height {H Hv b : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) (hHv : 0 < Hv) (hk : k ≤ L)
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentationOfHeight Hv b s.1)
    (t : T) (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (outputCoordinateHeight H Hv b k S.card) (t.1 x) := by
  exact E.coordinate_height_of_input
    (fun s x ↦ (hS s).coordinate_height_le hHv hk x) t x

/-- In particular, every physical coordinate of the compactly encoded output family is
Gaussian rational. -/
theorem coordinate_rational {H Hv b : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) (hHv : 0 < Hv) (hk : k ≤ L)
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentationOfHeight Hv b s.1)
    (t : T) (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinates (t.1 x) :=
  (E.coordinate_height hHv hk hS t x).forget

/-- A compact rational span encoding transports the coordinate-rational viable-MPS
invariant from its input family to any viable decoded output family. -/
theorem coordinateViableMPSData
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s₀ s b : ℕ} {δ δ' : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δ S)
    (hcard : T.card ≤ s) (hviable : IsViable Γ δ' (T : Set (LeftBlockVector L q k))) :
    RationalCoordinateViableMPSDataOfHeight
      (linearCombinationCoordinateHeight H Hv S.card)
      Γ s (S.card * max 1 b) δ' T where
  card_le := hcard
  isLeftOpenMPS t := E.isLeftOpenMPS
    (fun u hu ↦ D.isLeftOpenMPS ⟨u, hu⟩) t
  coordinate_height t x := E.coordinate_height_of_input D.coordinate_height t x
  viable := hviable

/-- Dyadic-exponent form of the preceding transport theorem.  It records the exact
one-step bit-height recurrence for a fully expanded output coordinate. -/
theorem coordinateViableMPSData_twoPow
    {H Hv p v : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s₀ s b : ℕ}
    {δ δ' : ℝ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δ S)
    (hH : H ≤ 2 ^ p) (hHv : Hv ≤ 2 ^ v)
    (hcard : T.card ≤ s) (hviable : IsViable Γ δ' (T : Set (LeftBlockVector L q k))) :
    RationalCoordinateViableMPSDataOfHeight
      (2 ^ ((2 * p + 2 * v + 2) * S.card))
      Γ s (S.card * max 1 b) δ' T :=
  (E.coordinateViableMPSData D hcard hviable).mono_height
    (linearCombinationCoordinateHeight_le_two_pow hH hHv S.card)

end RationalSpanFamilyEncodingOfHeight

/-- A shared multi-layer rational span representation at one cut.  The zeroth family
is the stored input family, and every later family is represented by rational linear
combinations of the preceding one.  Keeping the intermediate families shared gives a
directed acyclic representation: its storage is the sum of the coefficient arrays,
without expanding any physical coordinate through all preceding layers.

This is the fixed-cut arithmetic representation required when successive LVV size
selection steps are composed; see LVV13, `algo53.tex`, lines 472--527. -/
structure RationalSpanEncodingDAGOfHeight
    (depth : ℕ) (height : Fin depth → ℕ)
    (family : Fin (depth + 1) → Finset (LeftBlockVector L q k)) where
  layer : ∀ i : Fin depth,
    RationalSpanFamilyEncodingOfHeight (height i)
      (family i.castSucc) (family i.succ)

namespace RationalSpanEncodingDAGOfHeight

/-- The number of rational scalar coordinates stored by all coefficient arrays in a
shared span DAG. -/
def rationalCoordinateCount
    {depth : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (_D : RationalSpanEncodingDAGOfHeight depth height family) : ℕ :=
  ∑ i : Fin depth,
    RationalSpanFamilyEncodingOfHeight.rationalCoordinateCount
      (family i.castSucc) (family i.succ)

/-- The coefficient bit-size bound of a shared span DAG is the sum of the bounds for
its layers.  In particular, no flattened physical-coordinate height occurs here. -/
def coefficientBitSizeBound
    {depth : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (_D : RationalSpanEncodingDAGOfHeight depth height family) : ℕ :=
  ∑ i : Fin depth,
    RationalSpanFamilyEncodingOfHeight.coefficientBitSizeBound
      (height i) (family i.castSucc) (family i.succ)

/-- Every vector in a noninitial layer belongs to the span of the immediately
preceding family. -/
theorem mem_span_previous
    {depth : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (D : RationalSpanEncodingDAGOfHeight depth height family)
    (i : Fin depth) (t : family i.succ) :
    t.1 ∈ Submodule.span ℂ
      (family i.castSucc : Set (LeftBlockVector L q k)) :=
  (D.layer i).mem_span t

/-- The span of each noninitial layer is contained in the span of its immediate
predecessor. -/
theorem span_le_previous
    {depth : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (D : RationalSpanEncodingDAGOfHeight depth height family) (i : Fin depth) :
    Submodule.span ℂ (family i.succ : Set (LeftBlockVector L q k)) ≤
      Submodule.span ℂ (family i.castSucc : Set (LeftBlockVector L q k)) := by
  apply Submodule.span_le.mpr
  intro v hv
  exact D.mem_span_previous i ⟨v, hv⟩

/-- If every intermediate family has cardinality at most `s`, then the complete
shared coefficient representation has at most `depth · 2s²` rational scalar
coordinates.  Thus composition is additive in the number of layers. -/
theorem rationalCoordinateCount_le
    {depth s : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (D : RationalSpanEncodingDAGOfHeight depth height family)
    (hcard : ∀ i, (family i).card ≤ s) :
    D.rationalCoordinateCount ≤ depth * (2 * s * s) := by
  unfold rationalCoordinateCount
  calc
    (∑ i : Fin depth,
        RationalSpanFamilyEncodingOfHeight.rationalCoordinateCount
          (family i.castSucc) (family i.succ)) ≤
        ∑ _i : Fin depth, 2 * s * s := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold RationalSpanFamilyEncodingOfHeight.rationalCoordinateCount
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hcard i.succ)) (hcard i.castSucc)
    _ = depth * (2 * s * s) := by simp

/-- If every layer has cardinality at most `s` and coefficient height at most
`2^p`, then the complete shared representation has bit size at most
`depth · 2s²(p+1)`.  The dependence on the number of composed layers is additive. -/
theorem coefficientBitSizeBound_le
    {depth s p : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (D : RationalSpanEncodingDAGOfHeight depth height family)
    (hcard : ∀ i, (family i).card ≤ s) (hheight : ∀ i, height i ≤ 2 ^ p) :
    D.coefficientBitSizeBound ≤ depth * (2 * s * s * (p + 1)) := by
  unfold coefficientBitSizeBound
  calc
    (∑ i : Fin depth,
        RationalSpanFamilyEncodingOfHeight.coefficientBitSizeBound
          (height i) (family i.castSucc) (family i.succ)) ≤
        ∑ _i : Fin depth, 2 * s * s * (p + 1) := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold RationalSpanFamilyEncodingOfHeight.coefficientBitSizeBound
      apply Nat.mul_le_mul
      · unfold RationalSpanFamilyEncodingOfHeight.rationalCoordinateCount
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hcard i.succ)) (hcard i.castSucc)
      · apply Nat.add_le_add_right
        rw [Nat.log2_eq_log_two]
        calc
          Nat.log 2 (height i) ≤ Nat.log 2 (2 ^ p) :=
            Nat.log_mono_right (hheight i)
          _ = p := Nat.log_pow (by omega) p
    _ = depth * (2 * s * s * (p + 1)) := by simp

end RationalSpanEncodingDAGOfHeight

/-- A rational span encoding with explicit finite indices.  Unlike a `Finset` image,
the index types retain multiplicities.  This makes one-site extension functorial:
each node is paired with its computational-basis label, even when two decoded vectors
coincide. -/
structure RationalIndexedSpanEncodingOfHeight
    (H : ℕ) (I J : Type*) [Fintype I] [Fintype J]
    (input : I → LeftBlockVector L q k) (output : J → LeftBlockVector L q k) where
  coefficient : J → I → ℂ
  coefficient_height : ∀ j a,
    HasRationalComplexCoordinatesOfHeight H (coefficient j a)
  linearCombination_eq : ∀ j,
    output j = ∑ a : I, coefficient j a • input a

namespace RationalIndexedSpanEncodingOfHeight

/-- The finite family decoded from an explicitly indexed collection of vectors. -/
noncomputable def decodedFamily {J : Type*} [Fintype J]
    (output : J → LeftBlockVector L q k) : Finset (LeftBlockVector L q k) :=
  Finset.univ.image output

/-- The decoded family has at most as many elements as its finite index type. -/
theorem decodedFamily_card_le {J : Type*} [Fintype J]
    (output : J → LeftBlockVector L q k) :
    (decodedFamily output).card ≤ Fintype.card J := by
  classical
  exact Finset.card_image_le

/-- Every decoded vector has an index preimage. -/
theorem exists_decodedFamily_index {J : Type*} [Fintype J]
    (output : J → LeftBlockVector L q k) (t : decodedFamily output) :
    ∃ j : J, output j = t.1 := by
  classical
  obtain ⟨j, _hj, hjo⟩ := Finset.mem_image.mp t.2
  exact ⟨j, hjo⟩

/-- A finite-family span encoding is canonically an indexed encoding, using the
subtypes of its input and output finsets as node sets. -/
def ofFinset
    {H : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) :
    RationalIndexedSpanEncodingOfHeight H S T
      (fun s ↦ s.1) (fun t ↦ t.1) where
  coefficient := E.coefficient
  coefficient_height := E.coefficient_height
  linearCombination_eq := E.linearCombination_eq

/-- Every decoded output vector belongs to the span of the decoded input family. -/
theorem mem_span_decodedFamily
    {H : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {input : I → LeftBlockVector L q k} {output : J → LeftBlockVector L q k}
    (E : RationalIndexedSpanEncodingOfHeight H I J input output)
    (t : decodedFamily output) :
    t.1 ∈ Submodule.span ℂ
      (decodedFamily input : Set (LeftBlockVector L q k)) := by
  classical
  obtain ⟨j, hj⟩ := exists_decodedFamily_index output t
  rw [← hj, E.linearCombination_eq j]
  apply Submodule.sum_mem
  intro a _ha
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

/-- An indexed rational span encoding transports rational physical-coordinate bounds
without first quotienting coincident decoded nodes. -/
theorem coordinate_height
    {H Hv : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {input : I → LeftBlockVector L q k} {output : J → LeftBlockVector L q k}
    (E : RationalIndexedSpanEncodingOfHeight H I J input output)
    (hinput : ∀ a x,
      HasRationalComplexCoordinatesOfHeight Hv (input a x))
    (j : J) (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
        H Hv (Fintype.card I)) (output j x) := by
  rw [E.linearCombination_eq j]
  unfold RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
  simpa using HasRationalComplexCoordinatesOfHeight.finset_sum
    (s := Finset.univ) (fun a _ha ↦ (E.coefficient_height j a).mul (hinput a x))

/-- Decoding an indexed rational span layer gives the coordinate-rational viable-MPS
data expected by the finite-family search interface. -/
theorem coordinateViableMPSData
    {H Hv : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {b : ℕ} {δ : ℝ}
    {input : I → LeftBlockVector L q k} {output : J → LeftBlockVector L q k}
    (E : RationalIndexedSpanEncodingOfHeight H I J input output)
    (hinputMPS : ∀ a, IsLeftOpenMPS b (input a))
    (hinputHeight : ∀ a x,
      HasRationalComplexCoordinatesOfHeight Hv (input a x))
    (hviable : IsViable Γ δ
      (decodedFamily output : Set (LeftBlockVector L q k))) :
    RationalCoordinateViableMPSDataOfHeight
      (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
        H Hv (Fintype.card I))
      Γ (Fintype.card J) ((decodedFamily input).card * max 1 b) δ
      (decodedFamily output) where
  card_le := decodedFamily_card_le output
  isLeftOpenMPS t := isLeftOpenMPS_of_mem_span (decodedFamily input)
    (by
      intro v hv
      obtain ⟨a, _ha, hav⟩ := Finset.mem_image.mp hv
      rw [← hav]
      exact hinputMPS a)
    (E.mem_span_decodedFamily t)
  coordinate_height t x := by
    obtain ⟨j, hj⟩ := exists_decodedFamily_index output t
    rw [← hj]
    exact E.coordinate_height hinputHeight j x
  viable := hviable

/-- One-site extension preserves an indexed rational span encoding and its coefficient
height.  The new coefficient is the old coefficient when the computational-basis
labels agree, and zero otherwise.  Retaining the product indices avoids any expansion
of physical coordinates or quotienting of coincident decoded vectors. -/
noncomputable def extend
    {H : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {input : I → LeftBlockVector L q (i - 1)}
    {output : J → LeftBlockVector L q (i - 1)}
    (E : RationalIndexedSpanEncodingOfHeight H I J input output) (hH : 1 ≤ H) :
    RationalIndexedSpanEncodingOfHeight H (I × Fin q) (J × Fin q)
      (fun a ↦ AreaLaw.extendSite i a.2 (input a.1))
      (fun j ↦ AreaLaw.extendSite i j.2 (output j.1)) where
  coefficient j a := if j.2 = a.2 then E.coefficient j.1 a.1 else 0
  coefficient_height j a := by
    split_ifs
    · exact E.coefficient_height j.1 a.1
    · exact HasRationalComplexCoordinatesOfHeight.zero.mono hH
  linearCombination_eq j := by
    rw [E.linearCombination_eq j.1]
    simp only [map_sum, map_smul]
    rw [Fintype.sum_prod_type]
    simp

end RationalIndexedSpanEncodingOfHeight

/-- A multi-layer rational span DAG with explicit finite node indices.  The decoded
vectors may coincide, but their nodes remain distinct; hence shared arithmetic data
can be transported functorially through one-site extension. -/
structure RationalIndexedSpanEncodingDAGOfHeight
    (depth : ℕ) (height : Fin depth → ℕ)
    (node : Fin (depth + 1) → Type*)
    [nodeFintype : ∀ r, Fintype (node r)]
    (value : ∀ r, node r → LeftBlockVector L q k) where
  layer : ∀ j : Fin depth,
    RationalIndexedSpanEncodingOfHeight (height j)
      (node j.castSucc) (node j.succ) (value j.castSucc) (value j.succ)

namespace RationalIndexedSpanEncodingDAGOfHeight

/-- One-site extension transports every layer of an indexed span DAG simultaneously.
The node set at each layer is multiplied by the `q` computational-basis labels, while
all old coefficient heights are preserved. -/
noncomputable def extend
    {depth : ℕ} {height : Fin depth → ℕ}
    {node : Fin (depth + 1) → Type*}
    [nodeFintype : ∀ r, Fintype (node r)]
    {value : ∀ r, node r → LeftBlockVector L q (i - 1)}
    (D : RationalIndexedSpanEncodingDAGOfHeight depth height node value)
    (hheight : ∀ j, 1 ≤ height j) :
    RationalIndexedSpanEncodingDAGOfHeight depth height
      (fun r ↦ node r × Fin q)
      (fun r a ↦ AreaLaw.extendSite i a.2 (value r a.1)) where
  layer j := (D.layer j).extend (hheight j)

end RationalIndexedSpanEncodingDAGOfHeight

/-- The unconditional rational support-coordinate construction produces an explicit
finite family of compactly encoded rational columns over the original retained family.
Its cardinality is at most `n m`, and every exact support-isometry slice is close to a
member of this family.  The height and error retain the conditioning radius `R`; a
polynomial runtime corollary therefore requires a polynomial bound on `R`. -/
theorem exists_rational_spanColumnFamily
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ qc : Fin n → Fin m → S → ℂ,
      let H := rationalBoundedMatrixGridHeight R δ
      let T := spanColumnFamily S m qc
      (∀ j a s, HasRationalComplexCoordinatesOfHeight H (qc j a s)) ∧
      T.card ≤ n * m ∧
      Nonempty (RationalSpanFamilyEncodingOfHeight H S T) ∧
      ∀ j a, ∃ w ∈ T,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) - w‖ ≤
          S.card * δ * R := by
  obtain ⟨R, hR, qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinates S m Z hZ hZZ hδ
  refine ⟨R, hR, qc, hqc, spanColumnFamily_card_le S m qc,
    ⟨rationalSpanFamilyEncodingOfCoefficients S m qc hqc⟩, ?_⟩
  exact exists_mem_spanColumnFamily_close S m qc
    (fun j a ↦ WithLp.toLp 2 (fun x ↦
      gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))) hclose

/-- Data-bearing invariant for a viable output family stored as rational linear
combinations of a height-bounded rational MPS input family.  This is the compact form
appropriate after LVV size trimming. -/
structure RationalSpanViableMPSDataOfHeight
    (H Hv : ℕ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ)
    (S T : Finset (LeftBlockVector L q k)) where
  input_representation : ∀ u : S,
    RationalLeftOpenMPSRepresentationOfHeight Hv b u.1
  encoding : RationalSpanFamilyEncodingOfHeight H S T
  card_le : T.card ≤ s
  viable : IsViable Γ δ (T : Set (LeftBlockVector L q k))

namespace RationalSpanViableMPSDataOfHeight

/-- Forgetting the compact rational encoding gives the ordinary viable-MPS predicate,
with the finite-span bond budget. -/
theorem isViableMPS
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (D : RationalSpanViableMPSDataOfHeight H Hv Γ s b δ S T) :
    IsViableMPS Γ s (S.card * max 1 b) δ T :=
  ⟨D.card_le,
    fun v hv ↦ D.encoding.isLeftOpenMPS
      (fun u hu ↦ (D.input_representation ⟨u, hu⟩).data.isLeftOpenMPS) ⟨v, hv⟩,
    D.viable⟩

/-- Every queried coordinate of the compact viable output has the uniform rational
height bound inherited from its coefficients and input tensors. -/
theorem coordinate_height
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (D : RationalSpanViableMPSDataOfHeight H Hv Γ s b δ S T)
    (hHv : 0 < Hv) (hk : k ≤ L) (t : T)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (RationalSpanFamilyEncodingOfHeight.outputCoordinateHeight H Hv b k S.card)
      (t.1 x) :=
  D.encoding.coordinate_height hHv hk D.input_representation t x

/-- A compact span-encoded output supplies exactly the coordinate-rational viable-MPS
invariant required by the next LVV iteration.  No direct-sum tensor expansion is
performed: the bond bound follows from finite-span closure, while rationality is
queried through the stored coefficient array. -/
theorem coordinateViableMPSData
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (D : RationalSpanViableMPSDataOfHeight H Hv Γ s b δ S T)
    (hHv : 0 < Hv) (hk : k ≤ L) :
    RationalCoordinateViableMPSDataOfHeight
      (RationalSpanFamilyEncodingOfHeight.outputCoordinateHeight H Hv b k S.card)
      Γ s (S.card * max 1 b) δ T where
  card_le := D.card_le
  isLeftOpenMPS t := D.encoding.isLeftOpenMPS
    (fun u hu ↦ (D.input_representation ⟨u, hu⟩).data.isLeftOpenMPS) t
  coordinate_height t x := D.coordinate_height hHv hk t x
  viable := D.viable

/-- Enlarging the permitted overlap error leaves all rational encoding, cardinality,
and bond data unchanged. -/
noncomputable def mono_error
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ δ' : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (D : RationalSpanViableMPSDataOfHeight H Hv Γ s b δ S T)
    (hδ : δ ≤ δ') :
    RationalSpanViableMPSDataOfHeight H Hv Γ s b δ' S T where
  input_representation := D.input_representation
  encoding := D.encoding
  card_le := D.card_le
  viable := by
    obtain ⟨φ, hφ, hoverlap, hsupport⟩ := D.viable
    exact ⟨φ, hφ, hoverlap.trans' (by linarith), hsupport⟩

end RationalSpanViableMPSDataOfHeight

/-- Viability is stable under replacing a unit witness by a nearby supported vector.
After normalizing the replacement, the overlap loss is at most twice the vector error.
This elementary estimate is the bridge from exact LVV columns to their rational
approximations. -/
theorem isViable_of_close_supported_vector
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ ε : ℝ} (hε1 : ε < 1)
    {T : Set (LeftBlockVector L q k)}
    {φ ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : ‖φ‖ = 1) (hoverlap : 1 - δ ≤ ‖⟪φ, Γ⟫_ℂ‖)
    (hψT : ψ ∈ leftSupportSubmodule T) (hclose : ‖φ - ψ‖ ≤ ε) :
    IsViable Γ (δ + 2 * ε) T := by
  have hnormdiff : |‖φ‖ - ‖ψ‖| ≤ ε :=
    (abs_norm_sub_norm_le φ ψ).trans hclose
  have hnormdiff' : |1 - ‖ψ‖| ≤ ε := by
    simpa only [hφ] using hnormdiff
  have hψpos : 0 < ‖ψ‖ := by
    have : 1 - ε ≤ ‖ψ‖ := by
      have := (le_abs_self (1 - ‖ψ‖)).trans hnormdiff'
      linarith
    linarith
  let χ : EuclideanSpace ℂ (Fin L → Fin q) := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
  have hχ : ‖χ‖ = 1 := by
    simp only [χ, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hψpos]
    exact inv_mul_cancel₀ hψpos.ne'
  have hχT : χ ∈ leftSupportSubmodule T :=
    (leftSupportSubmodule T).smul_mem _ hψT
  have hχψ : ‖χ - ψ‖ = |1 - ‖ψ‖| := by
    rw [show χ - ψ = (((‖ψ‖⁻¹ - 1 : ℝ) : ℂ) • ψ) by
      simp only [χ, sub_smul, one_smul, Complex.ofReal_sub, Complex.ofReal_one]]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have heq : ‖ψ‖⁻¹ - 1 = (1 - ‖ψ‖) / ‖ψ‖ := by
      field_simp [hψpos.ne']
    rw [heq, abs_div, abs_of_pos hψpos, div_mul_cancel₀ _ hψpos.ne']
  have hχφ : ‖χ - φ‖ ≤ 2 * ε := by
    calc
      ‖χ - φ‖ ≤ ‖χ - ψ‖ + ‖ψ - φ‖ := norm_sub_le_norm_sub_add_norm_sub χ ψ φ
      _ = |1 - ‖ψ‖| + ‖φ - ψ‖ := by rw [hχψ, norm_sub_rev]
      _ ≤ ε + ε := add_le_add hnormdiff' hclose
      _ = 2 * ε := by ring
  refine ⟨χ, hχ, ?_, hχT⟩
  have hinner : ‖⟪φ, Γ⟫_ℂ‖ ≤ ‖⟪χ, Γ⟫_ℂ‖ + 2 * ε := by
    calc
      ‖⟪φ, Γ⟫_ℂ‖ ≤ ‖⟪χ, Γ⟫_ℂ‖ + ‖⟪φ - χ, Γ⟫_ℂ‖ := by
        rw [show ⟪φ, Γ⟫_ℂ = ⟪χ, Γ⟫_ℂ + ⟪φ - χ, Γ⟫_ℂ by
          rw [inner_sub_left]
          abel]
        exact norm_add_le _ _
      _ ≤ ‖⟪χ, Γ⟫_ℂ‖ + ‖φ - χ‖ * ‖Γ‖ := by
        gcongr
        exact norm_inner_le_norm _ _
      _ ≤ ‖⟪χ, Γ⟫_ℂ‖ + 2 * ε := by
        rw [hΓ, mul_one, norm_sub_rev]
        gcongr
  linarith

/-- Increasing the permitted overlap error preserves viability. -/
theorem IsViable.mono_error
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ δ' : ℝ}
    {T : Set (LeftBlockVector L q k)} (h : IsViable Γ δ T) (hδ : δ ≤ δ') :
    IsViable Γ δ' T := by
  obtain ⟨φ, hφ, hoverlap, hsupport⟩ := h
  exact ⟨φ, hφ, hoverlap.trans' (by linarith), hsupport⟩

/-- Assemble a finite collection of left-block columns into one vector with an auxiliary
right index. -/
noncomputable def assembleLeftColumns (w : Fin m → LeftBlockVector L q k) :
    EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m) :=
  WithLp.toLp 2 fun p ↦ w p.2 p.1

/-- Uniform column error `θ` gives joint Euclidean error at most `√m θ`. -/
theorem norm_sub_assembleLeftColumns_le
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (w : Fin m → LeftBlockVector L q k) {θ : ℝ} (hθ : 0 ≤ θ)
    (hclose : ∀ a,
      ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - w a‖ ≤ θ) :
    ‖u - assembleLeftColumns w‖ ≤ Real.sqrt m * θ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hθ)).mp
  calc
    ‖u - assembleLeftColumns w‖ ^ 2 =
        ∑ a : Fin m, ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - w a‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq]
      change (∑ p, ‖u p - w p.2 p.1‖ ^ 2) =
        ∑ a, ∑ x, ‖u (x, a) - w a x‖ ^ 2
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ ≤ ∑ _a : Fin m, θ ^ 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      exact pow_le_pow_left₀ (norm_nonneg _) (hclose a) 2
    _ = (m : ℝ) * θ ^ 2 := by simp
    _ = (Real.sqrt m * θ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m)]

/-- Applying an isometry on the auxiliary right factor preserves the Euclidean norm. -/
theorem norm_rightApply_eq_of_isometry
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (W : Matrix γ β ℂ) (hW : Wᴴ * W = 1) (u : EuclideanSpace ℂ (α × β)) :
    ‖rightApply W u‖ = ‖u‖ := by
  classical
  let J := (1 : Matrix α α ℂ) ⊗ₖ W
  have hJ : Jᴴ * J = 1 := by
    simp only [J, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hW, Matrix.one_kronecker_one]
  have h : rightApply W u = WithLp.toLp 2 (J *ᵥ WithLp.ofLp u) := by
    ext ⟨x, a⟩
    simp [J, rightApply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.one_apply, Matrix.kroneckerMap_apply, mul_comm]
  rw [h]
  exact norm_toLp_mulVec_of_isometry J hJ u

/-- Transport a right-extended cut vector back to the physical chain coordinates. -/
noncomputable def physicalRightApply
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    EuclideanSpace ℂ (Fin L → Fin q) :=
  WithLp.toLp 2 fun z ↦ rightApply W u
    (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z)

/-- Applying the right isometry after joining the two left regions is the physical
three-cut reconstruction used in the LVV leading-vector theorem. -/
theorem physicalRightApply_gluingLeftCoordinates
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    physicalRightApply W (gluingLeftCoordinates L q k m u) =
      WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k) := by
  exact (gluingLeftCoordinates_rightApply W u).symm

/-- In cut coordinates, `physicalRightApply` is exactly the corresponding right
extension. -/
theorem cutVector_physicalRightApply
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k)
      (physicalRightApply W u) = rightApply W u := by
  ext p
  change rightApply W u
    (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)
      ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm p)) =
        rightApply W u p
  rw [Equiv.apply_symm_apply]

/-- A right isometry preserves the norm after returning to physical coordinates. -/
theorem norm_physicalRightApply_eq_of_isometry
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    ‖physicalRightApply W u‖ = ‖u‖ := by
  rw [← Entropy.norm_cutVector (leftBlock L k), cutVector_physicalRightApply,
    norm_rightApply_eq_of_isometry W hW]

/-- A right isometry also preserves distances between two cut vectors. -/
theorem norm_physicalRightApply_sub_eq_of_isometry
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u v : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    ‖physicalRightApply W u - physicalRightApply W v‖ = ‖u - v‖ := by
  rw [show physicalRightApply W u - physicalRightApply W v =
      physicalRightApply W (u - v) by
    ext z
    let p := Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z
    change (∑ j, u (p.1, j) * W p.2 j) - (∑ j, v (p.1, j) * W p.2 j) =
      ∑ j, (u (p.1, j) - v (p.1, j)) * W p.2 j
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [sub_mul]]
  exact norm_physicalRightApply_eq_of_isometry W hW (u - v)

/-- Replacing every left column of an exact LVV witness within `θ` preserves viability,
with overlap error enlarged by at most `2 √m θ`. -/
theorem isViable_of_close_leftColumns
    {m : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ : ℝ} (hθ : 0 ≤ θ) (hsmall : Real.sqrt m * θ < 1)
    {T : Set (LeftBlockVector L q k)}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hunit : ‖physicalRightApply W u‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W u, Γ⟫_ℂ‖)
    (w : Fin m → LeftBlockVector L q k)
    (hwT : ∀ a, w a ∈ Submodule.span ℂ T)
    (hclose : ∀ a, ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - w a‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * θ)) T := by
  let u' := assembleLeftColumns w
  let ψ := physicalRightApply W u'
  have hψT : ψ ∈ leftSupportSubmodule T := by
    exact rightApply_mem_leftSupportSubmodule_of_columns T u' W (fun a ↦ by
      change w a ∈ Submodule.span ℂ T
      exact hwT a)
  have hclose' : ‖physicalRightApply W u - ψ‖ ≤ Real.sqrt m * θ := by
    rw [show ψ = physicalRightApply W u' from rfl,
      norm_physicalRightApply_sub_eq_of_isometry W hW]
    exact norm_sub_assembleLeftColumns_le u w hθ hclose
  exact isViable_of_close_supported_vector hΓ hsmall hunit hoverlap hψT hclose'

/-- A rational decoded column family is viable whenever it approximates all columns of
one exact LVV witness.  This is the stability statement needed to turn certificate
coordinates into an actual finite viable output family. -/
theorem isViable_spanColumnFamily_of_close
    {m n : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ : ℝ} (hθ : 0 ≤ θ) (hsmall : Real.sqrt m * θ < 1)
    (S : Finset (LeftBlockVector L q k))
    (c : Fin n → Fin m → S → ℂ) (j : Fin n)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hunit : ‖physicalRightApply W u‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W u, Γ⟫_ℂ‖)
    (hclose : ∀ a,
      ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - ∑ s : S, c j a s • s.1‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * θ))
      (spanColumnFamily S m c : Set (LeftBlockVector L q k)) := by
  apply isViable_of_close_leftColumns hΓ hθ hsmall W hW u hunit hoverlap
    (fun a ↦ ∑ s : S, c j a s • s.1)
  · intro a
    exact Submodule.subset_span (sum_mem_spanColumnFamily S m c j a)
  · exact hclose

/-- A linear combination of `n` uniformly approximated columns has error at most
`n θ` when every coefficient has norm at most one.  The deliberately elementary
bound is sufficient for the polynomial mesh estimate in LVV13, `algo53.tex`,
lines 472--478. -/
theorem norm_sum_smul_sub_sum_smul_le
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (v w : Fin n → LeftBlockVector L q k) {θ : ℝ}
    (hclose : ∀ j, ‖v j - w j‖ ≤ θ) :
    ‖(∑ j, z j • v j) - ∑ j, z j • w j‖ ≤ n * θ := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ j, (z j • v j - z j • w j)‖ ≤
        ∑ j, ‖z j • v j - z j • w j‖ := norm_sum_le Finset.univ _
    _ = ∑ j, ‖z j‖ * ‖v j - w j‖ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← smul_sub, norm_smul]
    _ ≤ ∑ _j : Fin n, θ := by
      apply Finset.sum_le_sum
      intro j _hj
      calc
        ‖z j‖ * ‖v j - w j‖ ≤ 1 * ‖v j - w j‖ :=
          mul_le_mul_of_nonneg_right (hz j) (norm_nonneg _)
        _ ≤ 1 * θ := mul_le_mul_of_nonneg_left (hclose j) zero_le_one
        _ = θ := one_mul θ
    _ = n * θ := by simp

/-- For unit coefficients in Euclidean norm, Cauchy--Schwarz improves the accumulated
error of `n` uniformly approximated columns from `n θ` to `√n θ`. -/
theorem norm_sum_smul_sub_sum_smul_le_sqrt
    {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (v w : Fin n → LeftBlockVector L q k) {θ : ℝ} (hθ : 0 ≤ θ)
    (hclose : ∀ j, ‖v j - w j‖ ≤ θ) :
    ‖(∑ j, z j • v j) - ∑ j, z j • w j‖ ≤ Real.sqrt n * θ := by
  rw [← Finset.sum_sub_distrib]
  have hcs := Finset.norm_sum_le_mul_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin n))
    (fun j ↦ z j • v j - z j • w j) (fun j ↦ ‖z j‖) (fun _ ↦ 1) hθ
    (fun j _hj ↦ by
      rw [← smul_sub, norm_smul]
      nlinarith only [hclose j, norm_nonneg (z j)])
  rw [show ∑ j : Fin n, ‖z j‖ ^ 2 = ‖z‖ ^ 2 by
      simp only [EuclideanSpace.norm_sq_eq],
    hz, one_pow, Real.sqrt_one] at hcs
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul, mul_comm] using hcs

/-- The decoded rational column family remains viable for an arbitrary linear
combination of exact compressed columns.  Thus the stability argument applies to a
leading vector of the compressed density matrix, rather than only to one coordinate
column.  This is the form used in LVV13, `algo53.tex`, lines 472--478 and 520--527. -/
theorem isViable_spanColumnFamily_of_close_linearCombination
    {m n : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ : ℝ} (hθ : 0 ≤ θ) (hsmall : Real.sqrt m * (n * θ) < 1)
    (S : Finset (LeftBlockVector L q k))
    (c : Fin n → Fin m → S → ℂ) (z : Fin n → ℂ)
    (hz : ∀ j, ‖z j‖ ≤ 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hunit : ‖physicalRightApply W u‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W u, Γ⟫_ℂ‖)
    (v : Fin n → Fin m → LeftBlockVector L q k)
    (hu : ∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) = ∑ j, z j • v j a)
    (hclose : ∀ j a, ‖v j a - ∑ s : S, c j a s • s.1‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * (n * θ)))
      (spanColumnFamily S m c : Set (LeftBlockVector L q k)) := by
  apply isViable_of_close_leftColumns hΓ (mul_nonneg (Nat.cast_nonneg n) hθ)
    hsmall W hW u hunit hoverlap
    (fun a ↦ ∑ j, z j • ∑ s : S, c j a s • s.1)
  · intro a
    apply Submodule.sum_mem
    intro j _hj
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (sum_mem_spanColumnFamily S m c j a))
  · intro a
    rw [hu a]
    exact norm_sum_smul_sub_sum_smul_le z hz (fun j ↦ v j a)
      (fun j ↦ ∑ s : S, c j a s • s.1) (fun j ↦ hclose j a)

/-- Specialization of the preceding stability theorem to the compressed vector `Z z`.
It removes the coordinate bookkeeping between matrix-vector multiplication and the
linear combination of the columns of `Z`.  This is the exact interface used by the
compressed leading vector in LVV13, `algo53.tex`, lines 477--478 and 493--505. -/
theorem isViable_spanColumnFamily_of_close_mulVec
    {m n : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ : ℝ} (hθ : 0 ≤ θ)
    (hsmall : Real.sqrt m * (Real.sqrt n * θ) < 1)
    (S : Finset (LeftBlockVector L q k))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (c : Fin n → Fin m → S → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖)
    (hclose : ∀ j a,
      ‖WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
        ∑ s : S, c j a s • s.1‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * (Real.sqrt n * θ)))
      (spanColumnFamily S m c : Set (LeftBlockVector L q k)) := by
  let u := gluingLeftCoordinates L q k m
    (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))
  let v : Fin n → Fin m → LeftBlockVector L q k := fun j a ↦
    WithLp.toLp 2 (fun x ↦
      gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))
  apply isViable_of_close_leftColumns hΓ
    (mul_nonneg (Real.sqrt_nonneg n) hθ) hsmall W hW u hunit hoverlap
    (fun a ↦ ∑ j, z j • ∑ s : S, c j a s • s.1)
  · intro a
    apply Submodule.sum_mem
    intro j _hj
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (sum_mem_spanColumnFamily S m c j a))
  · intro a
    rw [show WithLp.toLp 2 (fun x ↦ u (x, a)) = ∑ j, z j • v j a by
      ext x
      simp [u, v, gluingLeftCoordinates, Matrix.mulVec, dotProduct, mul_comm]]
    exact norm_sum_smul_sub_sum_smul_le_sqrt z hz (fun j ↦ v j a)
      (fun j ↦ ∑ s : S, c j a s • s.1) hθ (fun j ↦ hclose j a)

/-- Rational structured coefficients decode to a rational ambient matrix when every
retained vector carries rational open-chain tensor data. -/
theorem boundarySupportMatrixOfCoordinates_hasRationalEntries
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n b : ℕ}
    (hk : k ≤ L)
    (c : Fin n → Fin m → S → ℂ)
    (hc : ∀ j a s, HasRationalComplexCoordinates (c j a s))
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentation b s.1) :
    Matrix.HasRationalEntries (boundarySupportMatrixOfCoordinates S m c) := by
  intro p j
  apply HasRationalComplexCoordinates.fintype_sum
  intro s
  exact (hc j p.2 s).mul <| (hS s).coordinate_rational hk
    ((Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
      (leftBlock_mono (Nat.sub_le k 1))).symm p.1)

/-- A structured rational input decodes to an ambient rational support matrix once the
retained family itself carries rational open-chain tensor data. -/
theorem RationalStructuredCompressedSDPInputEncoding.boundarySupportMatrix_hasRationalEntries
    (S : Finset (LeftBlockVector L q k)) {m n r b : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hk : k ≤ L) (hS : ∀ s : S, RationalLeftOpenMPSRepresentation b s.1) :
    Matrix.HasRationalEntries (boundarySupportMatrixOfCoordinates S m c) :=
  boundarySupportMatrixOfCoordinates_hasRationalEntries S m hk c
    (fun j a s ↦ (h.coefficient_height j a s).forget) hS

/-- Uniform height bound for decoding structured support coordinates against a retained
family of height-bounded rational open-chain states. -/
theorem boundarySupportMatrixOfCoordinates_hasRationalEntriesOfHeight
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n b Hc Hv : ℕ}
    (hHv : 0 < Hv) (hk : k ≤ L)
    (c : Fin n → Fin m → S → ℂ)
    (hc : ∀ j a s, HasRationalComplexCoordinatesOfHeight Hc (c j a s))
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentationOfHeight Hv b s.1) :
    let HV := RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound Hv b k
    let HM := 2 * (Hc * HV) * (Hc * HV)
    Matrix.HasRationalEntriesOfHeight ((2 * HM) ^ S.card)
      (boundarySupportMatrixOfCoordinates S m c) := by
  dsimp only
  intro p j
  rw [boundarySupportMatrixOfCoordinates]
  simpa using HasRationalComplexCoordinatesOfHeight.finset_sum
    (s := Finset.univ) (fun s _hs ↦
      (hc j p.2 s).mul <| (hS s).coordinate_height_le hHv hk
        ((Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
          (leftBlock_mono (Nat.sub_le k 1))).symm p.1))

/-- A structured rational encoding over height-bounded rational MPS data therefore
decodes to an ambient support matrix with an explicit uniform height bound. -/
theorem RationalStructuredCompressedSDPInputEncoding.boundarySupportMatrix_height
    (S : Finset (LeftBlockVector L q k)) {m n r b Hv : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hHv : 0 < Hv) (hk : k ≤ L)
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentationOfHeight Hv b s.1) :
    let HV := RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound Hv b k
    let HM := 2 * (h.height * HV) * (h.height * HV)
    Matrix.HasRationalEntriesOfHeight ((2 * HM) ^ S.card)
      (boundarySupportMatrixOfCoordinates S m c) :=
  boundarySupportMatrixOfCoordinates_hasRationalEntriesOfHeight S m hHv hk c
    h.coefficient_height hS

/-- The support coefficients stored in a structured compressed input directly define
the compact rational encoding of its decoded left-column family. -/
noncomputable def RationalStructuredCompressedSDPInputEncoding.spanFamilyEncoding
    (S : Finset (LeftBlockVector L q k)) {m n r : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb) :
    RationalSpanFamilyEncodingOfHeight h.height S (spanColumnFamily S m c) :=
  rationalSpanFamilyEncodingOfCoefficients S m c h.coefficient_height

/-- The complete coefficient array of the decoded column family has the expected
compact bit-size bound. -/
theorem RationalStructuredCompressedSDPInputEncoding.spanFamilyBitSizeBound_le
    (S : Finset (LeftBlockVector L q k)) {m n r : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb) :
    RationalSpanFamilyEncodingOfHeight.coefficientBitSizeBound h.height S
        (spanColumnFamily S m c) ≤
      2 * (n * m) * S.card * (Nat.log2 h.height + 1) := by
  exact h.spanFamilyEncoding.coefficientBitSizeBound_le le_rfl
    (spanColumnFamily_card_le S m c)

/-- Once certificate soundness proves viability of the decoded columns, a structured
compressed input supplies the complete compact viable-MPS invariant without any further
choice of tensor data. -/
noncomputable def RationalStructuredCompressedSDPInputEncoding.spanViableMPSData
    (S : Finset (LeftBlockVector L q k))
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {m n r b Hv s : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb δ : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    (hcard : (spanColumnFamily S m c).card ≤ s)
    (hviable : IsViable Γ δ
      (spanColumnFamily S m c : Set (LeftBlockVector L q k))) :
    RationalSpanViableMPSDataOfHeight h.height Hv Γ s b δ S
      (spanColumnFamily S m c) where
  input_representation := hS
  encoding := h.spanFamilyEncoding S
  card_le := hcard
  viable := hviable

/-- A structured rational input whose decoded columns approximate one exact LVV witness
therefore yields the complete compact viable-MPS output invariant. -/
noncomputable def
    RationalStructuredCompressedSDPInputEncoding.spanViableMPSDataOfClose
    (S : Finset (LeftBlockVector L q k))
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {m n r b Hv : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb δ θ : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    (hΓ : ‖Γ‖ = 1) (hθ : 0 ≤ θ) (hsmall : Real.sqrt m * θ < 1)
    (j : Fin n) (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hunit : ‖physicalRightApply W u‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W u, Γ⟫_ℂ‖)
    (hclose : ∀ a,
      ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - ∑ s : S, c j a s • s.1‖ ≤ θ) :
    RationalSpanViableMPSDataOfHeight h.height Hv Γ (n * m) b
      (δ + 2 * (Real.sqrt m * θ)) S (spanColumnFamily S m c) :=
  h.spanViableMPSData S hS (spanColumnFamily_card_le S m c) <|
    isViable_spanColumnFamily_of_close hΓ hθ hsmall S c j W hW u hunit hoverlap hclose

/-- The compact rational viable-MPS output associated with a general compressed vector
`Z z`.  Unlike `spanViableMPSDataOfClose`, this constructor applies directly to the
leading vector returned by the compressed eigensolver. -/
noncomputable def
    RationalStructuredCompressedSDPInputEncoding.spanViableMPSDataOfCloseMulVec
    (S : Finset (LeftBlockVector L q k))
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {m n r b Hv : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb δ θ : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    (hΓ : ‖Γ‖ = 1) (hθ : 0 ≤ θ)
    (hsmall : Real.sqrt m * (Real.sqrt n * θ) < 1)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖)
    (hclose : ∀ j a,
      ‖WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
        ∑ s : S, c j a s • s.1‖ ≤ θ) :
    RationalSpanViableMPSDataOfHeight h.height Hv Γ (n * m) b
      (δ + 2 * (Real.sqrt m * (Real.sqrt n * θ))) S (spanColumnFamily S m c) :=
  h.spanViableMPSData S hS (spanColumnFamily_card_le S m c) <|
    isViable_spanColumnFamily_of_close_mulVec hΓ hθ hsmall S Z c z hz W hW
      hunit hoverlap hclose

/-- After the mesh-independent coordinate radius is chosen, an explicit rational mesh
produces a compact viable MPS family unconditionally.  The mesh is small enough that
the accumulated `n`-column and `m`-bond error is strictly below one.  The only remaining
runtime question is whether the resulting radius, and hence the displayed height, has a
polynomial bit bound. -/
theorem exists_rationalSpanViableMPSData_of_mulVec
    (S : Finset (LeftBlockVector L q k)) {m n b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ : ℝ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := 1 / (2 * (1 + A))
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (δ + 2 * (A * mesh)) S (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hRapprox⟩ := exists_boundarySupportCoordinateRadius S m Z hZ hZZ
  refine ⟨R, hR, ?_⟩
  let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
  let mesh := 1 / (2 * (1 + A))
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < 2 * (1 + A) := by positivity
  have hmesh : 0 < mesh := by
    dsimp only [mesh]
    positivity
  obtain ⟨c, hc, hclose⟩ := hRapprox hmesh
  refine ⟨c, hc, ⟨?_⟩⟩
  have hsmallA : A * mesh < 1 := by
    rw [show A * mesh = A / (2 * (1 + A)) by
      dsimp only [mesh]
      ring]
    exact (div_lt_iff₀ hden).2 (by nlinarith only [hA])
  have hsmall : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) < 1 := by
    calc
      Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
        dsimp only [A]
        ring
      _ < 1 := hsmallA
  refine ⟨hS, rationalSpanFamilyEncodingOfCoefficients S m c hc,
    spanColumnFamily_card_le S m c, ?_⟩
  have hviable := isViable_spanColumnFamily_of_close_mulVec hΓ
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hmesh.le) hR) hsmall
    S Z c z hz W hW hunit hoverlap hclose
  convert hviable using 1
  dsimp only [A, mesh]
  ring

/-- Arbitrary-precision form of the rational viable-family construction.  Given an
error budget `ξ ∈ (0,1)`, the mesh `ξ / (1 + A)` makes the rationalization contribution
strictly smaller than `2ξ`, where `A = √m √n |S| R`.  This is the form used when the
LVV `1/12` overlap budget is split among density, eigenvector, and rationalization
errors. -/
theorem exists_rationalSpanViableMPSData_of_mulVec_atError
    (S : Finset (LeftBlockVector L q k)) {m n b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξ / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (δ + 2 * ξ) S (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hRapprox⟩ := exists_boundarySupportCoordinateRadius S m Z hZ hZZ
  refine ⟨R, hR, ?_⟩
  let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
  let mesh := ξ / (1 + A)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < 1 + A := by positivity
  have hmesh : 0 < mesh := div_pos hξ hden
  have herror : A * mesh < ξ := by
    rw [show A * mesh = ξ * (A / (1 + A)) by
      dsimp only [mesh]
      field_simp]
    have hratio : A / (1 + A) < 1 :=
      (div_lt_one hden).2 (by linarith only [hA])
    nlinarith only [hξ, hratio]
  obtain ⟨c, hc, hclose⟩ := hRapprox hmesh
  refine ⟨c, hc, ⟨?_⟩⟩
  have hsmall : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) < 1 := by
    calc
      Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
        dsimp only [A]
        ring
      _ < ξ := herror
      _ < 1 := hξ1
  refine ⟨hS, rationalSpanFamilyEncodingOfCoefficients S m c hc,
    spanColumnFamily_card_le S m c, ?_⟩
  have hviable := isViable_spanColumnFamily_of_close_mulVec hΓ
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hmesh.le) hR) hsmall
    S Z c z hz W hW hunit hoverlap hclose
  apply hviable.mono_error
  have heq : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
    dsimp only [A]
    ring
  rw [heq]
  linarith only [herror]

/-- Target-error interface for the rational viable-family construction.  If the exact
witness error and the allocated rationalization error fit inside `δtarget`, the returned
compact family is recorded directly at that target.  Taking `δtarget = 1/12` is the
interface required by LVV size trimming. -/
theorem exists_rationalSpanViableMPSData_of_mulVec_atTarget
    (S : Finset (LeftBlockVector L q k)) {m n b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ ξ δtarget : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hbudget : δ + 2 * ξ ≤ δtarget)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξ / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          δtarget S (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hout⟩ := exists_rationalSpanViableMPSData_of_mulVec_atError
    S hS hΓ hξ hξ1 Z hZ hZZ z hz W hW hunit hoverlap
  refine ⟨R, hR, ?_⟩
  obtain ⟨c, hc, ⟨D⟩⟩ := hout
  exact ⟨c, hc, ⟨D.mono_error hbudget⟩⟩

/-- Coordinate-rational form of arbitrary-precision column rationalization.  This
version consumes precisely the compact invariant produced by a preceding trimming
step, rather than requiring every input vector to be expanded again as an
open-boundary tensor. -/
theorem exists_rationalCoordinateViableMPSData_of_mulVec_atError
    (S : Finset (LeftBlockVector L q k)) {m n s₀ b Hv : ℕ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ₀ : ℝ}
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δ₀ S)
    (hΓ : ‖Γ‖ = 1) {δ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξ / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (δ + 2 * ξ)
          (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hRapprox⟩ := exists_boundarySupportCoordinateRadius S m Z hZ hZZ
  refine ⟨R, hR, ?_⟩
  let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
  let mesh := ξ / (1 + A)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < 1 + A := by positivity
  have hmesh : 0 < mesh := div_pos hξ hden
  have herror : A * mesh < ξ := by
    rw [show A * mesh = ξ * (A / (1 + A)) by
      dsimp only [mesh]
      field_simp]
    have hratio : A / (1 + A) < 1 :=
      (div_lt_one hden).2 (by linarith only [hA])
    nlinarith only [hξ, hratio]
  obtain ⟨c, hc, hclose⟩ := hRapprox hmesh
  refine ⟨c, hc, ⟨?_⟩⟩
  have hsmall : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) < 1 := by
    calc
      Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
        dsimp only [A]
        ring
      _ < ξ := herror
      _ < 1 := hξ1
  let E := rationalSpanFamilyEncodingOfCoefficients S m c hc
  have hviable := isViable_spanColumnFamily_of_close_mulVec hΓ
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hmesh.le) hR) hsmall
    S Z c z hz W hW hunit hoverlap hclose
  apply E.coordinateViableMPSData D (spanColumnFamily_card_le S m c)
  apply hviable.mono_error
  have heq : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
    dsimp only [A]
    ring
  rw [heq]
  linarith only [herror]

/-- Target-error interface for successive coordinate-rational LVV trimming. -/
theorem exists_rationalCoordinateViableMPSData_of_mulVec_atTarget
    (S : Finset (LeftBlockVector L q k)) {m n s₀ b Hv : ℕ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ₀ : ℝ}
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δ₀ S)
    (hΓ : ‖Γ‖ = 1) {δ ξ δtarget : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hbudget : δ + 2 * ξ ≤ δtarget)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξ / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) δtarget
          (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hout⟩ := exists_rationalCoordinateViableMPSData_of_mulVec_atError
    S D hΓ hξ hξ1 Z hZ hZZ z hz W hW hunit hoverlap
  refine ⟨R, hR, ?_⟩
  obtain ⟨c, hc, ⟨D'⟩⟩ := hout
  exact ⟨c, hc, ⟨D'.mono_error hbudget⟩⟩

/-- A support isometry over a finite MPS family may be transported to an orthonormal
family spanning the same subspace.  The replacement has no larger cardinality and each
of its vectors has the finite-span bond budget `|S| max(1,b)`. -/
theorem exists_orthonormalBoundarySupport_isLeftOpenMPS
    (S : Finset (LeftBlockVector L q k)) (m b : ℕ)
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ S.card ∧ Orthonormal ℂ (fun t : T ↦ t.1) ∧
      Submodule.span ℂ (T : Set (LeftBlockVector L q k)) =
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      Z * Zᴴ = (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection (T : Set (LeftBlockVector L q k)))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ) := by
  obtain ⟨T, hcard, horth, hspan, hmps⟩ :=
    exists_orthonormal_isLeftOpenMPS_span_finset S hS
  have hproj : spanProjection (T : Set (LeftBlockVector L q k)) =
      spanProjection (S : Set (LeftBlockVector L q k)) := by
    simp only [spanProjection, hspan]
  exact ⟨T, hcard, horth, hspan, hmps, by simpa only [hproj] using hZZ⟩

/-- The auxiliary dimension of a support isometry is at most the dimension of the
retained left space times the bond dimension. -/
theorem boundarySupport_isometry_order_le
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    n ≤ S.card * m := by
  calc
    n = (1 : Matrix (Fin n) (Fin n) ℂ).rank := by simp
    _ = (Zᴴ * Z).rank := congrArg Matrix.rank hZ.symm
    _ ≤ Z.rank := Matrix.rank_mul_le_right _ _
    _ = (Z * Zᴴ).rank := (Matrix.rank_self_mul_conjTranspose Z).symm
    _ = ((reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ)).rank := congrArg Matrix.rank hZZ
    _ ≤ S.card * m := rank_boundarySupportProjection_le S m

/-- Every entry of an isometric compression is bounded by the operator norm of the
uncompressed observable. -/
theorem norm_isometricCompression_apply_le
    {a : Type*} [Fintype a] [DecidableEq a] {n : ℕ}
    (Z : Matrix a (Fin n) ℂ) (hZ : Zᴴ * Z = 1) (H : Matrix a a ℂ) (i j : Fin n) :
    ‖(Zᴴ * H * Z) i j‖ ≤ ‖H‖ :=
  (Matrix.norm_apply_le_l2_opNorm (Zᴴ * H * Z) i j).trans
    (l2_opNorm_isometricCompression_le Z hZ H)

/-- The physical LVV objective and a trace-norm-one boundary center have the common
dyadic entry bound `4L ≤ 2^(L+2)`.  Thus the bounded structured-input theorem may use
`R = 4L` and `u = L+2`, with no matrix-dependent radius. -/
theorem bounded_compressedObjective_and_boundaryCenter
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {n L : ℕ} (hL : 1 ≤ L) (Z : Matrix a (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (H : Matrix a a ℂ) (hH : ‖H‖ ≤ 4 * L) (X : Matrix b b ℂ)
    (hX : rectangularTraceNorm X ≤ 1) :
    0 ≤ (4 * L : ℝ) ∧
      (4 * L : ℝ) ≤ ((2 ^ (L + 2) : ℕ) : ℝ) ∧
      (∀ i j, ‖(Zᴴ * H * Z) i j‖ ≤ (4 * L : ℝ)) ∧
      ∀ i j, ‖X i j‖ ≤ (4 * L : ℝ) := by
  have hpowNat : 4 * L ≤ (2 : ℕ) ^ (L + 2) := by
    have hself' : ∀ r : ℕ, r ≤ (2 : ℕ) ^ r := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          rw [pow_succ]
          have hp : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_pow r 2 (by omega)
          omega
    have hself := hself' L
    rw [pow_add]
    norm_num
    simpa [mul_comm] using Nat.mul_le_mul_left 4 hself
  refine ⟨by positivity, by exact_mod_cast hpowNat, ?_, ?_⟩
  · intro i j
    exact (norm_isometricCompression_apply_le Z hZ H i j).trans hH
  · intro i j
    exact (Matrix.norm_apply_le_rectangularTraceNorm X i j).trans <|
      hX.trans (by exact_mod_cast (show 1 ≤ 4 * L by omega))

/-- If the retained support family is orthonormal, the support-isometry coefficients
may be chosen with modulus at most one.  They are the inner products of the retained
vectors with the corresponding bond slice. -/
theorem exists_boundarySupportOrthonormalCoordinateCoefficients
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ c : Fin n → Fin m → S → ℂ,
      (∀ j a, ∑ s : S, c j a s • s.1 =
        WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))) ∧
      ∀ j a s, ‖c j a s‖ ≤ 1 := by
  obtain ⟨c, hc⟩ := exists_boundarySupportCoordinateCoefficients S m Z hZ hZZ
  refine ⟨c, hc, ?_⟩
  intro j a s
  let u := gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j))
  let v : LeftBlockVector L q k := WithLp.toLp 2 (fun x ↦ u (x, a))
  have hv : ‖v‖ ≤ 1 := by
    calc
      ‖v‖ ≤ ‖u‖ := norm_euclidean_prod_slice_le u a
      _ = ‖(WithLp.toLp 2 (Z.col j) :
          EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))‖ :=
        (gluingLeftCoordinates L q k m).norm_map _
      _ = 1 := by
        change ‖(WithLp.toLp 2 (fun i ↦ Z i j) :
          EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))‖ = 1
        rw [Matrix.norm_column_eq_sqrt_gram, hZ, Matrix.one_apply, ite_eq_left rfl]
        norm_num
  have hcoeff : ⟪s.1, v⟫_ℂ = c j a s := by
    change ⟪s.1, WithLp.toLp 2 (fun x ↦
      gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))⟫_ℂ = c j a s
    rw [← hc j a]
    exact hS.inner_right_fintype (c j a) s
  rw [← hcoeff]
  exact (norm_inner_le_norm s.1 v).trans <| by
    rw [hS.norm_eq_one s, one_mul]
    exact hv

/-- For an orthonormal retained support family, every support isometry has rational
support coordinates of the universal grid height at radius one.  At mesh `δ`, every
reconstructed bond slice has error at most `|S| δ`; no condition-number parameter is
needed. -/
theorem exists_rational_boundarySupportOrthonormalCoordinates
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a s, HasRationalComplexCoordinatesOfHeight
        (rationalBoundedMatrixGridHeight 1 δ) (qc j a s)) ∧
      ∀ j a,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
          ∑ s : S, qc j a s • s.1‖ ≤ S.card * δ := by
  obtain ⟨c, hc, hcbound⟩ :=
    exists_boundarySupportOrthonormalCoordinateCoefficients S m Z hS hZ hZZ
  have hSbound : ∀ s : S, ‖s.1‖ ≤ 1 := fun s ↦ (hS.norm_eq_one s).le
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinateApproximation S c zero_le_one hδ
      hcbound hSbound
  refine ⟨qc, hqc, ?_⟩
  intro j a
  rw [← hc j a]
  simpa only [mul_one] using hclose j a

/-- If `n ≤ |S|m ≤ M` and the boundary order is at most `M`, the structured input has
at most `2(3M²+2)` rational scalar coordinates. -/
theorem structuredCompressedSDPInputRationalCoordinateCount_le_of_order_bounds
    (S : Finset (LeftBlockVector L q k)) {m n r M : ℕ}
    (hn : n ≤ S.card * m) (hSm : S.card * m ≤ M) (hr : r ≤ M) :
    structuredCompressedSDPInputRationalCoordinateCount S m n r ≤
      2 * (3 * M ^ 2 + 2) := by
  have hc := boundarySupportCoordinateCoefficientCount_le_sq S m n hn
  have hSm2 : (S.card * m) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hSm 2
  have hnM : n ≤ M := hn.trans hSm
  have hn2 : n ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hnM 2
  have hr2 : r ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hr 2
  unfold structuredCompressedSDPInputRationalCoordinateCount
  omega

/-- Exponentially bounded structured-coordinate height and polynomially bounded support
and boundary orders give an explicit polynomial structured-input bit-size bound. -/
theorem structuredCompressedSDPInputBitSizeBound_le_of_order_and_height_bounds
    (S : Finset (LeftBlockVector L q k)) {m n r H M p : ℕ}
    (hn : n ≤ S.card * m) (hSm : S.card * m ≤ M) (hr : r ≤ M)
    (hH : H ≤ 2 ^ p) :
    structuredCompressedSDPInputBitSizeBound S m n r H ≤
      2 * (3 * M ^ 2 + 2) * (p + 1) := by
  unfold structuredCompressedSDPInputBitSizeBound
  apply Nat.mul_le_mul
  · exact structuredCompressedSDPInputRationalCoordinateCount_le_of_order_bounds
      S hn hSm hr
  · apply Nat.add_le_add_right
    rw [Nat.log2_eq_log_two]
    calc
      Nat.log 2 H ≤ Nat.log 2 (2 ^ p) := Nat.log_mono_right hH
      _ = p := Nat.log_pow (by omega) p

/-- Canonical structured-coordinate bound, using the larger of the support order
`|S|m` and the boundary order `r`. -/
theorem structuredCompressedSDPInputRationalCoordinateCount_le_max_order
    (S : Finset (LeftBlockVector L q k)) {m n r : ℕ}
    (hn : n ≤ S.card * m) :
    structuredCompressedSDPInputRationalCoordinateCount S m n r ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) :=
  structuredCompressedSDPInputRationalCoordinateCount_le_of_order_bounds S hn
    (le_max_left _ _) (le_max_right _ _)

/-- Canonical structured bit-size bound at logarithmic height exponent `p`. -/
theorem structuredCompressedSDPInputBitSizeBound_le_max_order
    (S : Finset (LeftBlockVector L q k)) {m n r H p : ℕ}
    (hn : n ≤ S.card * m) (hH : H ≤ 2 ^ p) :
    structuredCompressedSDPInputBitSizeBound S m n r H ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) :=
  structuredCompressedSDPInputBitSizeBound_le_of_order_and_height_bounds S hn
    (le_max_left _ _) (le_max_right _ _) hH

/-- Separate exponential bounds for the support coefficients, objective, boundary
center, and shifts imply the canonical quadratic bit-size estimate for their common
structured encoding. -/
theorem structuredCompressedSDPInputBitSizeBound_le_of_component_height_bounds
    (S : Finset (LeftBlockVector L q k)) {m n r Hc HK HX Hε Hεb p : ℕ}
    (hn : n ≤ S.card * m) (hc : Hc ≤ 2 ^ p) (hK : HK ≤ 2 ^ p)
    (hX : HX ≤ 2 ^ p) (hε : Hε ≤ 2 ^ p) (hεb : Hεb ≤ 2 ^ p) :
    structuredCompressedSDPInputBitSizeBound S m n r
        (rationalStructuredCompressedSDPInputHeight Hc HK HX Hε Hεb) ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) :=
  structuredCompressedSDPInputBitSizeBound_le_max_order S hn
    (rationalStructuredCompressedSDPInputHeight_le_two_pow hc hK hX hε hεb)

/-- A structured rational encoding of height at most `2^p` has the canonical quadratic
bit-size bound. -/
theorem RationalStructuredCompressedSDPInputEncoding.bitSizeBound_le_max_order
    (S : Finset (LeftBlockVector L q k)) {m n r p : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hn : n ≤ S.card * m) (hheight : h.height ≤ 2 ^ p) :
    structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) :=
  structuredCompressedSDPInputBitSizeBound_le_max_order S hn hheight

/-- The orthonormal-support rational coordinates assemble with separately rational
objective, boundary, and shift data into a complete structured LVV input.  If all five
component heights are at most `2^p`, the resulting input has the canonical quadratic
bit-size bound. -/
theorem exists_rationalStructuredCompressedSDPInputEncoding_of_orthonormal
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (ε εb : ℝ) {HK HX Hε Hεb p : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hK : Matrix.HasRationalEntriesOfHeight HK K)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ))
    (hn : n ≤ S.card * m)
    (hcHeight : rationalBoundedMatrixGridHeight 1 δ ≤ 2 ^ p)
    (hKHeight : HK ≤ 2 ^ p) (hXHeight : HX ≤ 2 ^ p)
    (hεHeight : Hε ≤ 2 ^ p) (hεbHeight : Hεb ≤ 2 ^ p) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
          ∑ s : S, qc j a s • s.1‖ ≤ S.card * δ) ∧
      ∃ h : RationalStructuredCompressedSDPInputEncoding S m n r qc K X ε εb,
        structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
          2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) := by
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportOrthonormalCoordinates S m Z hS hZ hZZ hδ
  let h : RationalStructuredCompressedSDPInputEncoding S m n r qc K X ε εb :=
    rationalStructuredCompressedSDPInputEncodingOfHeightBounds S qc K X ε εb
      hqc hK hX hε hεb
  refine ⟨qc, hclose, h, ?_⟩
  apply h.bitSizeBound_le_max_order S hn
  exact rationalStructuredCompressedSDPInputHeight_le_two_pow hcHeight hKHeight
    hXHeight hεHeight hεbHeight

/-- Dyadic specialization of the orthonormal structured-input construction.  Precision
`2⁻ᵗ` gives coefficient height at most `2^(2t+5)` and hence an explicit bit-size bound
linear in `2t+6` per rational scalar coordinate. -/
theorem exists_dyadicRationalStructuredCompressedSDPInputEncoding_of_orthonormal
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (ε εb : ℝ) {HK HX Hε Hεb : ℕ} (t : ℕ)
    (hK : Matrix.HasRationalEntriesOfHeight HK K)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ))
    (hn : n ≤ S.card * m)
    (hKHeight : HK ≤ 2 ^ (2 * t + 5)) (hXHeight : HX ≤ 2 ^ (2 * t + 5))
    (hεHeight : Hε ≤ 2 ^ (2 * t + 5))
    (hεbHeight : Hεb ≤ 2 ^ (2 * t + 5)) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
          ∑ s : S, qc j a s • s.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
      ∃ h : RationalStructuredCompressedSDPInputEncoding S m n r qc K X ε εb,
        structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
          2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (2 * t + 6) := by
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    exists_rationalStructuredCompressedSDPInputEncoding_of_orthonormal
      S m Z hS hZ hZZ K X ε εb (inv_pos.mpr (by positivity)) hK hX hε hεb hn
      (rationalBoundedMatrixGridHeight_one_inv_two_pow_le t)
      hKHeight hXHeight hεHeight hεbHeight

/-- Bounded objective and boundary-center matrices can be rounded together with the
orthonormal support coordinates.  Radius `2^u` and mesh `2⁻ᵗ` give a common height
exponent `2u+2t+5`, entrywise matrix errors `2⁻ᵗ`, slice error `|S|2⁻ᵗ`, and the
displayed quadratic structured-input bit bound. -/
theorem exists_dyadicRationalStructuredCompressedSDPInputEncoding_of_bounded_orthonormal
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (ε εb : ℝ) {R : ℝ} (u t : ℕ) {Hε Hεb : ℕ}
    (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (hKbound : ∀ i j, ‖K i j‖ ≤ R) (hXbound : ∀ i j, ‖X i j‖ ≤ R)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ))
    (hn : n ≤ S.card * m)
    (hεHeight : Hε ≤ 2 ^ (2 * u + 2 * t + 5))
    (hεbHeight : Hεb ≤ 2 ^ (2 * u + 2 * t + 5)) :
    ∃ QK : Matrix (Fin n) (Fin n) ℂ,
      ∃ QX : Matrix (Fin r) (Fin r) ℂ,
        (∀ i j, ‖(K - QK) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
        (∀ i j, ‖(X - QX) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
        ∃ qc : Fin n → Fin m → S → ℂ,
          (∀ j a,
            ‖WithLp.toLp 2 (fun x ↦
                gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
              ∑ s : S, qc j a s • s.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
          ∃ h : RationalStructuredCompressedSDPInputEncoding S m n r qc QK QX ε εb,
            structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
              2 * (3 * (max (S.card * m) r) ^ 2 + 2) *
                (2 * u + 2 * t + 6) := by
  obtain ⟨QK, hQK, hQKclose⟩ :=
    exists_dyadic_rational_rectangular_approximation hR0 hR K hKbound
  obtain ⟨QX, hQX, hQXclose⟩ :=
    exists_dyadic_rational_rectangular_approximation hR0 hR X hXbound
  have hcHeight : rationalBoundedMatrixGridHeight 1 ((2 ^ t : ℝ)⁻¹) ≤
      2 ^ (2 * u + 2 * t + 5) := by
    exact (rationalBoundedMatrixGridHeight_one_inv_two_pow_le t).trans <|
      Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  obtain ⟨qc, hqcclose, h⟩ :=
    exists_rationalStructuredCompressedSDPInputEncoding_of_orthonormal
      S m Z hS hZ hZZ QK QX ε εb (inv_pos.mpr (by positivity)) hQK hQX hε hεb hn
      hcHeight le_rfl le_rfl hεHeight hεbHeight
  exact ⟨QK, QX, hQKclose, hQXclose, qc, hqcclose, h⟩

/-- Fully constructed dyadic structured input for the bounded orthonormal branch.  The
two cone shifts are the canonical positive rational tolerances below `2⁻ᵗ`, so no
external rational-height assumptions remain. -/
theorem exists_dyadicStructuredInput_of_bounded_orthonormal_withCanonicalShifts
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    {R : ℝ} (u t : ℕ) (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (hKbound : ∀ i j, ‖K i j‖ ≤ R) (hXbound : ∀ i j, ‖X i j‖ ≤ R)
    (hn : n ≤ S.card * m) :
    let ε := rationalPositiveTolerance ((2 ^ t : ℝ)⁻¹)
    ∃ QK : Matrix (Fin n) (Fin n) ℂ,
      ∃ QX : Matrix (Fin r) (Fin r) ℂ,
        (∀ i j, ‖(K - QK) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
        (∀ i j, ‖(X - QX) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
        ∃ qc : Fin n → Fin m → S → ℂ,
          (∀ j a,
            ‖WithLp.toLp 2 (fun x ↦
                gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
              ∑ s : S, qc j a s • s.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
          ∃ h : RationalStructuredCompressedSDPInputEncoding S m n r qc QK QX ε ε,
            structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
              2 * (3 * (max (S.card * m) r) ^ 2 + 2) *
                (2 * u + 2 * t + 6) := by
  dsimp only
  have hshift := rationalPositiveTolerance_inv_two_pow_hasRationalCoordinatesOfHeight t
  have hshiftHeight : 2 ^ (t + 2) ≤ 2 ^ (2 * u + 2 * t + 5) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact exists_dyadicRationalStructuredCompressedSDPInputEncoding_of_bounded_orthonormal
    S m Z hS hZ hZZ K X _ _ u t hR0 hR hKbound hXbound hshift hshift hn
    hshiftHeight hshiftHeight

/-- Fully constructed dyadic structured input for an arbitrary finite retained MPS
family.  The family is first replaced by a no-larger orthonormal family with the same
span; its vectors remain left-open matrix product states with bond dimension at most
`|S| max(1,b)`. -/
theorem exists_dyadicStructuredInput_of_bounded_isLeftOpenMPS_withCanonicalShifts
    (S : Finset (LeftBlockVector L q k)) (m b : ℕ)
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    {R : ℝ} (u t : ℕ) (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (hKbound : ∀ i j, ‖K i j‖ ≤ R) (hXbound : ∀ i j, ‖X i j‖ ≤ R) :
    let ε := rationalPositiveTolerance ((2 ^ t : ℝ)⁻¹)
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ S.card ∧
      Orthonormal ℂ (fun v : T ↦ v.1) ∧
      Submodule.span ℂ (T : Set (LeftBlockVector L q k)) =
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      ∃ QK : Matrix (Fin n) (Fin n) ℂ,
        ∃ QX : Matrix (Fin r) (Fin r) ℂ,
          (∀ i j, ‖(K - QK) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
          (∀ i j, ‖(X - QX) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
          ∃ qc : Fin n → Fin m → T → ℂ,
            (∀ j a,
              ‖WithLp.toLp 2 (fun x ↦
                  gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
                ∑ v : T, qc j a v • v.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
            (∀ p j, ‖(Z - boundarySupportMatrixOfCoordinates T m qc) p j‖ ≤
              S.card * (2 ^ t : ℝ)⁻¹) ∧
            ∃ h : RationalStructuredCompressedSDPInputEncoding T m n r qc QK QX ε ε,
              structuredCompressedSDPInputBitSizeBound T m n r h.height ≤
                2 * (3 * (max (S.card * m) r) ^ 2 + 2) *
                  (2 * u + 2 * t + 6) := by
  dsimp only
  obtain ⟨T, hcard, horth, hspan, hmps, hZZT⟩ :=
    exists_orthonormalBoundarySupport_isLeftOpenMPS S m b hS Z hZZ
  have hn : n ≤ T.card * m := boundarySupport_isometry_order_le T m Z hZ hZZT
  obtain ⟨QK, QX, hQK, hQX, qc, hqc, henc⟩ :=
    exists_dyadicStructuredInput_of_bounded_orthonormal_withCanonicalShifts
      T m Z horth hZ hZZT K X u t hR0 hR hKbound hXbound hn
  obtain ⟨h, henc⟩ := henc
  have hqcS : ∀ j a,
      ‖WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
        ∑ v : T, qc j a v • v.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹ := by
    intro j a
    exact (hqc j a).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity))
  have hencS : structuredCompressedSDPInputBitSizeBound T m n r h.height ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (2 * u + 2 * t + 6) := by
    refine henc.trans ?_
    gcongr
  have hQZS := norm_boundarySupportMatrixOfCoordinates_sub_apply_le T m Z qc hqcS
  exact ⟨T, hcard, horth, hspan, hmps, QK, QX, hQK, hQX, qc, hqcS, hQZS, h, hencS⟩

/-- Dyadic structured input for the physical LVV bounds.  If the uncompressed left
observable has norm at most `4L` and the boundary center has trace norm at most one,
then the common dyadic exponent is canonically `L+2`; no entrywise bounds or auxiliary
radius remain as hypotheses. -/
theorem exists_dyadicStructuredInput_of_physical_isLeftOpenMPS_withCanonicalShifts
    (S : Finset (LeftBlockVector L q k)) (m b : ℕ)
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) {n r : ℕ}
    (hL : 1 ≤ L)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (H : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
    (hH : ‖H‖ ≤ 4 * L) (X : Matrix (Fin r) (Fin r) ℂ)
    (hX : rectangularTraceNorm X ≤ 1) (t : ℕ) :
    let ε := rationalPositiveTolerance ((2 ^ t : ℝ)⁻¹)
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ S.card ∧
      Orthonormal ℂ (fun v : T ↦ v.1) ∧
      Submodule.span ℂ (T : Set (LeftBlockVector L q k)) =
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      ∃ QK : Matrix (Fin n) (Fin n) ℂ,
        ∃ QX : Matrix (Fin r) (Fin r) ℂ,
          (∀ i j, ‖(Zᴴ * H * Z - QK) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
          (∀ i j, ‖(X - QX) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
          ∃ qc : Fin n → Fin m → T → ℂ,
            (∀ j a,
              ‖WithLp.toLp 2 (fun x ↦
                  gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
                ∑ v : T, qc j a v • v.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
            (∀ p j, ‖(Z - boundarySupportMatrixOfCoordinates T m qc) p j‖ ≤
              S.card * (2 ^ t : ℝ)⁻¹) ∧
            ∃ h : RationalStructuredCompressedSDPInputEncoding T m n r qc QK QX ε ε,
              structuredCompressedSDPInputBitSizeBound T m n r h.height ≤
                2 * (3 * (max (S.card * m) r) ^ 2 + 2) *
                  (2 * (L + 2) + 2 * t + 6) := by
  obtain ⟨hR0, hR, hKbound, hXbound⟩ :=
    bounded_compressedObjective_and_boundaryCenter hL Z hZ H hH X hX
  obtain ⟨T, hcard, horth, hspan, hmps, QK, QX, hQK, hQX, qc, hqc, hQZ, henc⟩ :=
    exists_dyadicStructuredInput_of_bounded_isLeftOpenMPS_withCanonicalShifts
      S m b hS Z hZ hZZ (Zᴴ * H * Z) X (L + 2) t hR0 hR hKbound hXbound
  exact ⟨T, hcard, horth, hspan, hmps, QK, QX, hQK, hQX, qc, hqc, hQZ, henc⟩

/-- A support isometry admits structured coefficients together with the canonical
quadratic input-size bound.  This combines the geometric coordinate construction with
the structured rational-input accounting. -/
theorem exists_boundarySupportCoordinateCoefficients_with_bitSizeBound
    (S : Finset (LeftBlockVector L q k)) (m r H p : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hn : n ≤ S.card * m) (hH : H ≤ 2 ^ p)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ c : Fin n → Fin m → S → ℂ,
      (∀ j a, ∑ s : S, c j a s • s.1 =
        WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))) ∧
      structuredCompressedSDPInputBitSizeBound S m n r H ≤
        2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) := by
  obtain ⟨c, hc⟩ := exists_boundarySupportCoordinateCoefficients S m Z hZ hZZ
  exact ⟨c, hc, structuredCompressedSDPInputBitSizeBound_le_max_order S hn hH⟩

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

namespace IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy

set_option maxHeartbeats 400000 in
-- Elaborating the explicit cost inequality unfolds several nested cardinality bounds.
/-- Completeness after rational approximation of all fixed data, paired with the
schoolbook bit-cost bound for the same executable search.  The operand length is the
canonical height determined by the three input codes and the two cone shifts. -/
theorem exists_approx_data_search_result_and_cost_le
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
      let C := approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ)
      (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 * (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ)) ≤
          (Dt : ℝ)) :
    let r := Fintype.card (s × b)
    let θA := rationalUniformCertificateRoundingMesh n ρ
    let θb := rationalUniformCertificateRoundingMesh r ρ
    let bitLength := rationalCertificateOperandBitLength (Fintype.card a) (s × b)
      n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
        (rationalCompressedSDPInputCodeHeight QZ QK QX ε εb)
        ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
        ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
    (∃ c, searchRationalCertificateCodeGridOfTolerances
      η κ ε εb ρ QZ QK QX ε εb
      (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c) ∧
    uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
        n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
      uniformCertificateSearchCardBound (s × b)
          n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
        ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
          (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
            (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
              (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
          rationalSchoolbookOperationCost bitLength := by
  dsimp only
  constructor
  · exact h.exists_approx_data_search_result QZ QK QX hZ hρ hθZ
      hZclose hKclose hXclose hEt hDt
  · exact uniformCertificateSearchSchoolbookBitCost_le_uniformOperandBound
      (Fintype.card a) _
      (s × b) n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)

set_option maxHeartbeats 400000 in
-- The conclusion retains the complete explicit cost expression for the selected codes.
/-- End-to-end selection of rational fixed-data codes.  Bounded exact data determine
codes at the prescribed meshes; their canonical common height has the explicit grid
bound, and the resulting executable search succeeds with its schoolbook cost bound. -/
theorem exists_fixed_data_codes_search_result_and_cost_le
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ Et Dt : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ)
    (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX)
    (hEt : let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK ≤ (Et : ℝ))
    (hDt : let r := Fintype.card (s × b)
      let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 * (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ)) ≤
          (Dt : ℝ)) :
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
              rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb ∧
          (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
          (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
          (∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) ∧
          let r := Fintype.card (s × b)
          let θA := rationalUniformCertificateRoundingMesh n ρ
          let θb := rationalUniformCertificateRoundingMesh r ρ
          let bitLength := rationalCertificateOperandBitLength
            (Fintype.card a) (s × b)
            n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
              (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
              ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
              ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
          (∃ c, searchRationalCertificateCodeGridOfTolerances
            η κ ε εb ρ QZ QK QX ε εb
            (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
            ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c) ∧
          uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
              n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
            uniformCertificateSearchCardBound (s × b)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
              ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
                (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
                  (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
                    (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
                rationalSchoolbookOperationCost bitLength := by
  obtain ⟨QZ, QK, QX, hheight, hZclose, hKclose, hXclose⟩ :=
    exists_rational_fixed_data_codes_with_common_height
      Z hZ K X ε εb hRK hRX hθZ hθK hθX hK hX
  refine ⟨QZ, QK, QX, hheight, hZclose, hKclose, hXclose, ?_⟩
  dsimp only
  constructor
  · exact h.exists_approx_data_search_result QZ QK QX hZ hρ hθZ.le
      hZclose hKclose hXclose hEt hDt
  · exact uniformCertificateSearchSchoolbookBitCost_le_uniformOperandBound
      (Fintype.card a) _
      (s × b) n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)

set_option maxHeartbeats 400000 in
-- The explicit search-and-cost conclusion contains several nested cardinality bounds.
/-- The end-to-end fixed-data search with no external threshold choices.  The objective
and boundary thresholds are the canonical rational ceilings of their exact real loss
expressions. -/
theorem exists_fixed_data_codes_search_result_and_cost_le_canonical_thresholds
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ)
    (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    let r := Fintype.card (s × b)
    let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
    let Dt := rationalApproxDataBoundaryThreshold
      (Fintype.card a) n r δ κ ε ρ θZ θX
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
              rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb ∧
          (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
          (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
          (∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) ∧
          let θA := rationalUniformCertificateRoundingMesh n ρ
          let θb := rationalUniformCertificateRoundingMesh r ρ
          let bitLength := rationalCertificateOperandBitLength
            (Fintype.card a) (s × b)
            n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
              (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
              ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
              ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
          (∃ c, searchRationalCertificateCodeGridOfTolerances
            η κ ε εb ρ QZ QK QX ε εb
            (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
            ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c) ∧
          uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
              n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
            uniformCertificateSearchCardBound (s × b)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
              ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
                (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
                  (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
                    (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
                rationalSchoolbookOperationCost bitLength := by
  dsimp only
  apply h.exists_fixed_data_codes_search_result_and_cost_le hZ hρ hRK hRX
    hθZ hθK hθX hK hX
  · exact le_rationalApproxDataEnergyThreshold n E κ ε ρ K θK
  · exact le_rationalApproxDataBoundaryThreshold
      (Fintype.card a) n (Fintype.card (s × b)) δ κ ε ρ θZ θX

/-- Compact canonical-search package for downstream physical soundness.  It retains the
selected fixed-data codes, their common height bound, all three approximation witnesses,
the returned certificate code, the exact executable search equation, and the schoolbook
bit-cost bound for that same search. -/
theorem exists_fixed_data_codes_and_search_result_canonical_thresholds
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ)
    (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    let r := Fintype.card (s × b)
    let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
    let Dt := rationalApproxDataBoundaryThreshold
      (Fintype.card a) n r δ κ ε ρ θZ θX
    let θA := rationalUniformCertificateRoundingMesh n ρ
    let θb := rationalUniformCertificateRoundingMesh r ρ
    let bitLength := rationalCertificateOperandBitLength
      (Fintype.card a) (s × b) n
      (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
      (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
      ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          ∃ c : RationalCertificateCode (s × b) n,
            rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
                rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb ∧
            (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
            (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
            (∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) ∧
            searchRationalCertificateCodeGridOfTolerances
              η κ ε εb ρ QZ QK QX ε εb
              (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
              ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c ∧
            uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
              uniformCertificateSearchCardBound (s × b)
                  n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
                ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
                  (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
                    (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
                      (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
                  rationalSchoolbookOperationCost bitLength := by
  dsimp only
  obtain ⟨QZ, QK, QX, hheight, hZclose, hKclose, hXclose, hsearch, hcost⟩ :=
    h.exists_fixed_data_codes_search_result_and_cost_le_canonical_thresholds
      hZ hρ hRK hRX hθZ hθK hθX hK hX
  obtain ⟨c, hfind⟩ := hsearch
  exact ⟨QZ, QK, QX, c, hheight, hZclose, hKclose, hXclose, hfind, hcost⟩

end IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy

/-- Every exact feasible compressed SDP point is a fully approximate feasible point with
all four error parameters equal to zero. -/
theorem IsCompressedBoundarySDPFeasibleAtEnergy.toAllSpectralApprox
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E A P N) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E 0 0 0 0 A P N := by
  rcases h with ⟨hA, hAtrace, hP, hN, hsub, htraces, henergy⟩
  have hAmin : 0 ≤ minEigenvalue hA.isHermitian := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hA.isHermitian
    rw [← hi]
    exact hA.eigenvalues_nonneg i
  have hPmin : 0 ≤ minEigenvalue hP.isHermitian := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hP.isHermitian
    rw [← hi]
    exact hP.eigenvalues_nonneg i
  have hNmin : 0 ≤ minEigenvalue hN.isHermitian := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hN.isHermitian
    rw [← hi]
    exact hN.eigenvalues_nonneg i
  refine ⟨hA.isHermitian, hP.isHermitian, hN.isHermitian, ?_, by norm_num,
    ?_, by norm_num, ?_, ?_, ?_, htraces, henergy⟩
  · rw [hAtrace]
    norm_num
  · simpa only [neg_zero] using hAmin
  · simpa only [neg_zero] using hPmin
  · simpa only [neg_zero] using hNmin
  · rw [hsub, sub_self, rectangularTraceNorm_zero]

/-- An exact feasible density produces auxiliary matrices satisfying the unified
finite-precision feasibility statement with every error parameter equal to zero. -/
theorem exists_allSpectralApproxCompressedBoundarySDPFeasibleAtEnergy_zero
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) {η E : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hAtrace : A.trace = 1)
    (hAboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η)
    (hAenergy : (A * K).trace.re ≤ E) :
    ∃ P N : Matrix (s × b) (s × b) ℂ,
      IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
        Z K X η E 0 0 0 0 A P N := by
  obtain ⟨P, N, hP, hN, hsub, htraces⟩ :=
    (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
      Z hA.isHermitian X hX η).mp hAboundary
  exact ⟨P, N,
    IsCompressedBoundarySDPFeasibleAtEnergy.toAllSpectralApprox
      ⟨hA, hAtrace, hP, hN, hsub, htraces, hAenergy⟩⟩

/-- A numerical semidefinite certificate may also violate positivity of the auxiliary
boundary matrices by `εb`.  Repairing both by the same shift preserves their difference
and adds only `2 r εb` to the boundary trace budget. -/
theorem exists_density_of_all_spectral_approx_sdp_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {P N : Matrix (s × b) (s × b) ℂ} (hP : P.IsHermitian) (hN : N.IsHermitian)
    {η E δ κ ε εb : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hPmin : -εb ≤ minEigenvalue hP)
    (hNmin : -εb ≤ minEigenvalue hN)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        (η + 2 * Fintype.card (s × b) * εb) + δ + (κ + 2 * n * ε) ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (κ + 2 * n * ε) := by
  obtain ⟨P₀, N₀, hP₀, hN₀, hsub, htrace₀⟩ :=
    exists_posSemidef_pair_same_sub_of_neg_le_minEigenvalue
      hP hN hPmin hNmin
  have hresidual₀ : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P₀ - N₀)) ≤ δ := by
    rwa [hsub]
  have htraces₀ : P₀.trace.re + N₀.trace.re ≤
      η + 2 * Fintype.card (s × b) * εb := by
    rw [htrace₀]
    linarith
  exact exists_density_of_fully_approx_sdp_certificate
    Z hZ K X hA hP₀ hN₀ htrace hε hmin hresidual₀ htraces₀ henergy

/-- Every fully approximate feasible certificate repairs to an exact density with the
explicit trace-norm, boundary, and objective losses. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_density
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ} (hZ : Zᴴ * Z = 1)
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        (η + 2 * Fintype.card (s × b) * εb) + δ + (κ + 2 * n * ε) ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (κ + 2 * n * ε) := by
  rcases h with ⟨hA, hP, hN, htrace, hε, hmin, _hεb, hPmin, hNmin,
    hresidual, htraces, henergy⟩
  exact exists_density_of_all_spectral_approx_sdp_certificate
    Z hZ K X hA hP hN htrace hε hmin hPmin hNmin hresidual htraces henergy

/-- Equal independent precision targets for the four scalar losses in the fully
approximate semidefinite certificate fit inside the unused LVV margin.  Here `n` is
the compressed density dimension and `r` is the boundary-matrix dimension. -/
theorem fullyApproxSDP_errors_fit_lvv_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ : ℝ}
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : 2 * n * ε ≤ Δ / (64896 * L))
    (hεb : 2 * r * εb ≤ Δ / (64896 * L))
    (hδ : δ ≤ Δ / (64896 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * ((2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hκ' := (le_div_iff₀ hden).1 hκ
  have hε' := (le_div_iff₀ hden).1 hε
  have hεb' := (le_div_iff₀ hden).1 hεb
  have hδ' := (le_div_iff₀ hden).1 hδ
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2028)).2
  nlinarith only [hκ', hε', hεb', hδ']

/-- The same independent precision target also absorbs rational approximation of the
coordinate isometry.  The fifth loss `ω` is added only to the boundary-equation error,
while physical expansion continues to use the exact isometry. -/
theorem fullyApproxSDP_errors_with_coordinate_fit_lvv_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ ω : ℝ}
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : 2 * n * ε ≤ Δ / (64896 * L))
    (hεb : 2 * r * εb ≤ Δ / (64896 * L))
    (hδω : δ + ω ≤ Δ / (64896 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * (((2 * r * εb + δ) + ω) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  simpa only [add_assoc] using
    fullyApproxSDP_errors_fit_lvv_margin hL hκ hε hεb hδω

/-- Splitting the former boundary-equation precision target equally between solver
residual and coordinate-map approximation gives explicit independent targets for all
five losses. -/
theorem fullyApproxSDP_errors_with_coordinate_fit_lvv_margin_of_split
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ ω : ℝ}
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : 2 * n * ε ≤ Δ / (64896 * L))
    (hεb : 2 * r * εb ≤ Δ / (64896 * L))
    (hδ : δ ≤ Δ / (129792 * L))
    (hω : ω ≤ Δ / (129792 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * (((2 * r * εb + δ) + ω) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  apply fullyApproxSDP_errors_with_coordinate_fit_lvv_margin hL hκ hε hεb
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden : (129792 : ℝ) * L ≠ 0 := (mul_pos (by norm_num) hLreal).ne'
  calc
    δ + ω ≤ Δ / (129792 * L) + Δ / (129792 * L) := add_le_add hδ hω
    _ = Δ / (64896 * L) := by field_simp; ring

/-- Independent precision targets that also absorb rational approximation of the
objective matrix and boundary-net center.  The four original spectral and residual
losses use one half of the LVV margin.  The other half is divided between the
objective error `eK`, which enters the energy directly, and the two boundary errors
`eX` and `ω`, which enter after multiplication by the Hamiltonian norm bound. -/
theorem fullyApproxSDP_errors_with_fixed_data_fit_lvv_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ eK eX ω : ℝ}
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (129792 * L))
    (heK : eK ≤ Δ / 16224)
    (heX : eX ≤ Δ / (64896 * L))
    (hω : ω ≤ Δ / (64896 * L)) :
    2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((((2 * r * εb + δ) + eX) + ω) + (κ + 2 * n * ε))) ≤
        Δ / 2028 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden₁ : 0 < (129792 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hden₂ : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hκ' := (le_div_iff₀ hden₁).1 hκ
  have hε' := (le_div_iff₀ hden₁).1 hε
  have hεb' := (le_div_iff₀ hden₁).1 hεb
  have hδ' := (le_div_iff₀ hden₁).1 hδ
  have heK' := (le_div_iff₀ (by norm_num : (0 : ℝ) < 16224)).1 heK
  have heX' := (le_div_iff₀ hden₂).1 heX
  have hω' := (le_div_iff₀ hden₂).1 hω
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2028)).2
  nlinarith only [hκ', hε', hεb', hδ', heK', heX', hω']

/-- Independent bounds for a numerical certificate with both energy-threshold slack and
auxiliary-trace slack.  The residual and trace slack split one boundary-error share. -/
theorem fullyApproxSDP_errors_with_trace_energy_slack_fit_lvv_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ eη eK : ℝ}
    (hΔ : 0 ≤ Δ)
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (259584 * L))
    (heη : eη ≤ Δ / (259584 * L))
    (heK : eK ≤ Δ / 16224) :
    2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((eη + 2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  have hδ' : eη + δ ≤ Δ / (129792 * L) := by
    have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
    have hden : (259584 : ℝ) * L ≠ 0 := (mul_pos (by norm_num) hLreal).ne'
    calc
      eη + δ ≤ Δ / (259584 * L) + Δ / (259584 * L) := add_le_add heη hδ
      _ = Δ / (129792 * L) := by field_simp; ring
  have hfit := fullyApproxSDP_errors_with_fixed_data_fit_lvv_margin hL hκ hε hεb
    hδ' heK (by positivity) (by positivity)
  convert hfit using 1
  all_goals ring

/-- The canonical trace-, spectral-, boundary-, and energy-slack thresholds in fact use
only three quarters of the final LVV margin.  The remaining quarter is available for
rationalizing the selected physical columns. -/
theorem fullyApproxSDP_errors_with_trace_energy_slack_fit_rationalization_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ eη eK : ℝ}
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (259584 * L))
    (heη : eη ≤ Δ / (259584 * L))
    (heK : eK ≤ Δ / 16224) :
    2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((eη + 2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2704 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden₁ : 0 < (129792 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hden₂ : 0 < (259584 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hκ' := (le_div_iff₀ hden₁).1 hκ
  have hε' := (le_div_iff₀ hden₁).1 hε
  have hεb' := (le_div_iff₀ hden₁).1 hεb
  have hδ' := (le_div_iff₀ hden₂).1 hδ
  have heη' := (le_div_iff₀ hden₂).1 heη
  have heK' := (le_div_iff₀ (by norm_num : (0 : ℝ) < 16224)).1 heK
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2704)).2
  nlinarith only [hκ', hε', hεb', hδ', heη', heK']

/-- Entrywise mesh target for rational approximation of the compressed objective.
The added `1` makes the target meaningful without a separate nonvanishing assumption
on the matrix order or candidate entry bound. -/
noncomputable def rationalObjectiveApproximationTarget (n : ℕ) (C Δ : ℝ) : ℝ :=
  Δ / (16224 * ((n : ℝ) ^ 2 * C + 1))

/-- Entrywise mesh target for rational approximation of the boundary-net center.  Its
dependence on `L` reflects the Hamiltonian norm factor in the LVV energy estimate. -/
noncomputable def rationalBoundaryCenterApproximationTarget (L r : ℕ) (Δ : ℝ) : ℝ :=
  Δ / (64896 * L * ((r : ℝ) ^ 2 + 1))

theorem rationalObjectiveApproximationTarget_pos
    {n : ℕ} {C Δ : ℝ} (hC : 0 ≤ C) (hΔ : 0 < Δ) :
    0 < rationalObjectiveApproximationTarget n C Δ := by
  unfold rationalObjectiveApproximationTarget
  positivity

theorem rationalBoundaryCenterApproximationTarget_pos
    {L r : ℕ} (hL : 0 < L) {Δ : ℝ} (hΔ : 0 < Δ) :
    0 < rationalBoundaryCenterApproximationTarget L r Δ := by
  unfold rationalBoundaryCenterApproximationTarget
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  positivity

/-- The objective mesh target makes the energy loss fit its allocated part of the LVV
margin. -/
theorem objective_approximation_error_le_lvv_target
    {n : ℕ} {C Δ θ : ℝ} (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hmesh : θ ≤ rationalObjectiveApproximationTarget n C Δ) :
    (n : ℝ) ^ 2 * C * θ ≤ Δ / 16224 := by
  have hfactor : 0 ≤ (n : ℝ) ^ 2 * C := mul_nonneg (sq_nonneg _) hC
  calc
    (n : ℝ) ^ 2 * C * θ ≤
        (n : ℝ) ^ 2 * C * rationalObjectiveApproximationTarget n C Δ :=
      mul_le_mul_of_nonneg_left hmesh hfactor
    _ ≤ Δ / 16224 := by
      unfold rationalObjectiveApproximationTarget
      have hden : 0 < 16224 * ((n : ℝ) ^ 2 * C + 1) := by positivity
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).2
      field_simp
      nlinarith

/-- The boundary-center mesh target makes its trace-norm loss fit its allocated part
of the LVV margin. -/
theorem boundaryCenter_approximation_error_le_lvv_target
    {L r : ℕ} (hL : 0 < L) {Δ θ : ℝ} (hΔ : 0 ≤ Δ)
    (hmesh : θ ≤ rationalBoundaryCenterApproximationTarget L r Δ) :
    (r : ℝ) ^ 2 * θ ≤ Δ / (64896 * L) := by
  have hr : 0 ≤ (r : ℝ) ^ 2 := sq_nonneg _
  calc
    (r : ℝ) ^ 2 * θ ≤
        (r : ℝ) ^ 2 * rationalBoundaryCenterApproximationTarget L r Δ :=
      mul_le_mul_of_nonneg_left hmesh hr
    _ ≤ Δ / (64896 * L) := by
      unfold rationalBoundaryCenterApproximationTarget
      have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
      have hden : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
      have hplus : 0 < (r : ℝ) ^ 2 + 1 := by positivity
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (mul_pos hden hplus)).2
      field_simp
      nlinarith [mul_nonneg hΔ hr]

/-- The canonical objective and boundary-center meshes, together with the allocated
spectral, residual, and coordinate tolerances, imply the complete LVV margin bound. -/
theorem fullyApproxSDP_errors_fit_lvv_margin_of_fixed_data_meshes
    {L n r : ℕ} (hL : 0 < L) {Δ C κ ε εb δ θK θX ω : ℝ}
    (hΔ : 0 ≤ Δ) (hC : 0 ≤ C)
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (129792 * L))
    (hθK : θK ≤ rationalObjectiveApproximationTarget n C Δ)
    (hθX : θX ≤ rationalBoundaryCenterApproximationTarget L r Δ)
    (hω : ω ≤ Δ / (64896 * L)) :
    2 * ((4 * L * (κ + 2 * n * ε) + (n : ℝ) ^ 2 * C * θK) +
      2 * L * ((((2 * r * εb + δ) + (r : ℝ) ^ 2 * θX) + ω) +
        (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  apply fullyApproxSDP_errors_with_fixed_data_fit_lvv_margin hL hκ hε hεb hδ
  · exact objective_approximation_error_le_lvv_target hC hΔ hθK
  · exact boundaryCenter_approximation_error_le_lvv_target hL hΔ hθX
  · exact hω

/-- Explicit tolerances on the two spectral errors imply the four independent loss
bounds used in `fullyApproxSDP_errors_fit_lvv_margin`.  The required inverse tolerances
are linear in the matrix orders `n`, `r` and in the chain length `L` (and inverse-linear
in the gap `Δ`).  This quantifies the numerical precision required by the finite LVV
semidefinite program without selecting a particular numerical solver. -/
theorem fullyApproxSDP_errors_fit_lvv_margin_of_tolerances
    {L n r : ℕ} (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    {Δ κ ε εb δ : ℝ}
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : ε ≤ Δ / ((129792 : ℝ) * L * n))
    (hεb : εb ≤ Δ / ((129792 : ℝ) * L * r))
    (hδ : δ ≤ Δ / (64896 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * ((2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  have hdenL : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hdenN : 0 < (129792 : ℝ) * L * n :=
    mul_pos (mul_pos (by norm_num) hLreal) hnreal
  have hdenR : 0 < (129792 : ℝ) * L * r :=
    mul_pos (mul_pos (by norm_num) hLreal) hrreal
  have hε' : 2 * n * ε ≤ Δ / (64896 * L) := by
    apply (le_div_iff₀ hdenL).2
    have hεmul := (le_div_iff₀ hdenN).1 hε
    nlinarith only [hεmul]
  have hεb' : 2 * r * εb ≤ Δ / (64896 * L) := by
    apply (le_div_iff₀ hdenL).2
    have hεbmul := (le_div_iff₀ hdenR).1 hεb
    nlinarith only [hεbmul]
  exact fullyApproxSDP_errors_fit_lvv_margin hL hκ hε' hεb' hδ

/-- Tolerances chosen from upper bounds on the two cone orders imply the corresponding
realized spectral-error bounds. -/
theorem fullyApproxSDP_scaled_errors_of_order_bounds
    {L n r nMax rMax : ℕ} (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    (hnMax : n ≤ nMax) (hrMax : r ≤ rMax)
    {Δ ε εb : ℝ} (hεnonneg : 0 ≤ ε) (hεbnonneg : 0 ≤ εb)
    (hε : ε ≤ Δ / ((129792 : ℝ) * L * nMax))
    (hεb : εb ≤ Δ / ((129792 : ℝ) * L * rMax)) :
    2 * n * ε ≤ Δ / (64896 * L) ∧
      2 * r * εb ≤ Δ / (64896 * L) := by
  have hnMaxpos : 0 < nMax := hn.trans_le hnMax
  have hrMaxpos : 0 < rMax := hr.trans_le hrMax
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hnMaxreal : 0 < (nMax : ℝ) := by exact_mod_cast hnMaxpos
  have hrMaxreal : 0 < (rMax : ℝ) := by exact_mod_cast hrMaxpos
  have hdenL : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hdenN : 0 < (129792 : ℝ) * L * nMax :=
    mul_pos (mul_pos (by norm_num) hLreal) hnMaxreal
  have hdenR : 0 < (129792 : ℝ) * L * rMax :=
    mul_pos (mul_pos (by norm_num) hLreal) hrMaxreal
  have hεMax : 2 * nMax * ε ≤ Δ / (64896 * L) := by
    apply (le_div_iff₀ hdenL).2
    have hεmul := (le_div_iff₀ hdenN).1 hε
    nlinarith only [hεmul]
  have hεbMax : 2 * rMax * εb ≤ Δ / (64896 * L) := by
    apply (le_div_iff₀ hdenL).2
    have hεbmul := (le_div_iff₀ hdenR).1 hεb
    nlinarith only [hεbmul]
  have hε' : 2 * n * ε ≤ Δ / (64896 * L) := by
    refine le_trans ?_ hεMax
    gcongr
  have hεb' : 2 * r * εb ≤ Δ / (64896 * L) := by
    refine le_trans ?_ hεbMax
    gcongr
  exact ⟨hε', hεb'⟩

/-- A priori upper bounds for the two matrix orders give uniform solver tolerances.
Consequently the numerical precision can be fixed before the support coordinates and
the actual boundary order are constructed. -/
theorem fullyApproxSDP_errors_fit_lvv_margin_of_order_bounds
    {L n r nMax rMax : ℕ} (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    (hnMax : n ≤ nMax) (hrMax : r ≤ rMax)
    {Δ κ ε εb δ : ℝ} (hεnonneg : 0 ≤ ε) (hεbnonneg : 0 ≤ εb)
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : ε ≤ Δ / ((129792 : ℝ) * L * nMax))
    (hεb : εb ≤ Δ / ((129792 : ℝ) * L * rMax))
    (hδ : δ ≤ Δ / (64896 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * ((2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  obtain ⟨hε', hεb'⟩ := fullyApproxSDP_scaled_errors_of_order_bounds
    hL hn hr hnMax hrMax hεnonneg hεbnonneg hε hεb
  exact fullyApproxSDP_errors_fit_lvv_margin hL hκ hε' hεb' hδ

/-- Chain specialization of the uniform tolerance theorem.  The density tolerance is
chosen from the retained-support bound `|S| m`, and the auxiliary-matrix tolerance from
the boundary bound `q m`; neither depends on the subsequently constructed coordinate
isometry. -/
theorem chain_fullyApproxSDP_errors_fit_lvv_margin_of_support_bounds
    {L q k m n : ℕ} (S : Finset (LeftBlockVector L q k))
    (hL : 0 < L) (hq : 1 ≤ q) (hnpos : 0 < n)
    (hrpos : 0 < Fintype.card (CutSite L q k × Fin m))
    (hn : n ≤ S.card * m) {Δ κ ε εb δ : ℝ}
    (hεnonneg : 0 ≤ ε) (hεbnonneg : 0 ≤ εb)
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : ε ≤ Δ / ((129792 : ℝ) * L * (S.card * m)))
    (hεb : εb ≤ Δ / ((129792 : ℝ) * L * (q * m)))
    (hδ : δ ≤ Δ / (64896 * L)) :
    let r := Fintype.card (CutSite L q k × Fin m)
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * ((2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  classical
  intro r
  have hr : r ≤ q * m := by
    simpa only [r, Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_le_mul (card_cutSite_le (L := L) (k := k) hq) (Nat.le_refl m)
  apply fullyApproxSDP_errors_fit_lvv_margin_of_order_bounds
    hL hnpos hrpos hn hr hεnonneg hεbnonneg hκ
  · simpa only [Nat.cast_mul] using hε
  · simpa only [Nat.cast_mul] using hεb
  · exact hδ

end TNLean.MPS.AreaLaw
