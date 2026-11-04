/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.GluingCoordinates
import TNLean.MPS.AreaLaw.ViableSet.LeftColumns
import TNLean.Algebra.MatrixProjectionReindex
import QICLean.Algebra.MatrixRankKronecker
import QICLean.Algebra.PositiveSemidefiniteNormalization
import QICLean.Algebra.ProjectionRangeIsometry
import QICLean.Analysis.IsometricDomainExtension
import QICLean.Channel.RectangularTraceNormContraction
import QICLean.Channel.BoundaryDensitySelection
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# A finite family of minimizing boundary states

For every feasible point in a prescribed finite boundary set, choose a density matrix that
globally minimizes the left energy and a unit eigenvector for its largest eigenvalue. The
left columns of these vectors form an explicit finite set contained in the prescribed left
span. The choices use only that span, the left Hamiltonian, the bond dimension and the
boundary set; no ground vector or physical extension of the right bond is supplied.

This is an auxiliary construction for Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`References/1307.5143/algo53.tex`, equation `eq:conv`, lines 472–476, the column extraction,
lines 477–478, and Claim `c:2`, lines 520–527. Only feasible boundary points are retained.
The theorem concerns a fixed actual bond dimension and asserts neither viability nor the
source's quantitative AKLV bound. It asserts no matrix product state bond budget; the
positive-budget convention of `IsLeftOpenMPS` remains in that definition.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- For a positive semidefinite matrix, the rectangular trace norm is its real trace. -/
theorem rectangularTraceNorm_eq_re_trace_of_posSemidef {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    rectangularTraceNorm A = A.trace.re := by
  classical
  rw [Matrix.rectangularTraceNorm_eq_re_trace_abs,
    CFC.abs_of_nonneg _ hA.nonneg]

/-- Total trace normalization of a positive matrix changes it in trace norm by exactly its
trace defect. Thus an approximate trace constraint can be repaired without a dimension
factor or an additional loss. -/
theorem rectangularTraceNorm_normalizePosSemidef_sub
    {n : Type*} [Fintype n] [DecidableEq n] (x₀ : n)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    rectangularTraceNorm (Matrix.normalizePosSemidef x₀ A - A) = |1 - A.trace.re| := by
  classical
  let A₀ := Matrix.normalizePosSemidef x₀ A
  have hscale : (A.trace.re : ℂ) • A₀ = A := by
    simpa only [A₀] using Matrix.trace_re_smul_normalizePosSemidef x₀ hA
  have hA₀psd : A₀.PosSemidef := by
    exact Matrix.normalizePosSemidef_posSemidef x₀ hA
  have hA₀trace : A₀.trace = 1 := by
    exact Matrix.normalizePosSemidef_trace x₀ hA
  have heq : A₀ - A = ((1 - A.trace.re : ℝ) : ℂ) • A₀ := by
    calc
      A₀ - A = A₀ - (A.trace.re : ℂ) • A₀ :=
        congrArg (fun B : Matrix n n ℂ ↦ A₀ - B) hscale.symm
      _ = ((1 - A.trace.re : ℝ) : ℂ) • A₀ := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        ring
  rw [heq, Matrix.rectangularTraceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
    rectangularTraceNorm_eq_re_trace_of_posSemidef hA₀psd, hA₀trace, Complex.one_re, mul_one]

/-- Tracing out the first factor does not increase the rectangular trace norm. -/
theorem rectangularTraceNorm_partialTraceLeft_le {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (X : Matrix (a × b) (a × b) ℂ) :
    rectangularTraceNorm (Matrix.partialTraceLeft X) ≤ rectangularTraceNorm X := by
  let e : a × b ≃ b × a := Equiv.prodComm a b
  have heq : Matrix.partialTraceLeft X =
      Matrix.partialTraceRight (Matrix.reindex e e X) := by
    ext i j
    simp only [Matrix.partialTraceLeft_apply, Matrix.partialTraceRight_apply,
      Matrix.reindex_apply, e]
    rfl
  rw [heq]
  exact (Matrix.rectangularTraceNorm_partialTraceRight_le _).trans_eq
    (Matrix.rectangularTraceNorm_reindex e e X)

/-- The boundary partial trace used by LVV is trace-norm contractive. -/
theorem rectangularTraceNorm_partialTraceFirst_le {a s b : Type*}
    [Fintype a] [Fintype s] [Fintype b] [DecidableEq a] [DecidableEq s] [DecidableEq b]
    (X : Matrix ((a × s) × b) ((a × s) × b) ℂ) :
    rectangularTraceNorm (Matrix.partialTraceFirst X) ≤ rectangularTraceNorm X := by
  unfold Matrix.partialTraceFirst
  exact (rectangularTraceNorm_partialTraceLeft_le _).trans_eq
    (Matrix.rectangularTraceNorm_reindex (Equiv.prodAssoc a s b) (Equiv.prodAssoc a s b) X)

/-- The boundary marginal of an isometrically expanded density, as a linear map of the
compressed density matrix. -/
noncomputable def compressedBoundaryLM {a s b : Type*} [Fintype a]
    {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (s × b) (s × b) ℂ :=
  let e := (Equiv.prodAssoc a s b).trans (Equiv.prodComm a (s × b))
  Matrix.partialTraceRightLM.comp
    ((Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
      ((mulLeftLinearMap _ ℂ Z).comp (mulRightLinearMap _ ℂ Zᴴ)))

/-- Evaluation of the compressed boundary-marginal map. -/
theorem compressedBoundaryLM_apply {a s b : Type*} [Fintype a]
    {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (τ : Matrix (Fin n) (Fin n) ℂ) :
    compressedBoundaryLM Z τ = Matrix.partialTraceFirst (Z * τ * Zᴴ) := by
  ext i j
  simp only [compressedBoundaryLM, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Matrix.coe_reindexLinearEquiv, mulLeftLinearMap_apply, mulRightLinearMap_apply,
    Matrix.partialTraceRightLM, Matrix.partialTraceFirst,
    Matrix.partialTraceLeft_apply, Matrix.reindex_apply, Matrix.mul_assoc]
  rfl

/-- Isometric density expansion transports the boundary trace-norm constraint to the
explicit linear map on compressed matrices. -/
theorem isometricDensityExpansion_boundary_distance {a s b : Type*}
    [Fintype a] [Fintype s] [Fintype b] [DecidableEq s] [DecidableEq b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ)
    (τ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ = Z * τ * Zᴴ)
    (X : Matrix (s × b) (s × b) ℂ) :
    rectangularTraceNorm (Matrix.partialTraceFirst ρ - X) =
      rectangularTraceNorm (compressedBoundaryLM Z τ - X) := by
  classical
  rw [hρ, compressedBoundaryLM_apply]

/-- Isometric compression preserves the trace and transports a linear energy objective to
the compressed matrix.  This is the algebraic reduction of the objective in the
boundary-state minimization of LVV13, `algo53.tex`, equation `eq:conv`, lines 472--476. -/
theorem isometricDensityExpansion_trace_and_energy {a : Type*} [Fintype a]
    {n : ℕ} (Z : Matrix a (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (ρ : Matrix a a ℂ) (τ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ = Z * τ * Zᴴ)
    (H : Matrix a a ℂ) :
    τ.trace = ρ.trace ∧
      (ρ * H).trace = (τ * (Zᴴ * H * Z)).trace := by
  subst ρ
  constructor
  · rw [Matrix.trace_mul_cycle, hZ, Matrix.one_mul]
  · calc
      ((Z * τ * Zᴴ) * H).trace = ((Zᴴ * H * Z) * τ).trace := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle Z τ (Zᴴ * H)
      _ = (τ * (Zᴴ * H * Z)).trace := Matrix.trace_mul_comm _ _

/-- Compression by a column isometry does not increase the Euclidean operator norm. -/
theorem l2_opNorm_isometricCompression_le {a : Type*} [Fintype a] [DecidableEq a]
    {n : ℕ} (Z : Matrix a (Fin n) ℂ) (hZ : Zᴴ * Z = 1) (H : Matrix a a ℂ) :
    ‖Zᴴ * H * Z‖ ≤ ‖H‖ := by
  have hZn : ‖Z‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hZ
  have hZstar : ‖Zᴴ‖ ≤ 1 := by simpa only [l2_opNorm_conjTranspose] using hZn
  calc
    ‖Zᴴ * H * Z‖ ≤ ‖Zᴴ‖ * ‖H‖ * ‖Z‖ :=
      (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖H‖ * 1 := by gcongr
    _ = ‖H‖ := by ring

/-- Trace-norm accuracy of a compressed density controls both its normalization error and
the error in every compressed energy objective. This gives a dimension-free precision
requirement for the linear parts of the LVV boundary convex program. -/
theorem compressedDensity_trace_energy_perturbation {n : Type*} [Fintype n]
    [DecidableEq n] (τ σ K : Matrix n n ℂ) (ε : ℝ)
    (hε : Matrix.rectangularTraceNorm (σ - τ) ≤ ε) :
    ‖σ.trace - τ.trace‖ ≤ ε ∧
      |(σ * K).trace.re - (τ * K).trace.re| ≤ ‖K‖ * ε := by
  have htrace := Matrix.norm_trace_mul_le_l2_opNorm_mul_rectangularTraceNorm
    (σ - τ) (1 : Matrix n n ℂ)
  rw [Matrix.mul_one, Matrix.trace_sub] at htrace
  have hone : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := (IsStarProjection.one _).norm_le
  have htrace' : ‖σ.trace - τ.trace‖ ≤ ε :=
    htrace.trans ((mul_le_mul hone hε (Matrix.rectangularTraceNorm_nonneg _) (by norm_num)).trans
      (one_mul ε).le)
  refine ⟨htrace', ?_⟩
  have henergy := Matrix.norm_trace_mul_le_l2_opNorm_mul_rectangularTraceNorm (σ - τ) K
  have heq : ((σ - τ) * K).trace = (σ * K).trace - (τ * K).trace := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
  rw [heq] at henergy
  calc
    |(σ * K).trace.re - (τ * K).trace.re| = |((σ * K).trace - (τ * K).trace).re| := by
      rw [Complex.sub_re]
    _ ≤ ‖(σ * K).trace - (τ * K).trace‖ := Complex.abs_re_le_norm _
    _ ≤ ‖K‖ * Matrix.rectangularTraceNorm (σ - τ) := henergy
    _ ≤ ‖K‖ * ε := mul_le_mul_of_nonneg_left hε (norm_nonneg K)

/-- A positive approximate solution can be repaired to an exact density at trace-norm cost
at most twice its error from any trace-one target. The factor two accounts for the original
error and the sharp normalization correction. -/
theorem exists_normalizedPositiveMatrix_close_of_close {n : Type*} [Fintype n]
    [DecidableEq n] (x₀ : n) (τ σ : Matrix n n ℂ) (ε : ℝ)
    (hτtrace : τ.trace = 1) (hσpsd : σ.PosSemidef)
    (hclose : rectangularTraceNorm (σ - τ) ≤ ε) :
    ∃ σ₀ : Matrix n n ℂ, σ₀.PosSemidef ∧ σ₀.trace = 1 ∧
      rectangularTraceNorm (σ₀ - τ) ≤ 2 * ε := by
  let σ₀ := Matrix.normalizePosSemidef x₀ σ
  have htrace := (compressedDensity_trace_energy_perturbation τ σ 0 ε hclose).1
  have hdefect : |1 - σ.trace.re| ≤ ε := by
    calc
      |1 - σ.trace.re| = |(σ.trace - τ.trace).re| := by
        rw [hτtrace, Complex.sub_re, Complex.one_re, abs_sub_comm]
      _ ≤ ‖σ.trace - τ.trace‖ := Complex.abs_re_le_norm _
      _ ≤ ε := htrace
  have hnorm : rectangularTraceNorm (σ₀ - σ) = |1 - σ.trace.re| := by
    exact rectangularTraceNorm_normalizePosSemidef_sub x₀ hσpsd
  refine ⟨σ₀, Matrix.normalizePosSemidef_posSemidef x₀ hσpsd,
    Matrix.normalizePosSemidef_trace x₀ hσpsd, ?_⟩
  have heq : σ₀ - τ = (σ₀ - σ) + (σ - τ) := by abel
  rw [heq]
  exact (Matrix.rectangularTraceNorm_add_le _ _).trans (by linarith)

/-- The compressed boundary map is one-Lipschitz in trace norm. Consequently an
`ε`-accurate compressed density changes the LVV boundary constraint by at most `ε`. -/
theorem compressedBoundaryLM_distance_le {a s b : Type*} [Fintype a] [Fintype s]
    [Fintype b] [DecidableEq s] [DecidableEq b]
    {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (τ σ : Matrix (Fin n) (Fin n) ℂ) :
    rectangularTraceNorm (compressedBoundaryLM Z σ - compressedBoundaryLM Z τ) ≤
      rectangularTraceNorm (σ - τ) := by
  classical
  rw [compressedBoundaryLM_apply, compressedBoundaryLM_apply]
  have heq : Z * σ * Zᴴ - Z * τ * Zᴴ = Z * (σ - τ) * Zᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  have hpartial : Matrix.partialTraceFirst (Z * σ * Zᴴ) -
      Matrix.partialTraceFirst (Z * τ * Zᴴ) =
        Matrix.partialTraceFirst (Z * σ * Zᴴ - Z * τ * Zᴴ) := by
    ext i j
    simp only [Matrix.partialTraceFirst, Matrix.partialTraceLeft_apply, Matrix.reindex_apply,
      Matrix.submatrix_sub, Matrix.sub_apply]
    rw [← Finset.sum_sub_distrib]
    rfl
  rw [hpartial, heq]
  refine (rectangularTraceNorm_partialTraceFirst_le _).trans ?_
  exact Matrix.rectangularTraceNorm_mul_conjTranspose_le (σ - τ) Z Z
    (Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hZ)
    (Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hZ)

/-- Quantitative stability of all scalar and boundary conditions in the compressed LVV
program. A trace-norm perturbation by `ε` changes normalization and energy by their dual
bounds and enlarges the boundary tolerance by at most `ε`. -/
theorem compressedDensity_program_perturbation {a s b : Type*} [Fintype a] [Fintype s]
    [Fintype b] [DecidableEq s] [DecidableEq b]
    {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (τ σ K : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (s × b) (s × b) ℂ) (η ε : ℝ)
    (hclose : rectangularTraceNorm (σ - τ) ≤ ε)
    (hboundary : rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η) :
    ‖σ.trace - τ.trace‖ ≤ ε ∧
      |(σ * K).trace.re - (τ * K).trace.re| ≤ ‖K‖ * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤ η + ε := by
  classical
  obtain ⟨htrace, henergy⟩ := compressedDensity_trace_energy_perturbation τ σ K ε hclose
  refine ⟨htrace, henergy, ?_⟩
  have hmap := compressedBoundaryLM_distance_le Z hZ τ σ
  have hsum := Matrix.rectangularTraceNorm_add_le
    (compressedBoundaryLM Z σ - compressedBoundaryLM Z τ)
    (compressedBoundaryLM Z τ - X)
  have heq : compressedBoundaryLM Z σ - X =
      (compressedBoundaryLM Z σ - compressedBoundaryLM Z τ) +
        (compressedBoundaryLM Z τ - X) := by abel
  rw [heq]
  exact hsum.trans (by linarith)

/-- A positive numerical approximation to a feasible compressed density can be normalized
to an exact density satisfying the LVV program with explicit slack: `2 ‖K‖ ε` in the
one-sided energy objective and `2 ε` in the boundary tolerance. -/
theorem exists_normalizedPositiveMatrix_approximate_program
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} (x₀ : Fin n)
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (τ σ K : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (s × b) (s × b) ℂ) (E η ε : ℝ)
    (hτtrace : τ.trace = 1) (hσpsd : σ.PosSemidef)
    (hclose : rectangularTraceNorm (σ - τ) ≤ ε)
    (henergy : (τ * K).trace.re ≤ E)
    (hboundary : rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η) :
    ∃ σ₀ : Matrix (Fin n) (Fin n) ℂ, σ₀.PosSemidef ∧ σ₀.trace = 1 ∧
      (σ₀ * K).trace.re ≤ E + 2 * ‖K‖ * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z σ₀ - X) ≤ η + 2 * ε := by
  classical
  obtain ⟨σ₀, hσ₀psd, hσ₀trace, hσ₀close⟩ :=
    exists_normalizedPositiveMatrix_close_of_close x₀ τ σ ε hτtrace hσpsd hclose
  obtain ⟨_htrace, henergyError, hboundary₀⟩ :=
    compressedDensity_program_perturbation Z hZ τ σ₀ K X η (2 * ε)
      hσ₀close hboundary
  refine ⟨σ₀, hσ₀psd, hσ₀trace, ?_, hboundary₀⟩
  have hone := le_abs_self ((σ₀ * K).trace.re - (τ * K).trace.re)
  linarith

/-- A positive trace-one numerical solution of the compressed program expands to a genuine
physical density. Its energy and boundary errors are exactly those controlled in compressed
coordinates, with no dependence on the ambient left Hilbert-space dimension. -/
theorem isometricDensityExpansion_program_perturbation {a s b : Type*}
    [Fintype a] [Fintype s] [Fintype b] [DecidableEq s] [DecidableEq b]
    {n : ℕ} (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (τ σ : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix ((a × s) × b) ((a × s) × b) ℂ)
    (X : Matrix (s × b) (s × b) ℂ) (η ε : ℝ)
    (hσpsd : σ.PosSemidef) (hσtrace : σ.trace = 1)
    (hclose : rectangularTraceNorm (σ - τ) ≤ ε)
    (hboundary : rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η) :
    let ρτ := Z * τ * Zᴴ
    let ρσ := Z * σ * Zᴴ
    ρσ.PosSemidef ∧ ρσ.trace = 1 ∧
      |(ρσ * H).trace.re - (ρτ * H).trace.re| ≤ ‖Zᴴ * H * Z‖ * ε ∧
      rectangularTraceNorm (Matrix.partialTraceFirst ρσ - X) ≤ η + ε := by
  classical
  intro ρτ ρσ
  let K := Zᴴ * H * Z
  obtain ⟨_htrace, henergy, hboundary'⟩ :=
    compressedDensity_program_perturbation Z hZ τ σ K X η ε hclose hboundary
  have hτσ := isometricDensityExpansion_trace_and_energy Z hZ ρτ τ rfl H
  have hσσ := isometricDensityExpansion_trace_and_energy Z hZ ρσ σ rfl H
  refine ⟨hσpsd.mul_mul_conjTranspose_same Z, ?_, ?_, ?_⟩
  · exact hσσ.1.symm.trans hσtrace
  · rw [hσσ.2, hτσ.2]
    exact henergy
  · rw [isometricDensityExpansion_boundary_distance Z ρσ σ rfl X]
    exact hboundary'

/-- End-to-end repair of a positive numerical output. Normalize it in compressed
coordinates, then expand it isometrically; the resulting physical density has energy error
at most `2 ‖Zᴴ H Z‖ ε` and boundary tolerance `η + 2 ε`. -/
theorem exists_normalized_isometricDensityExpansion_program_perturbation
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] {n : ℕ} (x₀ : Fin n)
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (τ σ : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix ((a × s) × b) ((a × s) × b) ℂ)
    (X : Matrix (s × b) (s × b) ℂ) (η ε : ℝ)
    (hτtrace : τ.trace = 1) (hσpsd : σ.PosSemidef)
    (hclose : rectangularTraceNorm (σ - τ) ≤ ε)
    (hboundary : rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤ η) :
    ∃ σ₀ : Matrix (Fin n) (Fin n) ℂ, σ₀.PosSemidef ∧ σ₀.trace = 1 ∧
      let ρτ := Z * τ * Zᴴ
      let ρσ := Z * σ₀ * Zᴴ
      ρσ.PosSemidef ∧ ρσ.trace = 1 ∧
        |(ρσ * H).trace.re - (ρτ * H).trace.re| ≤ ‖Zᴴ * H * Z‖ * (2 * ε) ∧
        rectangularTraceNorm (Matrix.partialTraceFirst ρσ - X) ≤ η + 2 * ε := by
  obtain ⟨σ₀, hσ₀psd, hσ₀trace, hσ₀close⟩ :=
    exists_normalizedPositiveMatrix_close_of_close x₀ τ σ ε hτtrace hσpsd hclose
  refine ⟨σ₀, hσ₀psd, hσ₀trace, ?_⟩
  exact isometricDensityExpansion_program_perturbation Z hZ τ σ₀ H X η (2 * ε)
    hσ₀psd hσ₀trace hσ₀close hboundary

/-- A supported eigenvector of an isometrically expanded density has normalized coordinates
in the compressed space, and its eigenvalue equation is exactly the compressed eigenvalue
equation. Thus the leading-vector extraction in LVV13, `algo53.tex`, lines 477--478, can be
performed on the matrix of dimension at most `|S| m` supplied below and expanded by one
isometric matrix-vector multiplication. -/
theorem isometricDensityExpansion_eigenvector_coordinates {a : Type*} [Fintype a]
    {n : ℕ} (Z : Matrix a (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (ρ : Matrix a a ℂ) (τ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ = Z * τ * Zᴴ)
    (u : EuclideanSpace ℂ a) (μ : ℂ)
    (hsupp : (Z * Zᴴ) *ᵥ WithLp.ofLp u = WithLp.ofLp u)
    (heigen : ρ *ᵥ WithLp.ofLp u = μ • WithLp.ofLp u) :
    let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Zᴴ *ᵥ WithLp.ofLp u)
    ‖v‖ = ‖u‖ ∧
      WithLp.toLp 2 (Z *ᵥ WithLp.ofLp v) = u ∧
      τ *ᵥ WithLp.ofLp v = μ • WithLp.ofLp v := by
  intro v
  have hvraw : WithLp.ofLp v = Zᴴ *ᵥ WithLp.ofLp u := rfl
  have hreconstruct : WithLp.toLp 2 (Z *ᵥ WithLp.ofLp v) = u := by
    apply WithLp.ofLp_injective 2
    change Z *ᵥ WithLp.ofLp v = WithLp.ofLp u
    rw [hvraw, Matrix.mulVec_mulVec, hsupp]
  have hvnorm : ‖v‖ = ‖u‖ := by
    rw [← hreconstruct, Matrix.norm_toLp_mulVec_of_isometry Z hZ]
  refine ⟨hvnorm, hreconstruct, ?_⟩
  have hcompressed := congrArg (fun x ↦ Zᴴ *ᵥ x) heigen
  rw [hρ, Matrix.mulVec_mulVec, ← Matrix.mul_assoc Zᴴ (Z * τ) Zᴴ,
    ← Matrix.mul_assoc Zᴴ Z τ, hZ, Matrix.one_mul, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_smul] at hcompressed
  simpa only [hvraw] using hcompressed

/-- Isometric density expansion preserves an eigenvalue residual exactly. Hence numerical
accuracy for the compressed leading-vector problem is neither amplified nor degraded when
the vector is expanded to the physical support space. -/
theorem isometricDensityExpansion_eigenresidual_norm {a : Type*} [Fintype a]
    {n : ℕ} (Z : Matrix a (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (ρ : Matrix a a ℂ) (τ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ = Z * τ * Zᴴ)
    (v : EuclideanSpace ℂ (Fin n)) (μ : ℂ) :
    ‖WithLp.toLp 2 (ρ *ᵥ (Z *ᵥ WithLp.ofLp v) - μ • (Z *ᵥ WithLp.ofLp v))‖ =
      ‖WithLp.toLp 2 (τ *ᵥ WithLp.ofLp v - μ • WithLp.ofLp v)‖ := by
  have hresidual :
      ρ *ᵥ (Z *ᵥ WithLp.ofLp v) - μ • (Z *ᵥ WithLp.ofLp v) =
        Z *ᵥ (τ *ᵥ WithLp.ofLp v - μ • WithLp.ofLp v) := by
    rw [hρ, Matrix.mulVec_mulVec, Matrix.mul_assoc (Z * τ) Zᴴ Z, hZ,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [hresidual, Matrix.norm_toLp_mulVec_of_isometry Z hZ]

/-- The support projector in the boundary-state minimization has rank at most the number of
retained left vectors times the actual bond dimension. Thus the density matrix in LVV13,
`algo53.tex`, equation `eq:conv`, lines 472--476, is supported on a space of dimension at most
`|S| m`, independently of the exponentially large ambient left Hilbert space. -/
theorem rank_boundarySupportProjection_le (S : Finset (LeftBlockVector L q k)) (m : ℕ) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))
    (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)).rank ≤ S.card * m := by
  classical
  intro P
  rw [Matrix.rank_kronecker, Matrix.rank_one, Fintype.card_fin]
  exact Nat.mul_le_mul_right m (by
    simpa only [P, Matrix.rank_reindex] using rank_spanProjection_le_card S)

/-- The support constraint in the boundary-state minimization admits isometric coordinates
of dimension at most the number of retained left vectors times the actual bond dimension.
This is the coordinate reduction implicit in LVV13, `algo53.tex`, equation `eq:conv`, lines
472--476. -/
theorem exists_boundarySupportCoordinates (S : Finset (LeftBlockVector L q k)) (m : ℕ) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))
    let Q := P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
    ∃ (n : ℕ) (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ),
      n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧ Z * Zᴴ = Q := by
  classical
  intro P Q
  have hP : IsStarProjection P := Matrix.isStarProjection_reindex _ _
    (isStarProjection_spanProjection (S : Set (LeftBlockVector L q k)))
  have hQ : IsStarProjection Q := by
    constructor
    · change Q * Q = Q
      simp only [Q, ← Matrix.mul_kronecker_mul, hP.isIdempotentElem.eq,
        IsIdempotentElem.one.eq]
    · change (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))ᴴ = P ⊗ₖ 1
      rw [Matrix.conjTranspose_kronecker, show Pᴴ = P from hP.isSelfAdjoint,
        Matrix.conjTranspose_one]
  obtain ⟨n, Z, hZiso, hZrange⟩ := hQ.exists_matrix_range_isometry
  refine ⟨n, Z, ?_, hZiso, hZrange⟩
  calc
    n = (1 : Matrix (Fin n) (Fin n) ℂ).rank := by simp
    _ = (Zᴴ * Z).rank := congrArg Matrix.rank hZiso.symm
    _ ≤ Z.rank := Matrix.rank_mul_le_right _ _
    _ = (Z * Zᴴ).rank := (Matrix.rank_self_mul_conjTranspose Z).symm
    _ = Q.rank := congrArg Matrix.rank hZrange
    _ ≤ S.card * m := rank_boundarySupportProjection_le S m

/-- Every column of a support isometry has a structured description using one scalar for
each retained left vector and bond coordinate.  After joining the two left regions, each
bond slice is an explicit linear combination of `S`.  Thus the variable part of this
description has `n * m * |S|` complex coefficients, rather than one coefficient for every
ambient left configuration.

This is the coordinate structure implicit in LVV13, `algo53.tex`, equation `eq:conv`,
lines 472--476. -/
theorem exists_boundarySupportCoordinateCoefficients
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ c : Fin n → Fin m → S → ℂ, ∀ j a,
      ∑ s : S, c j a s • s.1 =
        WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) := by
  classical
  let Q := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
      (1 : Matrix (Fin m) (Fin m) ℂ)
  have hQZ : Q * Z = Z := by
    have hQ : Q = Z * Zᴴ := by simpa only [Q] using hZZ.symm
    rw [hQ, Matrix.mul_assoc, hZ, Matrix.mul_one]
  have hslice : ∀ j a, WithLp.toLp 2 (fun x ↦
      gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) ∈
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) := by
    intro j a
    let u := WithLp.toLp 2 (Z.col j)
    have hcolfix : Q *ᵥ WithLp.ofLp u = WithLp.ofLp u := by
      change Q *ᵥ Z.col j = Z.col j
      rw [← Matrix.col_mul_eq_mulVec_col, hQZ]
    have hfix := (gluingLeftCoordinates_spanProjection_eq_iff
      (S : Set (LeftBlockVector L q k)) u).mp (by simpa only [Q] using hcolfix)
    have hM := congrArg schmidtCoeffMatrix hfix
    rw [schmidtCoeffMatrix_kronecker_one_mulVec] at hM
    have hcol := congrArg (fun M ↦ M.col a) hM
    rw [Matrix.col_mul_eq_mulVec_col] at hcol
    change WithLp.toLp 2 (fun x ↦
      gluingLeftCoordinates L q k m u (x, a)) ∈
        Submodule.span ℂ (S : Set (LeftBlockVector L q k))
    apply (Submodule.starProjection_eq_self_iff).mp
    rw [← toLp_spanProjection_mulVec]
    have hslicecol : (fun x ↦ gluingLeftCoordinates L q k m u (x, a)) =
        (schmidtCoeffMatrix (WithLp.ofLp (gluingLeftCoordinates L q k m u))).col a := rfl
    rw [hslicecol, hcol]
  choose c hc using fun j a ↦ (Submodule.mem_span_finset').mp (hslice j a)
  exact ⟨c, hc⟩

/-- Number of complex coefficients in the structured support-coordinate description:
one coefficient for each compressed column, bond coordinate, and retained vector. -/
def boundarySupportCoordinateCoefficientCount (S : Finset (LeftBlockVector L q k))
    (m n : ℕ) : ℕ :=
  n * m * S.card

/-- Because the compressed dimension is at most `|S| m`, the structured coefficient
count is at most `(|S| m)²`, independently of the ambient left Hilbert-space dimension. -/
theorem boundarySupportCoordinateCoefficientCount_le_sq
    (S : Finset (LeftBlockVector L q k)) (m n : ℕ) (hn : n ≤ S.card * m) :
    boundarySupportCoordinateCoefficientCount S m n ≤ (S.card * m) ^ 2 := by
  unfold boundarySupportCoordinateCoefficientCount
  calc
    n * m * S.card ≤ (S.card * m) * m * S.card := by gcongr
    _ = (S.card * m) ^ 2 := by ring

/-- Every matrix satisfying the support constraint in the boundary-state minimization has
rank at most the number of retained left vectors times the actual bond dimension.  In
particular, this applies to every feasible density matrix in LVV13, `algo53.tex`, equation
`eq:conv`, lines 472--476. -/
theorem rank_boundarySupportedMatrix_le (S : Finset (LeftBlockVector L q k)) (m : ℕ)
    (ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
    (hρ : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ) :
    ρ.rank ≤ S.card * m := by
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection (S : Set (LeftBlockVector L q k)))
  calc
    ρ.rank = ((P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ).rank := congrArg Matrix.rank hρ.symm
    _ ≤ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ S.card * m := rank_boundarySupportProjection_le S m

/-- Every positive-semidefinite matrix satisfying the boundary support constraint is the
isometric expansion of a positive-semidefinite matrix of dimension at most `|S| m`.  This
places the density variable of LVV13, `algo53.tex`, equation `eq:conv`, lines 472--476, in
polynomially many coordinates once the viable-family size and bond dimension are polynomial. -/
theorem exists_boundarySupportedDensityCompression
    (S : Finset (LeftBlockVector L q k)) (m : ℕ)
    (ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
    (hρpsd : ρ.PosSemidef)
    (hρ : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))
    let Q := P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
    ∃ (n : ℕ) (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
      (τ : Matrix (Fin n) (Fin n) ℂ),
      n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧ Z * Zᴴ = Q ∧ τ.PosSemidef ∧
      ρ = Z * τ * Zᴴ := by
  classical
  intro P Q
  obtain ⟨n, Z, hn, hZiso, hZrange⟩ := exists_boundarySupportCoordinates S m
  have hZrangeQ : Z * Zᴴ = Q := by simpa only [P, Q] using hZrange
  have hρQ : Q * ρ = ρ := by simpa only [P, Q] using hρ
  let τ := Zᴴ * ρ * Z
  have hτpsd : τ.PosSemidef := hρpsd.conjTranspose_mul_mul_same Z
  have hρright : ρ * Q = ρ := by
    have h := congrArg Matrix.conjTranspose hρQ
    simpa only [Matrix.conjTranspose_mul, hρpsd.isHermitian.eq,
      show Qᴴ = Q by rw [← hZrangeQ, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]] using h
  refine ⟨n, Z, τ, hn, hZiso, hZrangeQ, hτpsd, ?_⟩
  calc
    ρ = Q * ρ * Q := by rw [hρQ, hρright]
    _ = (Z * Zᴴ) * ρ * (Z * Zᴴ) := by rw [hZrangeQ]
    _ = Z * τ * Zᴴ := by simp only [τ, Matrix.mul_assoc]

/-- A trace-one supported density has a compression of strictly positive order.  Its
compressed matrix is again a trace-one density, and its order is at most `|S| m`. -/
theorem exists_boundarySupportedDensityCompression_of_trace_eq_one
    (S : Finset (LeftBlockVector L q k)) (m : ℕ)
    (ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
    (hρpsd : ρ.PosSemidef) (hρtrace : ρ.trace = 1)
    (hρ : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))
    let Q := P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
    ∃ (n : ℕ) (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
      (τ : Matrix (Fin n) (Fin n) ℂ),
      0 < n ∧ n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧ Z * Zᴴ = Q ∧
      τ.PosSemidef ∧ τ.trace = 1 ∧ ρ = Z * τ * Zᴴ := by
  classical
  intro P Q
  obtain ⟨n, Z, τ, hn, hZ, hZZ, hτ, hρexpand⟩ :=
    exists_boundarySupportedDensityCompression S m ρ hρpsd hρ
  have hτtrace : τ.trace = 1 :=
    (isometricDensityExpansion_trace_and_energy Z hZ ρ τ hρexpand 0).1.trans hρtrace
  have hnpos : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
    subst n
    simp at hτtrace
  exact ⟨n, Z, τ, hnpos, hn, hZ, by simpa only [P, Q] using hZZ,
    hτ, hτtrace, hρexpand⟩

/-- A normalized vector in the retained boundary support has a rank-one density in
strictly positive compressed coordinates of order at most `|S| m`. -/
theorem exists_boundarySupportedVectorDensityCompression
    (S : Finset (LeftBlockVector L q k)) (m : ℕ)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    (hxnorm : ‖WithLp.toLp 2 x‖ = 1)
    (hx : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))
    let Q := P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
    ∃ (n : ℕ) (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
      (τ : Matrix (Fin n) (Fin n) ℂ),
      0 < n ∧ n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧ Z * Zᴴ = Q ∧
      τ.PosSemidef ∧ τ.trace = 1 ∧ vecMulVec x (star x) = Z * τ * Zᴴ := by
  classical
  intro P Q
  let ρ := vecMulVec x (star x)
  have hρpsd : ρ.PosSemidef := posSemidef_vecMulVec_self_star x
  have hρtrace : ρ.trace = 1 := by
    change (vecMulVec (WithLp.ofLp (WithLp.toLp 2 x))
      (star (WithLp.ofLp (WithLp.toLp 2 x)))).trace = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
  have hρsupport : Q * ρ = ρ := by
    dsimp only [Q, ρ]
    rw [mul_vecMulVec, hx]
  obtain ⟨n, Z, τ, hnpos, hn, hZ, hZZ, hτ, hτtrace, hρexpand⟩ :=
    exists_boundarySupportedDensityCompression_of_trace_eq_one
      S m ρ hρpsd hρtrace (by simpa only [P, Q] using hρsupport)
  exact ⟨n, Z, τ, hnpos, hn, hZ, by simpa only [P, Q] using hZZ,
    hτ, hτtrace, by simpa only [ρ] using hρexpand⟩

/-- A normalized supported eigenvector of a boundary density can be found in at most
`|S| m` coordinates. Its ambient vector is recovered by the same isometry that expands the
compressed density. This is the finite-dimensional spectral problem underlying the column
extraction in LVV13, `algo53.tex`, lines 477--478. -/
theorem exists_boundarySupportedDensity_eigenvector_coordinates
    (S : Finset (LeftBlockVector L q k)) (m : ℕ)
    (ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
    (hρpsd : ρ.PosSemidef)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) (μ : ℂ)
    (hu : ‖u‖ = 1)
    (hρ : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ)
    (husupp : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u)
    (heigen : ρ *ᵥ WithLp.ofLp u = μ • WithLp.ofLp u) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))
    let Q := P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
    ∃ (n : ℕ) (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
      (τ : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)),
      n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧ Z * Zᴴ = Q ∧ τ.PosSemidef ∧
      ρ = Z * τ * Zᴴ ∧ ‖v‖ = 1 ∧
      WithLp.toLp 2 (Z *ᵥ WithLp.ofLp v) = u ∧
      τ *ᵥ WithLp.ofLp v = μ • WithLp.ofLp v := by
  classical
  intro P Q
  obtain ⟨n, Z, τ, hn, hZ, hZZ, hτ, hρexpand⟩ :=
    exists_boundarySupportedDensityCompression S m ρ hρpsd hρ
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Zᴴ *ᵥ WithLp.ofLp u)
  have hcoords := isometricDensityExpansion_eigenvector_coordinates
    Z hZ ρ τ hρexpand u μ (by simpa only [Q, hZZ] using husupp) heigen
  refine ⟨n, Z, τ, v, hn, hZ, ?_, hτ, hρexpand, ?_, ?_, ?_⟩
  · simpa only [P, Q] using hZZ
  · exact (hcoords.1.trans hu)
  · exact hcoords.2.1
  · exact hcoords.2.2

/-- Choose global minimizers and top unit eigenvectors at exactly the feasible points of a
finite boundary set, and retain all their left columns. This is the fixed-bond construction
in LVV13, `algo53.tex`, equation `eq:conv`, lines 472–478, and Claim `c:2`, lines 520–527. -/
theorem exists_finite_boundary_minimizer_family (S : Set (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ)
    (N : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)) :
    let P := reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S)
    let feasible := fun X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ ↦
      {ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
          ((CutLeft L q k × CutSite L q k) × Fin m) ℂ |
        ρ.PosSemidef ∧ ρ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ ∧
        rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η}
    ∃ (F : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ))
      (σ : F → Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
        ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
      (u : F → EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
      (μ : F → ℝ) (T : Finset (LeftBlockVector L q k)),
      (∀ X, X ∈ F ↔ X ∈ N ∧ (feasible X).Nonempty) ∧
      T = leftColumns (Finset.univ : Finset F)
        (fun X ↦ gluingLeftCoordinates L q k m (u X)) ∧
      T.card ≤ m * N.card ∧ (T : Set (LeftBlockVector L q k)) ⊆ Submodule.span ℂ S ∧
      ∀ X : F, σ X ∈ feasible X ∧
        (∀ ρ ∈ feasible X,
          (σ X * (HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
            (ρ * (HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) ∧
        ‖u X‖ = 1 ∧ 0 < μ X ∧
        σ X *ᵥ WithLp.ofLp (u X) = (μ X : ℂ) • WithLp.ofLp (u X) ∧
        (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp (u X) = WithLp.ofLp (u X) ∧
        ∀ (ν : ℝ) (w : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)),
          w ≠ 0 → σ X *ᵥ WithLp.ofLp w = (ν : ℂ) • WithLp.ofLp w → ν ≤ μ X := by
  classical
  intro P feasible
  let F := N.filter fun X ↦ (feasible X).Nonempty
  have hF (X : F) : (feasible X).Nonempty := (Finset.mem_filter.mp X.property).2
  choose σ u μ hspec using
    fun X : F ↦ exists_boundary_density_minimizer_max_eigenvector
      (a := CutLeft L q k) (s := CutSite L q k) (b := Fin m) P HL X η (hF X)
  refine ⟨F, σ, u, μ, leftColumns Finset.univ
    (fun X ↦ gluingLeftCoordinates L q k m (u X)), ?_, rfl, ?_, ?_, ?_⟩
  · exact fun X ↦ Finset.mem_filter
  · calc
      _ ≤ F.card * m := by
        simpa only [Finset.card_univ, Fintype.card_coe] using
          card_leftColumns_le (Finset.univ : Finset F)
            (fun X ↦ gluingLeftCoordinates L q k m (u X))
      _ ≤ N.card * m := Nat.mul_le_mul_right m (Finset.card_filter_le _ _)
      _ = m * N.card := Nat.mul_comm _ _
  · exact leftColumns_subset_span S _ _ (fun X _ ↦
      (gluingLeftCoordinates_spanProjection_eq_iff S (u X)).mp
        (hspec X).2.2.2.2.2.2.2.2.1)
  · simpa only [feasible, Set.mem_ofPred_eq, and_imp, and_assoc] using hspec

end TNLean.MPS.AreaLaw
