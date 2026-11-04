/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SemidefiniteRepair

/-!
# Approximate semidefinite certificates and fixed-data perturbations

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
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

end TNLean.MPS.AreaLaw
