/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausCPTP

/-!
# Trace-preserving completion outside a matrix support

A completely positive map may preserve only the trace seen by a projection
onto an active subspace.  This file completes such a map by measuring the
orthogonal complement and preparing a fixed density matrix.  The completed
map agrees with the original map on matrices supported by the projection.

## Main definitions

* `Matrix.tracePrepareMap`: discard a matrix and prepare a fixed matrix with
  the same trace when the fixed matrix has trace one.
* `Matrix.supportComplementMap`: measure the weight outside a projection and
  prepare a fixed matrix.
* `Matrix.supportCompletion`: add the complementary term to a map supported
  by the projection.

## Main results

* `Matrix.supportCompletion_isKrausCPTP`: the completed map is trace-preserving
  and completely positive.
* `Matrix.supportCompletion_apply_of_supported`: the completed map agrees with
  the original map on matrices supported by the projection.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Definition 4.1,
  lines 638--660, and Appendix C.4, lines 2065--2085.  The completion supplies
  the otherwise unspecified action on discarded physical complements; see
  `docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.
-/

open scoped ComplexOrder Matrix

noncomputable section

namespace Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- The trace-and-prepare map sends `X` to `trace X • ρ`.

It is expressed as state preparation, interchange of the two tensor factors,
and partial trace.  This factorization supplies its rectangular Kraus form
without any nonemptiness assumption on either index type. -/
def tracePrepareMap (ρ : Matrix β β ℂ) :
    Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ :=
  (partialTraceRightLM (α := β) (β := α)).comp
    ((equivReindexMap (Equiv.prodComm α β)).comp (preparationMap ρ))

/-- The trace-and-prepare map has the formula `X ↦ trace X • ρ`. -/
@[simp]
theorem tracePrepareMap_apply (ρ : Matrix β β ℂ) (X : Matrix α α ℂ) :
    tracePrepareMap ρ X = Matrix.trace X • ρ := by
  classical
  ext b c
  change (∑ a, X a a * ρ b c) = (∑ a, X a a) * ρ b c
  rw [Finset.sum_mul]

/-- The output trace of the trace-and-prepare map is the product of the input
trace and the trace of the prepared matrix. -/
theorem tracePrepareMap_trace (ρ : Matrix β β ℂ) (X : Matrix α α ℂ) :
    Matrix.trace (tracePrepareMap ρ X) = Matrix.trace X * Matrix.trace ρ := by
  rw [tracePrepareMap_apply, Matrix.trace_smul, smul_eq_mul]

/-- Trace-and-prepare is completely positive when the prepared matrix is
positive semidefinite. -/
theorem tracePrepareMap_isKrausCP (ρ : Matrix β β ℂ) (hρ : ρ.PosSemidef) :
    IsKrausCP (tracePrepareMap (α := α) ρ) := by
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact preparationMap_isKrausCP ρ hρ
    · exact (equivReindexMap_isKrausCPTP (Equiv.prodComm α β)).isKrausCP
  · exact (partialTraceRightLM_isKrausCPTP (α := β) (β := α)).isKrausCP

/-- Trace-and-prepare is trace-preserving and completely positive when the
prepared matrix is positive semidefinite with trace one. -/
theorem tracePrepareMap_isKrausCPTP
    (ρ : Matrix β β ℂ) (hρ : ρ.PosSemidef) (hρtrace : Matrix.trace ρ = 1) :
    IsKrausCPTP (tracePrepareMap (α := α) ρ) := by
  apply isKrausCPTP_comp
  · apply isKrausCPTP_comp
    · exact preparationMap_isKrausCPTP ρ hρ hρtrace
    · exact equivReindexMap_isKrausCPTP (Equiv.prodComm α β)
  · exact partialTraceRightLM_isKrausCPTP (α := β) (β := α)

/-- The complementary map first applies the single Kraus operator `1 - P`,
then discards the resulting matrix and prepares `ρ`. -/
def supportComplementMap (P : Matrix α α ℂ) (ρ : Matrix β β ℂ) :
    Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ :=
  (tracePrepareMap ρ).comp (singleKrausMap (1 - P))

/-- The complementary map measures the weight of a matrix outside `P` and
prepares `ρ` with that weight. -/
@[simp]
theorem supportComplementMap_apply
    (P : Matrix α α ℂ) (ρ : Matrix β β ℂ) (X : Matrix α α ℂ) :
    supportComplementMap P ρ X =
      Matrix.trace ((1 - P) * X * (1 - P)ᴴ) • ρ := by
  rw [supportComplementMap, LinearMap.comp_apply, tracePrepareMap_apply,
    singleKrausMap_apply]

/-- The complementary map is completely positive when the prepared matrix
is positive semidefinite. -/
theorem supportComplementMap_isKrausCP
    (P : Matrix α α ℂ) (ρ : Matrix β β ℂ) (hρ : ρ.PosSemidef) :
    IsKrausCP (supportComplementMap P ρ) := by
  apply isKrausCP_comp
  · exact singleKrausMap_isKrausCP (1 - P)
  · exact tracePrepareMap_isKrausCP ρ hρ

/-- If `P` is a Hermitian projection and `ρ` has trace one, the
complementary term contributes precisely the trace outside `P`. -/
theorem supportComplementMap_trace
    (P : Matrix α α ℂ) (hPherm : P.IsHermitian) (hPidem : P * P = P)
    (ρ : Matrix β β ℂ) (hρtrace : Matrix.trace ρ = 1) (X : Matrix α α ℂ) :
    Matrix.trace (supportComplementMap P ρ X) =
      Matrix.trace ((1 - P) * X) := by
  let Q : Matrix α α ℂ := 1 - P
  have hQherm : Q.IsHermitian := by
    exact Matrix.isHermitian_one.sub hPherm
  have hQidem : Q * Q = Q := by
    rw [show Q = 1 - P from rfl]
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPidem]; abel
  rw [supportComplementMap_apply, Matrix.trace_smul, hρtrace, smul_eq_mul,
    mul_one]
  change Matrix.trace (Q * X * Qᴴ) = Matrix.trace (Q * X)
  rw [hQherm.eq]
  calc
    Matrix.trace (Q * X * Q) = Matrix.trace ((Q * Q) * X) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle Q X Q
    _ = Matrix.trace (Q * X) := by rw [hQidem]

/-- The support completion of `E` adds a map carrying the complementary
trace weight to the fixed matrix `ρ`. -/
def supportCompletion
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (P : Matrix α α ℂ) (ρ : Matrix β β ℂ) :
    Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ :=
  E + supportComplementMap P ρ

/-- The support completion is the sum of the original map and its
complementary term. -/
@[simp]
theorem supportCompletion_apply
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (P : Matrix α α ℂ) (ρ : Matrix β β ℂ)
    (X : Matrix α α ℂ) :
    supportCompletion E P ρ X = E X + supportComplementMap P ρ X := by
  rfl

/-- The support completion is completely positive when the original map is
completely positive and the prepared matrix is positive semidefinite. -/
theorem supportCompletion_isKrausCP
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (P : Matrix α α ℂ) (ρ : Matrix β β ℂ)
    (hE : IsKrausCP E) (hρ : ρ.PosSemidef) :
    IsKrausCP (supportCompletion E P ρ) := by
  exact hE.add (supportComplementMap_isKrausCP P ρ hρ)

/-- If `E` preserves the trace on the `P`-part, its support completion
preserves the full trace. -/
theorem supportCompletion_trace
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (P : Matrix α α ℂ) (ρ : Matrix β β ℂ)
    (hPherm : P.IsHermitian) (hPidem : P * P = P)
    (hEtrace : ∀ X, Matrix.trace (E X) = Matrix.trace (P * X))
    (hρtrace : Matrix.trace ρ = 1) (X : Matrix α α ℂ) :
    Matrix.trace (supportCompletion E P ρ X) = Matrix.trace X := by
  rw [supportCompletion_apply, Matrix.trace_add, hEtrace,
    supportComplementMap_trace P hPherm hPidem ρ hρtrace]
  calc
    Matrix.trace (P * X) + Matrix.trace ((1 - P) * X) =
        Matrix.trace (P * X + (1 - P) * X) := by rw [Matrix.trace_add]
    _ = Matrix.trace ((P + (1 - P)) * X) := by rw [Matrix.add_mul]
    _ = Matrix.trace X := by simp

/-- A completely positive map that preserves the trace on the part selected by
a Hermitian projection extends to a channel by the complementary construction. -/
theorem supportCompletion_isKrausCPTP
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (P : Matrix α α ℂ) (ρ : Matrix β β ℂ)
    (hE : IsKrausCP E) (hPherm : P.IsHermitian) (hPidem : P * P = P)
    (hEtrace : ∀ X, Matrix.trace (E X) = Matrix.trace (P * X))
    (hρ : ρ.PosSemidef) (hρtrace : Matrix.trace ρ = 1) :
    IsKrausCPTP (supportCompletion E P ρ) := by
  apply isKrausCPTP_of_isKrausCP_trace_preserving
  · exact supportCompletion_isKrausCP E P ρ hE hρ
  · exact supportCompletion_trace E P ρ hPherm hPidem hEtrace hρtrace

/-- The support completion agrees with the original map on matrices supported
on both sides by `P`. -/
theorem supportCompletion_apply_of_supported
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (P : Matrix α α ℂ) (ρ : Matrix β β ℂ)
    (X : Matrix α α ℂ) (hPherm : P.IsHermitian) (hPidem : P * P = P)
    (hX : P * X * P = X) :
    supportCompletion E P ρ X = E X := by
  let Q : Matrix α α ℂ := 1 - P
  have hQherm : Q.IsHermitian := by
    exact Matrix.isHermitian_one.sub hPherm
  have hPX : P * X = X := by
    calc
      P * X = P * (P * X * P) := by rw [hX]
      _ = (P * P) * X * P := by simp only [Matrix.mul_assoc]
      _ = P * X * P := by rw [hPidem]
      _ = X := hX
  have hXP : X * P = X := by
    calc
      X * P = (P * X * P) * P := by rw [hX]
      _ = P * X * (P * P) := by simp only [Matrix.mul_assoc]
      _ = P * X * P := by rw [hPidem]
      _ = X := hX
  have hQXQ : Q * X * Q = 0 := by
    rw [show Q = 1 - P from rfl]
    calc
      (1 - P) * X * (1 - P) = X - P * X - X * P + P * X * P := by
        noncomm_ring
      _ = 0 := by rw [hPX, hXP]; abel
  rw [supportCompletion_apply, supportComplementMap_apply]
  change E X + Matrix.trace (Q * X * Qᴴ) • ρ = E X
  rw [hQherm.eq, hQXQ, Matrix.trace_zero, zero_smul, add_zero]

end Matrix
