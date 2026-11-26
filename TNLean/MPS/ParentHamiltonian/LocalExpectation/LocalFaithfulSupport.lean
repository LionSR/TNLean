/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableExpectation
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Algebra.Combinatorics.FinSumPermutation
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableState
import QICLean.Channel.Positive.PositiveConditionalExpectation
import QICLean.Analysis.Optimization.SemidefiniteProgram
import QICLean.Channel.Schwarz.Closure
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableQuasiLocalState
import TNLean.QCA.QuasiLocal.QuasiLocalInterval

/-!
# Faithfulness and finite MPS support

For any tensor and positive-definite virtual matrix, the insertion expectation
of a square observable vanishes precisely when the observable annihilates the
MPS boundary space. Thus the support of the finite positive functional is
exactly this boundary space. Tensor normalization, transfer invariance,
injectivity, and primitivity are unnecessary; the interval may have length zero.

**Scope restriction (supplied faithful generators):** This finite-dimensional
support characterization applies to the faithful minimal generators in
Nachtergaele, arXiv:cond-mat/9410110, lines 1724--1738, when they are
supplied. Nonzero positive stationary data that are not faithful reduce to
this case by compression to the support of the stationary matrix. The
passage from an arbitrary GVBS boundary limit to normalized stationary data
is not formalized; it is recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

It also contains the following results.

* `MPSTensor.exists_local_density_range_eq_groundSpaceES`,
  `MPSTensor.exists_quasiLocalExpectation_density_range_eq_groundSpaceES`: finite local densities
  and their MPS support.
-/

section LocalFaithfulSupport

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D k : ℕ}

private theorem physicalObservableTransfer_square (A : MPSTensor d D)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A k (Xᴴ * X) ρ =
      ∑ b : Cfg d k,
        (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)) * ρ *
          (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ))ᴴ := by
  classical
  simp only [physicalObservableTransfer_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.sum_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  simp only [Finset.smul_sum, smul_smul]
  exact Fintype.sum_reverse_three _

private theorem contracted_words_eq_zero_of_faithful_square_expectation
    [NeZero D] (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hzero : observableInsertionExpectation A ρ (Xᴴ * X) = 0) :
    ∀ b : Cfg d k, (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)) = 0 := by
  classical
  let C (b : Cfg d k) := ∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)
  have htr : Matrix.trace (physicalObservableTransfer A k (Xᴴ * X) ρ) = 0 := by
    simpa only [observableInsertionExpectation, div_eq_zero_iff,
      ne_of_gt hρ.trace_pos, or_false] using hzero
  have htrace : Matrix.trace (ρ * ∑ b : Cfg d k, (C b)ᴴ * C b) = 0 := by
    calc
      Matrix.trace (ρ * ∑ b : Cfg d k, (C b)ᴴ * C b) =
          ∑ b : Cfg d k, Matrix.trace (ρ * ((C b)ᴴ * C b)) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
      _ = ∑ b : Cfg d k, Matrix.trace (C b * ρ * (C b)ᴴ) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [← Matrix.mul_assoc]
        exact Matrix.trace_mul_cycle ρ (C b)ᴴ (C b)
      _ = Matrix.trace (physicalObservableTransfer A k (Xᴴ * X) ρ) := by
        rw [physicalObservableTransfer_square, Matrix.trace_sum]
      _ = 0 := htr
  have hsum : (∑ b : Cfg d k, (C b)ᴴ * C b) = 0 :=
    Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero
      (Matrix.posSemidef_sum Finset.univ fun b _ => Matrix.posSemidef_conjTranspose_mul_self (C b))
      hρ htrace
  exact Matrix.eq_zero_of_sum_conjTranspose_mul_self_eq_zero C hsum

open scoped Matrix.Norms.Frobenius

private theorem groundSpaceES_le_ker_of_contracted_words_eq_zero
    (A : MPSTensor d D) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hC : ∀ b : Cfg d k,
      (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)) = 0) :
    groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X) := by
  rw [← range_groundSpaceMapES]
  rintro ψ ⟨v, rfl⟩
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective v
  rw [LinearMap.mem_ker]
  change Matrix.toEuclideanLin X (groundSpaceMapES A k
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) Y)) = 0
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply]
  apply PiLp.ext
  intro b
  change ∑ σ : Cfg d k, X b σ * Matrix.trace
    (Kraus.evalWord A (List.ofFn σ) * Y) = 0
  have h := congrArg (fun C => Matrix.trace (C * Y)) (hC b)
  simpa only [Finset.sum_mul, smul_mul_assoc, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, zero_mul, Matrix.trace_zero] using h

private theorem contracted_words_eq_zero_of_groundSpaceES_le_ker
    (A : MPSTensor d D) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hX : groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X)) :
    ∀ b : Cfg d k, (∑ σ : Cfg d k, X b σ • Kraus.evalWord A (List.ofFn σ)) = 0 := by
  classical
  intro b
  apply (Matrix.trace_mul_right_eq_zero_iff _).mp
  intro Y
  have h := LinearMap.mem_ker.mp (hX ((range_groundSpaceMapES A k).le
    ⟨Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) Y, rfl⟩))
  change Matrix.toEuclideanLin X (groundSpaceMapES A k
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) Y)) = 0 at h
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply] at h
  have hb := congrArg (fun v : EuclideanSpace ℂ (Cfg d k) => v b) h
  change (∑ σ : Cfg d k, X b σ * Matrix.trace
    (Kraus.evalWord A (List.ofFn σ) * Y)) = 0 at hb
  simpa only [Finset.sum_mul, smul_mul_assoc, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul] using hb

/-- A faithful virtual matrix gives exactly the MPS boundary space as the finite
support: a square observable has zero insertion expectation if and only if
its factor annihilates the boundary space. No tensor normalization, transfer
invariance, injectivity, or primitivity is required. This is the finite support
identification used in Nachtergaele, arXiv:cond-mat/9410110, lines 1724--1738,
once faithful generating data are supplied. -/
theorem observableInsertionExpectation_conjTranspose_mul_self_eq_zero_iff
    [NeZero D] (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectation A ρ (Xᴴ * X) = 0 ↔
      groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X) := by
  constructor
  · intro hzero
    exact groundSpaceES_le_ker_of_contracted_words_eq_zero A X
      (contracted_words_eq_zero_of_faithful_square_expectation A hρ X hzero)
  · intro hX
    have hC := contracted_words_eq_zero_of_groundSpaceES_le_ker A X hX
    simp only [observableInsertionExpectation, physicalObservableTransfer_square,
      hC, zero_mul, Finset.sum_const_zero, Matrix.trace_zero, zero_div]

end MPSTensor

end LocalFaithfulSupport

section LocalDensitySupport

/-!
## Finite local densities and their MPS support

A left-canonical tensor and a faithful virtual matrix define a positive
normalized functional on each finite interval, even when the virtual matrix
is not transfer invariant. Its representing density matrix has range exactly
equal to the MPS boundary space. The physical dimension is derived from the
left-canonical normalization and the positive bond dimension; intervals of
length zero are included.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b) and
lines 1724--1738, where faithful generating data identify the local supports.

**Scope restriction (faithful generating data):** This module constructs
finite densities from a supplied faithful virtual matrix. Nonzero positive
stationary data that are not faithful reduce to this case by compression to
the support of the stationary matrix. The module does not derive normalized
stationary data from an arbitrary GVBS boundary limit, nor assert
compatibility of these densities without transfer invariance. That separate
source passage is recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

### Finite restrictions of faithful MPS states

The quasi-local state defined by a trace-preserving tensor and a faithful
stationary matrix has the same finite density on every translated interval.
The range of that density is exactly the MPS boundary space, including on
the empty interval. The physical dimension is derived from normalization.

**Scope restriction (supplied faithful generators):** The generating tensor
and faithful stationary matrix are supplied. Their construction from an
arbitrary GVBS presentation is separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
and the local density support identification at lines 1724--1738.
-/

section

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D k : ℕ}

private theorem density_square_zero_iff_range_le_ker
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (X : Matrix n n ℂ) :
    Matrix.trace (σ * (Xᴴ * X)) = 0 ↔
      LinearMap.range (Matrix.toEuclideanLin σ) ≤ LinearMap.ker (Matrix.toEuclideanLin X) := by
  constructor
  · intro hzero
    have hprod : (Xᴴ * X) * σ = 0 :=
      (Matrix.posSemidef_conjTranspose_mul_self X).mul_eq_zero_of_trace_mul_eq_zero hσ
        ((Matrix.trace_mul_comm _ _).trans hzero)
    rw [← (Matrix.toEuclideanLin X).ker_adjoint_comp_self,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← Matrix.toLpLin_mul_same,
      LinearMap.range_le_ker_iff, ← Matrix.toLpLin_mul_same, hprod]
    exact map_zero _
  · intro hle
    have hprod : X * σ = 0 := (Matrix.toLpLin 2 2).injective
      (by simpa only [Matrix.toLpLin_mul_same, map_zero] using
        LinearMap.range_le_ker_iff.mp hle)
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, hprod, Matrix.zero_mul, Matrix.trace_zero]

private theorem density_range_eq_groundSpaceES [NeZero D]
    (A : MPSTensor d D) {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    {σ : Matrix (Cfg d k) (Cfg d k) ℂ} (hσ : σ.PosSemidef)
    (hrep : ∀ X, observableInsertionExpectation A ρ X = Matrix.trace (σ * X)) :
    LinearMap.range (Matrix.toEuclideanLin σ) = groundSpaceES A k := by
  have hiff (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
      LinearMap.range (Matrix.toEuclideanLin σ) ≤ LinearMap.ker (Matrix.toEuclideanLin X) ↔
        groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X) := by
    rw [← density_square_zero_iff_range_le_ker hσ X, ← hrep,
      observableInsertionExpectation_conjTranspose_mul_self_eq_zero_iff A hρ X]
  have htest (S : Submodule ℂ (EuclideanSpace ℂ (Cfg d k))) :
      ∃ X : Matrix (Cfg d k) (Cfg d k) ℂ, LinearMap.ker (Matrix.toEuclideanLin X) = S := by
    refine ⟨(Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ)).symm Sᗮ.starProjection, ?_⟩
    simp only [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, StarAlgEquiv.apply_symm_apply,
      Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
  obtain ⟨X, hX⟩ := htest (groundSpaceES A k)
  obtain ⟨Y, hY⟩ := htest (LinearMap.range (Matrix.toEuclideanLin σ))
  exact le_antisymm
    (by simpa only [hX] using (hiff X).mpr hX.ge)
    (by simpa only [hY] using (hiff Y).mp hY.ge)

/-- A left-canonical tensor and faithful virtual matrix have positive normalized
finite densities whose ranges are precisely the MPS boundary spaces.
No transfer fixed-point condition, injectivity, or primitivity is required.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b) and
lines 1724--1738, the identification of local support from faithful generators. -/
theorem exists_local_density_range_eq_groundSpaceES [NeZero D]
    (A : MPSTensor d D) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (k : ℕ) :
    ∃ σ : Matrix (Cfg d k) (Cfg d k) ℂ, σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      (∀ X, observableInsertionExpectation A ρ X = Matrix.trace (σ * X)) ∧
      LinearMap.range (Matrix.toEuclideanLin σ) = groundSpaceES A k := by
  let : NeZero d := ⟨IsLeftCanonical.physDim_ne_zero (A := A) hTP⟩
  have hone : observableInsertionExpectationₗ A ρ k 1 = 1 := by
    change Matrix.trace (physicalObservableTransfer A k 1 ρ) / Matrix.trace ρ = 1
    rw [physicalObservableTransfer_one,
      (Kraus.isTracePreservingMap_mapLM_of_isTP A hTP).pow k ρ,
      div_self (ne_of_gt hρ.trace_pos)]
  obtain ⟨σ, hσ, htr, hrep⟩ := Matrix.exists_density_of_positive_functional
    (observableInsertionExpectationₗ A ρ k)
    (fun X hX => observableInsertionExpectation_nonneg A hρ.posSemidef hX) hone
  exact ⟨σ, hσ, htr, hrep, density_range_eq_groundSpaceES A hρ hσ hrep⟩

end MPSTensor

end

section

open SpinChain
open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D : ℕ}

/-- Every finite restriction of the state defined by faithful stationary
generators has a density whose range is exactly the tensor boundary space.
The same density represents every translation of the interval.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
and lines 1724--1738. -/
theorem exists_quasiLocalExpectation_density_range_eq_groundSpaceES [NeZero D]
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.transferMap A ρ = ρ) (k : ℕ) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    ∃ σ : Matrix (Cfg d k) (Cfg d k) ℂ, σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      (∀ (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ),
        quasiLocalExpectation A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos)
          (quasiLocalIntervalObservable d a k X) = Matrix.trace (σ * X)) ∧
      LinearMap.range (Matrix.toEuclideanLin σ) = groundSpaceES A k := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  change (∑ i, (A i)ᴴ * A i) = 1 at hA
  obtain ⟨σ, hσ, htr, hrep, hRange⟩ :=
    exists_local_density_range_eq_groundSpaceES A hA hρ k
  refine ⟨σ, hσ, htr, ?_, hRange⟩
  intro a X
  rw [quasiLocalExpectation_quasiLocalIntervalObservable]
  exact hrep X

end MPSTensor

end

end LocalDensitySupport
