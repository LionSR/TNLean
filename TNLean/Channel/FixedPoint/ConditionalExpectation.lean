/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Algebra
import TNLean.Channel.Semigroup.CPClosure
import TNLean.Algebra.MatrixFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order

/-!
# Conditional expectation onto fixed-point algebra (Wolf Theorem 6.15)

This file formalizes the conditional expectation projecting onto the
fixed-point *-subalgebra of a quantum channel's Heisenberg-picture map,
following Wolf Theorem 6.15.

When the fixed-point *-subalgebra is the scalar algebra `ℂ · 1` (as for
primitive channels), the conditional expectation takes the explicit form
`E_σ(X) = (tr(σ X) / tr(σ)) • 1`, where `σ` is the unique positive-definite
stationary state. The general irreducible case (period > 1) requires the
Wedderburn block decomposition from Wolf Theorem 6.14 (issue #27).

## Main results

* `IsConditionalExpectation`: predicate stating that a linear map is
  idempotent, unital, maps into a `StarSubalgebra`, and fixes it pointwise.
  Defined generically over any `StarAlgebra` for upstream compatibility.
* `scalarConditionalExpectation`: the linear map `X ↦ (tr(σX)/tr(σ)) • 1`.
* `scalarConditionalExpectation_idempotent`: `E_σ² = E_σ`.
* `scalarConditionalExpectation_unital`: `E_σ(1) = 1`.
* `scalarConditionalExpectation_absorbs_adjointMap`:
  `E_σ(T*(X)) = E_σ(X)` when `T(σ) = σ`.
* `adjointMap_absorbs_scalarConditionalExpectation`:
  `T*(E_σ(X)) = E_σ(X)` when `T` is trace-preserving.
* `scalarConditionalExpectation_mem_adjointFixedPoints`:
  `E_σ(X)` is always a fixed point of `T*`.
* `scalarConditionalExpectation_isConditionalExpectation`:
  **Wolf Theorem 6.15** for the scalar fixed-point algebra case.

## Cross-references

* Wolf Proposition 6.6 (Similarity preserving irreducibility):
  `TNLean.Channel.Irreducible.Similarity`.
* Wolf Proposition 6.8 (Hermitian fixed-point decomposition):
  `TNLean.Channel.FixedPoint.Cesaro`,
  `IsChannel.posSemidef_parts_of_hermitian_fixedPoint`.
* Wolf Theorems 6.12-6.13 (fixed-point *-algebra and Kraus commutant):
  `TNLean.Channel.FixedPoint.Algebra`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 6.15, §6.4]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators TNMatrixCFC
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## Abstract conditional expectation -/

/-- A **conditional expectation** onto a `StarSubalgebra` `S ⊆ A` is a
ℂ-linear map that is idempotent, unital, maps into `S`, and fixes every
element of `S`. This is the abstract property from Wolf Theorem 6.15.

The definition is generic over any `StarAlgebra` so that it can be reused
for non-matrix algebras (e.g., Wedderburn blocks) in future work. -/
structure IsConditionalExpectation {A : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (E : A →ₗ[ℂ] A) (S : StarSubalgebra ℂ A) : Prop where
  /-- Idempotent: `E(E(X)) = E(X)`. -/
  idempotent : ∀ X : A, E (E X) = E X
  /-- Unital: `E(1) = 1`. -/
  unital : E 1 = 1
  /-- Range contained in `S`. -/
  range_subset : ∀ X : A, E X ∈ S
  /-- Fixes `S` pointwise. -/
  fixes : ∀ X : A, X ∈ S → E X = X

/-! ## Scalar conditional expectation -/

/-- The **scalar conditional expectation** weighted by `σ`:

`E_σ(X) = (tr(σ X) / tr(σ)) • 1`.

This is the conditional expectation from Wolf Theorem 6.15 in the case where
the fixed-point *-subalgebra of the adjoint map is the scalar algebra `ℂ · 1`
(i.e., the channel is primitive).

The definition does not require `trace σ ≠ 0`; when `trace σ = 0` the map
sends everything to zero. The nonzero-trace hypothesis is instead required
by the theorems that use this map (idempotence, unitality, etc.). -/
noncomputable def scalarConditionalExpectation
    (σ : Mat) : Mat →ₗ[ℂ] Mat where
  toFun X := (trace (σ * X) / trace σ) • (1 : Mat)
  map_add' X Y := by
    change (trace (σ * (X + Y)) / trace σ) • (1 : Mat) =
      (trace (σ * X) / trace σ) • 1 + (trace (σ * Y) / trace σ) • 1
    rw [mul_add, trace_add, add_div, add_smul]
  map_smul' c X := by
    simp only [RingHom.id_apply, smul_smul]
    congr 1
    rw [Algebra.mul_smul_comm, trace_smul, smul_eq_mul, mul_div_assoc]

@[simp]
theorem scalarConditionalExpectation_apply
    (σ : Mat) (X : Mat) :
    scalarConditionalExpectation σ X =
      (trace (σ * X) / trace σ) • (1 : Mat) := rfl

/-- `E_σ(1) = 1`: the scalar conditional expectation is unital. -/
@[simp]
theorem scalarConditionalExpectation_unital
    (σ : Mat) (hσ_tr : trace σ ≠ 0) :
    scalarConditionalExpectation σ 1 = (1 : Mat) := by
  simp [scalarConditionalExpectation_apply, mul_one, div_self hσ_tr]

/-- `E_σ(E_σ(X)) = E_σ(X)`: the scalar conditional expectation is
idempotent. -/
theorem scalarConditionalExpectation_idempotent
    (σ : Mat) (hσ_tr : trace σ ≠ 0) (X : Mat) :
    scalarConditionalExpectation σ
      (scalarConditionalExpectation σ X) =
      scalarConditionalExpectation σ X := by
  simp only [scalarConditionalExpectation_apply]
  congr 1
  rw [Algebra.mul_smul_comm, mul_one, trace_smul, smul_eq_mul,
    div_mul_cancel₀ (trace (σ * X)) hσ_tr]

/-- `E_σ` maps every matrix to a scalar multiple of `1`. -/
theorem scalarConditionalExpectation_range_scalar
    (σ : Mat) (X : Mat) :
    ∃ c : ℂ, scalarConditionalExpectation σ X = c • (1 : Mat) :=
  ⟨trace (σ * X) / trace σ, rfl⟩

/-- `E_σ(c • 1) = c • 1`: the scalar conditional expectation fixes scalar
matrices. -/
theorem scalarConditionalExpectation_fixes_scalar
    (σ : Mat) (hσ_tr : trace σ ≠ 0) (c : ℂ) :
    scalarConditionalExpectation σ (c • (1 : Mat)) =
      c • (1 : Mat) := by
  simp only [scalarConditionalExpectation_apply, Algebra.mul_smul_comm, mul_one,
    trace_smul, smul_eq_mul, mul_div_cancel_right₀ c hσ_tr]

/-! ## Commutation with the adjoint map -/

/-- `E_σ` absorbs the adjoint map: `E_σ(adjointMap K X) = E_σ(X)`,
provided `σ` is a fixed point of `map K`.

This uses the Kraus adjointness identity
`tr(ρ · map K X) = tr(adjointMap K ρ · X)`. -/
theorem scalarConditionalExpectation_absorbs_adjointMap
    (σ : Mat)
    (K : Fin d → Mat) (hσ_fix : map K σ = σ) (X : Mat) :
    scalarConditionalExpectation σ (adjointMap K X) =
      scalarConditionalExpectation σ X := by
  simp only [scalarConditionalExpectation_apply]
  congr 1
  have : trace (σ * adjointMap K X) = trace (σ * X) :=
    calc trace (σ * adjointMap K X)
        = trace (adjointMap K X * σ) := trace_mul_comm σ (adjointMap K X)
      _ = trace (X * map K σ) := by
          rw [← trace_mul_map_eq_trace_adjointMap_mul K X σ]
      _ = trace (X * σ) := by rw [hσ_fix]
      _ = trace (σ * X) := trace_mul_comm X σ
  rw [this]

/-- The adjoint map absorbs `E_σ`: `adjointMap K (E_σ(X)) = E_σ(X)`,
provided `K` is trace-preserving (equivalently, `adjointMap K` is unital). -/
theorem adjointMap_absorbs_scalarConditionalExpectation
    (σ : Mat)
    (K : Fin d → Mat) (h_tp : IsTP K) (X : Mat) :
    adjointMap K (scalarConditionalExpectation σ X) =
      scalarConditionalExpectation σ X := by
  simp only [scalarConditionalExpectation_apply, adjointMap_smul,
    adjointMap_one_of_isTP K h_tp]

/-- `E_σ(X)` is always a fixed point of the adjoint map (when `K` is TP). -/
theorem scalarConditionalExpectation_mem_adjointFixedPoints
    (σ : Mat)
    (K : Fin d → Mat) (h_tp : IsTP K) (X : Mat) :
    scalarConditionalExpectation σ X ∈ adjointFixedPoints K :=
  adjointMap_absorbs_scalarConditionalExpectation σ K h_tp X

/-! ## Complete positivity and weighted trace preservation -/

/-- An auxiliary lemma identity: `∑ j, single j j c = c • 1` for `c : ℂ`.

The sum of diagonal basis matrices with a common scalar equals that scalar
times the identity. -/
private lemma sum_single_diag_const {D : ℕ} (c : ℂ) :
    (∑ j : Fin D, Matrix.single j j c : Matrix (Fin D) (Fin D) ℂ) =
      c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  rw [Matrix.sum_single_eq_diagonal, Matrix.smul_one_eq_diagonal]

/-- **Wolf Corollary 6.6, CP part.**

The scalar conditional expectation `E_σ` is completely positive whenever `σ`
is positive semidefinite.

The proof constructs a Kraus representation with operators
`K_{j,i} = |j⟩⟨i| · √σ` (indexed by `Fin D × Fin D`). Their Kraus sum
evaluates to `tr(σ X) • 1`, and we then scale by the nonnegative real factor
`(σ.trace.re)⁻¹` using the PSD closure of complete positivity. When `σ = 0`
the scale factor is `0`, covered uniformly by the convention `(0 : ℝ)⁻¹ = 0`
and `0 / 0 = 0`. -/
theorem scalarConditionalExpectation_isCPMap
    (σ : Mat) (hσ : σ.PosSemidef) :
    IsCPMap (scalarConditionalExpectation σ) := by
  classical
  have hσ_nn : (0 : Mat) ≤ σ := Matrix.nonneg_iff_posSemidef.mpr hσ
  -- S := √σ, S Hermitian, S * S = σ.
  set S : Mat := CFC.sqrt σ with hS_def
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ_nn
  have hS_psd : S.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)
  have hSH : Sᴴ = S := hS_psd.isHermitian.eq
  -- Unnormalised Kraus family: `K_{j,i} = |j⟩⟨i| · S`.
  let K : Fin D × Fin D → Mat :=
    fun p => Matrix.single p.1 p.2 (1 : ℂ) * S
  -- Core identity: `Kraus.mapLM K X = trace (σ * X) • 1`.
  have hunnorm : ∀ X : Mat,
      Kraus.mapLM K X = (Matrix.trace (σ * X)) • (1 : Mat) := by
    intro X
    change Kraus.map K X = _
    rw [Kraus.map_apply]
    -- Step A: simplify each term K(j,i) X K(j,i)ᴴ.
    have step : ∀ p : Fin D × Fin D,
        K p * X * (K p)ᴴ =
          Matrix.single p.1 p.1 ((S * X * S) p.2 p.2) := by
      rintro ⟨j, i⟩
      change Matrix.single j i (1 : ℂ) * S * X *
            (Matrix.single j i (1 : ℂ) * S)ᴴ =
          Matrix.single j j ((S * X * S) i i)
      rw [Matrix.conjTranspose_mul, hSH, Matrix.conjTranspose_single, star_one]
      -- Goal: single j i 1 * S * X * (S * single i j 1) =
      --      single j j ((S * X * S) i i)
      have hrearr :
          Matrix.single j i (1 : ℂ) * S * X * (S * Matrix.single i j (1 : ℂ)) =
            Matrix.single j i (1 : ℂ) * (S * X * S) *
              Matrix.single i j (1 : ℂ) := by
        simp only [Matrix.mul_assoc]
      rw [hrearr, Matrix.single_mul_mul_single]
      simp
    calc
      ∑ p : Fin D × Fin D, K p * X * (K p)ᴴ
          = ∑ p : Fin D × Fin D,
              Matrix.single p.1 p.1 ((S * X * S) p.2 p.2) :=
            Finset.sum_congr rfl (fun p _ => step p)
      _ = ∑ j : Fin D, ∑ i : Fin D,
              Matrix.single j j ((S * X * S) i i) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ j : Fin D,
              Matrix.single j j (∑ i : Fin D, (S * X * S) i i) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            -- `Matrix.single j j` is an additive homomorphism in the scalar
            -- argument, so it commutes with finite sums.
            exact
              (map_sum (Matrix.singleAddMonoidHom (α := ℂ) j j)
                (fun i => (S * X * S) i i) Finset.univ).symm
      _ = ∑ j : Fin D, Matrix.single j j (Matrix.trace (S * X * S)) := by
            simp [Matrix.trace, Matrix.diag]
      _ = (Matrix.trace (S * X * S)) • (1 : Mat) :=
            sum_single_diag_const (D := D) (Matrix.trace (S * X * S))
      _ = (Matrix.trace (σ * X)) • (1 : Mat) := by
            congr 1
            calc Matrix.trace (S * X * S)
                = Matrix.trace (S * (X * S)) := by rw [Matrix.mul_assoc]
              _ = Matrix.trace ((X * S) * S) := Matrix.trace_mul_comm _ _
              _ = Matrix.trace (X * (S * S)) := by rw [Matrix.mul_assoc]
              _ = Matrix.trace (X * σ) := by rw [hSS]
              _ = Matrix.trace (σ * X) := Matrix.trace_mul_comm _ _
  -- The Kraus family yields a CP map.
  have hcpK : IsCPMap (Kraus.mapLM K) := isCPMap_of_krausMapLM K
  -- Rewrite `scalarConditionalExpectation σ` as `(σ.trace.re)⁻¹ • Kraus.mapLM K`.
  have htr_nn : (0 : ℂ) ≤ σ.trace := Matrix.PosSemidef.trace_nonneg hσ
  have htr_re_nn : (0 : ℝ) ≤ σ.trace.re := (Complex.nonneg_iff.mp htr_nn).1
  have htr_im : σ.trace.im = 0 := (Complex.nonneg_iff.mp htr_nn).2.symm
  have htr_eq : ((σ.trace.re : ℝ) : ℂ) = σ.trace := by
    apply Complex.ext
    · simp
    · simp [htr_im]
  -- `scalarConditionalExpectation σ = ((σ.trace.re)⁻¹ : ℂ) • Kraus.mapLM K`.
  have hrw : scalarConditionalExpectation σ =
      (((σ.trace.re : ℝ)⁻¹ : ℝ) : ℂ) • Kraus.mapLM K := by
    ext X
    rw [LinearMap.smul_apply, hunnorm X, scalarConditionalExpectation_apply,
      smul_smul]
    -- Goal: (trace (σ * X) / σ.trace) • 1 =
    --      (((σ.trace.re : ℝ)⁻¹ : ℂ) * trace (σ * X)) • 1
    rw [Complex.ofReal_inv, htr_eq, div_eq_mul_inv, mul_comm]
  rw [hrw]
  -- The scaling factor is a nonneg real, so CP is preserved.
  exact hcpK.smul_nonneg (inv_nonneg.mpr htr_re_nn)

/-- **Wolf Corollary 6.6, trace-preservation part.**

The scalar conditional expectation `E_σ` preserves the σ-weighted trace:
`tr(σ · E_σ(X)) = tr(σ · X)` for every `X`, provided `tr σ ≠ 0`.

This is the Heisenberg-picture analogue of trace preservation relative to
the stationary state `σ`. -/
theorem scalarConditionalExpectation_preserves_weighted_trace
    (σ : Mat) (hσ_tr : Matrix.trace σ ≠ 0) (X : Mat) :
    Matrix.trace (σ * scalarConditionalExpectation σ X) =
      Matrix.trace (σ * X) := by
  rw [scalarConditionalExpectation_apply, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul, div_mul_cancel₀ _ hσ_tr]

/-! ## Conditional expectation onto the adjoint fixed-point *-subalgebra -/

/-- **Wolf Theorem 6.15** (scalar fixed-point algebra case):

When a TP Kraus family has `ρ` as a positive-definite fixed point of the
Schrödinger map, and the adjoint fixed-point set consists only of scalar
matrices, the scalar conditional expectation `E_ρ` is a conditional
expectation onto the adjoint fixed-point `StarSubalgebra`.

This covers the primitive channel case. In the general irreducible case
with period `h > 1`, the fixed-point algebra is `h`-dimensional and the
conditional expectation requires the Wedderburn block decomposition
(Wolf Theorem 6.14, issue #27). -/
theorem scalarConditionalExpectation_isConditionalExpectation
    [NeZero D]
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)
    (h_scalar : ∀ X : Mat, X ∈ adjointFixedPoints K →
      ∃ c : ℂ, X = c • (1 : Mat)) :
    IsConditionalExpectation
      (scalarConditionalExpectation ρ)
      (adjointFixedPointsStarSubalgebra K h_tp hρ hρ_fix) where
  idempotent := scalarConditionalExpectation_idempotent ρ
    (ne_of_gt hρ.trace_pos)
  unital := scalarConditionalExpectation_unital ρ
    (ne_of_gt hρ.trace_pos)
  range_subset X := by
    rw [mem_adjointFixedPointsStarSubalgebra]
    exact scalarConditionalExpectation_mem_adjointFixedPoints ρ K h_tp X
  fixes X hX := by
    rw [mem_adjointFixedPointsStarSubalgebra] at hX
    obtain ⟨c, hc⟩ := h_scalar X hX
    rw [hc]
    exact scalarConditionalExpectation_fixes_scalar ρ
      (ne_of_gt hρ.trace_pos) c

end Kraus
