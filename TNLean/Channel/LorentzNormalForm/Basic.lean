/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Basic
import TNLean.Channel.TransferMatrix
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.ChoiRectangular
import TNLean.Analysis.MarginalSupport

/-!
# Lorentz normal form: filtering operations and doubly-stochastic maps

This module collects the shared definitions and matrix-algebra lemmas for the
normal-form development of Wolf Section 2.3 (Equations (2.35)–(2.37)):
SL-filtering operations, the doubly-stochastic predicates, and the
Kronecker-conjugation and partial-trace identities used by the minimisation
argument.

## Main definitions

* `Wolf.SLFiltering` — a filtering operation `Φ(X) = S X S†` with `det S = 1`
* `Wolf.DoublyStochastic` — square doubly-stochastic predicate: `T(𝟙) ∝ 𝟙`
  and `tr₁[τ] ∝ 𝟙`
* `Wolf.DoublyStochasticRect` — rectangular doubly-stochastic predicate:
  `T(𝟙) ∝ 𝟙` and `T*(𝟙) ∝ 𝟙` (Wolf Proposition 2.9's condition)

## Main results

* `Wolf.unitaryConjLM_comp` — conjugation maps compose
* `Wolf.kron_one_conj_entry`, `Wolf.one_kron_conj_entry` — entry formulas for
  conjugation by `A ⊗ₖ 1` and `1 ⊗ₖ B` on possibly different tensor factors
* `Wolf.traceLeft_one_kron_conj`, `Wolf.traceRight_kron_one_conj` — the
  partial traces commute with one-sided conjugation
* `Wolf.choiMatrix_unitaryConj_comp`, `Wolf.choiMatrix_comp_unitaryConj` —
  the square Choi matrix of a conjugated map
* `Wolf.choiMatrixRect_unitaryConj_comp`, `Wolf.choiMatrixRect_comp_unitaryConj`
  — the rectangular Choi matrix of a conjugated map

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.3][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix Finset
open ChoiJamiolkowski

namespace Wolf

section FilteringOperations

/-- An `SLFiltering` for `D × D` matrices bundles a matrix `S` with
`det S = 1` (and `S` invertible) together with its associated CP map
`Φ(X) = S X S†`.  Such maps are called *filtering operations* in Wolf Section 2.3. -/
structure SLFiltering (D : ℕ) where
  /-- The filtering matrix, with determinant 1. -/
  S : Matrix (Fin D) (Fin D) ℂ
  /-- `det S = 1`. -/
  det_eq_one : S.det = 1
  /-- The CP map: Φ(X) = S X S†. -/
  map : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ
  /-- `map` is exactly the unitary conjugation by `S`. -/
  map_eq : map = unitaryConjLM (D := D) S
  /-- SL-filterings are CP. -/
  cp : IsCPMap map

/-- The matrix `S` of an SL-filtering is invertible (follows from `det_eq_one`). -/
lemma SLFiltering.S_isUnit {D : ℕ} (Φ : SLFiltering D) : IsUnit Φ.S := by
  have h : Φ.S.det = 1 := Φ.det_eq_one
  have hdet : IsUnit (Φ.S.det) := by rw [h]; exact isUnit_one
  -- In a CommRing, a matrix is invertible iff its determinant is a unit.
  refine (Matrix.isUnit_iff_isUnit_det Φ.S).mpr hdet

/-- The identity map is an SL-filtering (S = 1). -/
noncomputable def SLFiltering.id (D : ℕ) : SLFiltering D where
  S := 1
  det_eq_one := by simp
  map := unitaryConjLM (D := D) 1
  map_eq := rfl
  cp := unitaryConjLM_isCPMap (D := D) 1

/-- Composition of two SL-filterings is an SL-filtering. -/
noncomputable def SLFiltering.comp {D : ℕ} (Φ Ψ : SLFiltering D) : SLFiltering D where
  S := Φ.S * Ψ.S
  det_eq_one := by
    rw [Matrix.det_mul, Φ.det_eq_one, Ψ.det_eq_one, one_mul]
  map := unitaryConjLM (D := D) (Φ.S * Ψ.S)
  map_eq := rfl
  cp := unitaryConjLM_isCPMap (D := D) (Φ.S * Ψ.S)

/-- `unitaryConjLM A ∘ₗ unitaryConjLM B = unitaryConjLM (A * B)`. -/
lemma unitaryConjLM_comp {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    unitaryConjLM (D := D) A ∘ₗ unitaryConjLM (D := D) B =
    unitaryConjLM (D := D) (A * B) := by
  ext X; simp [unitaryConjLM_apply, Matrix.mul_assoc, Matrix.conjTranspose_mul]

end FilteringOperations

/-! ### Doubly-stochastic maps -/

section DoublyStochastic

variable {D : ℕ} (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- A CP map `T` is **doubly-stochastic** if `T(1) ∝ 1` and the reduced density
matrix `tr₁[τ]` of its Choi matrix `τ = (T ⊗ id)(|Ω⟩⟨Ω|)` is proportional to
the identity.  By Choi–Jamiołkowski, this is equivalent to both `T(1)` and
`T*(1)` being proportional to identity, which is the target normal form in
Wolf Proposition 2.9.

We use the partial-trace formulation to avoid depending on the adjoint of `T`
as a Hilbert–Schmidt operator. -/
def DoublyStochastic : Prop :=
  (∃ c₁ : ℂ, T 1 = c₁ • (1 : Matrix (Fin D) (Fin D) ℂ)) ∧
  (∃ c₂ : ℂ, Matrix.traceLeft (choiMatrix T) = c₂ • (1 : Matrix (Fin D) (Fin D) ℂ))

/-- Doubly-stochastic implies T(1) ∝ 1. -/
lemma DoublyStochastic.unital (hT : DoublyStochastic T) :
    ∃ c : ℂ, T 1 = c • (1 : Matrix (Fin D) (Fin D) ℂ) := hT.1

/-- Doubly-stochastic implies the partial trace of the Choi matrix is ∝ 1
(equivalently, T*(1) ∝ 1). -/
lemma DoublyStochastic.tracePreserving (hT : DoublyStochastic T) :
    ∃ c : ℂ, Matrix.traceLeft (choiMatrix T) =
      c • (1 : Matrix (Fin D) (Fin D) ℂ) := hT.2

end DoublyStochastic

/-! ### Shared Kronecker-conjugation and partial-trace lemmas -/

section SharedLemmas

variable {D : ℕ}

/-- Entry formula for conjugation by `A ⊗ₖ 1` (identity on the second factor).
The two tensor factors may have different dimensions. -/
lemma kron_one_conj_entry {dOut dIn : ℕ} (A : Matrix (Fin dOut) (Fin dOut) ℂ)
    (M : Matrix (Fin dOut × Fin dIn) (Fin dOut × Fin dIn) ℂ)
    (i₁ : Fin dOut) (i₂ : Fin dIn) (j₁ : Fin dOut) (j₂ : Fin dIn) :
    ((A ⊗ₖ (1 : Matrix (Fin dIn) (Fin dIn) ℂ)) * M *
        (A ⊗ₖ (1 : Matrix (Fin dIn) (Fin dIn) ℂ))ᴴ) (i₁, i₂) (j₁, j₂)
      = ∑ c, ∑ d, A i₁ c * M (c, i₂) (d, j₂) * star (A j₁ d) := by
  have L : ∀ s : Fin dOut × Fin dIn,
      ((A ⊗ₖ (1 : Matrix (Fin dIn) (Fin dIn) ℂ)) * M) (i₁, i₂) s
        = ∑ c, A i₁ c * M (c, i₂) s := by
    intro s
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one,
      mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i₂ (fun w₂ => A i₁ c * M (c, w₂) s)]
    simp
  have key : ((A ⊗ₖ (1 : Matrix (Fin dIn) (Fin dIn) ℂ)) * M *
        (A ⊗ₖ (1 : Matrix (Fin dIn) (Fin dIn) ℂ))ᴴ) (i₁, i₂) (j₁, j₂)
      = ∑ d, ∑ c, A i₁ c * M (c, i₂) (d, j₂) * star (A j₁ d) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single j₂]
    · rw [L (d, j₂), Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
    · intro b _ hb
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ j₂) h
  rw [key, Finset.sum_comm]

/-- Entry formula for conjugation by `1 ⊗ₖ B` (identity on the first factor).
The two tensor factors may have different dimensions. -/
lemma one_kron_conj_entry {dOut dIn : ℕ} (B : Matrix (Fin dIn) (Fin dIn) ℂ)
    (M : Matrix (Fin dOut × Fin dIn) (Fin dOut × Fin dIn) ℂ)
    (i₁ : Fin dOut) (i₂ : Fin dIn) (j₁ : Fin dOut) (j₂ : Fin dIn) :
    (((1 : Matrix (Fin dOut) (Fin dOut) ℂ) ⊗ₖ B) * M *
        ((1 : Matrix (Fin dOut) (Fin dOut) ℂ) ⊗ₖ B)ᴴ) (i₁, i₂) (j₁, j₂)
      = ∑ a, ∑ b, B i₂ a * M (i₁, a) (j₁, b) * star (B j₂ b) := by
  have L : ∀ s : Fin dOut × Fin dIn,
      (((1 : Matrix (Fin dOut) (Fin dOut) ℂ) ⊗ₖ B) * M) (i₁, i₂) s
        = ∑ a, B i₂ a * M (i₁, a) s := by
    intro s
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i₁ (fun w₁ => B i₂ a * M (w₁, a) s)]
    simp
  have key : (((1 : Matrix (Fin dOut) (Fin dOut) ℂ) ⊗ₖ B) * M *
        ((1 : Matrix (Fin dOut) (Fin dOut) ℂ) ⊗ₖ B)ᴴ) (i₁, i₂) (j₁, j₂)
      = ∑ b, ∑ a, B i₂ a * M (i₁, a) (j₁, b) * star (B j₂ b) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single j₁]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [L (j₁, b), Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
    · intro c _ hc
      apply Finset.sum_eq_zero
      intro b _
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Ne.symm hc]
    · intro h; exact absurd (Finset.mem_univ j₁) h
  rw [key, Finset.sum_comm]

/-- `tr_A` commutes with conjugation by `1 ⊗ₖ X` (acting on the second factor):
`tr_A((1 ⊗ X) ρ (1 ⊗ X)†) = X (tr_A ρ) X†`. -/
lemma traceLeft_one_kron_conj {dOut dIn : ℕ} (X : Matrix (Fin dIn) (Fin dIn) ℂ)
    (ρ : Matrix (Fin dOut × Fin dIn) (Fin dOut × Fin dIn) ℂ) :
    Matrix.traceLeft (((1 : Matrix (Fin dOut) (Fin dOut) ℂ) ⊗ₖ X) * ρ *
        ((1 : Matrix (Fin dOut) (Fin dOut) ℂ) ⊗ₖ X)ᴴ)
      = X * Matrix.traceLeft ρ * Xᴴ := by
  ext i j
  rw [Matrix.traceLeft_apply]
  have hRHS : (X * Matrix.traceLeft ρ * Xᴴ) i j
      = ∑ a, ∑ b, X i a * (∑ k, ρ (k, a) (k, b)) * star (X j b) := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.traceLeft_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hRHS]
  simp_rw [one_kron_conj_entry X ρ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

/-- `tr_B` commutes with conjugation by `X ⊗ₖ 1` (acting on the first factor):
`tr_B((X ⊗ 1) ρ (X ⊗ 1)†) = X (tr_B ρ) X†`. -/
lemma traceRight_kron_one_conj {dOut dIn : ℕ} (X : Matrix (Fin dOut) (Fin dOut) ℂ)
    (ρ : Matrix (Fin dOut × Fin dIn) (Fin dOut × Fin dIn) ℂ) :
    Matrix.traceRight ((X ⊗ₖ (1 : Matrix (Fin dIn) (Fin dIn) ℂ)) * ρ *
        (X ⊗ₖ (1 : Matrix (Fin dIn) (Fin dIn) ℂ))ᴴ)
      = X * Matrix.traceRight ρ * Xᴴ := by
  ext i j
  rw [Matrix.traceRight_apply]
  have hRHS : (X * Matrix.traceRight ρ * Xᴴ) i j
      = ∑ c, ∑ d, X i c * (∑ k, ρ (c, k) (d, k)) * star (X j d) := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.traceRight_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hRHS]
  simp_rw [kron_one_conj_entry X ρ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Conjugating a matrix unit by `B` spreads it over all matrix units:
`B (single i₂ j₂ c) B† = ∑ a b, (B a i₂ · conj(B b j₂)) (single a b c)`. -/
lemma single_conj_spread {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (i₂ j₂ : Fin n) (c : ℂ) :
    B * Matrix.single i₂ j₂ c * Bᴴ
      = ∑ a, ∑ b, (B a i₂ * star (B b j₂)) • Matrix.single a b c := by
  ext p q
  have hL : (B * Matrix.single i₂ j₂ c * Bᴴ) p q = B p i₂ * c * star (B q j₂) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j₂]
    · rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply]
    · intro x _ hx; rw [Matrix.mul_single_apply_of_ne (hbj := hx) (M := B), zero_mul]
    · intro h; exact absurd (Finset.mem_univ j₂) h
  have hR : (∑ a, ∑ b, (B a i₂ * star (B b j₂)) • Matrix.single a b c) p q
      = B p i₂ * star (B q j₂) * c := by
    rw [Matrix.sum_apply, Finset.sum_eq_single p]
    · rw [Matrix.sum_apply, Finset.sum_eq_single q]
      · rw [Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul]
      · intro b _ hb
        rw [Matrix.smul_apply, Matrix.single_apply_of_col_ne p p hb c, smul_zero]
      · intro h; exact absurd (Finset.mem_univ q) h
    · intro a _ ha
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.smul_apply, Matrix.single_apply_of_row_ne ha b q c, smul_zero]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [hL, hR]; ring

/-- Choi matrix of post-composition with conjugation by `A`:
`choi(Ad_A ∘ T) = (A ⊗ 1) choi(T) (A ⊗ 1)†`. -/
lemma choiMatrix_unitaryConj_comp (A : Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    choiMatrix (unitaryConjLM A ∘ₗ T)
      = (A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * choiMatrix T *
          (A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [kron_one_conj_entry A (choiMatrix T) i₁ i₂ j₁ j₂, choiMatrix_apply,
    LinearMap.comp_apply, unitaryConjLM_apply, Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [choiMatrix_apply]

/-- Choi matrix of pre-composition with conjugation by `B`:
`choi(T ∘ Ad_B) = (1 ⊗ Bᵀ) choi(T) (1 ⊗ Bᵀ)†`. -/
lemma choiMatrix_comp_unitaryConj (B : Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    choiMatrix (T ∘ₗ unitaryConjLM B)
      = ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ Bᵀ) * choiMatrix T *
          ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ Bᵀ)ᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [one_kron_conj_entry Bᵀ (choiMatrix T) i₁ i₂ j₁ j₂, choiMatrix_apply,
    LinearMap.comp_apply, unitaryConjLM_apply, omegaSlice_eq_single, single_conj_spread,
    map_sum]
  simp_rw [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [choiMatrix_apply, omegaSlice_eq_single, Matrix.transpose_apply, Matrix.transpose_apply]
  ring

/-- `Matrix.traceLeft` agrees with `Matrix.traceLeftA`. -/
lemma traceLeft_eq_traceLeftA (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    Matrix.traceLeft ρ = Matrix.traceLeftA ρ := rfl

/-- The full trace equals the trace of the right partial trace: `tr(X) = tr(tr_B(X))`. -/
lemma trace_eq_trace_traceRight {dOut dIn : ℕ}
    (X : Matrix (Fin dOut × Fin dIn) (Fin dOut × Fin dIn) ℂ) :
    X.trace = (Matrix.traceRight X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.traceRight_apply]
  exact Fintype.sum_prod_type _
/-- The reduced state `tr_B(choi T)` equals (up to the `|Ω⟩` normalization) `T 1`. -/
lemma traceRight_choiMatrix
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Matrix.traceRight (choiMatrix T)
      = (((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) *
          star ((1 : ℂ) / ((D : ℝ).sqrt : ℂ))) • T 1 := by
  set cc : ℂ := ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) *
    star ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) with hcc
  ext i j
  rw [Matrix.traceRight_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 : ∀ k : Fin D, choiMatrix T (i, k) (j, k) = cc * T (Matrix.single k k 1) i j := by
    intro k
    rw [choiMatrix_apply, omegaSlice_eq_single,
      show Matrix.single k k cc = cc • Matrix.single k k (1 : ℂ) by
        rw [Matrix.smul_single, smul_eq_mul, mul_one],
      map_smul, Matrix.smul_apply, smul_eq_mul]
  simp_rw [h1, ← Finset.mul_sum]
  congr 1
  rw [← Matrix.sum_apply, ← map_sum, Matrix.sum_single_one]

/-- The `|Ω⟩` normalization constant is nonzero. -/
lemma omega_coeff_ne_zero (hD : 0 < D) :
    (((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * star ((1 : ℂ) / ((D : ℝ).sqrt : ℂ))) ≠ 0 := by
  have hsqrt : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD)
  have h1 : (1 : ℂ) / ((D : ℝ).sqrt : ℂ) ≠ 0 := one_div_ne_zero hsqrt
  exact mul_ne_zero h1 (star_ne_zero.mpr h1)
end SharedLemmas

/-! ### Rectangular Choi-conjugation lemmas and the doubly-stochastic predicate -/

section RectangularBasics

variable {d₁ d₂ : ℕ}

/-- Choi matrix of post-composition with conjugation by `A`, rectangular form:
`choi(Ad_A ∘ T) = (A ⊗ 1) choi(T) (A ⊗ 1)†` for `A` on the output factor. -/
lemma choiMatrixRect_unitaryConj_comp (A : Matrix (Fin d₂) (Fin d₂) ℂ)
    (T : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ) :
    ChoiRectangular.choiMatrix (unitaryConjLM A ∘ₗ T)
      = (A ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) * ChoiRectangular.choiMatrix T *
          (A ⊗ₖ (1 : Matrix (Fin d₁) (Fin d₁) ℂ))ᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [kron_one_conj_entry A (ChoiRectangular.choiMatrix T) i₁ i₂ j₁ j₂,
    ChoiRectangular.choiMatrix_apply, LinearMap.comp_apply, unitaryConjLM_apply,
    Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ChoiRectangular.choiMatrix_apply]

/-- Choi matrix of pre-composition with conjugation by `B`, rectangular form:
`choi(T ∘ Ad_B) = (1 ⊗ Bᵀ) choi(T) (1 ⊗ Bᵀ)†` for `B` on the input factor.
This is Wolf's "irrelevant transposition" of the first filtering factor. -/
lemma choiMatrixRect_comp_unitaryConj (B : Matrix (Fin d₁) (Fin d₁) ℂ)
    (T : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ) :
    ChoiRectangular.choiMatrix (T ∘ₗ unitaryConjLM B)
      = ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ Bᵀ) * ChoiRectangular.choiMatrix T *
          ((1 : Matrix (Fin d₂) (Fin d₂) ℂ) ⊗ₖ Bᵀ)ᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [one_kron_conj_entry Bᵀ (ChoiRectangular.choiMatrix T) i₁ i₂ j₁ j₂,
    ChoiRectangular.choiMatrix_apply, LinearMap.comp_apply, unitaryConjLM_apply,
    ChoiJamiolkowski.omegaSlice_eq_single, single_conj_spread, map_sum]
  simp_rw [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ChoiRectangular.choiMatrix_apply, ChoiJamiolkowski.omegaSlice_eq_single,
    Matrix.transpose_apply, Matrix.transpose_apply]
  ring
/-- A linear map `T : M_{d₁}(ℂ) → M_{d₂}(ℂ)` between possibly different matrix
algebras is **doubly-stochastic** if `T(𝟙)` and `T*(𝟙)` are both proportional
to the identity matrix, where `T*` is the trace-pairing adjoint.  This is the
rectangular normal-form condition of Wolf Proposition 2.9
(`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 923–929). -/
def DoublyStochasticRect
    (T : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ) : Prop :=
  (∃ c₁ : ℂ, T 1 = c₁ • (1 : Matrix (Fin d₂) (Fin d₂) ℂ)) ∧
  (∃ c₂ : ℂ, Matrix.traceAdjointMap T 1 = c₂ • (1 : Matrix (Fin d₁) (Fin d₁) ℂ))
end RectangularBasics

end Wolf
