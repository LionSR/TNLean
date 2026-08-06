/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.OperatorSystem
import TNLean.Channel.ChoiRectangular
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Cone.Extension

/-!
# Extending completely positive maps from operator systems

This file proves Wolf's proposition "Extending cp maps from operator systems"
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 616–626): a
completely positive linear map `T : S → M_n(ℂ)` defined on an operator system
`S ⊆ M_m(ℂ)` extends to a completely positive map `T' : M_m(ℂ) → M_n(ℂ)`
agreeing with `T` on `S`.

## Proof route

Following Wolf's proof, fix the ancilla dimension to be `n`, the codomain
size, so that `B = M_n(ℂ)` is (trivially, in the finite-dimensional case)
already a subalgebra of `M_n(ℂ)`. Define the scalar functional

  `τ(A) := ⟨Ω|(T ⊗ id_n)(A)|Ω⟩`, `A ∈ S ⊗ M_n(ℂ)`,

with `Ω` the maximally entangled vector of dimension `n`
(`Matrix.omegaProj`). Complete positivity of `T` at level `n` is equivalent to
the bound `τ(A) ≤ f(A) := ‖A‖∞ · τ(1)` for Hermitian `A ∈ S ⊗ M_n(ℂ)`; since
`f` is sublinear, the Hahn–Banach theorem
(`exists_extension_of_le_sublinear`) extends `τ` from the Hermitian part of
`S ⊗ M_n(ℂ)` to that of `M_m(ℂ) ⊗ M_n(ℂ)`, and by linearity to a full
`ℂ`-linear functional `τ'`. The same bound applied to `‖A‖∞ • 1 - A` shows
`τ'` is positive on positive semidefinite matrices, which by the
Choi–Jamiolkowski correspondence yields a completely positive extension `T'`.

## Main results

* `Matrix.exists_cp_extension_of_operatorSystem`: the proposition itself.
* `Matrix.exists_tau_extension`: the Hahn–Banach/complexification step, `τ`
  extends to a `ℂ`-linear `τ' = complexify g` agreeing with `τ` on
  `S ⊗ M_n(ℂ)` and obeying the same norm-domination bound everywhere.
* `Matrix.rieszMatrix_complexify_posSemidef`: the Riesz matrix of `τ'` is
  positive semidefinite.
* `Matrix.reconstructedMap_eq_kraus_sum`: the map recovered from `τ'` by
  Wolf's inversion formula is completely positive.
* `Matrix.tau_kron_single`: Wolf's inversion formula holds for the original
  `T` on `S`, giving `T'|_S = T`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

variable {m n : ℕ}

/-- A `CStarAlgebra` instance for a matrix algebra using the `ℓ²`-operator
norm, matching the pattern used elsewhere in `TNLean.Channel.Schwarz`. -/
noncomputable local instance matrixCStarAlgebraOfFintype (ι : Type*) [Fintype ι] [DecidableEq ι] :
    CStarAlgebra (Matrix ι ι ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := Matrix.instCStarRing
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance

/-! ### Wolf's functional `τ` -/

/-- **Wolf's functional** (Ch. 1, line 623): `τ(A) = ⟨Ω|(T ⊗ id_n)(A)|Ω⟩` for
`A` in the operator system `S ⊗ M_n(ℂ)`, where `Ω` is the maximally entangled
vector of dimension `n` (the codomain size), so that `B = M_n(ℂ)` is
(trivially) a subalgebra of `M_n(ℂ)`. -/
noncomputable def tau {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    ↥(tensorSubmodule S n) →ₗ[ℂ] ℂ where
  toFun A := Matrix.trace (Matrix.omegaProj n * tensorMapIdSubLM T A)
  map_add' A B := by rw [map_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' c A := by
    rw [map_smul, Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul]

theorem tau_apply {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (A : ↥(tensorSubmodule S n)) :
    tau T A = Matrix.trace (Matrix.omegaProj n * tensorMapIdSub T A) :=
  rfl

/-! ### The norm-domination bound for Hermitian matrices -/

/-- For Hermitian `A`, `‖A‖∞ • 1 - A` is positive semidefinite: the spectrum of
a self-adjoint element of a `C^*`-algebra lies in `[-‖A‖, ‖A‖]`
(`IsSelfAdjoint.le_algebraMap_norm_self`). -/
theorem IsHermitian.norm_smul_one_sub_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (‖A‖ • (1 : Matrix ι ι ℂ) - A).PosSemidef := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := matrixCStarAlgebraOfFintype ι
  have hsa : IsSelfAdjoint A := isSelfAdjoint_iff.mpr (Matrix.star_eq_conjTranspose A ▸ hA)
  have hle : A ≤ algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ := hsa.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at hle
  exact Matrix.le_iff.mp hle

/-- The `+` companion of `IsHermitian.norm_smul_one_sub_posSemidef`, obtained by
applying it to `-A`. -/
theorem IsHermitian.norm_smul_one_add_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (‖A‖ • (1 : Matrix ι ι ℂ) + A).PosSemidef := by
  have h := (hA.neg).norm_smul_one_sub_posSemidef
  rwa [norm_neg, sub_neg_eq_add] at h

/-- For positive semidefinite `A`, `‖A‖∞ • 1 - A` has norm at most `‖A‖∞`:
both `‖A‖∞ • 1 - A` and `‖A‖∞ • 1` are positive semidefinite, `‖A‖∞ • 1 - A ≤
‖A‖∞ • 1`, and the `C^*`-order is norm-monotone on the positive cone. -/
theorem PosSemidef.norm_smul_one_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ‖‖A‖ • (1 : Matrix ι ι ℂ) - A‖ ≤ ‖A‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := matrixCStarAlgebraOfFintype ι
  have hnn : (0 : Matrix ι ι ℂ) ≤ ‖A‖ • (1 : Matrix ι ι ℂ) - A :=
    (hA.1.norm_smul_one_sub_posSemidef).nonneg
  have hle : ‖A‖ • (1 : Matrix ι ι ℂ) - A ≤ ‖A‖ • (1 : Matrix ι ι ℂ) := by
    rw [Matrix.le_iff]
    simpa using hA
  have hmono := CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg A)] at hmono
  have hone : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
    by_cases hnt : Nontrivial (Matrix ι ι ℂ)
    · haveI := hnt
      exact (norm_one (α := Matrix ι ι ℂ)).le
    · rw [not_nontrivial_iff_subsingleton] at hnt
      simp [Subsingleton.elim (1 : Matrix ι ι ℂ) 0]
  calc ‖‖A‖ • (1 : Matrix ι ι ℂ) - A‖ ≤ ‖A‖ * ‖(1 : Matrix ι ι ℂ)‖ := hmono
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hone (norm_nonneg A)
    _ = ‖A‖ := mul_one _

/-- **Positivity of a bounded functional** (Wolf Ch. 1, line 626 converse): a
`ℂ`-linear functional `τ'` dominated by `X ↦ ‖X‖∞ · τ'(1)` on Hermitian
matrices is nonnegative on every positive semidefinite matrix. Applying the
bound to `‖A‖∞ • 1 - A` and using `PosSemidef.norm_smul_one_sub_le` gives
`τ'(A) ≥ 0`. -/
theorem tau'_nonneg_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tau' : Matrix ι ι ℂ →ₗ[ℂ] ℂ}
    (hdom : ∀ X : Matrix ι ι ℂ, X.IsHermitian → (tau' X).re ≤ ‖X‖ * (tau' 1).re)
    (hK : 0 ≤ (tau' 1).re) {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    0 ≤ (tau' A).re := by
  have hB := hdom (‖A‖ • (1 : Matrix ι ι ℂ) - A) (hA.1.norm_smul_one_sub_posSemidef).1
  have hBnorm : ‖‖A‖ • (1 : Matrix ι ι ℂ) - A‖ ≤ ‖A‖ := hA.norm_smul_one_sub_le
  have hlin : tau' (‖A‖ • (1 : Matrix ι ι ℂ) - A) = (‖A‖ : ℂ) * tau' 1 - tau' A := by
    have heq : ‖A‖ • (1 : Matrix ι ι ℂ) = (‖A‖ : ℂ) • (1 : Matrix ι ι ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [map_sub, heq, map_smul, smul_eq_mul]
  rw [hlin] at hB
  have hre : ((‖A‖ : ℂ) * tau' 1 - tau' A).re = ‖A‖ * (tau' 1).re - (tau' A).re := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [hre] at hB
  have hmul : ‖‖A‖ • (1 : Matrix ι ι ℂ) - A‖ * (tau' 1).re ≤ ‖A‖ * (tau' 1).re :=
    mul_le_mul_of_nonneg_right hBnorm hK
  linarith

/-- `Matrix.omegaProj` is Hermitian (it is a rank-one projector `|Ω⟩⟨Ω|`). -/
theorem omegaProj_isHermitian (d : ℕ) : (Matrix.omegaProj d).IsHermitian :=
  (Matrix.posSemidef_vecMulVec_self_star (Matrix.omegaVec d)).1

/-- The unit of `M_m(ℂ) ⊗ M_n(ℂ)` lies in `S ⊗ M_n(ℂ)` whenever `S` is an
operator system: its blocks are `0` or `1_m ∈ S`. -/
theorem one_mem_tensorSubmodule {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) :
    (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ∈ tensorSubmodule S n := by
  intro i j
  by_cases hij : i = j
  · subst hij
    have : Matrix.bipartiteSlice (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) i i = 1 := by
      ext a b
      simp only [Matrix.bipartiteSlice_apply, Matrix.one_apply, Prod.mk.injEq]
      by_cases hab : a = b <;> simp [hab]
    rw [this]; exact hS.one_mem
  · have : Matrix.bipartiteSlice (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) i j = 0 := by
      ext a b
      simp only [Matrix.bipartiteSlice_apply, Matrix.one_apply, Matrix.zero_apply, Prod.mk.injEq]
      simp [hij]
    rw [this]; exact S.zero_mem

/-- Real scalar multiples of the unit are positive semidefinite, and their
`tensorMapIdSub`-preimage membership in `S ⊗ M_n(ℂ)` is inherited from `1`. -/
private theorem real_smul_one_mem_tensorSubmodule {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) (r : ℝ) :
    r • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ∈ tensorSubmodule S n := by
  have hone := one_mem_tensorSubmodule (n := n) hS
  have heq : r • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) =
      (r : ℂ) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) := by
    ext i j; simp [Complex.real_smul]
  rw [heq]; exact (tensorSubmodule S n).smul_mem (r : ℂ) hone

private theorem real_smul_one_posSemidef {ι : Type*} [Finite ι] [DecidableEq ι]
    {r : ℝ} (hr : 0 ≤ r) : (r • (1 : Matrix ι ι ℂ)).PosSemidef := by
  have _ := Fintype.ofFinite ι
  have heq : r • (1 : Matrix ι ι ℂ) = (r : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j; simp [Complex.real_smul]
  rw [heq]
  exact (Matrix.PosSemidef.one).smul (by exact_mod_cast hr)

/-- `T ⊗ id_n` preserves Hermiticity on `S ⊗ M_n(ℂ)`: a completely positive map
sends the difference of the two positive semidefinite matrices
`‖A‖∞ • 1 + A` and `‖A‖∞ • 1` (both in `S ⊗ M_n(ℂ)`) to a Hermitian matrix. -/
theorem tensorMapIdSub_isHermitian {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hT : IsCPAtLevel T n) (A : ↥(tensorSubmodule S n))
    (hA : (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).IsHermitian) :
    (tensorMapIdSub T A).IsHermitian := by
  set nA : ℝ := ‖(A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)‖ with hnA
  have hscalar_mem : nA • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ∈ tensorSubmodule S n :=
    real_smul_one_mem_tensorSubmodule hS nA
  have hsum_mem : nA • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) + (A : _) ∈
      tensorSubmodule S n :=
    (tensorSubmodule S n).add_mem hscalar_mem A.2
  have hsum_psd := hT ⟨_, hsum_mem⟩ hA.norm_smul_one_add_posSemidef
  have hscalar_psd := hT ⟨_, hscalar_mem⟩ (real_smul_one_posSemidef (norm_nonneg _))
  have hA_eq : (⟨nA • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) + (A : _), hsum_mem⟩ :
      ↥(tensorSubmodule S n)) =
      (⟨_, hscalar_mem⟩ : ↥(tensorSubmodule S n)) + A := rfl
  have hsplit : tensorMapIdSub T (⟨_, hsum_mem⟩ : ↥(tensorSubmodule S n)) =
      tensorMapIdSub T (⟨_, hscalar_mem⟩ : ↥(tensorSubmodule S n)) + tensorMapIdSub T A := by
    have hlin := (tensorMapIdSubLM T (S := S) (k := n)).map_add
      (⟨_, hscalar_mem⟩ : ↥(tensorSubmodule S n)) A
    rw [← hA_eq] at hlin
    simpa using hlin
  have hAeq2 : tensorMapIdSub T A = tensorMapIdSub T (⟨_, hsum_mem⟩ : ↥(tensorSubmodule S n)) -
      tensorMapIdSub T (⟨_, hscalar_mem⟩ : ↥(tensorSubmodule S n)) := by
    rw [hsplit]; abel
  rw [hAeq2]
  exact hsum_psd.1.sub hscalar_psd.1

/-- `τ(A)` is real (fixed by complex conjugation) for Hermitian `A ∈ S ⊗ M_n(ℂ)`:
`Ω`-expectation values of a Hermitian operator are real. -/
theorem tau_star_eq {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hT : IsCPAtLevel T n) (A : ↥(tensorSubmodule S n))
    (hA : (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).IsHermitian) :
    star (tau T A) = tau T A := by
  have hherm := tensorMapIdSub_isHermitian hS hT A hA
  have homega := omegaProj_isHermitian n
  rw [tau_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hherm.eq, homega.eq,
    Matrix.trace_mul_comm]

/-- `⟨u|X|u⟩ = tr[vecMulVec u (star u) * X]` for any vector `u` and matrix `X`:
the expectation-value identity used to evaluate `τ` on positive semidefinite
matrices. -/
private theorem trace_vecMulVec_star_mul_eq_dotProduct {ι : Type*} [Fintype ι]
    (u : ι → ℂ) (X : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.vecMulVec u (star u) * X) = star u ⬝ᵥ X.mulVec u := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `τ` is nonnegative on positive semidefinite matrices of `S ⊗ M_n(ℂ)`: this
is complete positivity at level `n` applied directly, since
`τ(X) = ⟨Ω|X|Ω⟩` and `⟨Ω|X|Ω⟩ ≥ 0` for any positive semidefinite `X`. -/
theorem tau_nonneg_of_posSemidef {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} (hT : IsCPAtLevel T n)
    (X : ↥(tensorSubmodule S n)) (hX : (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).PosSemidef) :
    0 ≤ tau T X := by
  have hpsd := hT X hX
  rw [tau_apply, show Matrix.omegaProj n =
      Matrix.vecMulVec (Matrix.omegaVec n) (star (Matrix.omegaVec n)) from rfl,
    trace_vecMulVec_star_mul_eq_dotProduct]
  exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 (Matrix.omegaVec n)

/-- **The norm-domination bound** (Wolf Ch. 1, line 626): for `T` completely
positive on `S` and Hermitian `A ∈ S ⊗ M_n(ℂ)`,

  `τ(A) ≤ ‖A‖∞ · τ(1)`.

Equivalently `τ(1 - A/‖A‖∞) ≥ 0`: since `‖A‖∞ • 1 - A` is positive
semidefinite and `1 ∈ S ⊗ M_n(ℂ)`, complete positivity at level `n` gives
`τ(‖A‖∞ • 1 - A) ≥ 0`, and `τ` is linear. -/
theorem tau_le_norm_mul_tau_one {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hT : IsCPAtLevel T n) (A : ↥(tensorSubmodule S n))
    (hA : (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).IsHermitian) :
    (tau T A).re ≤ ‖(A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)‖ *
      (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re := by
  set nA : ℝ := ‖(A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)‖ with hnA
  have hscalar_mem : nA • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ∈ tensorSubmodule S n :=
    real_smul_one_mem_tensorSubmodule hS nA
  have hsub_mem : nA • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) - (A : _) ∈
      tensorSubmodule S n :=
    (tensorSubmodule S n).sub_mem hscalar_mem A.2
  have hsub_eq : (⟨nA • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) - (A : _), hsub_mem⟩ :
      ↥(tensorSubmodule S n)) =
      (⟨_, hscalar_mem⟩ : ↥(tensorSubmodule S n)) - A := rfl
  have htau_nonneg_c : (0:ℂ) ≤ tau T ⟨_, hsub_mem⟩ :=
    tau_nonneg_of_posSemidef hT ⟨_, hsub_mem⟩ hA.norm_smul_one_sub_posSemidef
  have htau_nonneg : 0 ≤ (tau T ⟨_, hsub_mem⟩).re := (RCLike.nonneg_iff.mp htau_nonneg_c).1
  have hlin : tau T ⟨_, hsub_mem⟩ =
      tau T (⟨_, hscalar_mem⟩ : ↥(tensorSubmodule S n)) - tau T A := by
    rw [hsub_eq, map_sub]
  have hone_eq : (⟨nA • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ), hscalar_mem⟩ :
      ↥(tensorSubmodule S n)) = nA • (⟨1, one_mem_tensorSubmodule hS⟩ : ↥(tensorSubmodule S n)) :=
    rfl
  have hscal : tau T (⟨_, hscalar_mem⟩ : ↥(tensorSubmodule S n)) =
      (nA : ℂ) * tau T ⟨1, one_mem_tensorSubmodule hS⟩ := by
    rw [hone_eq]
    have := (tau T (S := S)).map_smul (nA : ℝ) (⟨1, one_mem_tensorSubmodule hS⟩ :
      ↥(tensorSubmodule S n))
    simpa [Complex.real_smul] using this
  rw [hlin, hscal, Complex.sub_re, Complex.mul_re] at htau_nonneg
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at htau_nonneg
  linarith

/-! ### Hahn–Banach extension of `τ` -/

/-- The `ℝ`-submodule of Hermitian matrices in `S ⊗ M_k(ℂ)`, the domain on
which the Hahn–Banach extension theorem is applied. -/
def hermitianTensorSubmodule (S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)) (k : ℕ) :
    Submodule ℝ (Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) where
  carrier := {X | X.IsHermitian ∧ X ∈ tensorSubmodule S k}
  zero_mem' := ⟨Matrix.isHermitian_zero, (tensorSubmodule S k).zero_mem⟩
  add_mem' hX hY := ⟨hX.1.add hY.1, (tensorSubmodule S k).add_mem hX.2 hY.2⟩
  smul_mem' c X hX := by
    have heq : c • X = (c : ℂ) • X := by ext i j; simp [Complex.real_smul]
    refine ⟨?_, ?_⟩
    · exact hX.1.smul (IsSelfAdjoint.all c)
    · rw [heq]; exact (tensorSubmodule S k).smul_mem (c : ℂ) hX.2

theorem mem_hermitianTensorSubmodule_iff {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)} {k : ℕ}
    {X : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ} :
    X ∈ hermitianTensorSubmodule S k ↔ X.IsHermitian ∧ X ∈ tensorSubmodule S k :=
  Iff.rfl

/-- The real-linear functional `A ↦ τ(A).re` on the Hermitian part of
`S ⊗ M_n(ℂ)`, the partial map that Hahn–Banach extends. -/
noncomputable def tauReLM {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    ↥(hermitianTensorSubmodule S n) →ₗ[ℝ] ℝ where
  toFun A := (tau T ⟨A.1, A.2.2⟩).re
  map_add' A B := by
    change (tau T ⟨(A + B : ↥(hermitianTensorSubmodule S n)).1, _⟩).re = _
    have hval : (⟨(A + B : ↥(hermitianTensorSubmodule S n)).1, (A + B).2.2⟩ :
        ↥(tensorSubmodule S n)) = ⟨A.1, A.2.2⟩ + ⟨B.1, B.2.2⟩ := rfl
    rw [hval, map_add, Complex.add_re]
  map_smul' c A := by
    change (tau T ⟨(c • A : ↥(hermitianTensorSubmodule S n)).1, _⟩).re = _
    have hval : (⟨(c • A : ↥(hermitianTensorSubmodule S n)).1, (c • A).2.2⟩ :
        ↥(tensorSubmodule S n)) = (c : ℂ) • (⟨A.1, A.2.2⟩ : ↥(tensorSubmodule S n)) := by
      apply Subtype.ext
      change c • A.1 = (c : ℂ) • A.1
      ext i j; simp [Complex.real_smul]
    rw [hval, map_smul, smul_eq_mul, Complex.mul_re]
    simp

/-- `τ(1) ≥ 0`: the unit is positive semidefinite. -/
theorem tau_one_nonneg {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} (hT : IsCPAtLevel T n) :
    0 ≤ (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re :=
  (RCLike.nonneg_iff.mp
    (tau_nonneg_of_posSemidef hT ⟨1, one_mem_tensorSubmodule hS⟩ Matrix.PosSemidef.one)).1

/-- The sublinear functional `N(A) = ‖A‖∞ · τ(1)` dominating `τ`. -/
noncomputable def sublinearN {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ → ℝ :=
  fun X => ‖X‖ * (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re

theorem sublinearN_hom {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) (T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hc : 0 < c)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    sublinearN hS T (c • X) = c * sublinearN hS T X := by
  simp only [sublinearN, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_assoc]

theorem sublinearN_add {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} (hT : IsCPAtLevel T n)
    (X Y : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    sublinearN hS T (X + Y) ≤ sublinearN hS T X + sublinearN hS T Y := by
  have hK : 0 ≤ (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re := tau_one_nonneg hS hT
  have hnorm : ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := norm_add_le X Y
  simp only [sublinearN]
  calc ‖X + Y‖ * (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re
      ≤ (‖X‖ + ‖Y‖) * (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re :=
        mul_le_mul_of_nonneg_right hnorm hK
    _ = ‖X‖ * (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re +
          ‖Y‖ * (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re := by rw [add_mul]

/-- **The Hahn–Banach extension of `τ`**: a real-linear functional on the
Hermitian matrices of `M_m(ℂ) ⊗ M_n(ℂ)` agreeing with `τ.re` on `S ⊗ M_n(ℂ)`
and dominated by the same sublinear bound `N`. -/
theorem exists_hahnBanach_extension {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hT : IsCPOnOperatorSystem T) :
    ∃ g : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℝ] ℝ,
      (∀ A : ↥(hermitianTensorSubmodule S n), g A = tauReLM T A) ∧
      (∀ X, g X ≤ sublinearN hS T X) := by
  have hf : ∀ A : (⟨hermitianTensorSubmodule S n, tauReLM T⟩ :
      Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ.[ℝ] ℝ).domain,
      (⟨hermitianTensorSubmodule S n, tauReLM T⟩ :
        Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ.[ℝ] ℝ) A ≤ sublinearN hS T A := by
    rintro ⟨A, hA1, hA2⟩
    exact tau_le_norm_mul_tau_one hS (hT n) ⟨A, hA2⟩ hA1
  obtain ⟨g, hg_agree, hg_le⟩ := exists_extension_of_le_sublinear
    (f := (⟨hermitianTensorSubmodule S n, tauReLM T⟩ :
      Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ.[ℝ] ℝ))
    (N := sublinearN hS T) (sublinearN_hom hS T) (sublinearN_add hS (hT n)) hf
  refine ⟨g, fun A => ?_, hg_le⟩
  have h := hg_agree A
  rwa [LinearPMap.mk_apply] at h

/-! ### Complexifying the Hahn–Banach extension -/

section Complexify

variable {ι : Type*}

/-- The Hermitian part of `X`, scaled so that `X = hermPart1 X + I • hermPart2 X`. -/
private noncomputable def hermPart1 (X : Matrix ι ι ℂ) : Matrix ι ι ℂ := (2⁻¹ : ℂ) • (X + Xᴴ)

/-- The Hermitian matrix `H` with `I • H` equal to the skew-Hermitian part of `X`. -/
private noncomputable def hermPart2 (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (-Complex.I / 2) • (X - Xᴴ)

private theorem star_half : star (2⁻¹ : ℂ) = 2⁻¹ := by simp

private theorem star_negI_div_two : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by
  simp

private theorem star_I : star (Complex.I : ℂ) = -Complex.I := by
  rw [Complex.star_def, Complex.conj_I]

/-- The normal form for `star` of the scalar expressions appearing in
`hermPart1`, `hermPart2`: push `star` onto matrix entries and simplify the
fixed scalars `2⁻¹`, `-I/2`, `I`. -/
private theorem herm_entry_eq (z w : ℂ) :
    (2⁻¹ : ℂ) * (z + star w) = star ((2⁻¹ : ℂ) * (w + star z)) ∧
    (-Complex.I / 2) * (z - star w) = star ((-Complex.I / 2) * (w - star z)) := by
  constructor
  · rw [star_mul', star_add, star_star, star_half]; ring
  · rw [star_mul', star_sub, star_star, star_negI_div_two]; ring

private theorem hermPart1_isHermitian (X : Matrix ι ι ℂ) : (hermPart1 X).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, hermPart1, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  exact (herm_entry_eq (X i j) (X j i)).1.symm

private theorem hermPart2_isHermitian (X : Matrix ι ι ℂ) : (hermPart2 X).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, hermPart2, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]
  exact (herm_entry_eq (X i j) (X j i)).2.symm

private theorem decomp_entry_eq (z w : ℂ) :
    (2⁻¹ : ℂ) * (z + star w) + Complex.I * ((-Complex.I / 2) * (z - star w)) = z := by
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (star w - z) / 2 * hI2

private theorem hermPart1_add_I_smul_hermPart2 (X : Matrix ι ι ℂ) :
    hermPart1 X + Complex.I • hermPart2 X = X := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, hermPart1, hermPart2,
    Matrix.conjTranspose_apply, smul_eq_mul]
  exact decomp_entry_eq (X i j) (X j i)

private theorem hermPart1_add (X Y : Matrix ι ι ℂ) :
    hermPart1 (X + Y) = hermPart1 X + hermPart1 Y := by
  ext i j
  simp only [hermPart1, Matrix.add_apply, Matrix.smul_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, star_add]
  ring

private theorem hermPart2_add (X Y : Matrix ι ι ℂ) :
    hermPart2 (X + Y) = hermPart2 X + hermPart2 Y := by
  ext i j
  simp only [hermPart2, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, star_add]
  ring

private theorem hermPart1_smul_real (c : ℝ) (X : Matrix ι ι ℂ) :
    hermPart1 ((c : ℂ) • X) = (c : ℂ) • hermPart1 X := by
  ext i j
  simp only [hermPart1, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, Complex.star_def, map_mul, Complex.conj_ofReal]
  ring

private theorem hermPart2_smul_real (c : ℝ) (X : Matrix ι ι ℂ) :
    hermPart2 ((c : ℂ) • X) = (c : ℂ) • hermPart2 X := by
  ext i j
  simp only [hermPart2, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, Complex.star_def, map_mul, Complex.conj_ofReal]
  ring

private theorem hermPart1_smul_I (X : Matrix ι ι ℂ) :
    hermPart1 (Complex.I • X) = -hermPart2 X := by
  ext i j
  simp only [hermPart1, hermPart2, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.neg_apply, Matrix.conjTranspose_apply, smul_eq_mul, star_mul', star_I]
  ring

private theorem hermPart2_smul_I (X : Matrix ι ι ℂ) :
    hermPart2 (Complex.I • X) = hermPart1 X := by
  ext i j
  simp only [hermPart1, hermPart2, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, star_mul', star_I]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(X i j) - star (X j i)) / 2 * hI2

/-- **Complexification via Hermitian decomposition**: extend a real-linear
functional `g` on the whole matrix space to a `ℂ`-linear functional, using
`g` on the (always Hermitian) matrices `hermPart1 X`, `hermPart2 X` with
`X = hermPart1 X + I • hermPart2 X`. Unlike the generic
`Module.Dual.extendRCLike`, this construction keeps the extension real on
every Hermitian matrix, which is essential to matching `τ` on `S ⊗ M_n(ℂ)`. -/
private theorem g_smul_real (g : Matrix ι ι ℂ →ₗ[ℝ] ℝ) (r : ℝ) (M : Matrix ι ι ℂ) :
    g ((r : ℂ) • M) = r * g M := by
  have heq : (r : ℂ) • M = r • M := by ext i j; simp [Complex.real_smul]
  rw [heq, g.map_smul r M, smul_eq_mul]

noncomputable def complexify (g : Matrix ι ι ℂ →ₗ[ℝ] ℝ) : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun X := (g (hermPart1 X) : ℂ) + Complex.I * (g (hermPart2 X) : ℂ)
  map_add' X Y := by
    simp only [hermPart1_add, hermPart2_add, map_add, Complex.ofReal_add]
    ring
  map_smul' c X := by
    simp only [RingHom.id_apply]
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨c.re, c.im, by simp⟩
    have hexpand : ((a : ℂ) + (b : ℂ) * Complex.I) • X = (a : ℂ) • X + (b : ℂ) • Complex.I • X :=
      by rw [add_smul, smul_smul, mul_comm]
    rw [hexpand, hermPart1_add, hermPart2_add, hermPart1_smul_real, hermPart2_smul_real,
      show (b : ℂ) • Complex.I • X = Complex.I • ((b : ℂ) • X) from by
        rw [smul_smul, smul_smul, mul_comm],
      hermPart1_smul_I, hermPart2_smul_I, hermPart1_smul_real, hermPart2_smul_real]
    simp only [map_add, map_neg, g_smul_real, Complex.ofReal_add, Complex.ofReal_neg,
      Complex.ofReal_mul]
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-(b : ℂ)) * (g (hermPart2 X) : ℂ) * hI2

theorem complexify_apply (g : Matrix ι ι ℂ →ₗ[ℝ] ℝ) (X : Matrix ι ι ℂ) :
    complexify g X = (g (hermPart1 X) : ℂ) + Complex.I * (g (hermPart2 X) : ℂ) := rfl

/-- `complexify g` reproduces `g` on Hermitian matrices. -/
theorem complexify_apply_of_isHermitian (g : Matrix ι ι ℂ →ₗ[ℝ] ℝ) {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) : complexify g H = (g H : ℂ) := by
  rw [complexify_apply]
  have h1 : hermPart1 H = H := by
    unfold hermPart1; rw [hH.eq]; rw [← two_smul ℂ H, smul_smul]; norm_num
  have h2 : hermPart2 H = 0 := by
    unfold hermPart2; rw [hH.eq, sub_self, smul_zero]
  rw [h1, h2, map_zero]
  simp

/-- `complexify g` is Hermiticity-preserving-to-conjugate: `complexify g Xᴴ =
star (complexify g X)` for every `X`, not only Hermitian `X`. -/
theorem complexify_conjTranspose (g : Matrix ι ι ℂ →ₗ[ℝ] ℝ) (X : Matrix ι ι ℂ) :
    complexify g Xᴴ = star (complexify g X) := by
  have hH1 : hermPart1 Xᴴ = hermPart1 X := by
    unfold hermPart1
    rw [Matrix.conjTranspose_conjTranspose, add_comm]
  have hH2 : hermPart2 Xᴴ = -hermPart2 X := by
    unfold hermPart2
    rw [Matrix.conjTranspose_conjTranspose,
      show Xᴴ - X = -(X - Xᴴ) from by abel, smul_neg]
  rw [complexify_apply, complexify_apply, hH1, hH2, map_neg]
  rw [star_add, star_mul', star_I]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

end Complexify

/-! ### The complex-linear extension of `τ` -/

theorem hermPart1_mem_tensorSubmodule {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : A ∈ tensorSubmodule S n) : hermPart1 A ∈ tensorSubmodule S n :=
  (tensorSubmodule S n).smul_mem _
    ((tensorSubmodule S n).add_mem hA (hS.conjTranspose_mem_tensorSubmodule hA))

theorem hermPart2_mem_tensorSubmodule {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : A ∈ tensorSubmodule S n) : hermPart2 A ∈ tensorSubmodule S n :=
  (tensorSubmodule S n).smul_mem _
    ((tensorSubmodule S n).sub_mem hA (hS.conjTranspose_mem_tensorSubmodule hA))

/-- A complex number fixed by conjugation is (the cast of) its own real part. -/
private theorem eq_ofReal_re_of_star_eq {z : ℂ} (h : star z = z) : z = (z.re : ℂ) := by
  have him : z.im = 0 := by
    have hc := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at hc
    linarith
  exact Complex.ext rfl (by simp [him])

/-- **The complex-linear extension of `τ`** (Wolf Ch. 1, lines 626–627): for
`T` completely positive on the operator system `S`, `τ` extends to a full
`ℂ`-linear functional `τ'` on `M_m(ℂ) ⊗ M_n(ℂ)` that agrees with `τ` on
`S ⊗ M_n(ℂ)` and satisfies the same norm-domination bound on all of
`M_m(ℂ) ⊗ M_n(ℂ)`. -/
theorem exists_tau_extension {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    (hS : IsOperatorSystem S) {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (hT : IsCPOnOperatorSystem T) :
    ∃ g : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℝ] ℝ,
      (∀ A : ↥(tensorSubmodule S n), complexify g A = tau T A) ∧
      ∀ X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ, X.IsHermitian →
        (complexify g X).re ≤ ‖X‖ *
          (complexify g (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)).re := by
  obtain ⟨g, hg_agree, hg_le⟩ := exists_hahnBanach_extension hS hT
  have hone_herm : (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ∈
      hermitianTensorSubmodule S n :=
    ⟨Matrix.isHermitian_one, one_mem_tensorSubmodule hS⟩
  refine ⟨g, ?_, ?_⟩
  · intro A
    obtain ⟨A, hA⟩ := A
    have hAH := hS.conjTranspose_mem_tensorSubmodule hA
    have h1mem : hermPart1 A ∈ tensorSubmodule S n := hermPart1_mem_tensorSubmodule hS hA
    have h2mem : hermPart2 A ∈ tensorSubmodule S n := hermPart2_mem_tensorSubmodule hS hA
    have h1herm := hermPart1_isHermitian A
    have h2herm := hermPart2_isHermitian A
    have hg1 : (g (hermPart1 A) : ℝ) = (tau T ⟨hermPart1 A, h1mem⟩).re :=
      hg_agree ⟨hermPart1 A, h1herm, h1mem⟩
    have hg2 : (g (hermPart2 A) : ℝ) = (tau T ⟨hermPart2 A, h2mem⟩).re :=
      hg_agree ⟨hermPart2 A, h2herm, h2mem⟩
    have htau1 : (tau T ⟨hermPart1 A, h1mem⟩ : ℂ) = ((tau T ⟨hermPart1 A, h1mem⟩).re : ℂ) :=
      eq_ofReal_re_of_star_eq (tau_star_eq hS (hT n) ⟨hermPart1 A, h1mem⟩ h1herm)
    have htau2 : (tau T ⟨hermPart2 A, h2mem⟩ : ℂ) = ((tau T ⟨hermPart2 A, h2mem⟩).re : ℂ) :=
      eq_ofReal_re_of_star_eq (tau_star_eq hS (hT n) ⟨hermPart2 A, h2mem⟩ h2herm)
    change complexify g A = tau T ⟨A, hA⟩
    rw [complexify_apply, hg1, hg2, ← htau1, ← htau2,
      show (⟨A, hA⟩ : ↥(tensorSubmodule S n)) =
          ⟨hermPart1 A, h1mem⟩ + Complex.I • (⟨hermPart2 A, h2mem⟩ : ↥(tensorSubmodule S n))
        from Subtype.ext (hermPart1_add_I_smul_hermPart2 A).symm,
      map_add, map_smul, smul_eq_mul]
  · intro X hX
    have h1 : complexify g X = (g X : ℂ) := complexify_apply_of_isHermitian g hX
    have h1one : complexify g (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = (g 1 : ℂ) :=
      complexify_apply_of_isHermitian g Matrix.isHermitian_one
    rw [h1, h1one, Complex.ofReal_re, Complex.ofReal_re]
    have hg1 : g (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) =
        (tau T ⟨1, one_mem_tensorSubmodule hS⟩).re := hg_agree ⟨1, hone_herm⟩
    rw [hg1]
    exact hg_le X

/-! ### Riesz representation of `τ'` -/

/-- The matrix representing `τ'` via the trace pairing: `τ'(X) = tr[Y X]`
(`trace_rieszMatrix_mul`). -/
noncomputable def rieszMatrix (tau' : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ] ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  fun a b => tau' (Matrix.single b a 1)

theorem trace_rieszMatrix_mul [NeZero m] [NeZero n]
    (tau' : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ] ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix.trace (rieszMatrix tau' * X) = tau' X := by
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  refine Matrix.induction_on X ?_ ?_
  · intro p q hp hq
    rw [Matrix.mul_add, Matrix.trace_add, hp, hq, map_add]
  · intro i j z
    rw [Matrix.trace_mul_single]
    change MulOpposite.op z • rieszMatrix tau' j i = tau' (Matrix.single i j z)
    simp only [rieszMatrix, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rw [show (Matrix.single i j z : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) =
        z • Matrix.single i j 1 from by rw [Matrix.smul_single, smul_eq_mul, mul_one],
      map_smul, smul_eq_mul, mul_comm]

/-- `rieszMatrix (complexify g)` is positive semidefinite: it is Hermitian
(`complexify_conjTranspose`) and the quadratic form `star v ⬝ᵥ (Y *ᵥ v)`
equals `complexify g (vecMulVec v (star v))`, which is nonnegative because
`vecMulVec v (star v)` is positive semidefinite. -/
theorem rieszMatrix_complexify_posSemidef [NeZero m] [NeZero n]
    (g : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℝ] ℝ)
    (hNonneg : ∀ X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      X.PosSemidef → 0 ≤ (complexify g X).re) :
    (rieszMatrix (complexify g)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hHerm : ∀ X, complexify g Xᴴ = star (complexify g X) := complexify_conjTranspose g
  refine ⟨?_, ?_⟩
  · ext a b
    rw [Matrix.conjTranspose_apply]
    change star (complexify g (Matrix.single a b 1)) = complexify g (Matrix.single b a 1)
    rw [← hHerm, Matrix.conjTranspose_single, star_one]
  · intro v
    have hvv : (Matrix.vecMulVec v (star v)).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star v
    have key : star v ⬝ᵥ (rieszMatrix (complexify g)).mulVec v =
        complexify g (Matrix.vecMulVec v (star v)) := by
      rw [← trace_vecMulVec_star_mul_eq_dotProduct, Matrix.trace_mul_comm,
        trace_rieszMatrix_mul]
    rw [key]
    have hre : 0 ≤ (complexify g (Matrix.vecMulVec v (star v))).re := hNonneg _ hvv
    have him0 : star (complexify g (Matrix.vecMulVec v (star v))) =
        complexify g (Matrix.vecMulVec v (star v)) := by
      conv_rhs => rw [← hvv.1]
      exact (hHerm _).symm
    rw [eq_ofReal_re_of_star_eq him0]
    exact_mod_cast hre

/-! ### Reconstructing the extended map -/

/-- The linear map recovered from `τ'` by Wolf's own inversion formula (Ch. 1,
line 623, run backwards): `T'(B) i j = n · τ'(B ⊗ |i⟩⟨j|)`. -/
noncomputable def reconstructedMap (tau' : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ] ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun B i j := (n : ℂ) * tau' (kroneckerMap (· * ·) B (Matrix.single i j 1))
  map_add' X Y := by
    ext i j
    rw [Matrix.add_apply, kroneckerMap_add_left (· * ·) (fun a₁ a₂ b => add_mul a₁ a₂ b) X Y,
      map_add, mul_add]
  map_smul' c X := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
      kroneckerMap_smul_left (· * ·) c (fun a b => smul_mul_assoc c a b) X, map_smul, smul_eq_mul]
    ring

theorem reconstructedMap_apply (tau' : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ] ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) (i j : Fin n) :
    reconstructedMap tau' B i j = (n : ℂ) * tau' (kroneckerMap (· * ·) B (Matrix.single i j 1)) :=
  rfl

/-- The rectangular Kraus family reconstructed from a rank-one decomposition
`Y = Σₖ vₖ vₖ†` of the Riesz matrix: `Kₖ i p := √n · star(vₖ(p, i))`
(Wolf Eq. (1.13)-style reshaping, as in `ChoiRectangular.krausOfChoiDecomp`). -/
noncomputable def reconstructedKraus {ι : Type*}
    (v : ι → (Fin m × Fin n) → ℂ) : ι → Matrix (Fin n) (Fin m) ℂ :=
  fun k i p => ((n : ℝ).sqrt : ℂ) * star (v k (p, i))

/-- **`reconstructedMap tau'` is the Kraus map built from a rank-one
decomposition of the Riesz matrix**: both sides expand to the same double
sum `n · Σₖ Σ_{p,q} star(vₖ(p,i)) · B p q · vₖ(q,j)`, obtained on the left
from the trace-pairing identity `trace_vecMulVec_star_mul_eq_dotProduct` and
on the right by unfolding the Kraus sum. -/
theorem reconstructedMap_eq_kraus_sum [NeZero m] [NeZero n]
    {tau' : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ] ℂ}
    {ι : Type*} [Fintype ι] {v : ι → (Fin m × Fin n) → ℂ}
    (hY : rieszMatrix tau' = ∑ k, Matrix.vecMulVec (v k) (star (v k)))
    (B : Matrix (Fin m) (Fin m) ℂ) :
    reconstructedMap tau' B =
      ∑ k, reconstructedKraus v k * B * (reconstructedKraus v k)ᴴ := by
  ext i0 j0
  have hsum_apply : (∑ k : ι, reconstructedKraus v k * B * (reconstructedKraus v k)ᴴ) i0 j0 =
      ∑ k : ι, (reconstructedKraus v k * B * (reconstructedKraus v k)ᴴ) i0 j0 :=
    Matrix.sum_apply i0 j0 _ _
  rw [hsum_apply]
  have hsqrt : ((n : ℝ).sqrt : ℂ) * ((n : ℝ).sqrt : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    norm_cast
  have hentry : ∀ k : ι, (reconstructedKraus v k * B * (reconstructedKraus v k)ᴴ) i0 j0 =
      (n : ℂ) * ∑ p : Fin m, ∑ q : Fin m, star (v k (p, i0)) * B p q * v k (q, j0) := by
    intro k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, reconstructedKraus]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    have hstar : star (((n : ℝ).sqrt : ℂ) * star (v k (p, j0))) =
        ((n : ℝ).sqrt : ℂ) * v k (p, j0) := by
      rw [star_mul', star_star]
      congr 1
      simp
    rw [hstar]
    calc ((n : ℝ).sqrt : ℂ) * star (v k (q, i0)) * B q p *
          (((n : ℝ).sqrt : ℂ) * v k (p, j0))
        = (((n : ℝ).sqrt : ℂ) * ((n : ℝ).sqrt : ℂ)) *
            (star (v k (q, i0)) * B q p * v k (p, j0)) := by ring
      _ = (n : ℂ) * (star (v k (q, i0)) * B q p * v k (p, j0)) := by rw [hsqrt]
  simp only [hentry, ← Finset.mul_sum]
  rw [reconstructedMap_apply, ← trace_rieszMatrix_mul, hY, Finset.sum_mul, Matrix.trace_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  set u := v k with hu
  have hlhs : Matrix.trace (Matrix.vecMulVec u (star u) *
      kroneckerMap (· * ·) B (Matrix.single i0 j0 1)) =
      ∑ p2 : Fin m × Fin n, ∑ q2 : Fin m × Fin n,
        u p2 * star (u q2) *
          (kroneckerMap (· * ·) B (Matrix.single i0 j0 1) q2 p2) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply]
  rw [hlhs]
  have hM : ∀ q2 p2 : Fin m × Fin n,
      kroneckerMap (· * ·) B (Matrix.single i0 j0 1) q2 p2 =
        B q2.1 p2.1 * (if p2.2 = j0 then (1 : ℂ) else 0) * (if q2.2 = i0 then (1 : ℂ) else 0) := by
    intro q2 p2
    rw [Matrix.kroneckerMap_apply, Matrix.single_apply]
    split_ifs with h1 h2 h3 h4 h5 h6 <;> first | rfl | (exfalso; tauto) | ring
  simp only [hM]
  have hstep1 : ∀ p2 : Fin m × Fin n, (∑ q2 : Fin m × Fin n,
      u p2 * star (u q2) * (B q2.1 p2.1 * (if p2.2 = j0 then (1 : ℂ) else 0) *
        (if q2.2 = i0 then (1 : ℂ) else 0))) =
      ∑ q1 : Fin m, u p2 * star (u (q1, i0)) *
        (B q1 p2.1 * (if p2.2 = j0 then (1 : ℂ) else 0)) := by
    intro p2
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q1 _ => ?_
    dsimp only
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h; exact absurd (Finset.mem_univ i0) h
  simp only [hstep1]
  rw [Fintype.sum_prod_type]
  dsimp only
  have hstep2 : ∀ p1 : Fin m, (∑ p2b : Fin n, ∑ q1 : Fin m,
      u (p1, p2b) * star (u (q1, i0)) * (B q1 p1 * (if p2b = j0 then (1 : ℂ) else 0))) =
      ∑ q1 : Fin m, u (p1, j0) * star (u (q1, i0)) * B q1 p1 := by
    intro p1
    rw [Finset.sum_eq_single j0]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun q1 _ => ?_
      simp [hb]
    · intro h; exact absurd (Finset.mem_univ j0) h
  rw [Finset.sum_congr rfl (fun (p1 : Fin m) _ => hstep2 p1), Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-! ### `reconstructedMap tau'` agrees with `T` on `S` -/

/-- The bipartite slices of `B ⊗ |i⟩⟨j|` are scalar multiples of `B`. -/
private theorem bipartiteSlice_kron_single (B : Matrix (Fin m) (Fin m) ℂ) (i0 j0 i j : Fin n) :
    Matrix.bipartiteSlice (kroneckerMap (· * ·) B (Matrix.single i0 j0 (1 : ℂ))) i j =
      (Matrix.single i0 j0 (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) i j • B := by
  ext a b
  simp only [Matrix.bipartiteSlice, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem kron_single_mem_tensorSubmodule {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    {B : Matrix (Fin m) (Fin m) ℂ} (hB : B ∈ S) (i0 j0 : Fin n) :
    kroneckerMap (· * ·) B (Matrix.single i0 j0 (1 : ℂ)) ∈ tensorSubmodule S n := by
  intro i j
  rw [bipartiteSlice_kron_single, Matrix.single_apply]
  split_ifs with h
  · simpa using hB
  · simp [S.zero_mem]

/-- The entries of `tensorMapIdSub T` on `B ⊗ |i⟩⟨j|` are scalar multiples of
`T(B)`, via `T`'s linearity applied to `bipartiteSlice_kron_single`. -/
private theorem tensorMapIdSub_kron_single {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ} (hB : B ∈ S)
    (i0 j0 q1 q2 p1 p2 : Fin n) :
    tensorMapIdSub T ⟨kroneckerMap (· * ·) B (Matrix.single i0 j0 (1 : ℂ)),
        kron_single_mem_tensorSubmodule hB i0 j0⟩ (q1, q2) (p1, p2) =
      (if q2 = i0 ∧ p2 = j0 then (1 : ℂ) else 0) * T ⟨B, hB⟩ q1 p1 := by
  rw [tensorMapIdSub_apply]
  have hval : (⟨Matrix.bipartiteSlice (kroneckerMap (· * ·) B (Matrix.single i0 j0 (1 : ℂ))) q2 p2,
      mem_tensorSubmodule_iff.mp (kron_single_mem_tensorSubmodule hB i0 j0) q2 p2⟩ : ↥S) =
      ((Matrix.single i0 j0 (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) q2 p2) • (⟨B, hB⟩ : ↥S) := by
    apply Subtype.ext
    exact bipartiteSlice_kron_single B i0 j0 q2 p2
  rw [hval, map_smul]
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hi : q2 = i0 <;> by_cases hj : p2 = j0
  · subst hi; subst hj; simp
  · subst hi; simp [hj, Ne.symm hj]
  · subst hj; simp [hi, Ne.symm hi]
  · simp [hi, hj, Ne.symm hi, Ne.symm hj]

/-- **Wolf's inversion formula on `S`** (Ch. 1, line 623): for `B ∈ S`,
`τ(B ⊗ |i⟩⟨j|) = (1/n) · T(B) i j`, matching `tau_apply`'s definition. -/
theorem tau_kron_single {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)}
    {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ} (hB : B ∈ S)
    (i0 j0 : Fin n) :
    tau T ⟨kroneckerMap (· * ·) B (Matrix.single i0 j0 (1 : ℂ)),
        kron_single_mem_tensorSubmodule hB i0 j0⟩ =
      (1 / (n : ℂ)) * T ⟨B, hB⟩ i0 j0 := by
  rw [tau_apply]
  have hentry : Matrix.trace (Matrix.omegaProj n * tensorMapIdSub T
      ⟨kroneckerMap (· * ·) B (Matrix.single i0 j0 (1 : ℂ)),
        kron_single_mem_tensorSubmodule hB i0 j0⟩) =
      ∑ p2a : Fin n, ∑ p2b : Fin n, ∑ q2a : Fin n, ∑ q2b : Fin n,
        Matrix.omegaProj n (p2a, p2b) (q2a, q2b) * tensorMapIdSub T
          ⟨kroneckerMap (· * ·) B (Matrix.single i0 j0 (1 : ℂ)),
            kron_single_mem_tensorSubmodule hB i0 j0⟩ (q2a, q2b) (p2a, p2b) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [hentry]
  have hc : ((1 : ℂ) / ((n : ℝ).sqrt : ℂ)) * (1 / ((n : ℝ).sqrt : ℂ)) = 1 / (n : ℂ) := by
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    norm_num
  have hterm : ∀ p2a p2b q2a q2b : Fin n,
      Matrix.omegaProj n (p2a, p2b) (q2a, q2b) * tensorMapIdSub T
          ⟨kroneckerMap (· * ·) B (Matrix.single i0 j0 (1 : ℂ)),
            kron_single_mem_tensorSubmodule hB i0 j0⟩ (q2a, q2b) (p2a, p2b) =
        (if p2a = p2b then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
          ((if q2a = q2b then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
            ((if q2b = i0 ∧ p2b = j0 then (1 : ℂ) else 0) * T ⟨B, hB⟩ q2a p2a)) := by
    intro p2a p2b q2a q2b
    rw [tensorMapIdSub_kron_single hB,
      show Matrix.omegaProj n (p2a, p2b) (q2a, q2b) =
        Matrix.omegaVec n (p2a, p2b) * star (Matrix.omegaVec n (q2a, q2b)) from rfl,
      Matrix.omegaVec_apply, Matrix.omegaVec_apply]
    by_cases hp : p2a = p2b <;> by_cases hq : q2a = q2b <;>
      simp [hp, hq, mul_assoc]
  simp only [hterm]
  -- Collapse the innermost sum (q2b) to i0: the summand vanishes unless q2b = i0.
  have hq2b : ∀ p2a p2b q2a : Fin n, (∑ q2b : Fin n,
      (if p2a = p2b then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
        ((if q2a = q2b then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
          ((if q2b = i0 ∧ p2b = j0 then (1 : ℂ) else 0) * T ⟨B, hB⟩ q2a p2a))) =
      (if p2a = p2b then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
        ((if q2a = i0 then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
          ((if p2b = j0 then (1 : ℂ) else 0) * T ⟨B, hB⟩ q2a p2a)) := by
    intro p2a p2b q2a
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb
      have : ¬(b = i0 ∧ p2b = j0) := fun h => hb h.1
      simp [this]
    · intro h; exact absurd (Finset.mem_univ i0) h
  simp only [hq2b]
  -- Collapse q2a to i0.
  have hq2a : ∀ p2a p2b : Fin n, (∑ q2a : Fin n,
      (if p2a = p2b then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
        ((if q2a = i0 then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
          ((if p2b = j0 then (1 : ℂ) else 0) * T ⟨B, hB⟩ q2a p2a))) =
      (if p2a = p2b then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
        ((1 / ((n : ℝ).sqrt : ℂ)) * ((if p2b = j0 then (1 : ℂ) else 0) * T ⟨B, hB⟩ i0 p2a)) := by
    intro p2a p2b
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i0) h
  simp only [hq2a]
  -- Collapse p2b to j0.
  have hp2b : ∀ p2a : Fin n, (∑ p2b : Fin n,
      (if p2a = p2b then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
        ((1 / ((n : ℝ).sqrt : ℂ)) * ((if p2b = j0 then (1 : ℂ) else 0) * T ⟨B, hB⟩ i0 p2a))) =
      (if p2a = j0 then (1 / ((n : ℝ).sqrt : ℂ)) else 0) *
        ((1 / ((n : ℝ).sqrt : ℂ)) * T ⟨B, hB⟩ i0 p2a) := by
    intro p2a
    rw [Finset.sum_eq_single j0]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h; exact absurd (Finset.mem_univ j0) h
  simp only [hp2b]
  -- Collapse p2a to j0.
  rw [Finset.sum_eq_single j0]
  · simp only [if_true]
    rw [← mul_assoc, hc]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ j0) h

/-! ### The extension theorem -/

/-- **Extending cp maps from operator systems** (Wolf Ch. 1, lines 616–626): a
completely positive linear map `T : S → M_n(ℂ)` defined on an operator system
`S ⊆ M_m(ℂ)` extends to a completely positive map `T' : M_m(ℂ) → M_n(ℂ)`
agreeing with `T` on `S`.

The dimension hypotheses `[NeZero m] [NeZero n]` are the same standing
finite-dimensionality convention already used for the rectangular
Choi–Jamiolkowski reconstruction (`ChoiJamiolkowski.exists_cpMap_of_choi_posSemidef`,
`ChoiRectangular.exists_isKrausCP_of_posSemidef`): a `0`-dimensional matrix
algebra is a degenerate case outside the scope of a finite-dimensional
`C^*`-algebra as Wolf uses the term, and `Matrix.induction_on` (used to build
`rieszMatrix`/`reconstructedMap`) itself requires the index types to be
nonempty. -/
theorem exists_cp_extension_of_operatorSystem [NeZero m] [NeZero n]
    {S : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ)} (hS : IsOperatorSystem S)
    {T : ↥S →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} (hT : IsCPOnOperatorSystem T) :
    ∃ T' : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      IsKrausCP T' ∧ ∀ x : ↥S, T' x = T x := by
  obtain ⟨g, hg_agree, hg_le⟩ := exists_tau_extension hS hT
  have hone_herm : (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ∈
      hermitianTensorSubmodule S n :=
    ⟨Matrix.isHermitian_one, one_mem_tensorSubmodule hS⟩
  have hK : 0 ≤ (complexify g (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)).re := by
    rw [hg_agree ⟨1, one_mem_tensorSubmodule hS⟩]
    exact tau_one_nonneg hS (hT n)
  have hNonneg : ∀ X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      X.PosSemidef → 0 ≤ (complexify g X).re :=
    fun X hX => tau'_nonneg_of_posSemidef hg_le hK hX
  obtain ⟨r, v, hv⟩ :=
    Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (rieszMatrix_complexify_posSemidef g hNonneg)
  refine ⟨reconstructedMap (complexify g),
    ⟨r, reconstructedKraus v, reconstructedMap_eq_kraus_sum hv⟩, ?_⟩
  rintro ⟨B, hB⟩
  ext i0 j0
  rw [reconstructedMap_apply, hg_agree ⟨_, kron_single_mem_tensorSubmodule hB i0 j0⟩,
    tau_kron_single hB]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

end Matrix
