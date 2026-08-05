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
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 622–640): a
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

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

variable {m n : ℕ}

/-- A `CStarAlgebra` instance for a matrix algebra using the `ℓ²`-operator
norm, matching the pattern used elsewhere in `TNLean.Channel.Schwarz`. -/
noncomputable local instance matrixCStarAlgebra (ι : Type*) [Fintype ι] [DecidableEq ι] :
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
  letI : CStarAlgebra (Matrix ι ι ℂ) := matrixCStarAlgebra ι
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

end Matrix
