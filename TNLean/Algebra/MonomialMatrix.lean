/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Monomial matrices

A monomial matrix is a permutation matrix whose single nonzero entry in each
column is an arbitrary scalar. The matrix `Matrix.monomial σ φ` sends the basis
vector at `s` to `φ s` times the basis vector at `σ s`:

`(monomial σ φ) t s = if t = σ s then φ s else 0`.

Such matrices describe operators of the form
$T\ket{s}=\varphi(s)\ket{\sigma(s)}$; a vector `v` is fixed by `T` exactly
when `v (σ s) = φ s * v s` for every `s`. Products, adjoints, reindexings, and
scalar multiples of monomial matrices are again monomial, and a monomial
matrix with unimodular phases is unitary.
-/

namespace Matrix

variable {ι κ R : Type*} [DecidableEq ι]

/-- The monomial matrix with permutation `σ` and column phases `φ`: the entry in
row `σ s` and column `s` is `φ s`, and every other entry vanishes. -/
def monomial [Zero R] (σ : Equiv.Perm ι) (φ : ι → R) : Matrix ι ι R :=
  Matrix.of fun t s ↦ if t = σ s then φ s else 0

theorem monomial_apply [Zero R] (σ : Equiv.Perm ι) (φ : ι → R) (t s : ι) :
    monomial σ φ t s = if t = σ s then φ s else 0 :=
  rfl

@[simp]
theorem monomial_apply_perm [Zero R] (σ : Equiv.Perm ι) (φ : ι → R) (s : ι) :
    monomial σ φ (σ s) s = φ s := by
  simp [monomial_apply]

theorem monomial_apply_of_ne [Zero R] (σ : Equiv.Perm ι) (φ : ι → R) {t s : ι}
    (h : t ≠ σ s) :
    monomial σ φ t s = 0 := by
  simp [monomial_apply, h]

/-- Scalar multiples of monomial matrices are monomial. -/
theorem smul_monomial [MulZeroClass R] (σ : Equiv.Perm ι) (φ : ι → R) (c : R) :
    c • monomial σ φ = monomial σ (c • φ) := by
  ext t s
  by_cases h : t = σ s <;> simp [monomial_apply, h]

/-- The identity is the monomial matrix of the identity permutation with all
phases equal to one. -/
theorem monomial_one [MulZeroOneClass R] :
    monomial (1 : Equiv.Perm ι) (fun _ ↦ (1 : R)) = 1 := by
  ext t s
  by_cases h : t = s <;> simp [monomial_apply, one_apply, h]

/-- The adjoint of a monomial matrix is monomial for the inverse permutation, with
conjugated phases. -/
theorem conjTranspose_monomial [AddMonoid R] [StarAddMonoid R] (σ : Equiv.Perm ι)
    (φ : ι → R) :
    (monomial σ φ)ᴴ = monomial σ.symm fun t ↦ star (φ (σ.symm t)) := by
  ext s t
  simp only [conjTranspose_apply, monomial_apply]
  by_cases h : t = σ s
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right, star_zero]
    intro h'
    exact h (by rw [h', Equiv.apply_symm_apply])

/-- Simultaneous reindexing of a monomial matrix is monomial for the conjugated
permutation. -/
theorem reindex_monomial [Zero R] [DecidableEq κ] (e : ι ≃ κ) (σ : Equiv.Perm ι)
    (φ : ι → R) :
    reindex e e (monomial σ φ) =
      monomial (e.symm.trans (σ.trans e)) (φ ∘ e.symm) := by
  ext t s
  by_cases h : t = e (σ (e.symm s)) <;>
    simp [reindex_apply, monomial_apply, Equiv.symm_apply_eq, h]

variable [Fintype ι]

/-- A monomial matrix acts on a vector by permuting coordinates and multiplying by
the phases. -/
theorem monomial_mulVec [NonAssocSemiring R] (σ : Equiv.Perm ι) (φ : ι → R)
    (v : ι → R) :
    monomial σ φ *ᵥ v = fun t ↦ φ (σ.symm t) * v (σ.symm t) := by
  funext t
  simp only [mulVec, dotProduct, monomial_apply]
  rw [Finset.sum_eq_single (σ.symm t)]
  · simp
  · intro s _ hs
    rw [ite_eq_right, zero_mul]
    intro h
    exact hs (by rw [h, Equiv.symm_apply_apply])
  · simp

/-- A monomial matrix carries a standard basis vector to its phase times the
permuted standard basis vector. -/
theorem monomial_mulVec_single [NonAssocSemiring R] (σ : Equiv.Perm ι) (φ : ι → R) (s : ι) :
    monomial σ φ *ᵥ Pi.single s 1 = φ s • Pi.single (σ s) 1 := by
  rw [monomial_mulVec]
  funext t
  by_cases h : t = σ s
  · subst h
    simp
  · have hne : σ.symm t ≠ s := fun hc ↦ h (by rw [← hc, Equiv.apply_symm_apply])
    simp [h, hne]

/-- A vector is fixed by a monomial matrix exactly when its coordinates transport
along the permutation with the given phases. -/
theorem monomial_mulVec_eq_self_iff [NonAssocSemiring R] (σ : Equiv.Perm ι) (φ : ι → R)
    (v : ι → R) :
    monomial σ φ *ᵥ v = v ↔ ∀ s, v (σ s) = φ s * v s := by
  rw [monomial_mulVec, funext_iff]
  constructor
  · intro h s
    simpa using (h (σ s)).symm
  · intro h t
    simpa using (h (σ.symm t)).symm

/-- The product of two monomial matrices is monomial for the composite permutation,
with the phases multiplied along the way. -/
theorem monomial_mul_monomial [NonAssocSemiring R] (σ τ : Equiv.Perm ι) (φ ψ : ι → R) :
    monomial σ φ * monomial τ ψ = monomial (σ * τ) fun s ↦ φ (τ s) * ψ s := by
  ext t s
  simp only [mul_apply, monomial_apply]
  rw [Finset.sum_eq_single (τ s)]
  · by_cases h : t = σ (τ s) <;> simp [h, Equiv.Perm.mul_apply]
  · intro r _ hr
    simp [hr]
  · simp

/-- A monomial matrix with unimodular phases is unitary. -/
theorem monomial_mem_unitaryGroup [CommRing R] [StarRing R] (σ : Equiv.Perm ι) (φ : ι → R)
    (h : ∀ s, star (φ s) * φ s = 1) :
    monomial σ φ ∈ unitaryGroup ι R := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_monomial,
    monomial_mul_monomial]
  have hσ : σ.symm * σ = 1 := by
    ext x
    simp
  rw [hσ]
  simp only [Equiv.symm_apply_apply, h]
  exact monomial_one

end Matrix
