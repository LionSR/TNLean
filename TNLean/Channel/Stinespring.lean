/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.KrausRepresentation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Stinespring representation theorem (Wolf Section 2.1, Theorem 2.2)

This file states and proves the Stinespring dilation theorem:
every completely positive map can be written as `T*(A) = V†(A ⊗ 𝟙)V`
for an explicit isometry `V` constructed from the Kraus operators (Wolf Eq. (2.11)).

## Main definitions

* `stinespringV`: the Stinespring matrix `V = ∑ⱼ Kⱼ ⊗ |j⟩` for a possibly
  rectangular Kraus family, satisfying `V(i, j) k = (Kⱼ)_{ik}`
* `stinespringV_apply`: entrywise evaluation lemma for `stinespringV`
* `stinespringPi`: the concrete finite-dimensional representation `π(A) = A ⊗ 𝟙_r`

## Main results (Wolf Theorem 2.2)

* `stinespringV_conjTranspose_mul` — `V†V = ∑ⱼ Kⱼ†Kⱼ`
* `stinespringV_isometry_iff_kraus_normalized` — `V†V = 𝟙` ↔ `∑ⱼ Kⱼ†Kⱼ = 𝟙`
* `stinespring_dual_representation` — `T*(A) = V†(A ⊗ 𝟙)V` (Heisenberg picture)
* `stinespring_schrodinger_representation` — `T(ρ) = tr_r(VρV†)` (Schrödinger picture)
* `exists_stinespring_dilation` — existential Heisenberg-form dilation witness for CP maps
* `exists_stinespring_isometry_of_cptp` — existential isometric dilation witness for CPTP maps

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.2][Wolf2012QChannels]
-/

open scoped Matrix Kronecker
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### Stinespring matrix construction -/

/-- The Stinespring matrix `V : ℂ^α → ℂ^β ⊗ ℂ^r` constructed from a possibly
rectangular Kraus family.

Concretely, `V` is defined by `V (i, j) k = (Kⱼ)_{ik}`.
This encodes `V = ∑ⱼ Kⱼ ⊗ |j⟩`, where `|j⟩` is the `j`-th standard basis vector. -/
noncomputable def stinespringV {r : ℕ} {α β : Type*}
    (K : Fin r → Matrix β α ℂ) :
    Matrix (β × Fin r) α ℂ :=
  fun ⟨i, j⟩ k => K j i k

@[simp]
theorem stinespringV_apply {r : ℕ} {α β : Type*}
    (K : Fin r → Matrix β α ℂ) (i : β)
    (j : Fin r) (k : α) :
    stinespringV K (i, j) k = K j i k := rfl

/-- `V†V = ∑ⱼ Kⱼ†Kⱼ` for the Stinespring matrix. -/
theorem stinespringV_conjTranspose_mul {r : ℕ} {α β : Type*} [Fintype β]
    (K : Fin r → Matrix β α ℂ) :
    (stinespringV K)ᴴ * stinespringV K =
      ∑ j : Fin r, (K j)ᴴ * K j := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, stinespringV_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

/-- Tensor a Stinespring matrix with the identity on an untouched finite
factor. -/
noncomputable def localStinespringV
    {α β δ : Type*} [Fintype δ] [DecidableEq δ]
    (V : Matrix β α ℂ) : Matrix (β × δ) (α × δ) ℂ :=
  V ⊗ₖ (1 : Matrix δ δ ℂ)

/-- Tensoring an isometry with an identity matrix again gives an isometry. -/
theorem localStinespringV_conjTranspose_mul
    {α β δ : Type*} [DecidableEq α] [Fintype β]
    [Fintype δ] [DecidableEq δ] (V : Matrix β α ℂ)
    (hV : Vᴴ * V = 1) :
    (localStinespringV (δ := δ) V)ᴴ * localStinespringV (δ := δ) V = 1 := by
  rw [localStinespringV, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, hV,
    Matrix.one_mul, Matrix.one_kronecker_one]

/-- **Stinespring isometry condition** (Wolf Theorem 2.2):
`V†V = 𝟙` if and only if `∑ⱼ Kⱼ†Kⱼ = 𝟙`, i.e., the Kraus operators are normalized
(equivalently, the map is trace-preserving). -/
theorem stinespringV_isometry_iff_kraus_normalized {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    (stinespringV K)ᴴ * stinespringV K = 1 ↔
      ∑ j : Fin r, (K j)ᴴ * K j = 1 := by
  rw [stinespringV_conjTranspose_mul]

/-! ### Stinespring representation of the dual and Schrödinger maps -/

/-- **Stinespring representation, Heisenberg picture** (Wolf Theorem 2.2, Eq. (2.11)):

  `T*(A) = V† (A ⊗ 𝟙_r) V`

where `V` is the Stinespring isometry. This matches the Kraus form
`T*(A) = ∑ⱼ Kⱼ† A Kⱼ`.
In this file, `T*` is the Heisenberg dual acting on observables, while the
Schrödinger map uses adjoints in the opposite order. -/
theorem stinespring_dual_representation {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (A : Matrix (Fin D) (Fin D) ℂ) :
    (stinespringV K)ᴴ *
      -- This is `stinespringPi A` (defined below); kept inline to avoid forward reference.
      (kroneckerMap (· * ·) A (1 : Matrix (Fin r) (Fin r) ℂ)) *
      stinespringV K =
      ∑ j : Fin r, (K j)ᴴ * A * K j := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    stinespringV_apply, kroneckerMap_apply, Matrix.one_apply,
    Matrix.sum_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]

/-! ### Finite-index Stinespring compression lemmas -/

/-- The Stinespring matrix for a Kraus family indexed by an arbitrary finite type.

This is the same coordinate construction as `stinespringV`; the latter is kept
`Fin`-indexed because most channel declarations use a natural number as Kraus
rank. Wolf's Radon--Nikodym theorem for instruments naturally groups Kraus
operators by a finite outcome type. -/
noncomputable def stinespringVGen {η α β : Type*}
    (K : η → Matrix β α ℂ) :
    Matrix (β × η) α ℂ :=
  fun ⟨i, j⟩ k => K j i k

@[simp]
theorem stinespringVGen_apply {η α β : Type*}
    (K : η → Matrix β α ℂ) (i : β) (j : η) (k : α) :
    stinespringVGen K (i, j) k = K j i k := rfl

/-- Stinespring dual representation for a Kraus family indexed by an arbitrary
finite type. -/
theorem stinespring_dual_representation_gen {η : Type*} [Fintype η] [DecidableEq η]
    (K : η → Matrix (Fin D) (Fin D) ℂ) (A : Matrix (Fin D) (Fin D) ℂ) :
    (stinespringVGen K)ᴴ *
      (kroneckerMap (· * ·) A (1 : Matrix η η ℂ)) *
      stinespringVGen K =
      ∑ j : η, (K j)ᴴ * A * K j := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    stinespringVGen_apply, kroneckerMap_apply, Matrix.one_apply,
    Matrix.sum_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_comm

/-- A linear combination of Kraus blocks is obtained by left-multiplying the
Stinespring matrix by `1 ⊗ C`. -/
theorem stinespringVGen_linear_combination
    {η : Type*}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (C : Matrix η (Fin r) ℂ) :
    stinespringVGen (fun α : η => ∑ j : Fin r, C α j • K j) =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ) C *
        stinespringV K := by
  ext x b
  rcases x with ⟨a, α⟩
  simp only [stinespringVGen_apply, stinespringV_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha'
    have haa' : a ≠ a' := fun h => ha' h.symm
    simp [haa']
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The Kronecker identity
`A ⊗ (CᴴC) = (𝟙 ⊗ C)ᴴ (A ⊗ 𝟙)(𝟙 ⊗ C)` for an arbitrary finite row type. -/
theorem Matrix.kroneckerMap_conjTranspose_mul_kroneckerMap_gen
    {η : Type*} [Fintype η] [DecidableEq η]
    (A : Matrix (Fin D) (Fin D) ℂ) (C : Matrix η (Fin r) ℂ) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ) C)ᴴ *
        Matrix.kroneckerMap (· * ·) A (1 : Matrix η η ℂ) *
        Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ) C =
      Matrix.kroneckerMap (· * ·) A (Cᴴ * C) := by
  rw [Matrix.conjTranspose_kronecker]
  rw [show (1 : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 from Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul (A := (1 : Matrix (Fin D) (Fin D) ℂ)) (B := A)
      (A' := Cᴴ) (B' := (1 : Matrix η η ℂ))]
  rw [← Matrix.mul_kronecker_mul (A := (1 * A : Matrix (Fin D) (Fin D) ℂ))
      (B := (1 : Matrix (Fin D) (Fin D) ℂ)) (A' := Cᴴ * 1) (B' := C)]
  simp

/-- **Stinespring representation, Schrödinger picture** (Wolf Theorem 2.2):

  `T(ρ)_{ij} = ∑_k (V ρ V†)_{(i,k),(j,k)} = tr_r(V ρ V†)`

where `tr_r` denotes partial trace over the dilation space `ℂ^r`. -/
theorem stinespring_schrodinger_representation {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin D) :
    (∑ l : Fin r, K l * X * (K l)ᴴ) i j =
    ∑ k : Fin r,
      (stinespringV K * X * (stinespringV K)ᴴ) (i, k) (j, k) := by
  -- Unfold stinespringV and match matrix entries on both sides.
  simp only [Matrix.mul_apply, Matrix.sum_apply,
    stinespringV_apply, Matrix.conjTranspose_apply]

/-! ### `π` as a concrete `*`-representation and existential Stinespring statements -/

/-- The concrete representation `π(A) = A ⊗ 𝟙_r` used in the finite-dimensional
Stinespring construction. -/
noncomputable def stinespringPi {r : ℕ}
    (A : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
  kroneckerMap (· * ·) A (1 : Matrix (Fin r) (Fin r) ℂ)

@[simp]
theorem stinespringPi_apply {r : ℕ}
    (A : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) (a b : Fin r) :
    stinespringPi (r := r) A (i, a) (j, b) = A i j * (1 : Matrix (Fin r) (Fin r) ℂ) a b := rfl

@[simp]
theorem stinespringPi_one {r : ℕ} :
    stinespringPi (D := D) (r := r) (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
  unfold stinespringPi
  exact Matrix.one_kronecker_one (m := Fin D) (n := Fin r) (α := ℂ)

@[simp]
theorem stinespringPi_mul {r : ℕ}
    (A B : Matrix (Fin D) (Fin D) ℂ) :
    stinespringPi (r := r) (A * B) = stinespringPi (r := r) A * stinespringPi (r := r) B := by
  unfold stinespringPi
  convert Matrix.mul_kronecker_mul (A := A) (B := B)
      (A' := (1 : Matrix (Fin r) (Fin r) ℂ)) (B' := (1 : Matrix (Fin r) (Fin r) ℂ)) using 1
  simp

@[simp]
theorem stinespringPi_conjTranspose {r : ℕ}
    (A : Matrix (Fin D) (Fin D) ℂ) :
    (stinespringPi (r := r) A)ᴴ = stinespringPi (r := r) Aᴴ := by
  unfold stinespringPi
  convert Matrix.conjTranspose_kronecker (x := A) (y := (1 : Matrix (Fin r) (Fin r) ℂ)) using 1
  simp

/-- **Stinespring dilation (existential form, Wolf Theorem 2.2)**:
every CP map `E` admits an ancilla dimension `r`, a Kraus family `K`,
and the concrete `*`-representation `π(A) = A ⊗ 𝟙_r` such that
`E(A) = V† π(A) V` with `V = stinespringV K`.

Convention: the returned witness `K` is in the Heisenberg orientation
(i.e. conjugated relative to a Schrödinger-form Kraus family). -/
theorem exists_stinespring_dilation
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : IsCPMap E) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin D) (Fin D) ℂ),
      ∀ A, E A = (stinespringV K)ᴴ * stinespringPi (r := r) A * stinespringV K := by
  rcases hE with ⟨r, K, hK⟩
  -- Witness convention: we return the conjugate-transposed family `fun j => (K j)ᴴ`
  -- so the theorem matches the Heisenberg-form identity `Φ(X) = ∑ j, Kⱼᴴ * X * Kⱼ`.
  refine ⟨r, fun j => (K j)ᴴ, ?_⟩
  intro A
  calc
    E A = ∑ i : Fin r, K i * A * (K i)ᴴ := hK A
    _ = ∑ i : Fin r, ((K i)ᴴ)ᴴ * A * (K i)ᴴ := by
      simp [Matrix.conjTranspose_conjTranspose]
    _ = (stinespringV (fun j => (K j)ᴴ))ᴴ * stinespringPi (r := r) A *
          stinespringV (fun j => (K j)ᴴ) :=
      (stinespring_dual_representation (K := fun j => (K j)ᴴ) (A := A)).symm

/-- **Stinespring dilation with isometry (CPTP case)**:
if `E` is CP and trace-preserving, the Stinespring witness can be chosen so that
`V†V = 𝟙`, i.e. `V` is an isometry, and `E` is recovered by partial trace:
`E(ρ)_{ij} = ∑ₖ (VρV†)_{(i,k),(j,k)}`.

Unlike `exists_stinespring_dilation` (Heisenberg picture, conjugated Kraus witness),
this theorem keeps the original Schrödinger-picture Kraus family. -/
theorem exists_stinespring_isometry_of_cptp
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hEcp : IsCPMap E) (hEtp : IsTracePreservingMap E) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin D) (Fin D) ℂ),
      (∀ A i j, (E A) i j =
        ∑ k : Fin r, (stinespringV K * A * (stinespringV K)ᴴ) (i, k) (j, k)) ∧
      (stinespringV K)ᴴ * stinespringV K = 1 := by
  rcases hEcp with ⟨r, K, hK⟩
  refine ⟨r, K, ?_, ?_⟩
  · intro A i j
    rw [hK A]
    exact stinespring_schrodinger_representation (K := K) (X := A) (i := i) (j := j)
  · rw [stinespringV_conjTranspose_mul]
    exact kraus_sum_conjTranspose_mul_of_tp K E hK hEtp
