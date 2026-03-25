/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.KrausRepresentation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Stinespring representation theorem (Wolf Ch. 2, Thm 2.2)

This file states and proves the Stinespring dilation theorem:
every completely positive map can be written as `T*(A) = V†(A ⊗ 𝟙)V`
for an explicit isometry `V` constructed from the Kraus operators.

## Main definitions

* `stinespringV`: the Stinespring isometry `V = ∑ⱼ Kⱼ ⊗ |j⟩`, a `(D·r) × D`
  matrix satisfying `V(i, j) k = (Kⱼ)_{ik}`
* `stinespringV_apply`: entrywise evaluation lemma for `stinespringV`
* `stinespringPi`: the concrete finite-dimensional representation `π(A) = A ⊗ 𝟙_r`

## Main results (Wolf Thm 2.2)

* `stinespringV_conjTranspose_mul` — `V†V = ∑ⱼ Kⱼ†Kⱼ`
* `stinespringV_isometry_iff_kraus_normalized` — `V†V = 𝟙` ↔ `∑ⱼ Kⱼ†Kⱼ = 𝟙`
* `stinespring_dual_representation` — `T*(A) = V†(A ⊗ 𝟙)V` (Heisenberg picture)
* `stinespring_schrodinger_representation` — `T(ρ) = tr_r(VρV†)` (Schrödinger picture)
* `exists_stinespring_dilation` — existential Heisenberg-form dilation witness for CP maps
* `exists_stinespring_isometry_of_cptp` — existential isometric dilation witness for CPTP maps

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 2.2][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### Stinespring isometry construction -/

/-- The Stinespring isometry `V : ℂ^D → ℂ^D ⊗ ℂ^r` constructed from Kraus operators.

Concretely, `V` is a `(D·r) × D` matrix defined by `V (i, j) k = (Kⱼ)_{ik}`.
This encodes `V = ∑ⱼ Kⱼ ⊗ |j⟩`, where `|j⟩` is the `j`-th standard basis vector. -/
noncomputable def stinespringV {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin r) (Fin D) ℂ :=
  fun ⟨i, j⟩ k => K j i k

@[simp]
theorem stinespringV_apply {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (j : Fin r) (k : Fin D) :
    stinespringV K (i, j) k = K j i k := rfl

/-- `V†V = ∑ⱼ Kⱼ†Kⱼ` for the Stinespring isometry. -/
theorem stinespringV_conjTranspose_mul {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    (stinespringV K)ᴴ * stinespringV K =
      ∑ j : Fin r, (K j)ᴴ * K j := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, stinespringV_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

/-- **Stinespring isometry condition** (Wolf Thm 2.2):
`V†V = 𝟙` if and only if `∑ⱼ Kⱼ†Kⱼ = 𝟙`, i.e., the Kraus operators are normalized
(equivalently, the map is trace-preserving). -/
theorem stinespringV_isometry_iff_kraus_normalized {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    (stinespringV K)ᴴ * stinespringV K = 1 ↔
      ∑ j : Fin r, (K j)ᴴ * K j = 1 := by
  rw [stinespringV_conjTranspose_mul]

/-! ### `π` as a concrete `*`-representation -/

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

/-! ### Stinespring representation of the dual and Schrödinger maps -/

/-- **Stinespring representation, Heisenberg picture** (Wolf Thm 2.2):

  `T*(A) = V† (A ⊗ 𝟙_r) V`

where `V` is the Stinespring isometry. This matches the Kraus form
`T*(A) = ∑ⱼ Kⱼ† A Kⱼ`.
In this file, `T*` is the Heisenberg dual acting on observables, while the
Schrödinger map uses adjoints in the opposite order. -/
theorem stinespring_dual_representation {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (A : Matrix (Fin D) (Fin D) ℂ) :
    (stinespringV K)ᴴ * stinespringPi (r := r) A * stinespringV K =
      ∑ j : Fin r, (K j)ᴴ * A * K j := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    stinespringV_apply, stinespringPi, kroneckerMap_apply, Matrix.one_apply,
    Matrix.sum_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]

/-- **Stinespring representation, Schrödinger picture** (Wolf Thm 2.2):

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

/-! ### Existential Stinespring statements -/

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

/-- **Stinespring dilation (existential form, Wolf Thm 2.2)**:
every CP map `E` admits an ancilla dimension `r`, a Kraus family `K`,
and the concrete `*`-representation `π(A) = A ⊗ 𝟙_r` such that
`E(A) = V† π(A) V` with `V = stinespringV K`.

Note: the Kraus witness appears in conjugation form `V† (A ⊗ 𝟙) V`, not
mere left multiplication — this is the key structural content of
Stinespring's theorem.

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
