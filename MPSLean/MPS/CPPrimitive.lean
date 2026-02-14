/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.MPS.Transfer

import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.NoncommRing

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Completely positive maps on matrices

We define what it means for a linear map `E : M_D(ℂ) →ₗ[ℂ] M_D(ℂ)` to be completely
positive and irreducible, in the context of MPS transfer operators.

Key results:
- `injective_implies_irreducibleCP`: injectivity of an MPS tensor implies
  irreducibility of its transfer map.
- `HasUniqueFixedPoint`: the unique-fixed-point property used by
  `QuantumPerronFrobenius.lean`.
-/

/-! ### Irreducibility of CP maps

For the definitions of positive maps, trace-preserving maps, and channels,
see `IsPositiveMap`, `IsTracePreservingMap`, and `IsChannel` in
`PositiveMapSpectral.lean`. -/

/-- An orthogonal projection in `M_D(ℂ)`: a matrix that is both Hermitian and idempotent.
These correspond to projections onto subspaces of `ℂ^D`. -/
def IsOrthogonalProjection (P : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- The zero matrix is an orthogonal projection. -/
lemma isOrthogonalProjection_zero : IsOrthogonalProjection (0 : Matrix (Fin D) (Fin D) ℂ) :=
  ⟨Matrix.isHermitian_zero, by simp⟩

/-- The identity matrix is an orthogonal projection. -/
lemma isOrthogonalProjection_one : IsOrthogonalProjection (1 : Matrix (Fin D) (Fin D) ℂ) :=
  ⟨Matrix.isHermitian_one, by simp⟩

/-- A CP map `E` is *irreducible* if the only orthogonal projections `P` satisfying
`E(P X P) = P · E(P X P) · P` for all `X` are `P = 0` and `P = 1`.

Equivalently, `E` has no non-trivial invariant subspace in the sense that
there is no proper non-zero subspace `S ⊆ ℂ^D` such that `E` maps the
"compressed" algebra `P_S · M_D · P_S` into itself.

This is the quantum analogue of a positive matrix being irreducible
(having no non-trivial invariant face in the PSD cone). -/
def IsIrreducibleCP (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ P : Matrix (Fin D) (Fin D) ℂ,
    IsOrthogonalProjection P →
    (∀ X : Matrix (Fin D) (Fin D) ℂ, P * E (P * X * P) * P = E (P * X * P)) →
    P = 0 ∨ P = 1

/-! ### Unique fixed point property -/

/-- `E` has `ρ` as its unique PSD fixed point (up to scalar multiples), and `ρ` is
positive definite. This is the conclusion of the quantum Perron–Frobenius theorem. -/
structure HasUniqueFixedPoint [DecidableEq (Fin D)]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Prop where
  /-- `ρ` is a fixed point of `E`. -/
  fixed : E ρ = ρ
  /-- `ρ` is positive definite. -/
  pos_def : ρ.PosDef
  /-- Any PSD fixed point is a scalar multiple of `ρ`. -/
  unique : ∀ σ : Matrix (Fin D) (Fin D) ℂ, σ.PosSemidef → E σ = σ → ∃ c : ℂ, σ = c • ρ

/-! ### Connection to MPS injectivity -/

/-! #### Auxiliary lemmas for the irreducibility proof -/

/-- Entry computation for a sandwich product with a single-entry matrix. -/
private lemma mul_single_mul_eq [DecidableEq (Fin D)]
    (Q P : Matrix (Fin D) (Fin D) ℂ) (k l : Fin D) :
    Q * Matrix.single k l (1 : ℂ) * P =
      Matrix.of (fun i j => Q i k * P l j) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.single_apply]
  have inner_eq : ∀ x, ∑ x₁, Q i x₁ * (if k = x₁ ∧ l = x then 1 else 0) =
      if l = x then Q i k else 0 := by
    intro x
    by_cases hlx : l = x
    · subst hlx; simp only [and_true]
      rw [Finset.sum_eq_single k] <;> simp (config := { contextual := true }) [Ne.symm]
    · simp only [hlx, and_false, ite_false, mul_zero, Finset.sum_const_zero]
  simp_rw [inner_eq]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hbl; simp [Ne.symm hbl]
  · simp

/-- If `(1 - P) * M * P = 0` for all matrices `M`, then `P = 0` or `P = 1`.
This is the final step: an invariant subspace of every matrix must be trivial. -/
private lemma proj_zero_or_one_of_sandwich [DecidableEq (Fin D)]
    (P : Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ M : Matrix (Fin D) (Fin D) ℂ, (1 - P) * M * P = 0) :
    P = 0 ∨ P = 1 := by
  by_cases hP : P = 0
  · left; exact hP
  · right; symm; rw [← sub_eq_zero]
    have hP' : ∃ l₀ j₀, P l₀ j₀ ≠ 0 := by
      by_contra h_all; push_neg at h_all
      exact hP (Matrix.ext (fun i j => h_all i j))
    obtain ⟨l₀, j₀, hlj⟩ := hP'
    ext i k
    have h_eq := mul_single_mul_eq (1 - P) P k l₀
    rw [h (Matrix.single k l₀ 1)] at h_eq
    have h_entry := congr_fun (congr_fun h_eq i) j₀
    simp [Matrix.of_apply] at h_entry
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply]
    exact h_entry.resolve_right hlj

private lemma one_sub_mul_self_of_idem (P : Matrix (Fin D) (Fin D) ℂ) (hP : P * P = P) :
    (1 - P) * P = 0 := by
  rw [sub_mul, one_mul, hP, sub_self]

/-- `(M * Mᴴ) c c = ∑ x, ‖M c x‖²` for any matrix `M`. -/
lemma diagonal_mul_conjTranspose_eq_normSq_sum
    (M : Matrix (Fin D) (Fin D) ℂ) (c : Fin D) :
    (M * Mᴴ) c c = ↑(∑ x, Complex.normSq (M c x)) := by
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  congr 1; ext x
  simp [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]; ring

/-- If `M * Mᴴ = 0` then `M = 0`, since the diagonal entries are sums of squared norms. -/
private lemma eq_zero_of_mul_conjTranspose_eq_zero
    (M : Matrix (Fin D) (Fin D) ℂ) (h : M * Mᴴ = 0) : M = 0 := by
  ext i j
  have hii : (M * Mᴴ) i i = 0 := by rw [h]; simp
  rw [diagonal_mul_conjTranspose_eq_normSq_sum] at hii
  have h_sum_real : ∑ x : Fin D, Complex.normSq (M i x) = 0 := by exact_mod_cast hii
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg _)).mp
      h_sum_real j (Finset.mem_univ _))

/-- If `∑ᵢ Bᵢ * Bᵢᴴ = 0` then each `Bᵢ = 0`, since each term is PSD. -/
lemma eq_zero_of_sum_mul_conjTranspose_eq_zero {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin D) (Fin D) ℂ)
    (h : ∑ i : ι, B i * (B i)ᴴ = 0) :
    ∀ i, B i = 0 := by
  -- Key fact: the diagonal entries of each `Bₖ * Bₖᴴ` are nonneg reals that sum to 0.
  have h_diag_eq : ∀ c, ∑ k : ι, (B k * (B k)ᴴ) c c = 0 := by
    intro c; have := congr_fun (congr_fun h c) c
    rwa [Finset.sum_apply, Finset.sum_apply, Matrix.zero_apply] at this
  have h_each_diag : ∀ k c, (B k * (B k)ᴴ) c c = 0 := by
    intro k c
    simp_rw [diagonal_mul_conjTranspose_eq_normSq_sum] at h_diag_eq ⊢
    have h_nonneg : ∀ k', (0 : ℝ) ≤ ∑ x, Complex.normSq (B k' c x) :=
      fun k' => Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg _)
    have h_sum_real : ∑ k' : ι, ∑ x, Complex.normSq (B k' c x) = 0 := by
      exact_mod_cast h_diag_eq c
    simp [(Finset.sum_eq_zero_iff_of_nonneg (fun k' _ => h_nonneg k')).mp
      h_sum_real k (Finset.mem_univ _)]
  -- Extract: each Bᵢ a b = 0 from the vanishing diagonal of Bᵢ * Bᵢᴴ.
  intro i; ext a b
  have h_ii := h_each_diag i a
  rw [diagonal_mul_conjTranspose_eq_normSq_sum] at h_ii
  have h_sum_real : ∑ x, Complex.normSq (B i a x) = 0 := by exact_mod_cast h_ii
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg _)).mp
      h_sum_real b (Finset.mem_univ _))

/-- The invariance condition for a projection `P` under a transfer map implies that
each Kraus operator `Aᵢ` maps `Im(P)` into `Im(P)`, i.e., `(1 - P) * Aᵢ * P = 0`. -/
private lemma invariance_implies_complement_zero (A : MPSTensor d D)
    (P : Matrix (Fin D) (Fin D) ℂ)
    (hProj : IsOrthogonalProjection P)
    (hInv : ∀ X, P * transferMap (d := d) (D := D) A (P * X * P) * P =
                  transferMap (d := d) (D := D) A (P * X * P)) :
    ∀ i : Fin d, (1 - P) * A i * P = 0 := by
  -- Step 1: (1-P)*E(PXP) = 0 for all X
  have h_vanish : ∀ X, (1 - P) * transferMap (d := d) (D := D) A (P * X * P) = 0 := by
    intro X
    set E := transferMap (d := d) (D := D) A (P * X * P)
    have hPEP : P * E * P = E := hInv X
    calc (1 - P) * E
        = (1 - P) * (P * E * P) := by rw [hPEP]
      _ = ((1 - P) * P) * E * P := by noncomm_ring
      _ = 0 := by rw [one_sub_mul_self_of_idem P hProj.2]; noncomm_ring
  -- Step 2: specialise to X = 1 to get (1-P)*E(P) = 0
  have h_EP_zero : (1 - P) * transferMap (d := d) (D := D) A P = 0 := by
    have := h_vanish 1; rwa [mul_one, hProj.2] at this
  -- Step 3: ∑ᵢ Bᵢ * Bᵢᴴ = 0 where Bᵢ = (1-P)*Aᵢ*P
  have h_sum_zero : ∑ i : Fin d, ((1 - P) * A i * P) * ((1 - P) * A i * P)ᴴ = 0 := by
    have key : ∀ i : Fin d,
        ((1 - P) * A i * P) * ((1 - P) * A i * P)ᴴ =
        (1 - P) * (A i * P * (A i)ᴴ) * (1 - P) := by
      intro i
      have hPH : Pᴴ = P := hProj.1.eq
      have h1PH : (1 - P)ᴴ = 1 - P := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH, h1PH]
      have hPP := hProj.2
      calc (1 - P) * A i * P * (P * ((A i)ᴴ * (1 - P)))
          = (1 - P) * A i * (P * P) * (A i)ᴴ * (1 - P) := by noncomm_ring
        _ = (1 - P) * A i * P * (A i)ᴴ * (1 - P) := by rw [hPP]
        _ = (1 - P) * (A i * P * (A i)ᴴ) * (1 - P) := by noncomm_ring
    simp_rw [key, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [show ∑ i : Fin d, A i * P * (A i)ᴴ = transferMap (d := d) (D := D) A P from by
      rw [transferMap_apply]]
    rw [h_EP_zero, zero_mul]
  -- Step 4: each Bᵢ = 0
  exact eq_zero_of_sum_mul_conjTranspose_eq_zero _ h_sum_zero

/-! #### The main irreducibility theorem -/

/-- If an MPS tensor `A` is injective (its matrices span the full matrix algebra),
then its transfer map `E_A` is irreducible.

**Proof.** Suppose `P` is a non-trivial projection with
`P · E_A(P X P) · P = E_A(P X P)` for all `X`. Expanding
`E_A(Y) = ∑ᵢ Aᵢ Y Aᵢ†`, the invariance condition gives
`(1 - P) Aᵢ P = 0` for all `i`, i.e., each `Aᵢ` maps `Im(P)` into `Im(P)`.
Since the `{Aᵢ}` span all of `M_D(ℂ)`, the linear map `M ↦ (1-P)MP` vanishes
on all matrices. Testing with single-entry matrices forces either `P = 0` or `P = 1`. -/
theorem injective_implies_irreducibleCP (A : MPSTensor d D) (hA : IsInjective A) :
    IsIrreducibleCP (transferMap (d := d) (D := D) A) := by
  intro P hProj hInv
  -- Step 1: derive (1-P)*Aᵢ*P = 0 for each i
  have h_on_A := invariance_implies_complement_zero A P hProj hInv
  -- Step 2: extend to all matrices via span
  have h_all : ∀ M : Matrix (Fin D) (Fin D) ℂ, (1 - P) * M * P = 0 := by
    intro M
    have hM : M ∈ Submodule.span ℂ (Set.range A) := hA ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h_on_A i
    | zero => simp
    | add x y _ _ hx hy =>
      calc (1 - P) * (x + y) * P
          = (1 - P) * x * P + (1 - P) * y * P := by noncomm_ring
        _ = 0 + 0 := by rw [hx, hy]
        _ = 0 := add_zero 0
    | smul c x _ hx =>
      calc (1 - P) * (c • x) * P
          = c • ((1 - P) * x * P) := by rw [mul_smul_comm, smul_mul_assoc]
        _ = c • 0 := by rw [hx]
        _ = 0 := smul_zero c
  -- Step 3: conclude P = 0 or P = 1
  exact proj_zero_or_one_of_sandwich P h_all

/-! ### Iterated transfer map

The iterated transfer map identity (iterating the transfer map `n` times gives
the sum over word evaluations) is proved in `TransferSpectral.lean` as
`transferMap_pow_apply'`, using the more general mixed transfer map framework. -/

end MPSTensor
