/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.SuccPred
import TNLean.Algebra.MatrixGramUnitary
import TNLean.Channel.POVM

/-!
# Sharp rank-one Neumark extension (Wolf lines 480--499)

This file proves the sharp form of Neumark's theorem for rank-one POVM
effects, following Wolf, *Quantum Channels & Operations*, lines 480--499
of `Notes/WolfNoteTexSource/ch02_representations.tex`.

Given `n` vectors `ψᵢ ∈ ℂᵈ` with the rank-one resolution of the identity
`∑ᵢ |ψᵢ⟩⟨ψᵢ| = 1_d` and the dimension condition `d ≤ n` (so that `ℂᵈ`
is a subspace of `ℂⁿ`), there exists an orthonormal basis `{φᵢ}ᵢ₌₁ⁿ`
of `ℂⁿ` such that each `ψᵢ` is the restriction of `φᵢ` to the first `d`
coordinates.

## Ambient dimension

`POVM.exists_naimark_dilation` dilates a general POVM onto
`ℂ^D ⊗ ℂ^n` (dimension `D·n`).  The source asserts the sharper
`n`-dimensional ambient space for rank-one effects.  The present theorem
(`exists_orthonormal_basis_restriction`) provides the `n × n` unitary
extension directly, without the tensor-product factor.

## Main results

* `exists_orthonormal_basis_restriction` — the sharp rank-one extension:
  from `ψᵢ` on `ℂᵈ` with `d ≤ n` and `∑ |ψᵢ⟩⟨ψᵢ| = 1`, obtain a unitary
  `U ∈ U(n)` whose rows restrict to `ψᵢ`.
* `of_rank_one_povm` — the rank-one POVM corollary: given a `POVM d n` with
  an explicit decomposition `E_i = |ψᵢ⟩⟨ψᵢ|`, apply the sharp extension.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*,
  Theorem "Neumark's theorem", lines 480--499][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset

namespace POVM

variable {d n : ℕ}

section rankOneNeumarkSharp

/-- Given a family `ψᵢ : Fin d → ℂ` of `n` vectors satisfying the
resolution of identity `∑_i |ψᵢ⟩⟨ψᵢ| = 1_d`, the `n×d` matrix
`Ψ i j := ψ i j` satisfies `Ψᴴ * Ψ = 1_d`. -/
private lemma gram_eq_one_of_vecMulVec_sum_eq_one (ψ : Fin n → (Fin d → ℂ))
    (h_sum : ∑ i : Fin n, Matrix.vecMulVec (ψ i) (star (ψ i)) = 1) :
    ((Matrix.of fun (i : Fin n) (j : Fin d) => ψ i j)ᴴ *
      (Matrix.of fun (i : Fin n) (j : Fin d) => ψ i j)) = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have h_entry := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j k) h_sum
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
    Pi.star_apply] at h_entry
  calc
    (∑ i : Fin n, star (ψ i j) * ψ i k)
        = (∑ i : Fin n, star (ψ i j * star (ψ i k))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_mul, star_star, mul_comm]
    _ = star (∑ i : Fin n, ψ i j * star (ψ i k)) := by
      simpa using ((starRingEnd ℂ).map_sum (Finset.univ : Finset (Fin n))
        (fun i ↦ ψ i j * star (ψ i k))).symm
    _ = star (if j = k then (1 : ℂ) else 0) := by rw [h_entry]
    _ = if j = k then (1 : ℂ) else 0 := by split <;> simp

/-- The `n×d` inclusion matrix `J` with `J i j = 1` when `i` is the
natural embedding of `j` into `Fin n` via `Fin.castLE hd` and `0`
otherwise.  For `d ≤ n`, `J` is an isometry: `Jᴴ * J = 1_d`. -/
private lemma inclusion_conjTranspose_mul_self (hd : d ≤ n) :
    ((Matrix.of fun (i : Fin n) (j : Fin d) =>
        if i = Fin.castLE hd j then (1 : ℂ) else 0)ᴴ *
      (Matrix.of fun (i : Fin n) (j : Fin d) =>
        if i = Fin.castLE hd j then (1 : ℂ) else 0)) = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [Finset.sum_eq_single (Fin.castLE hd j)]
    · simp
    · intro i _ hi
      have hterm : (if i = Fin.castLE hd j then (1 : ℂ) else 0) = 0 := by
        simp [hi]
      simp [hterm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hcast_ne : Fin.castLE hd j ≠ Fin.castLE hd k :=
      fun h ↦ hjk ((Fin.castLE_injective hd) h)
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hij : i = Fin.castLE hd j
    · subst hij; rw [if_neg hcast_ne]; simp
    · by_cases hik : i = Fin.castLE hd k
      · subst hik; rw [if_neg (Ne.symm hcast_ne)]; simp
      · simp [hij, hik]

/-- **Sharp rank-one Neumark extension** (Wolf, *Quantum Channels & Operations*,
Theorem "Neumark's theorem", lines 480--499).

Given `n` vectors `ψᵢ : Fin d → ℂ` (`i = 1,…,n`) forming a rank-one resolution
of the identity `∑ᵢ |ψᵢ⟩⟨ψᵢ| = 1_d` on `ℂᵈ` and the dimension condition
`d ≤ n` (so that `ℂᵈ` is a subspace of `ℂⁿ`), there exists a unitary
`U ∈ U(n)` such that each `ψᵢ` is the restriction of the `i`-th row of `U`
to the first `d` coordinates.

In coordinates: `ψ i j = (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j)`.
The rows `φᵢ j := U i j` form an orthonormal basis of `ℂⁿ` (because `U`
is unitary) and each `ψᵢ` is the restriction of `φᵢ` to the embedded
subspace `ℂᵈ ⊂ ℂⁿ`.

The ambient dimension of this extension is `n` (the number of outcomes),
in contrast to `POVM.exists_naimark_dilation` which constructs an isometry
onto `ℂ^D ⊗ ℂ^n` of dimension `D·n`. -/
theorem exists_orthonormal_basis_restriction (ψ : Fin n → (Fin d → ℂ))
    (hd : d ≤ n)
    (h_sum : ∑ i : Fin n, Matrix.vecMulVec (ψ i) (star (ψ i)) = 1) :
    ∃ (U : Matrix.unitaryGroup (Fin n) ℂ),
      (∀ i j, (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j) = ψ i j) := by
  let Ψ : Matrix (Fin n) (Fin d) ℂ := Matrix.of fun i j => ψ i j
  have hΨGram : Ψᴴ * Ψ = 1 := by
    dsimp [Ψ]
    exact gram_eq_one_of_vecMulVec_sum_eq_one ψ h_sum
  let J : Matrix (Fin n) (Fin d) ℂ :=
    Matrix.of fun i j => if i = Fin.castLE hd j then (1 : ℂ) else 0
  have hJGram : Jᴴ * J = 1 := inclusion_conjTranspose_mul_self hd
  obtain ⟨U, hU⟩ :=
    Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq Ψ J (hΨGram.trans hJGram.symm)
  -- hU: Ψ = (U : Matrix (Fin n) (Fin n) ℂ) * J
  have h_restrict (i : Fin n) (j : Fin d) :
      (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j) = ψ i j := by
    calc
      (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j)
          = (∑ k : Fin n, (U : Matrix (Fin n) (Fin n) ℂ) i k * J k j) := by
        rw [Finset.sum_eq_single (Fin.castLE hd j)]
        · simp [J]
        · intro k _ hk
          have hJzero : J k j = 0 := by
            dsimp [J]
            simp [hk]
          simp [hJzero]
        · intro h; exact absurd (Finset.mem_univ _) h
      _ = ((U : Matrix (Fin n) (Fin n) ℂ) * J) i j := rfl
      _ = Ψ i j := by rw [hU]
      _ = ψ i j := rfl
  exact ⟨U, h_restrict⟩

end rankOneNeumarkSharp

/-! ### The rank-one POVM corollary -/

/-- **Rank-one POVM corollary**: start from a `POVM d n` whose effects are
explicitly given as rank-one `|ψᵢ⟩⟨ψᵢ|`.  The POVM axioms guarantee the resolution
`∑ᵢ |ψᵢ⟩⟨ψᵢ| = 1`, so `exists_orthonormal_basis_restriction` applies and
yields the sharp `n`-dimensional orthonormal-basis extension recorded in
Wolf lines 480--499.

This specializes the general POVM structure to the vector-level
hypotheses of the sharp theorem.  Unlike `exists_naimark_dilation`,
whose ambient Hilbert space is `ℂ^D ⊗ ℂ^n` (dimension `D·n`), this
corollary gives the source's assertion of an `n`-dimensional ambient
space under the rank-one hypothesis. -/
theorem of_rank_one_povm (E : POVM d n) (ψ : Fin n → (Fin d → ℂ))
    (hd : d ≤ n)
    (h_ops : ∀ i, E.ops i = Matrix.vecMulVec (ψ i) (star (ψ i))) :
    ∃ (U : Matrix.unitaryGroup (Fin n) ℂ),
      (∀ i j, (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j) = ψ i j) := by
  have h_sum : ∑ i : Fin n, Matrix.vecMulVec (ψ i) (star (ψ i)) = 1 := by
    calc
      ∑ i : Fin n, Matrix.vecMulVec (ψ i) (star (ψ i))
          = ∑ i : Fin n, E.ops i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h_ops i]
      _ = 1 := E.sum_eq_one
  exact exists_orthonormal_basis_restriction ψ hd h_sum

end POVM
