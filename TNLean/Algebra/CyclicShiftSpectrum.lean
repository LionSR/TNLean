/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinCyclicInduction
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Complex.Basic

/-!
# Eigenvalues of a cyclically shifted independent family

If an endomorphism cyclically permutes a linearly independent family of
length `n`, its invariant span has every `n`-th root of unity as an
eigenvalue. The Fourier eigenvectors give the lower spectral bound needed
for cyclic sectors in arXiv:1708.00029, Section 4.1.
-/

open scoped BigOperators

/-- Every root of unity of order dividing the length of a cyclically
shifted independent family is an eigenvalue of the shifting operator.
Source: arXiv:1708.00029, Section 4.1. -/
theorem LinearMap.hasEigenvalue_of_cyclic_shift
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (T : V →ₗ[ℂ] V) (R : Fin (n + 1) → V)
    (hR : LinearIndependent ℂ R)
    (hshift : ∀ t, T (R t) = R (finRotate (n + 1) t))
    (ζ : ℂ) (hζ : ζ ^ (n + 1) = 1) :
    Module.End.HasEigenvalue T ζ := by
  classical
  let a : ℂ := ζ⁻¹
  have ha : a ^ (n + 1) = 1 := by
    dsimp [a]
    rw [inv_pow, hζ, inv_one]
  have hζne : ζ ≠ 0 := by
    intro hz
    simp [hz] at hζ
  have hphase (i : Fin (n + 1)) :
      a ^ (finRotate (n + 1) i).val = a * a ^ i.val := by
    by_cases hi : i = Fin.last n
    · subst i
      rw [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last]
      simpa only [pow_succ', mul_comm] using ha.symm
    · rw [coe_finRotate_of_ne_last hi, pow_succ']
  have hcoef (j : Fin (n + 1)) :
      a ^ ((finRotate (n + 1)).symm j).val = ζ * a ^ j.val := by
    have hp := hphase ((finRotate (n + 1)).symm j)
    rw [Equiv.apply_symm_apply] at hp
    calc
      a ^ ((finRotate (n + 1)).symm j).val =
          (ζ * a) * a ^ ((finRotate (n + 1)).symm j).val := by
            simp [a, hζne]
      _ = ζ * a ^ j.val := by rw [hp]; ring
  let v : V := ∑ i : Fin (n + 1), a ^ i.val • R i
  have hvne : v ≠ 0 := by
    intro hv
    have hcoeff := (linearIndependent_iff'.mp hR) Finset.univ
      (fun i : Fin (n + 1) => a ^ i.val)
      (by simpa [v] using hv) (0 : Fin (n + 1))
      (Finset.mem_univ _)
    simp at hcoeff
  have hsum :
      (∑ i : Fin (n + 1), a ^ i.val • R (finRotate (n + 1) i)) =
        ∑ j : Fin (n + 1),
          a ^ ((finRotate (n + 1)).symm j).val • R j := by
    apply Fintype.sum_equiv (finRotate (n + 1))
    intro i
    simp
  have hTv : T v = ζ • v := by
    calc
      T v = ∑ i : Fin (n + 1), a ^ i.val • R (finRotate (n + 1) i) := by
        simp [v, map_sum, map_smul, hshift]
      _ = ∑ j : Fin (n + 1),
          a ^ ((finRotate (n + 1)).symm j).val • R j := hsum
      _ = ζ • v := by
        simp_rw [hcoef]
        simp [v, Finset.smul_sum, smul_smul]
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hTv, hvne⟩
