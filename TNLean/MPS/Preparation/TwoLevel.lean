/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Two-level unitaries

For two distinct basis vectors `|a⟩`, `|b⟩` of `ℂ^ι` and a `2 × 2` matrix `g`, the two-level
operator `twoLevel a b g` acts as `g` on the span of `|a⟩, |b⟩` and as the identity on its
orthogonal complement. Two-level unitaries are the elementary factors in the standard
decomposition of a unitary on a finite-dimensional space into gates; the local circuits of
arXiv:2307.01696 ("gates with constant support", paragraph "The sequential-RG circuit") are
decomposed into two-site gates through them.

The file also records the `2 × 2` matrices used: real rotations `rotTwo z`, diagonal phases
`diagTwo ν`, and the commutator identities `rotTwo (w ^ 2) = [rotTwo w, J]`,
`diagTwo (w ^ 2) = [diagTwo w, J']` for unit `w`.
-/

open Matrix
open scoped BigOperators ComplexConjugate

namespace MPSPreparation

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate of `x ∈ {a, b}` in the two-level block: `0` for `a`, `1` otherwise. -/
def twoLevelIdx (a x : ι) : Fin 2 := if x = a then 0 else 1

/-- The **two-level operator** acting as `g` on the span of `|a⟩, |b⟩` (in this order) and as
the identity on the other basis vectors. -/
def twoLevel (a b : ι) (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix ι ι ℂ :=
  of fun x y => if (x = a ∨ x = b) ∧ (y = a ∨ y = b) then g (twoLevelIdx a x) (twoLevelIdx a y)
    else if x = y then 1 else 0

variable {a b : ι}

theorem twoLevel_apply_of_not_mem_left (g : Matrix (Fin 2) (Fin 2) ℂ) {x : ι}
    (hx : ¬(x = a ∨ x = b)) (y : ι) : twoLevel a b g x y = if x = y then 1 else 0 := by
  simp [twoLevel, hx]

theorem twoLevel_apply_of_not_mem_right (g : Matrix (Fin 2) (Fin 2) ℂ) (x : ι) {y : ι}
    (hy : ¬(y = a ∨ y = b)) : twoLevel a b g x y = if x = y then 1 else 0 := by
  simp [twoLevel, hy]

theorem twoLevelIdx_self (a : ι) : twoLevelIdx a a = 0 := by simp [twoLevelIdx]

theorem twoLevelIdx_of_ne (hab : a ≠ b) : twoLevelIdx a b = 1 := by
  simp [twoLevelIdx, Ne.symm hab]

theorem twoLevel_mul [Fintype ι] (hab : a ≠ b) (g h : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevel a b g * twoLevel a b h = twoLevel a b (g * h) := by
  ext x y
  rw [mul_apply]
  by_cases hx : x = a ∨ x = b
  · by_cases hy : y = a ∨ y = b
    · rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ _) (Finset.mem_univ _) hab]
      · simp only [twoLevel, of_apply, hx, hy, true_or, or_true, and_self, ite_true,
          twoLevelIdx_self, twoLevelIdx_of_ne hab, mul_apply, Fin.sum_univ_two]
      · rintro z - ⟨hza, hzb⟩
        rw [twoLevel_apply_of_not_mem_right g x (by tauto)]
        rw [ite_eq_right (by rintro rfl; tauto), zero_mul]
    · rw [twoLevel_apply_of_not_mem_right _ x hy]
      simp_rw [twoLevel_apply_of_not_mem_right h _ hy]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [twoLevel_apply_of_not_mem_right _ x hy]
  · rw [twoLevel_apply_of_not_mem_left _ hx]
    simp_rw [twoLevel_apply_of_not_mem_left g hx]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [twoLevel_apply_of_not_mem_left _ hx]

@[simp] theorem twoLevel_one (a b : ι) : twoLevel a b (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext x y
  simp only [twoLevel, of_apply, one_apply]
  by_cases hxy : x = y
  · subst hxy; split_ifs <;> simp_all
  · have hidx : (x = a ∨ x = b) ∧ (y = a ∨ y = b) → twoLevelIdx a x ≠ twoLevelIdx a y := by
      rintro ⟨hx, hy⟩ h
      unfold twoLevelIdx at h
      split_ifs at h with h1 h2 h2 <;> simp_all
    split_ifs with h h' <;> first | rfl | exact absurd h' hxy | exact absurd h' (hidx h)

theorem twoLevel_conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (twoLevel a b g)ᴴ = twoLevel a b gᴴ := by
  ext x y
  simp only [conjTranspose_apply, twoLevel, of_apply]
  have hc : ((y = a ∨ y = b) ∧ (x = a ∨ x = b)) ↔ ((x = a ∨ x = b) ∧ (y = a ∨ y = b)) :=
    And.comm
  by_cases h : (x = a ∨ x = b) ∧ (y = a ∨ y = b)
  · rw [ite_eq_left (hc.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hc.1 h')), ite_eq_right h]
    by_cases hxy : y = x
    · subst hxy; simp
    · rw [ite_eq_right hxy, ite_eq_right (Ne.symm hxy), star_zero]

theorem twoLevel_mem_unitary [Fintype ι] (hab : a ≠ b) {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) :
    twoLevel a b g ∈ unitary (Matrix ι ι ℂ) := by
  rw [Unitary.mem_iff] at hg ⊢
  simp only [star_eq_conjTranspose] at hg ⊢
  rw [twoLevel_conjTranspose, twoLevel_mul hab, twoLevel_mul hab, hg.1, hg.2, twoLevel_one]
  exact ⟨rfl, rfl⟩

/-- Relabelling the basis by a permutation `σ` moves the two-level block to `σ⁻¹ a, σ⁻¹ b`. -/
theorem twoLevel_submatrix (σ : Equiv.Perm ι) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (twoLevel a b g).submatrix σ σ = twoLevel (σ.symm a) (σ.symm b) g := by
  ext x y
  simp only [submatrix_apply, twoLevel, of_apply, twoLevelIdx, Equiv.eq_symm_apply,
    EmbeddingLike.apply_eq_iff_eq]

/-- The two-level operator applied to a vector. -/
theorem twoLevel_mulVec_apply [Fintype ι] (hab : a ≠ b) (g : Matrix (Fin 2) (Fin 2) ℂ) (v : ι → ℂ)
    (x : ι) : (twoLevel a b g *ᵥ v) x =
      if x = a then g 0 0 * v a + g 0 1 * v b
      else if x = b then g 1 0 * v a + g 1 1 * v b else v x := by
  rw [mulVec, dotProduct]
  by_cases hx : x = a ∨ x = b
  · rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ _) (Finset.mem_univ _) hab]
    · rcases hx with rfl | rfl
      · simp [twoLevel, twoLevelIdx, hab, Ne.symm hab]
      · simp [twoLevel, twoLevelIdx, hab, Ne.symm hab]
    · rintro z - ⟨hza, hzb⟩
      rw [twoLevel_apply_of_not_mem_right g x (by tauto), ite_eq_right (by rintro rfl; tauto),
        zero_mul]
  · simp_rw [twoLevel_apply_of_not_mem_left g hx]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [ite_eq_right (fun h => hx (Or.inl h)), ite_eq_right (fun h => hx (Or.inr h))]

/-! ### Two-by-two matrices -/

/-- The real rotation `[[Re z, -Im z], [Im z, Re z]]` of the unit complex number `z`. -/
def rotTwo (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(z.re : ℂ), -(z.im : ℂ); (z.im : ℂ), (z.re : ℂ)]

/-- The diagonal phase `diag(ν, star ν)`. -/
def diagTwo (ν : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![ν, 0; 0, star ν]

/-- The phase `diag(i, -i)`. -/
def phaseTwo : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- The rotation by a quarter turn, `[[0, 1], [-1, 0]]`. -/
def quarterTwo : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem rotTwo_mul (z w : ℂ) : rotTwo z * rotTwo w = rotTwo (z * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotTwo, mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem rotTwo_one : rotTwo 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotTwo]

theorem rotTwo_conjTranspose (z : ℂ) : (rotTwo z)ᴴ = rotTwo (conj z) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotTwo, conjTranspose_apply]

theorem rotTwo_mem_unitary {z : ℂ} (hz : ‖z‖ = 1) :
    rotTwo z ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : conj z * z = 1 := by
    rw [Complex.conj_mul', hz]; simp
  have h2 : z * conj z = 1 := by rw [mul_comm, h1]
  rw [Unitary.mem_iff, star_eq_conjTranspose, rotTwo_conjTranspose, rotTwo_mul, rotTwo_mul, h1,
    h2, rotTwo_one]
  exact ⟨rfl, rfl⟩

theorem phaseTwo_mem_unitary : phaseTwo ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [phaseTwo, mul_apply, Fin.sum_univ_two, conjTranspose_apply]

theorem quarterTwo_mem_unitary : quarterTwo ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quarterTwo, mul_apply, Fin.sum_univ_two, conjTranspose_apply]

theorem diagTwo_mem_unitary {ν : ℂ} (hν : ‖ν‖ = 1) :
    diagTwo ν ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : conj ν * ν = 1 := by
    rw [Complex.conj_mul', hν]; simp
  have h2 : ν * conj ν = 1 := by rw [mul_comm, h1]
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagTwo, mul_apply, Fin.sum_univ_two, conjTranspose_apply, h1, h2]

/-- A rotation by `w²` is the group commutator of the rotation by `w` and `diag(i, -i)`. -/
theorem rotTwo_sq_eq_commutator {w : ℂ} :
    rotTwo (w * w) = rotTwo w * phaseTwo * rotTwo (conj w) * phaseTwoᴴ := by
  have h : phaseTwo * rotTwo (conj w) * phaseTwoᴴ = rotTwo w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phaseTwo, rotTwo, mul_apply, Fin.sum_univ_two, conjTranspose_apply] <;>
      ring_nf <;> simp [Complex.I_sq]
  rw [Matrix.mul_assoc (rotTwo w * phaseTwo), Matrix.mul_assoc (rotTwo w), ← Matrix.mul_assoc
    phaseTwo, h, rotTwo_mul]

/-- The phase `diag(w², (star w)²)` is the group commutator of `diag(w, star w)` and a quarter turn. -/
theorem diagTwo_sq_eq_commutator {w : ℂ} :
    diagTwo (w * w) = diagTwo w * quarterTwo * diagTwo (star w) * quarterTwoᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagTwo, quarterTwo, mul_apply, Fin.sum_univ_two, conjTranspose_apply]

end MPSPreparation
