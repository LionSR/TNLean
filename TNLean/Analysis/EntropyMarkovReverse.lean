/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.EntropyDecomposition
import TNLean.Analysis.HayashiMarkovStructure

/-!
# Reverse direction of the Hayashi strong-subadditivity equality characterization

This file proves that a quantum-Markov-chain (block-diagonal) state attains
equality in strong subadditivity, the reverse direction of the Hayashi
characterization. The forward direction (equality forces the block-diagonal
structure) remains a sanctioned axiom resting on Petz-recovery theory; see
`docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`.

## Strategy

A quantum-Markov-chain decomposition `HayashiMarkovDecomposition ρ_ABC` exhibits
`ρ_ABC`, after a unitary basis change on the middle system `B` and a reindexing,
as the block-diagonal direct sum
\(\bigoplus_j p_j (\rho_{A B_j^L} \otimes \rho_{B_j^R C})\). The four reduced
states and their entropies decompose through the additivity lemmas in
`TNLean.Analysis.EntropyDecomposition`, and the four entropy terms of strong
subadditivity cancel.

## References

* Hayashi, *Quantum Information: An Introduction*, Springer 2006, Theorem 5.24
* `docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex`
-/

open scoped Matrix Kronecker ComplexOrder
open Matrix Finset Real

namespace HayashiMarkov

variable {dA dB dC : ℕ} {m : ℕ} {dL dR : Fin m → ℕ}

/-! ## Entry formulas for the lifted unitary -/

/-- Entry formula for `liftB`. -/
theorem liftB_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (a a' : Fin dA) (b b' : Fin dB) (c c' : Fin dC) :
    liftB (dA := dA) (dC := dC) U_B (a, b, c) (a', b', c')
      = (if a = a' then 1 else 0) * U_B b b' * (if c = c' then 1 else 0) := by
  unfold liftB
  simp only [kroneckerMap_apply, Matrix.one_apply]
  ring

/-- Entry formula for `(liftB U_B) * ρ`. -/
theorem liftB_mul_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (a : Fin dA) (b : Fin dB) (c : Fin dC) (w : Fin dA × Fin dB × Fin dC) :
    (liftB (dA := dA) (dC := dC) U_B * ρ) (a, b, c) w
      = ∑ β : Fin dB, U_B b β * ρ (a, β, c) w := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a ?_ ?_]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_eq_single c ?_ ?_]
    · rw [liftB_apply, if_pos rfl, if_pos rfl, one_mul, mul_one]
    · intro c'' _ hc''
      rw [liftB_apply, if_neg (Ne.symm hc''), mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro a'' _ ha''
    refine Finset.sum_eq_zero fun bc _ => ?_
    obtain ⟨β, γ⟩ := bc
    rw [liftB_apply, if_neg (Ne.symm ha''), zero_mul, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Entry formula for `X * (liftB U_B)ᴴ`. -/
theorem mul_liftB_conjTranspose_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (X : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (z : Fin dA × Fin dB × Fin dC) (a' : Fin dA) (b' : Fin dB) (c' : Fin dC) :
    (X * (liftB (dA := dA) (dC := dC) U_B)ᴴ) z (a', b', c')
      = ∑ β' : Fin dB, X z (a', β', c') * (starRingEnd ℂ) (U_B b' β') := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a' ?_ ?_]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun β' _ => ?_
    rw [Finset.sum_eq_single c' ?_ ?_]
    · rw [Matrix.conjTranspose_apply, liftB_apply, if_pos rfl, if_pos rfl,
        one_mul, mul_one, Complex.star_def]
    · intro c'' _ hc''
      rw [Matrix.conjTranspose_apply, liftB_apply, if_neg (Ne.symm hc''), mul_zero]
      simp
    · intro h; exact absurd (Finset.mem_univ c') h
  · intro a'' _ ha''
    refine Finset.sum_eq_zero fun bc _ => ?_
    obtain ⟨β', γ⟩ := bc
    rw [Matrix.conjTranspose_apply, liftB_apply, if_neg (Ne.symm ha''), zero_mul]
    simp
  · intro h; exact absurd (Finset.mem_univ a') h

/-- Entry formula for the full conjugation `liftB U_B * ρ * (liftB U_B)ᴴ`. -/
theorem liftB_conj_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (a a' : Fin dA) (b b' : Fin dB) (c c' : Fin dC) :
    (liftB (dA := dA) (dC := dC) U_B * ρ * (liftB (dA := dA) (dC := dC) U_B)ᴴ)
        (a, b, c) (a', b', c')
      = ∑ β : Fin dB, ∑ β' : Fin dB,
          U_B b β * ρ (a, β, c) (a', β', c') * (starRingEnd ℂ) (U_B b' β') := by
  rw [mul_liftB_conjTranspose_apply]
  rw [show (∑ β' : Fin dB, (liftB (dA := dA) (dC := dC) U_B * ρ) (a, b, c) (a', β', c')
        * (starRingEnd ℂ) (U_B b' β'))
      = ∑ β' : Fin dB, ∑ β : Fin dB,
          U_B b β * ρ (a, β, c) (a', β', c') * (starRingEnd ℂ) (U_B b' β') from by
    refine Finset.sum_congr rfl fun β' _ => ?_
    rw [liftB_mul_apply, Finset.sum_mul]]
  rw [Finset.sum_comm]

/-- `liftB U_B` is in the unitary group when `U_B` is. -/
theorem liftB_mem_unitary (U_B : Matrix.unitaryGroup (Fin dB) ℂ) :
    liftB (dA := dA) (dC := dC) (U_B : Matrix (Fin dB) (Fin dB) ℂ)
      ∈ Matrix.unitaryGroup (Fin dA × Fin dB × Fin dC) ℂ := by
  unfold liftB
  exact Matrix.kronecker_mem_unitary (one_mem _)
    (Matrix.kronecker_mem_unitary U_B.2 (one_mem _))

/-! ## Entrywise value of the block-diagonal state -/

/-- Entrywise value of the block-diagonal quantum-Markov-chain state. The entry
between two indices vanishes unless their block labels agree, in which case it is
the weight times the product of the left and right component entries. -/
theorem blockState_apply (p : Fin m → ℝ)
    (ρ_left : (j : Fin m) → Matrix (Fin dA × Fin (dL j)) (Fin dA × Fin (dL j)) ℂ)
    (ρ_right : (j : Fin m) → Matrix (Fin (dR j) × Fin dC) (Fin (dR j) × Fin dC) ℂ)
    (a a' : Fin dA) (c c' : Fin dC)
    (j j' : Fin m) (lr : Fin (dL j) × Fin (dR j)) (lr' : Fin (dL j') × Fin (dR j')) :
    blockState (dA := dA) (dC := dC) dL dR p ρ_left ρ_right
        (a, (⟨j, lr⟩, c)) (a', (⟨j', lr'⟩, c'))
      = if h : j = j' then
          (p j : ℂ) * ρ_left j (a, lr.1) (a', h ▸ lr'.1)
            * ρ_right j (lr.2, c) (h ▸ lr'.2, c')
        else 0 := by
  classical
  rw [blockState]
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hidx1 : (sigmaAssoc (dA := dA) (dC := dC) dL dR).symm (a, (⟨j, lr⟩, c))
      = (⟨j, ((a, lr.1), (lr.2, c))⟩ :
        Σ j : Fin m, (Fin dA × Fin (dL j)) × (Fin (dR j) × Fin dC)) := rfl
  have hidx2 : (sigmaAssoc (dA := dA) (dC := dC) dL dR).symm (a', (⟨j', lr'⟩, c'))
      = (⟨j', ((a', lr'.1), (lr'.2, c'))⟩ :
        Σ j : Fin m, (Fin dA × Fin (dL j)) × (Fin (dR j) × Fin dC)) := rfl
  rw [hidx1, hidx2]
  by_cases h : j = j'
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq, dif_pos rfl]
    simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
    ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, dif_neg h]

/-! ## Partial-trace naturality of the lifted conjugation -/

/-- Tracing out A and C of the lifted conjugation is conjugation of the B-marginal
by `U_B`. -/
theorem traceAC_liftB_conj (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ) :
    Matrix.traceAC_ABC
        (liftB (dA := dA) (dC := dC) U_B * ρ * (liftB (dA := dA) (dC := dC) U_B)ᴴ)
      = U_B * Matrix.traceAC_ABC ρ * U_Bᴴ := by
  classical
  ext b₁ b₂
  rw [Matrix.traceAC_ABC]
  simp only [liftB_conj_apply]
  rw [Matrix.mul_apply]
  rw [show (∑ a : Fin dA, ∑ c : Fin dC, ∑ β : Fin dB, ∑ β' : Fin dB,
          U_B b₁ β * ρ (a, β, c) (a, β', c) * (starRingEnd ℂ) (U_B b₂ β'))
      = ∑ p : Fin dA × Fin dC, ∑ q : Fin dB × Fin dB,
          U_B b₁ q.1 * ρ (p.1, q.1, p.2) (p.1, q.2, p.2) * (starRingEnd ℂ) (U_B b₂ q.2)
        from by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [Fintype.sum_prod_type]]
  rw [show (∑ β : Fin dB, (U_B * Matrix.traceAC_ABC ρ) b₁ β * U_Bᴴ β b₂)
      = ∑ q : Fin dB × Fin dB, ∑ p : Fin dA × Fin dC,
          U_B b₁ q.1 * ρ (p.1, q.1, p.2) (p.1, q.2, p.2) * (starRingEnd ℂ) (U_B b₂ q.2)
        from by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun β'' _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Matrix.traceAC_ABC,
        Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]]
  rw [Finset.sum_comm]

/-! ## Reindexing of the block-diagonal marginals -/

/-- `traceAC` of the reindexed blockState equals a reindexing (via `decompB`) of
the block-diagonal of weighted Kronecker products of the A,C-traced components. -/
theorem traceAC_blockState_submatrix
    (decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j))
    (p : Fin m → ℝ)
    (ρ_left : (j : Fin m) → Matrix (Fin dA × Fin (dL j)) (Fin dA × Fin (dL j)) ℂ)
    (ρ_right : (j : Fin m) → Matrix (Fin (dR j) × Fin dC) (Fin (dR j) × Fin dC) ℂ) :
    Matrix.traceAC_ABC
        ((blockState (dA := dA) (dC := dC) dL dR p ρ_left ρ_right).submatrix
          (abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB)
          (abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB))
      = (Matrix.blockDiagonal' (fun j : Fin m =>
          (p j : ℂ) • (Matrix.traceLeft (ρ_left j) ⊗ₖ
            Matrix.traceRight (ρ_right j)))).submatrix
          decompB decompB := by
  classical
  ext b₁ b₂
  rw [Matrix.traceAC_ABC]
  have habc : ∀ (a : Fin dA) (b : Fin dB) (c : Fin dC),
      abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB (a, b, c) = (a, (decompB b, c)) := by
    intro a b c; rfl
  simp only [Matrix.submatrix_apply, habc, Matrix.blockDiagonal'_apply]
  rcases h₁ : decompB b₁ with ⟨j₁, l₁, r₁⟩
  rcases h₂ : decompB b₂ with ⟨j₂, l₂, r₂⟩
  simp only [blockState_apply]
  by_cases hj : j₁ = j₂
  · subst hj
    simp only [dif_pos, cast_eq]
    rw [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul,
      Matrix.traceLeft_apply, Matrix.traceRight_apply]
    rw [show (p j₁ : ℂ) * ((∑ x : Fin dA, ρ_left j₁ (x, l₁) (x, l₂))
          * ∑ x_1 : Fin dC, ρ_right j₁ (r₁, x_1) (r₂, x_1))
        = ∑ x : Fin dA, ∑ x_1 : Fin dC,
            (p j₁ : ℂ) * ρ_left j₁ (x, l₁) (x, l₂)
              * ρ_right j₁ (r₁, x_1) (r₂, x_1) from by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x_1 _ => ?_
      ring]
  · simp only [dif_neg hj, Finset.sum_const_zero]

/-! ## Entry formulas for `1_A ⊗ U_B` and `U_B ⊗ 1_C` -/

/-- Entry formula for `1_A ⊗ U_B` on `Fin dA × Fin dB`. -/
theorem liftAB_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ) (a a' : Fin dA) (b b' : Fin dB) :
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) U_B (a, b) (a', b')
      = (if a = a' then 1 else 0) * U_B b b' := by
  simp only [kroneckerMap_apply, Matrix.one_apply]

/-- Entry formula for `(1_A ⊗ U_B) * X`. -/
theorem liftAB_mul_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (a : Fin dA) (b : Fin dB) (w : Fin dA × Fin dB) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) U_B * X) (a, b) w
      = ∑ β : Fin dB, U_B b β * X (a, β) w := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a ?_ ?_]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [liftAB_apply, if_pos rfl, one_mul]
  · intro a'' _ ha''
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [liftAB_apply, if_neg (Ne.symm ha''), zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Entry formula for `X * (1_A ⊗ U_B)ᴴ`. -/
theorem mul_liftAB_conjTranspose_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (z : Fin dA × Fin dB) (a' : Fin dA) (b' : Fin dB) :
    (X * (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) U_B)ᴴ) z (a', b')
      = ∑ β' : Fin dB, X z (a', β') * (starRingEnd ℂ) (U_B b' β') := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a' ?_ ?_]
  · refine Finset.sum_congr rfl fun β' _ => ?_
    rw [Matrix.conjTranspose_apply, liftAB_apply, if_pos rfl, one_mul, Complex.star_def]
  · intro a'' _ ha''
    refine Finset.sum_eq_zero fun β' _ => ?_
    rw [Matrix.conjTranspose_apply, liftAB_apply, if_neg (Ne.symm ha''), zero_mul]
    simp
  · intro h; exact absurd (Finset.mem_univ a') h

/-- Conjugation entry formula for `(1_A ⊗ U_B) X (1_A ⊗ U_B)ᴴ` on `Fin dA × Fin dB`. -/
theorem liftAB_conj_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (a a' : Fin dA) (b b' : Fin dB) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) U_B * X
        * (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) U_B)ᴴ) (a, b) (a', b')
      = ∑ β : Fin dB, ∑ β' : Fin dB,
          U_B b β * X (a, β) (a', β') * (starRingEnd ℂ) (U_B b' β') := by
  rw [mul_liftAB_conjTranspose_apply]
  rw [show (∑ β' : Fin dB,
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) U_B * X) (a, b) (a', β')
          * (starRingEnd ℂ) (U_B b' β'))
      = ∑ β' : Fin dB, ∑ β : Fin dB,
          U_B b β * X (a, β) (a', β') * (starRingEnd ℂ) (U_B b' β') from by
    refine Finset.sum_congr rfl fun β' _ => ?_
    rw [liftAB_mul_apply, Finset.sum_mul]]
  rw [Finset.sum_comm]

/-- Entry formula for `U_B ⊗ 1_C` on `Fin dB × Fin dC`. -/
theorem liftBC_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ) (b b' : Fin dB) (c c' : Fin dC) :
    Matrix.kroneckerMap (· * ·) U_B (1 : Matrix (Fin dC) (Fin dC) ℂ) (b, c) (b', c')
      = U_B b b' * (if c = c' then 1 else 0) := by
  simp only [kroneckerMap_apply, Matrix.one_apply]

/-- Entry formula for `(U_B ⊗ 1_C) * X`. -/
theorem liftBC_mul_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (X : Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ)
    (b : Fin dB) (c : Fin dC) (w : Fin dB × Fin dC) :
    (Matrix.kroneckerMap (· * ·) U_B (1 : Matrix (Fin dC) (Fin dC) ℂ) * X) (b, c) w
      = ∑ β : Fin dB, U_B b β * X (β, c) w := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_eq_single c ?_ ?_]
  · rw [liftBC_apply, if_pos rfl, mul_one]
  · intro c'' _ hc''
    rw [liftBC_apply, if_neg (Ne.symm hc''), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ c) h

/-- Entry formula for `X * (U_B ⊗ 1_C)ᴴ`. -/
theorem mul_liftBC_conjTranspose_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (X : Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ)
    (z : Fin dB × Fin dC) (b' : Fin dB) (c' : Fin dC) :
    (X * (Matrix.kroneckerMap (· * ·) U_B (1 : Matrix (Fin dC) (Fin dC) ℂ))ᴴ) z (b', c')
      = ∑ β' : Fin dB, X z (β', c') * (starRingEnd ℂ) (U_B b' β') := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun β' _ => ?_
  rw [Finset.sum_eq_single c' ?_ ?_]
  · rw [Matrix.conjTranspose_apply, liftBC_apply, if_pos rfl, mul_one, Complex.star_def]
  · intro c'' _ hc''
    rw [Matrix.conjTranspose_apply, liftBC_apply, if_neg (Ne.symm hc''), mul_zero]
    simp
  · intro h; exact absurd (Finset.mem_univ c') h

/-- Conjugation entry formula for `(U_B ⊗ 1_C) X (U_B ⊗ 1_C)ᴴ` on `Fin dB × Fin dC`. -/
theorem liftBC_conj_apply (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (X : Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ)
    (b b' : Fin dB) (c c' : Fin dC) :
    (Matrix.kroneckerMap (· * ·) U_B (1 : Matrix (Fin dC) (Fin dC) ℂ) * X
        * (Matrix.kroneckerMap (· * ·) U_B (1 : Matrix (Fin dC) (Fin dC) ℂ))ᴴ) (b, c) (b', c')
      = ∑ β : Fin dB, ∑ β' : Fin dB,
          U_B b β * X (β, c) (β', c') * (starRingEnd ℂ) (U_B b' β') := by
  rw [mul_liftBC_conjTranspose_apply]
  rw [show (∑ β' : Fin dB,
        (Matrix.kroneckerMap (· * ·) U_B (1 : Matrix (Fin dC) (Fin dC) ℂ) * X) (b, c) (β', c')
          * (starRingEnd ℂ) (U_B b' β'))
      = ∑ β' : Fin dB, ∑ β : Fin dB,
          U_B b β * X (β, c) (β', c') * (starRingEnd ℂ) (U_B b' β') from by
    refine Finset.sum_congr rfl fun β' _ => ?_
    rw [liftBC_mul_apply, Finset.sum_mul]]
  rw [Finset.sum_comm]

/-- Tracing out C of the lifted conjugation is conjugation of the AB-marginal by
`1_A ⊗ U_B`. -/
theorem traceC_liftB_conj (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ) :
    Matrix.traceC_ABC
        (liftB (dA := dA) (dC := dC) U_B * ρ * (liftB (dA := dA) (dC := dC) U_B)ᴴ)
      = Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) U_B
          * Matrix.traceC_ABC ρ
          * (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ) U_B)ᴴ := by
  classical
  ext ab₁ ab₂
  obtain ⟨a₁, b₁⟩ := ab₁
  obtain ⟨a₂, b₂⟩ := ab₂
  rw [Matrix.traceC_ABC, liftAB_conj_apply]
  simp only [liftB_conj_apply]
  rw [show (∑ c : Fin dC, ∑ β : Fin dB, ∑ β' : Fin dB,
          U_B b₁ β * ρ (a₁, β, c) (a₂, β', c) * (starRingEnd ℂ) (U_B b₂ β'))
      = ∑ β : Fin dB, ∑ β' : Fin dB, ∑ c : Fin dC,
          U_B b₁ β * ρ (a₁, β, c) (a₂, β', c) * (starRingEnd ℂ) (U_B b₂ β') from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.sum_comm]]
  refine Finset.sum_congr rfl fun β _ => ?_
  refine Finset.sum_congr rfl fun β' _ => ?_
  rw [Matrix.traceC_ABC, Finset.mul_sum, Finset.sum_mul]

/-- Tracing out A of the lifted conjugation is conjugation of the BC-marginal by
`U_B ⊗ 1_C`. -/
theorem traceA_liftB_conj (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ) :
    Matrix.traceA_ABC
        (liftB (dA := dA) (dC := dC) U_B * ρ * (liftB (dA := dA) (dC := dC) U_B)ᴴ)
      = Matrix.kroneckerMap (· * ·) U_B (1 : Matrix (Fin dC) (Fin dC) ℂ)
          * Matrix.traceA_ABC ρ
          * (Matrix.kroneckerMap (· * ·) U_B (1 : Matrix (Fin dC) (Fin dC) ℂ))ᴴ := by
  classical
  ext bc₁ bc₂
  obtain ⟨b₁, c₁⟩ := bc₁
  obtain ⟨b₂, c₂⟩ := bc₂
  rw [Matrix.traceA_ABC, liftBC_conj_apply]
  simp only [liftB_conj_apply]
  rw [show (∑ a : Fin dA, ∑ β : Fin dB, ∑ β' : Fin dB,
          U_B b₁ β * ρ (a, β, c₁) (a, β', c₂) * (starRingEnd ℂ) (U_B b₂ β'))
      = ∑ β : Fin dB, ∑ β' : Fin dB, ∑ a : Fin dA,
          U_B b₁ β * ρ (a, β, c₁) (a, β', c₂) * (starRingEnd ℂ) (U_B b₂ β') from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.sum_comm]]
  refine Finset.sum_congr rfl fun β _ => ?_
  refine Finset.sum_congr rfl fun β' _ => ?_
  rw [Matrix.traceA_ABC, Finset.mul_sum, Finset.sum_mul]

/-! ## Reindexing equivalences for the AB- and BC-marginals -/

/-- The equivalence on the AB-index used to recognise `traceC` of the blockState
as a reindexed block-diagonal. -/
def cEquiv (decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j)) :
    (Fin dA × Fin dB) ≃ (Σ j : Fin m, (Fin dA × Fin (dL j)) × Fin (dR j)) :=
  calc (Fin dA × Fin dB) ≃ (Fin dA × Σ j : Fin m, Fin (dL j) × Fin (dR j)) :=
        Equiv.prodCongr (Equiv.refl _) decompB
    _ ≃ ((Σ j : Fin m, Fin (dL j) × Fin (dR j)) × Fin dA) := Equiv.prodComm _ _
    _ ≃ (Σ j : Fin m, (Fin (dL j) × Fin (dR j)) × Fin dA) := Equiv.sigmaProdDistrib _ _
    _ ≃ (Σ j : Fin m, (Fin dA × Fin (dL j)) × Fin (dR j)) :=
        Equiv.sigmaCongrRight (fun j =>
          (Equiv.prodComm _ _).trans
            ((Equiv.prodAssoc (Fin dA) (Fin (dL j)) (Fin (dR j))).symm))

theorem cEquiv_apply (decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j))
    (a : Fin dA) (b : Fin dB) :
    cEquiv (dA := dA) decompB (a, b)
      = ⟨(decompB b).1, ((a, (decompB b).2.1), (decompB b).2.2)⟩ := rfl

/-- The equivalence on the BC-index used to recognise `traceA` of the blockState
as a reindexed block-diagonal. -/
def aEquiv (decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j)) :
    (Fin dB × Fin dC) ≃ (Σ j : Fin m, Fin (dL j) × (Fin (dR j) × Fin dC)) :=
  calc (Fin dB × Fin dC) ≃ ((Σ j : Fin m, Fin (dL j) × Fin (dR j)) × Fin dC) :=
        Equiv.prodCongr decompB (Equiv.refl _)
    _ ≃ (Σ j : Fin m, (Fin (dL j) × Fin (dR j)) × Fin dC) := Equiv.sigmaProdDistrib _ _
    _ ≃ (Σ j : Fin m, Fin (dL j) × (Fin (dR j) × Fin dC)) :=
        Equiv.sigmaCongrRight (fun j =>
          Equiv.prodAssoc (Fin (dL j)) (Fin (dR j)) (Fin dC))

theorem aEquiv_apply (decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j))
    (b : Fin dB) (c : Fin dC) :
    aEquiv (dC := dC) decompB (b, c)
      = ⟨(decompB b).1, ((decompB b).2.1, ((decompB b).2.2, c))⟩ := rfl

/-- `traceC` of the reindexed blockState equals a reindexing (via `cEquiv`) of the
block-diagonal of weighted Kronecker products with the C-traced right components. -/
theorem traceC_blockState_submatrix
    (decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j))
    (p : Fin m → ℝ)
    (ρ_left : (j : Fin m) → Matrix (Fin dA × Fin (dL j)) (Fin dA × Fin (dL j)) ℂ)
    (ρ_right : (j : Fin m) → Matrix (Fin (dR j) × Fin dC) (Fin (dR j) × Fin dC) ℂ) :
    Matrix.traceC_ABC
        ((blockState (dA := dA) (dC := dC) dL dR p ρ_left ρ_right).submatrix
          (abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB)
          (abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB))
      = (Matrix.blockDiagonal' (fun j : Fin m =>
          (p j : ℂ) • ((ρ_left j) ⊗ₖ Matrix.traceRight (ρ_right j)))).submatrix
          (cEquiv (dA := dA) decompB) (cEquiv (dA := dA) decompB) := by
  classical
  ext ab₁ ab₂
  obtain ⟨a₁, b₁⟩ := ab₁
  obtain ⟨a₂, b₂⟩ := ab₂
  rw [Matrix.traceC_ABC]
  have habc : ∀ (a : Fin dA) (b : Fin dB) (c : Fin dC),
      abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB (a, b, c) = (a, (decompB b, c)) := by
    intro a b c; rfl
  simp only [Matrix.submatrix_apply, habc, cEquiv_apply, Matrix.blockDiagonal'_apply]
  rcases h₁ : decompB b₁ with ⟨j₁, l₁, r₁⟩
  rcases h₂ : decompB b₂ with ⟨j₂, l₂, r₂⟩
  simp only [blockState_apply]
  by_cases hj : j₁ = j₂
  · subst hj
    simp only [dif_pos, cast_eq]
    rw [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul, Matrix.traceRight_apply]
    rw [show (p j₁ : ℂ) * (ρ_left j₁ (a₁, l₁) (a₂, l₂)
          * ∑ x : Fin dC, ρ_right j₁ (r₁, x) (r₂, x))
        = ∑ c : Fin dC,
            (p j₁ : ℂ) * ρ_left j₁ (a₁, l₁) (a₂, l₂)
              * ρ_right j₁ (r₁, c) (r₂, c) from by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring]
  · simp only [dif_neg hj, Finset.sum_const_zero]

/-- `traceA` of the reindexed blockState equals a reindexing (via `aEquiv`) of the
block-diagonal of weighted Kronecker products with the A-traced left components. -/
theorem traceA_blockState_submatrix
    (decompB : Fin dB ≃ Σ j : Fin m, Fin (dL j) × Fin (dR j))
    (p : Fin m → ℝ)
    (ρ_left : (j : Fin m) → Matrix (Fin dA × Fin (dL j)) (Fin dA × Fin (dL j)) ℂ)
    (ρ_right : (j : Fin m) → Matrix (Fin (dR j) × Fin dC) (Fin (dR j) × Fin dC) ℂ) :
    Matrix.traceA_ABC
        ((blockState (dA := dA) (dC := dC) dL dR p ρ_left ρ_right).submatrix
          (abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB)
          (abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB))
      = (Matrix.blockDiagonal' (fun j : Fin m =>
          (p j : ℂ) • (Matrix.traceLeft (ρ_left j) ⊗ₖ (ρ_right j)))).submatrix
          (aEquiv (dC := dC) decompB) (aEquiv (dC := dC) decompB) := by
  classical
  ext bc₁ bc₂
  obtain ⟨b₁, c₁⟩ := bc₁
  obtain ⟨b₂, c₂⟩ := bc₂
  rw [Matrix.traceA_ABC]
  have habc : ∀ (a : Fin dA) (b : Fin dB) (c : Fin dC),
      abcEquiv (dA := dA) (dB := dB) (dC := dC) decompB (a, b, c) = (a, (decompB b, c)) := by
    intro a b c; rfl
  simp only [Matrix.submatrix_apply, habc, aEquiv_apply, Matrix.blockDiagonal'_apply]
  rcases h₁ : decompB b₁ with ⟨j₁, l₁, r₁⟩
  rcases h₂ : decompB b₂ with ⟨j₂, l₂, r₂⟩
  simp only [blockState_apply]
  by_cases hj : j₁ = j₂
  · subst hj
    simp only [dif_pos, cast_eq]
    rw [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul, Matrix.traceLeft_apply]
    rw [show (p j₁ : ℂ) * ((∑ x : Fin dA, ρ_left j₁ (x, l₁) (x, l₂))
          * ρ_right j₁ (r₁, c₁) (r₂, c₂))
        = ∑ a : Fin dA,
            (p j₁ : ℂ) * ρ_left j₁ (a, l₁) (a, l₂)
              * ρ_right j₁ (r₁, c₁) (r₂, c₂) from by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring]
  · simp only [dif_neg hj, Finset.sum_const_zero]

end HayashiMarkov

/-! ## Entropy of weighted Kronecker blocks -/

/-- A Kronecker product of two density matrices is a density matrix. -/
theorem kronecker_density {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {L : Matrix m m ℂ} {R : Matrix n n ℂ}
    (hL : L.PosSemidef) (hR : R.PosSemidef) (hLt : L.trace = 1) (hRt : R.trace = 1) :
    (L ⊗ₖ R).PosSemidef ∧ (L ⊗ₖ R).trace = 1 := by
  refine ⟨hL.kronecker hR, ?_⟩
  rw [Matrix.trace_kronecker, hLt, hRt, mul_one]

/-- The entropy of a single weighted Kronecker block. -/
theorem entropy_smul_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {L : Matrix m m ℂ} {R : Matrix n n ℂ}
    (hL : L.PosSemidef) (hR : R.PosSemidef) (hLt : L.trace = 1) (hRt : R.trace = 1)
    (c : ℝ) (hHerm : ((c : ℂ) • (L ⊗ₖ R)).IsHermitian) :
    vonNeumannEntropy ((c : ℂ) • (L ⊗ₖ R)) hHerm
      = negMulLog c + c * (vonNeumannEntropy L hL.isHermitian + vonNeumannEntropy R hR.isHermitian)
      := by
  obtain ⟨hkron, hkront⟩ := kronecker_density hL hR hLt hRt
  rw [vonNeumannEntropy_congr rfl hHerm
    (hkron.isHermitian.smul (k := (c : ℂ))
      (isSelfAdjoint_iff.mpr (by rw [RCLike.star_def, Complex.conj_ofReal])))]
  rw [vonNeumannEntropy_smul hkron hkront c]
  rw [vonNeumannEntropy_kronecker hL hR hLt hRt]
  ring

/-- The entropy of a block-diagonal sum of weighted Kronecker blocks. -/
theorem entropy_blockDiagonal_smul_kronecker {o : Type*} [Fintype o] [DecidableEq o]
    {mL mR : o → Type*} [∀ j, Fintype (mL j)] [∀ j, DecidableEq (mL j)]
    [∀ j, Fintype (mR j)] [∀ j, DecidableEq (mR j)]
    (p : o → ℝ) (L : ∀ j, Matrix (mL j) (mL j) ℂ) (R : ∀ j, Matrix (mR j) (mR j) ℂ)
    (hL : ∀ j, (L j).PosSemidef) (hR : ∀ j, (R j).PosSemidef)
    (hLt : ∀ j, (L j).trace = 1) (hRt : ∀ j, (R j).trace = 1)
    (hHerm : (Matrix.blockDiagonal'
      (fun j => (p j : ℂ) • ((L j) ⊗ₖ (R j)))).IsHermitian) :
    vonNeumannEntropy (Matrix.blockDiagonal'
        (fun j => (p j : ℂ) • ((L j) ⊗ₖ (R j)))) hHerm
      = ∑ j, (negMulLog (p j)
          + p j * (vonNeumannEntropy (L j) (hL j).isHermitian
              + vonNeumannEntropy (R j) (hR j).isHermitian)) := by
  have hBlockHerm : ∀ j, ((p j : ℂ) • ((L j) ⊗ₖ (R j))).IsHermitian := fun j =>
    ((hL j).kronecker (hR j)).isHermitian.smul (k := (p j : ℂ))
      (isSelfAdjoint_iff.mpr (by rw [RCLike.star_def, Complex.conj_ofReal]))
  rw [vonNeumannEntropy_blockDiagonal' _ hBlockHerm hHerm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [entropy_smul_kronecker (hL j) (hR j) (hLt j) (hRt j) (p j) (hBlockHerm j)]

/-! ## Entropy invariance under conjugation by a unitary-group element -/

/-- The von Neumann entropy is invariant under conjugation `W X Wᴴ` by a
unitary-group element `W`. -/
theorem vonNeumannEntropy_unitaryGroup_conj {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix.unitaryGroup n ℂ) {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (hconj : ((W : Matrix n n ℂ) * X * (W : Matrix n n ℂ)ᴴ).IsHermitian) :
    vonNeumannEntropy ((W : Matrix n n ℂ) * X * (W : Matrix n n ℂ)ᴴ) hconj
      = vonNeumannEntropy X hX := by
  have hWmulstar : (W : Matrix n n ℂ) * star (W : Matrix n n ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp W.2
  have hstarmulW : star (W : Matrix n n ℂ) * (W : Matrix n n ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp W.2
  set Wu : (Matrix n n ℂ)ˣ :=
    ⟨(W : Matrix n n ℂ), star (W : Matrix n n ℂ), hWmulstar, hstarmulW⟩ with hWu
  have hWinv : Wu.val⁻¹ = (W : Matrix n n ℂ)ᴴ := by
    rw [← Matrix.coe_units_inv Wu]; rfl
  have heq : (W : Matrix n n ℂ) * X * (W : Matrix n n ℂ)ᴴ = Wu.val * X * Wu.val⁻¹ := by
    rw [hWinv]
  have hconj' : (Wu.val * X * Wu.val⁻¹).IsHermitian := by rw [← heq]; exact hconj
  rw [vonNeumannEntropy_congr heq hconj hconj']
  exact vonNeumannEntropy_units_conj Wu hX hconj'

/-! ## Density properties of the partial traces of the component states -/

/-- The left partial trace of a density matrix is a density matrix. -/
theorem traceLeft_density {d d' : ℕ} {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : ρ.PosSemidef) (hρt : ρ.trace = 1) :
    (Matrix.traceLeft ρ).PosSemidef ∧ (Matrix.traceLeft ρ).trace = 1 :=
  ⟨hρ.traceLeft, by rw [← Matrix.trace_eq_trace_traceLeft, hρt]⟩

/-- The right partial trace of a density matrix is a density matrix. -/
theorem traceRight_density {d d' : ℕ} {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : ρ.PosSemidef) (hρt : ρ.trace = 1) :
    (Matrix.traceRight ρ).PosSemidef ∧ (Matrix.traceRight ρ).trace = 1 :=
  ⟨hρ.traceRight, by rw [Matrix.traceRight, Matrix.trace_partialTraceRight, hρt]⟩

/-! ## Entropy of a reindexed block-diagonal of weighted Kronecker blocks

This packages the chain `entropy of a submatrix-reindexed block-diagonal = entropy
of the block-diagonal = block formula`, used by each of the four entropy terms. -/

/-- The entropy of a reindexed block-diagonal of weighted Kronecker blocks of
density matrices equals the block formula. -/
theorem entropy_submatrix_blockDiagonal_smul_kronecker {o : Type*} [Fintype o] [DecidableEq o]
    {mL mR : o → Type*} [∀ j, Fintype (mL j)] [∀ j, DecidableEq (mL j)]
    [∀ j, Fintype (mR j)] [∀ j, DecidableEq (mR j)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι ≃ Σ j, mL j × mR j)
    (p : o → ℝ) (L : ∀ j, Matrix (mL j) (mL j) ℂ) (R : ∀ j, Matrix (mR j) (mR j) ℂ)
    (hL : ∀ j, (L j).PosSemidef) (hR : ∀ j, (R j).PosSemidef)
    (hLt : ∀ j, (L j).trace = 1) (hRt : ∀ j, (R j).trace = 1)
    (hHerm : ((Matrix.blockDiagonal'
        (fun j => (p j : ℂ) • ((L j) ⊗ₖ (R j)))).submatrix φ φ).IsHermitian) :
    vonNeumannEntropy ((Matrix.blockDiagonal'
        (fun j => (p j : ℂ) • ((L j) ⊗ₖ (R j)))).submatrix φ φ) hHerm
      = ∑ j, (negMulLog (p j)
          + p j * (vonNeumannEntropy (L j) (hL j).isHermitian
              + vonNeumannEntropy (R j) (hR j).isHermitian)) := by
  have hBlockHerm : (Matrix.blockDiagonal'
      (fun j => (p j : ℂ) • ((L j) ⊗ₖ (R j)))).IsHermitian := by
    rw [Matrix.isHermitian_blockDiagonal'_iff]
    exact fun j => ((hL j).kronecker (hR j)).isHermitian.smul (k := (p j : ℂ))
      (isSelfAdjoint_iff.mpr (by rw [RCLike.star_def, Complex.conj_ofReal]))
  rw [vonNeumannEntropy_congr rfl hHerm ((isHermitian_submatrix_equiv φ).mpr hBlockHerm)]
  rw [vonNeumannEntropy_submatrix_equiv φ _ hBlockHerm]
  exact entropy_blockDiagonal_smul_kronecker p L R hL hR hLt hRt hBlockHerm


/-! ## Reverse direction of the Hayashi strong-subadditivity equality characterization -/

/-- **Reverse direction of the Hayashi characterization of strong-subadditivity
equality.** A tripartite density matrix that admits a quantum-Markov-chain
decomposition attains equality in strong subadditivity.

After the unitary basis change on the middle system and the reindexing recorded
by the decomposition, the state is the block-diagonal direct sum
\(\bigoplus_j p_j (\rho_{A B_j^L} \otimes \rho_{B_j^R C})\). Each of the four
reduced-state entropies decomposes through the additivity lemmas as a Shannon
term \(H(\{p_j\})\) plus a weighted sum of component entropies, and the four
terms of strong subadditivity cancel.

Source: Hayashi, *Quantum Information: An Introduction*, Springer 2006,
Theorem 5.24; blueprint `thm:hayashi_ssa_equality_characterization` (reverse
implication). -/
theorem hayashi_ssa_equality_characterization_reverse {dA dB dC : ℕ}
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    Nonempty (HayashiMarkovDecomposition ρ_ABC) → IsSSAEquality ρ_ABC hρ_dm.1.isHermitian := by
  rintro ⟨H⟩
  classical
  -- Abbreviations from the decomposition data.
  set e := HayashiMarkov.abcEquiv (dA := dA) (dB := dB) (dC := dC) H.decompB with he
  set L := HayashiMarkov.liftB (dA := dA) (dC := dC) (H.U_B : Matrix (Fin dB) (Fin dB) ℂ) with hL
  set M := L * ρ_ABC * Lᴴ with hM
  -- `M` is the reindexed block-diagonal state.
  have hMsub : M = (HayashiMarkov.blockState (dA := dA) (dC := dC)
      H.dL H.dR H.p H.ρ_left H.ρ_right).submatrix e e := by
    have hst := H.h_state
    rw [Matrix.reindex_apply] at hst
    rw [← hM, ← he] at hst
    have h2 := congrArg (fun X => X.submatrix e e) hst
    simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] at h2
    exact h2
  -- Density facts for the components.
  have hLdm := H.hρ_left_dm
  have hRdm := H.hρ_right_dm
  have hHermAC := Matrix.traceAC_ABC_isHermitian hρ_dm.1.isHermitian
  -- `U_B (traceAC ρ_ABC) U_Bᴴ` equals the reindexed block-diagonal.
  have hAC_eq : (H.U_B : Matrix (Fin dB) (Fin dB) ℂ) * Matrix.traceAC_ABC ρ_ABC
        * (H.U_B : Matrix (Fin dB) (Fin dB) ℂ)ᴴ
      = (Matrix.blockDiagonal' (fun j : Fin H.m =>
          (H.p j : ℂ) • (Matrix.traceLeft (H.ρ_left j) ⊗ₖ
            Matrix.traceRight (H.ρ_right j)))).submatrix H.decompB H.decompB := by
    rw [← HayashiMarkov.traceAC_liftB_conj (H.U_B : Matrix (Fin dB) (Fin dB) ℂ) ρ_ABC,
      ← hL, ← hM, hMsub, he]
    exact HayashiMarkov.traceAC_blockState_submatrix _ _ _ _
  -- Block-diagonal entropy of `traceAC ρ_ABC`.
  have hHermBD_AC : ((Matrix.blockDiagonal' (fun j : Fin H.m =>
        (H.p j : ℂ) • (Matrix.traceLeft (H.ρ_left j) ⊗ₖ
          Matrix.traceRight (H.ρ_right j)))).submatrix H.decompB H.decompB).IsHermitian :=
    (isHermitian_submatrix_equiv H.decompB).mpr (by
      rw [Matrix.isHermitian_blockDiagonal'_iff]
      exact fun j => (((traceLeft_density (hLdm j).1 (hLdm j).2).1.kronecker
        (traceRight_density (hRdm j).1 (hRdm j).2).1).isHermitian.smul (k := (H.p j : ℂ))
        (isSelfAdjoint_iff.mpr (by rw [RCLike.star_def, Complex.conj_ofReal]))))
  have hConjAC : ((H.U_B : Matrix (Fin dB) (Fin dB) ℂ) * Matrix.traceAC_ABC ρ_ABC
      * (H.U_B : Matrix (Fin dB) (Fin dB) ℂ)ᴴ).IsHermitian := by
    rw [hAC_eq]; exact hHermBD_AC
  have hAC : vonNeumannEntropy (Matrix.traceAC_ABC ρ_ABC) hHermAC
      = ∑ j, (negMulLog (H.p j)
          + H.p j * (vonNeumannEntropy (Matrix.traceLeft (H.ρ_left j))
              (traceLeft_density (hLdm j).1 (hLdm j).2).1.isHermitian
            + vonNeumannEntropy (Matrix.traceRight (H.ρ_right j))
              (traceRight_density (hRdm j).1 (hRdm j).2).1.isHermitian)) := by
    rw [← vonNeumannEntropy_unitaryGroup_conj H.U_B hHermAC hConjAC]
    rw [vonNeumannEntropy_congr hAC_eq hConjAC hHermBD_AC]
    rw [entropy_submatrix_blockDiagonal_smul_kronecker H.decompB H.p
      (fun j => Matrix.traceLeft (H.ρ_left j)) (fun j => Matrix.traceRight (H.ρ_right j))
      (fun j => (traceLeft_density (hLdm j).1 (hLdm j).2).1)
      (fun j => (traceRight_density (hRdm j).1 (hRdm j).2).1)
      (fun j => (traceLeft_density (hLdm j).1 (hLdm j).2).2)
      (fun j => (traceRight_density (hRdm j).1 (hRdm j).2).2) hHermBD_AC]
  -- Entropy of `ρ_ABC` itself.
  set φ0 := e.trans (HayashiMarkov.sigmaAssoc (dA := dA) (dC := dC) H.dL H.dR).symm with hφ0
  have hM_eq : M = (Matrix.blockDiagonal' (fun j : Fin H.m =>
      (H.p j : ℂ) • ((H.ρ_left j) ⊗ₖ (H.ρ_right j)))).submatrix φ0 φ0 := by
    rw [hMsub, HayashiMarkov.blockState, Matrix.reindex_apply, Matrix.submatrix_submatrix,
      hφ0]
    rfl
  have hWfull : L ∈ Matrix.unitaryGroup (Fin dA × Fin dB × Fin dC) ℂ := by
    rw [hL]; exact HayashiMarkov.liftB_mem_unitary H.U_B
  set Wfull : Matrix.unitaryGroup (Fin dA × Fin dB × Fin dC) ℂ := ⟨L, hWfull⟩ with hWfulldef
  have hHermBD0 : ((Matrix.blockDiagonal' (fun j : Fin H.m =>
        (H.p j : ℂ) • ((H.ρ_left j) ⊗ₖ (H.ρ_right j)))).submatrix φ0 φ0).IsHermitian :=
    (isHermitian_submatrix_equiv φ0).mpr (by
      rw [Matrix.isHermitian_blockDiagonal'_iff]
      exact fun j => (((hLdm j).1.kronecker (hRdm j).1).isHermitian.smul (k := (H.p j : ℂ))
        (isSelfAdjoint_iff.mpr (by rw [RCLike.star_def, Complex.conj_ofReal]))))
  set WfullM : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ :=
    (Wfull : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ) with hWfullM
  have hConjFull : (WfullM * ρ_ABC * WfullMᴴ).IsHermitian := by
    show (L * ρ_ABC * Lᴴ).IsHermitian
    rw [← hM, hM_eq]; exact hHermBD0
  have hABC : vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
      = ∑ j, (negMulLog (H.p j)
          + H.p j * (vonNeumannEntropy (H.ρ_left j) (hLdm j).1.isHermitian
            + vonNeumannEntropy (H.ρ_right j) (hRdm j).1.isHermitian)) := by
    rw [← vonNeumannEntropy_unitaryGroup_conj Wfull hρ_dm.1.isHermitian hConjFull]
    have hWconj : WfullM * ρ_ABC * WfullMᴴ
        = (Matrix.blockDiagonal' (fun j : Fin H.m =>
          (H.p j : ℂ) • ((H.ρ_left j) ⊗ₖ (H.ρ_right j)))).submatrix φ0 φ0 := by
      show L * ρ_ABC * Lᴴ = _
      rw [← hM, hM_eq]
    rw [vonNeumannEntropy_congr hWconj hConjFull hHermBD0]
    rw [entropy_submatrix_blockDiagonal_smul_kronecker φ0 H.p H.ρ_left H.ρ_right
      (fun j => (hLdm j).1) (fun j => (hRdm j).1)
      (fun j => (hLdm j).2) (fun j => (hRdm j).2) hHermBD0]
  -- Entropy of `traceC ρ_ABC = ρ_AB`.
  have hHermC := Matrix.traceC_ABC_isHermitian hρ_dm.1.isHermitian
  have hC_eq : Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ)
        (H.U_B : Matrix (Fin dB) (Fin dB) ℂ) * Matrix.traceC_ABC ρ_ABC
        * (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ)
          (H.U_B : Matrix (Fin dB) (Fin dB) ℂ))ᴴ
      = (Matrix.blockDiagonal' (fun j : Fin H.m =>
          (H.p j : ℂ) • ((H.ρ_left j) ⊗ₖ
            Matrix.traceRight (H.ρ_right j)))).submatrix
          (HayashiMarkov.cEquiv (dA := dA) H.decompB)
          (HayashiMarkov.cEquiv (dA := dA) H.decompB) := by
    rw [← HayashiMarkov.traceC_liftB_conj (H.U_B : Matrix (Fin dB) (Fin dB) ℂ) ρ_ABC,
      ← hL, ← hM, hMsub, he]
    exact HayashiMarkov.traceC_blockState_submatrix _ _ _ _
  have hWC : Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ)
      (H.U_B : Matrix (Fin dB) (Fin dB) ℂ) ∈ Matrix.unitaryGroup (Fin dA × Fin dB) ℂ :=
    Matrix.kronecker_mem_unitary (one_mem _) H.U_B.2
  set WC : Matrix.unitaryGroup (Fin dA × Fin dB) ℂ :=
    ⟨Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ)
      (H.U_B : Matrix (Fin dB) (Fin dB) ℂ), hWC⟩ with hWCdef
  have hHermBD_C : ((Matrix.blockDiagonal' (fun j : Fin H.m =>
        (H.p j : ℂ) • ((H.ρ_left j) ⊗ₖ Matrix.traceRight (H.ρ_right j)))).submatrix
        (HayashiMarkov.cEquiv (dA := dA) H.decompB)
        (HayashiMarkov.cEquiv (dA := dA) H.decompB)).IsHermitian :=
    (isHermitian_submatrix_equiv _).mpr (by
      rw [Matrix.isHermitian_blockDiagonal'_iff]
      exact fun j => (((hLdm j).1.kronecker
        (traceRight_density (hRdm j).1 (hRdm j).2).1).isHermitian.smul (k := (H.p j : ℂ))
        (isSelfAdjoint_iff.mpr (by rw [RCLike.star_def, Complex.conj_ofReal]))))
  have hConjC : ((WC : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) * Matrix.traceC_ABC ρ_ABC
      * (WC : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)ᴴ).IsHermitian := by
    show (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin dA) (Fin dA) ℂ)
      (H.U_B : Matrix (Fin dB) (Fin dB) ℂ) * _ * _).IsHermitian
    rw [hC_eq]; exact hHermBD_C
  have hC : vonNeumannEntropy (Matrix.traceC_ABC ρ_ABC) hHermC
      = ∑ j, (negMulLog (H.p j)
          + H.p j * (vonNeumannEntropy (H.ρ_left j) (hLdm j).1.isHermitian
            + vonNeumannEntropy (Matrix.traceRight (H.ρ_right j))
              (traceRight_density (hRdm j).1 (hRdm j).2).1.isHermitian)) := by
    rw [← vonNeumannEntropy_unitaryGroup_conj WC hHermC hConjC]
    rw [vonNeumannEntropy_congr hC_eq hConjC hHermBD_C]
    rw [entropy_submatrix_blockDiagonal_smul_kronecker
      (HayashiMarkov.cEquiv (dA := dA) H.decompB) H.p H.ρ_left
      (fun j => Matrix.traceRight (H.ρ_right j))
      (fun j => (hLdm j).1) (fun j => (traceRight_density (hRdm j).1 (hRdm j).2).1)
      (fun j => (hLdm j).2) (fun j => (traceRight_density (hRdm j).1 (hRdm j).2).2) hHermBD_C]
  -- Entropy of `traceA ρ_ABC = ρ_BC`.
  have hHermA := Matrix.traceA_ABC_isHermitian hρ_dm.1.isHermitian
  have hA_eq : Matrix.kroneckerMap (· * ·) (H.U_B : Matrix (Fin dB) (Fin dB) ℂ)
        (1 : Matrix (Fin dC) (Fin dC) ℂ) * Matrix.traceA_ABC ρ_ABC
        * (Matrix.kroneckerMap (· * ·) (H.U_B : Matrix (Fin dB) (Fin dB) ℂ)
          (1 : Matrix (Fin dC) (Fin dC) ℂ))ᴴ
      = (Matrix.blockDiagonal' (fun j : Fin H.m =>
          (H.p j : ℂ) • (Matrix.traceLeft (H.ρ_left j) ⊗ₖ
            (H.ρ_right j)))).submatrix
          (HayashiMarkov.aEquiv (dC := dC) H.decompB)
          (HayashiMarkov.aEquiv (dC := dC) H.decompB) := by
    rw [← HayashiMarkov.traceA_liftB_conj (H.U_B : Matrix (Fin dB) (Fin dB) ℂ) ρ_ABC,
      ← hL, ← hM, hMsub, he]
    exact HayashiMarkov.traceA_blockState_submatrix _ _ _ _
  have hWA : Matrix.kroneckerMap (· * ·) (H.U_B : Matrix (Fin dB) (Fin dB) ℂ)
      (1 : Matrix (Fin dC) (Fin dC) ℂ) ∈ Matrix.unitaryGroup (Fin dB × Fin dC) ℂ :=
    Matrix.kronecker_mem_unitary H.U_B.2 (one_mem _)
  set WA : Matrix.unitaryGroup (Fin dB × Fin dC) ℂ :=
    ⟨Matrix.kroneckerMap (· * ·) (H.U_B : Matrix (Fin dB) (Fin dB) ℂ)
      (1 : Matrix (Fin dC) (Fin dC) ℂ), hWA⟩ with hWAdef
  have hHermBD_A : ((Matrix.blockDiagonal' (fun j : Fin H.m =>
        (H.p j : ℂ) • (Matrix.traceLeft (H.ρ_left j) ⊗ₖ (H.ρ_right j)))).submatrix
        (HayashiMarkov.aEquiv (dC := dC) H.decompB)
        (HayashiMarkov.aEquiv (dC := dC) H.decompB)).IsHermitian :=
    (isHermitian_submatrix_equiv _).mpr (by
      rw [Matrix.isHermitian_blockDiagonal'_iff]
      exact fun j => (((traceLeft_density (hLdm j).1 (hLdm j).2).1.kronecker
        (hRdm j).1).isHermitian.smul (k := (H.p j : ℂ))
        (isSelfAdjoint_iff.mpr (by rw [RCLike.star_def, Complex.conj_ofReal]))))
  have hConjA : ((WA : Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ) * Matrix.traceA_ABC ρ_ABC
      * (WA : Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ)ᴴ).IsHermitian := by
    show (Matrix.kroneckerMap (· * ·) (H.U_B : Matrix (Fin dB) (Fin dB) ℂ)
      (1 : Matrix (Fin dC) (Fin dC) ℂ) * _ * _).IsHermitian
    rw [hA_eq]; exact hHermBD_A
  have hA : vonNeumannEntropy (Matrix.traceA_ABC ρ_ABC) hHermA
      = ∑ j, (negMulLog (H.p j)
          + H.p j * (vonNeumannEntropy (Matrix.traceLeft (H.ρ_left j))
              (traceLeft_density (hLdm j).1 (hLdm j).2).1.isHermitian
            + vonNeumannEntropy (H.ρ_right j) (hRdm j).1.isHermitian)) := by
    rw [← vonNeumannEntropy_unitaryGroup_conj WA hHermA hConjA]
    rw [vonNeumannEntropy_congr hA_eq hConjA hHermBD_A]
    rw [entropy_submatrix_blockDiagonal_smul_kronecker
      (HayashiMarkov.aEquiv (dC := dC) H.decompB) H.p
      (fun j => Matrix.traceLeft (H.ρ_left j)) H.ρ_right
      (fun j => (traceLeft_density (hLdm j).1 (hLdm j).2).1) (fun j => (hRdm j).1)
      (fun j => (traceLeft_density (hLdm j).1 (hLdm j).2).2) (fun j => (hRdm j).2) hHermBD_A]
  -- Assemble: both sides equal the same per-block sum.
  rw [IsSSAEquality, hABC, hAC, hC, hA, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
