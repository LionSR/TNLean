/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.MPS.MPDO.OperatorCyclicSum
import TNLean.MPS.MPU.Basic
import TNLean.MPS.MPU.SourceCuts

/-!
# A tensor that is unitary on odd rings only

The tensor of Sahinoglu, Shukla, Bi and Chen (arXiv:1704.01943, Section 6, Figure `M_f`) has
physical and bond dimension three, with indices in `Fin 3` read as `ℤ/3`, and letters
$$M^{ij}=|{-(i+j)})(j|.$$
Its periodic operator on `N` sites is the matrix of the map $j\mapsto i$ with
$i_n=-(j_{n-1}+j_n)$. For odd `N` this map is a bijection, so the operator is a permutation
matrix and unitary; at `N = 2` the inputs `(0, 1)` and `(1, 0)` have the same image `(2, 2)`, so
the tensor is not a matrix product unitary. Its source ranks are `r = 9` and `ℓ = 3`, so
`r ℓ = 27 ≠ d ^ 2`.

The figure's labels `1, 2, 3` are `0, 1, 2` here, and the closed form `-(i + j)` of the figure's
rule (the third index for `i ≠ j`, and `j` for `i = j`) is ours. The kernel argument for
unitarity on odd rings is ours; the source asserts the unitarity without a written proof.

## Main results

* `MPOTensor.mpo_oddRingTensor_apply`: the periodic operator as the matrix of the map.
* `MPOTensor.mpo_oddRingTensor_mem_unitaryGroup_of_odd`: unitarity on odd rings.
* `MPOTensor.mpo_oddRingTensor_not_mem_unitaryGroup_of_even`: non-unitarity on even rings.
* `MPOTensor.not_isMPU_oddRingTensor`: the tensor is not a matrix product unitary.
* `MPOTensor.rightRank_oddRingTensor`, `MPOTensor.leftRank_oddRingTensor`: `r = 9`, `ℓ = 3`.

## References

* Sahinoglu, Shukla, Bi, Chen, *Matrix product representation of locality preserving
  unitaries*, arXiv:1704.01943, Section 6.
-/

open scoped Matrix

namespace MPOTensor

/-- The odd-ring tensor of Sahinoglu, Shukla, Bi and Chen (arXiv:1704.01943, Section 6,
Figure `M_f`): `M^{ij} = |-(i+j))(j|` over `Fin 3` with its ring structure. -/
noncomputable def oddRingTensor : MPOTensor 3 3 :=
  fun i j => Matrix.single (-(i + j)) j 1

/-- The entries of the odd-ring tensor. -/
theorem oddRingTensor_apply (i j α β : Fin 3) :
    oddRingTensor i j α β = if -(i + j) = α ∧ j = β then 1 else 0 := rfl

/-- **The periodic operator of the odd-ring tensor** is the matrix of the map
$j\mapsto i$, $i_n=-(j_{n-1}+j_n)$ (arXiv:1704.01943, Section 6). -/
theorem mpo_oddRingTensor_apply (N : ℕ) [NeZero N] (s t : Fin N → Fin 3) :
    mpo oddRingTensor N s t = if (∀ n, s n = -(t (n - 1) + t n)) then 1 else 0 := by
  rw [mpo_apply_eq_prod_of_forced_bond oddRingTensor s t (fun n ↦ t (n - 1)) fun g hg ↦ ?_]
  · simp only [oddRingTensor_apply, add_sub_cancel_right, and_true]
    rw [Fintype.prod_boole]
    have key : ∀ a b c : Fin 3, -(b + c) = a ↔ b = -(a + c) := by decide
    simp only [key]
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    refine ⟨n - 1, ?_⟩
    rw [oddRingTensor_apply, sub_add_cancel, ite_eq_right fun h ↦ absurd h.2.symm hn]

/-- The input-to-output map of the odd-ring operator, $i_n=-(j_{n-1}+j_n)$
(arXiv:1704.01943, Section 6). -/
def oddRingMap (N : ℕ) [NeZero N] (t : Fin N → Fin 3) : Fin N → Fin 3 :=
  fun n ↦ -(t (n - 1) + t n)

/-- The periodic operator of the odd-ring tensor is the matrix of `oddRingMap`. -/
theorem mpo_oddRingTensor_eq (N : ℕ) [NeZero N] :
    mpo oddRingTensor N = Matrix.of fun s t ↦ if s = oddRingMap N t then 1 else 0 := by
  ext s t
  rw [mpo_oddRingTensor_apply, Matrix.of_apply]
  exact if_congr funext_iff.symm rfl rfl

open Fin.NatCast in
/-- On a ring of odd length the odd-ring map is injective: its kernel is trivial, since
$j_n=-j_{n-1}$ forces $j_0=(-1)^Nj_0=-j_0$, hence $j_0=0$ in `Fin 3`. -/
theorem oddRingMap_injective {N : ℕ} [NeZero N] (hN : Odd N) :
    Function.Injective (oddRingMap N) := by
  intro t t' h
  have step : ∀ n : Fin N, t n - t' n = -(t (n - 1) - t' (n - 1)) := by
    intro n
    have key : ∀ a b c e : Fin 3, -(a + b) = -(c + e) → b - e = -(a - c) := by decide
    exact key _ _ _ _ (congrFun h n)
  have hk : ∀ k : ℕ,
      t (k : Fin N) - t' (k : Fin N) = if Even k then t 0 - t' 0 else -(t 0 - t' 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := step ((k + 1 : ℕ) : Fin N)
      rw [Nat.cast_succ, add_sub_cancel_right, ih] at hs
      rw [Nat.cast_succ, hs]
      by_cases he : Even k <;> simp [he, Nat.even_add_one]
  have h0 : t 0 - t' 0 = 0 := by
    have hN' := hk N
    have hne : ¬ Even N := Nat.not_even_iff_odd.mpr hN
    simp only [Fin.natCast_self, hne, ↓reduceIte] at hN'
    have key : ∀ a : Fin 3, a = -a → a = 0 := by decide
    exact key _ hN'
  funext n
  have hn := hk n.val
  rw [Fin.cast_val_eq_self, h0] at hn
  have key : ∀ a b : Fin 3, a - b = 0 → a = b := by decide
  rw [neg_zero, ite_self] at hn
  exact key _ _ hn

/-- **The odd-ring operator is unitary on odd rings** (arXiv:1704.01943, Section 6): for odd
`N` the odd-ring map is a bijection, so the operator is a permutation matrix. -/
theorem mpo_oddRingTensor_mem_unitaryGroup_of_odd (N : ℕ) [NeZero N] (hN : Odd N) :
    mpo oddRingTensor N ∈ Matrix.unitaryGroup (Fin N → Fin 3) ℂ := by
  let σ : Equiv.Perm (Fin N → Fin 3) :=
    Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (oddRingMap_injective hN))
  have h : mpo oddRingTensor N = Equiv.Perm.permMatrix ℂ σ.symm := by
    ext s t
    simp only [mpo_oddRingTensor_eq, Matrix.of_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some_inj,
      Equiv.symm_apply_eq, σ, Equiv.ofBijective_apply]
  rw [h]
  exact Equiv.Perm.permMatrix_mem_unitaryGroup _

/-- A square complex matrix with two equal columns is not unitary. -/
private theorem not_mem_unitaryGroup_of_col_eq {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} {t₁ t₂ : n} (hne : t₁ ≠ t₂) (hcol : ∀ s, M s t₁ = M s t₂) :
    M ∉ Matrix.unitaryGroup n ℂ := by
  intro hU
  have hM : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h := congrFun (congrFun hM t₁) t₂
  have h' := congrFun (congrFun hM t₂) t₂
  simp only [Matrix.mul_apply, Matrix.star_apply, hcol] at h
  rw [Matrix.mul_apply] at h'
  simp only [Matrix.star_apply] at h'
  rw [h', Matrix.one_apply_eq, Matrix.one_apply_ne hne] at h
  exact one_ne_zero h

/-- **The odd-ring operator is not unitary on even rings** (arXiv:1704.01943, Section 6): for
even `N` the alternating configuration $a_n=(-1)^n$ (that is, `1` at even and `2` at odd sites)
lies in the kernel of the odd-ring map, including across the closing bond because `N` is even,
so the columns of the operator at `a` and at `0` coincide. -/
theorem mpo_oddRingTensor_not_mem_unitaryGroup_of_even (N : ℕ) [NeZero N] (hN : Even N) :
    mpo oddRingTensor N ∉ Matrix.unitaryGroup (Fin N → Fin 3) ℂ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne N)
  let a : Fin (m + 1) → Fin 3 := fun n ↦ if Even (n : ℕ) then 1 else 2
  have hpar : ∀ n : Fin (m + 1), Even ((n - 1 : Fin (m + 1)) : ℕ) ↔ ¬ Even (n : ℕ) := by
    intro n
    rw [Fin.coe_sub_one]
    split_ifs with h
    · subst h
      rw [Fin.val_zero]
      exact iff_of_false (Nat.even_add_one.mp hN) fun h ↦ h ⟨0, rfl⟩
    · have hn0 : (n : ℕ) ≠ 0 := fun h' ↦ h (Fin.ext (by simpa using h'))
      simp only [Nat.even_iff]
      omega
  have hmap : oddRingMap (m + 1) a = oddRingMap (m + 1) 0 := by
    funext n
    simp only [oddRingMap, Pi.zero_apply, a]
    by_cases hn : Even (n : ℕ)
    · have h2 : ¬ Even ((n - 1 : Fin (m + 1)) : ℕ) := fun h ↦ (hpar n).mp h hn
      simp only [hn, h2, ↓reduceIte]
      decide
    · have h2 : Even ((n - 1 : Fin (m + 1)) : ℕ) := (hpar n).mpr hn
      simp only [hn, h2, ↓reduceIte]
      decide
  have hne : a ≠ 0 := fun h ↦ by simpa [a] using congrFun h 0
  refine not_mem_unitaryGroup_of_col_eq hne fun s ↦ ?_
  simp only [mpo_oddRingTensor_eq, Matrix.of_apply, hmap]

/-- **The odd-ring tensor is not a matrix product unitary** (arXiv:1704.01943, Section 6): the
operator is not unitary at `N = 2`; for instance the inputs `(0, 1)` and `(1, 0)` have the same
image `(2, 2)`. -/
theorem not_isMPU_oddRingTensor : ¬ IsMPU oddRingTensor := fun hU ↦
  mpo_oddRingTensor_not_mem_unitaryGroup_of_even 2 even_two (hU 2 one_lt_two)

/-- The bijection `(i, β) ↦ (-(i + β), β)` of `Fin 3 × Fin 3` carrying the rows of the first
source cut of the odd-ring tensor to its columns. -/
def oddRingCutPerm : Equiv.Perm (Fin 3 × Fin 3) where
  toFun p := (-(p.1 + p.2), p.2)
  invFun p := (-(p.1 + p.2), p.2)
  left_inv p := by revert p; decide
  right_inv p := by revert p; decide

/-- The first source cut of the odd-ring tensor is a permutation matrix. -/
theorem sourceCutM₁_oddRingTensor :
    sourceCutM₁ oddRingTensor = Matrix.reindex oddRingCutPerm.symm (Equiv.refl _) 1 := by
  ext ⟨i, β⟩ ⟨α, j⟩
  have key : ∀ i β α j : Fin 3,
      (-(i + j) = α ∧ j = β) ↔ oddRingCutPerm (i, β) = (α, j) := by decide
  simp only [sourceCutM₁_apply, oddRingTensor_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Equiv.refl_symm, Equiv.refl_apply,
    Matrix.one_apply]
  exact if_congr (key i β α j) rfl rfl

/-- **The right source rank of the odd-ring tensor is nine** (arXiv:1704.01943, Section 6; the
ranks follow arXiv:1703.09188, definition `defnrl`, lines 450--477): the first source cut is a
`9 × 9` permutation matrix. -/
theorem rightRank_oddRingTensor : r[oddRingTensor] = 9 := by
  rw [rightRank, sourceCutM₁_oddRingTensor, Matrix.rank_reindex, Matrix.rank_one]
  simp

/-- **The left source rank of the odd-ring tensor is three** (arXiv:1704.01943, Section 6; the
ranks follow arXiv:1703.09188, definition `defnrl`, lines 450--477): the second source cut has
the three nonzero columns `(j, j)`, with disjoint supports. -/
theorem leftRank_oddRingTensor : ℓ[oddRingTensor] = 3 := by
  let A : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ := fun p k ↦ if -(p.2 + k) = p.1 then 1 else 0
  let B : Matrix (Fin 3) (Fin 3 × Fin 3) ℂ := fun k p ↦ if k = p.1 ∧ p.1 = p.2 then 1 else 0
  have hAB : sourceCutM₂ oddRingTensor = A * B := by
    ext ⟨α, i⟩ ⟨j, β⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · by_cases h₁ : -(i + j) = α <;> by_cases h₂ : j = β <;>
        simp [A, B, oddRingTensor_apply, h₁, h₂]
    · intro k _ hk
      simp [B, hk]
    · simp
  have hle : ℓ[oddRingTensor] ≤ 3 := by
    rw [leftRank, hAB]
    exact (Matrix.rank_mul_le_right A B).trans (by simpa using Matrix.rank_le_card_height B)
  have hsub : (sourceCutM₂ oddRingTensor).submatrix (fun k : Fin 3 ↦ (-k, 0))
      (fun k : Fin 3 ↦ (k, k)) = 1 := by
    ext a b
    have key : ∀ a b : Fin 3, (-(0 + b) = -a ∧ True) ↔ a = b := by decide
    simp only [Matrix.submatrix_apply, sourceCutM₂_apply, oddRingTensor_apply,
      Matrix.one_apply]
    exact if_congr (key a b) rfl rfl
  have hge := Matrix.rank_submatrix_le (sourceCutM₂ oddRingTensor)
    (fun k : Fin 3 ↦ (-k, 0)) (fun k : Fin 3 ↦ (k, k))
  rw [hsub, Matrix.rank_one, Fintype.card_fin] at hge
  exact le_antisymm hle hge

end MPOTensor
