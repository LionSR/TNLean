/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Stinespring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Ordered completely positive maps (Wolf Section 2.1, Theorem 2.3)

This file relates two CP maps `T₁ ≤ T₂` through canonical Stinespring
realizations. The central statement is Wolf's Theorem 2.3 (Eq. (2.13)): if `T₂ - T₁` is CP,
then a Heisenberg-form Stinespring realization for `T₁` factors through one for
`T₂` via a **contraction** on the dilation space.

In the canonical realization provided here, the Stinespring matrix for `T₂` is
obtained by concatenating Kraus operators of `T₁` with Kraus operators of
`T₂ - T₁`, and the intertwining contraction is the explicit block-top
co-isometry `C : ℂ^{r₁+s} → ℂ^{r₁}` (taking the first `r₁` coordinates).

## Main definitions

* `CPDominates S T` — the CP partial order: `S - T` is completely positive.
* `Matrix.blockTopRows r s` — the rectangular `r × (r+s)` matrix whose rows
  are the first `r` rows of the identity; equivalently, the block `[𝟙_r | 0]`.

## Main results (Wolf Theorem 2.3)

* `Matrix.blockTopRows_mul_conjTranspose` — `C * Cᴴ = 1_r` (co-isometry).
* `Matrix.blockTopRows_conjTranspose_mul_le_one` — `Cᴴ * C ≤ 1` (contraction).
* `stinespringV_eq_kronecker_blockTopRows_mul_append` — entrywise intertwining:
  `V₁ = (𝟙_D ⊗ C) * V₂` where `V₂ = stinespringV (Fin.append K L)`.
* `CPDominates.exists_stinespring_contraction` — existential form of Wolf
  Theorem 2.3: if `T₁ ≤ T₂` (in the CP order), there exist Stinespring
  realizations for both and a contraction on the dilation space that
  intertwines them.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.3][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### The CP partial order -/

/-- **CP partial order**: `S` dominates `T` iff `S - T` is completely positive.
This is the partial order on CP maps used throughout Wolf Chapter 2. -/
def CPDominates
    (S T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop :=
  IsCPMap (S - T)

/-- Reflexivity of the CP order: `T - T = 0` has the empty Kraus family. -/
theorem CPDominates.refl
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    CPDominates T T := by
  refine ⟨0, (fun i : Fin 0 => i.elim0), ?_⟩
  intro X
  simp

/-! ### The block-top rectangular co-isometry -/

/-- The block-top rectangular matrix `C : Fin r → Fin (r+s)` whose rows are
the first `r` rows of `𝟙_{r+s}`. Concretely, `C i j = 1` if `j = castAdd s i`
and `0` otherwise. This is the canonical co-isometry from `ℂ^{r+s}` onto
`ℂ^r` that picks out the first `r` coordinates. -/
noncomputable def Matrix.blockTopRows (r s : ℕ) :
    Matrix (Fin r) (Fin (r + s)) ℂ :=
  fun i j => if j = Fin.castAdd s i then 1 else 0

theorem Matrix.blockTopRows_apply (r s : ℕ) (i : Fin r) (j : Fin (r + s)) :
    blockTopRows r s i j = if j = Fin.castAdd s i then 1 else 0 := rfl

@[simp] theorem Matrix.blockTopRows_apply_castAdd (r s : ℕ) (i : Fin r) :
    blockTopRows r s i (Fin.castAdd s i) = 1 := by
  simp [Matrix.blockTopRows]

/-- `C * Cᴴ = 𝟙_r` for the block-top projector. -/
theorem Matrix.blockTopRows_mul_conjTranspose (r s : ℕ) :
    (blockTopRows r s) * (blockTopRows r s)ᴴ = (1 : Matrix (Fin r) (Fin r) ℂ) := by
  ext i i'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.blockTopRows_apply]
  have hterm : ∀ j : Fin (r + s),
      (if j = Fin.castAdd s i then (1 : ℂ) else 0) *
        star (if j = Fin.castAdd s i' then (1 : ℂ) else 0) =
      if j = Fin.castAdd s i ∧ j = Fin.castAdd s i' then 1 else 0 := by
    intro j
    by_cases h1 : j = Fin.castAdd s i <;> by_cases h2 : j = Fin.castAdd s i' <;>
      simp [h1, h2]
  simp_rw [hterm]
  by_cases hii : i = i'
  · subst hii
    rw [Finset.sum_eq_single (Fin.castAdd s i)]
    · simp [Matrix.one_apply_eq]
    · intro b _ hb
      simp [hb]
    · intro hj; exact absurd (Finset.mem_univ (Fin.castAdd s i)) hj
  · have hcast : Fin.castAdd s i ≠ Fin.castAdd s i' := by
      intro h; exact hii (Fin.castAdd_injective r s h)
    have hsum : ∑ j : Fin (r + s),
        (if j = Fin.castAdd s i ∧ j = Fin.castAdd s i' then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      split_ifs with hk
      · exact absurd (hk.1.symm.trans hk.2) hcast
      · rfl
    rw [hsum, Matrix.one_apply_ne hii]

/-- The "diagonal" block-top projector `Cᴴ * C` equals the diagonal matrix that
is `1` on the first `r` coordinates and `0` on the last `s`. -/
theorem Matrix.blockTopRows_conjTranspose_mul_apply (r s : ℕ)
    (j j' : Fin (r + s)) :
    ((blockTopRows r s)ᴴ * blockTopRows r s) j j' =
      if j = j' ∧ (j : ℕ) < r then 1 else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.blockTopRows_apply]
  have hterm : ∀ k : Fin r,
      star (if j = Fin.castAdd s k then (1 : ℂ) else 0) *
        (if j' = Fin.castAdd s k then 1 else 0) =
      if j = Fin.castAdd s k ∧ j' = Fin.castAdd s k then 1 else 0 := by
    intro k
    by_cases h1 : j = Fin.castAdd s k <;> by_cases h2 : j' = Fin.castAdd s k <;>
      simp [h1, h2]
  simp_rw [hterm]
  by_cases hjr : (j : ℕ) < r
  · set jFin : Fin r := ⟨(j : ℕ), hjr⟩ with hjFin
    have hj : j = Fin.castAdd s jFin := by
      ext; simp [Fin.castAdd, hjFin]
    by_cases hjeq : j = j'
    · subst hjeq
      have hconv : ∀ k : Fin r,
          (if j = Fin.castAdd s k ∧ j = Fin.castAdd s k then (1 : ℂ) else 0) =
          if k = jFin then 1 else 0 := by
        intro k
        by_cases hk : j = Fin.castAdd s k
        · have hkF : k = jFin := by
            have : Fin.castAdd s k = Fin.castAdd s jFin := hk.symm.trans hj
            exact Fin.castAdd_injective r s this
          simp [hk, hkF]
        · have hkF : k ≠ jFin := by
            intro he; apply hk; rw [he]; exact hj
          simp [hk, hkF]
      simp_rw [hconv]
      rw [Finset.sum_eq_single jFin]
      · simp [hjr]
      · intro b _ hb; simp [hb]
      · intro hj'; exact absurd (Finset.mem_univ jFin) hj'
    · have hrhs : ¬ (j = j' ∧ (j : ℕ) < r) := fun ⟨h, _⟩ => hjeq h
      rw [if_neg hrhs]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) hjeq
      · rfl
  · have hrhs : ¬ (j = j' ∧ (j : ℕ) < r) := fun ⟨_, h⟩ => hjr h
    rw [if_neg hrhs]
    apply Finset.sum_eq_zero
    intro k _
    have hk : j ≠ Fin.castAdd s k := by
      intro he
      have := Fin.val_eq_of_eq he
      simp [Fin.castAdd] at this
      omega
    simp [hk]

/-- **C is a contraction**: `Cᴴ * C ≤ 𝟙_{r+s}`. -/
theorem Matrix.blockTopRows_conjTranspose_mul_le_one (r s : ℕ) :
    (blockTopRows r s)ᴴ * blockTopRows r s ≤ (1 : Matrix (Fin (r+s)) (Fin (r+s)) ℂ) := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian.
    ext j j'
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      Matrix.blockTopRows_conjTranspose_mul_apply]
    by_cases hjj : j = j'
    · subst hjj
      by_cases hjr : (j : ℕ) < r
      all_goals simp [hjr]
    · have hne : j' ≠ j := fun h => hjj h.symm
      simp [hjj, hne]
  · -- PSD condition.
    intro x
    -- Compute ((1 - CᴴC).mulVec x) j entrywise.
    have hmul : ∀ j : Fin (r + s),
        (((1 : Matrix (Fin (r+s)) (Fin (r+s)) ℂ) -
            ((blockTopRows r s)ᴴ * blockTopRows r s)) *ᵥ x) j =
        (if (j : ℕ) < r then 0 else x j) := by
      intro j
      rw [Matrix.sub_mulVec]
      rw [Matrix.one_mulVec]
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
      simp_rw [Matrix.blockTopRows_conjTranspose_mul_apply]
      by_cases hjr : (j : ℕ) < r
      · rw [if_pos hjr]
        have hsum : ∑ j' : Fin (r + s),
            (if j = j' ∧ (j : ℕ) < r then (1 : ℂ) else 0) * x j' = x j := by
          rw [Finset.sum_eq_single j]
          · simp [hjr]
          · intro b _ hb
            have : ¬ (j = b ∧ (j : ℕ) < r) := fun ⟨hjb, _⟩ => hb hjb.symm
            simp [this]
          · intro hj; exact absurd (Finset.mem_univ j) hj
        rw [hsum, sub_self]
      · rw [if_neg hjr]
        have hsum : ∑ j' : Fin (r + s),
            (if j = j' ∧ (j : ℕ) < r then (1 : ℂ) else 0) * x j' = 0 := by
          apply Finset.sum_eq_zero
          intro j' _
          split_ifs with h
          · exact absurd h.2 hjr
          · ring
        rw [hsum, sub_zero]
    simp only [dotProduct]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [hmul]
    by_cases hjr : (j : ℕ) < r
    · simp [hjr]
    · simp only [hjr, if_false]
      change 0 ≤ star (x j) * x j
      have hsq : star (x j) * x j = ((‖x j‖ : ℝ) ^ 2 : ℂ) := by
        rw [show star (x j) = starRingEnd ℂ (x j) from rfl, RCLike.conj_mul]
        norm_cast
      rw [hsq]
      exact_mod_cast sq_nonneg ‖x j‖

/-! ### Intertwining identity for the canonical Stinespring matrices -/

/-- **Entrywise intertwining (Wolf Theorem 2.3 canonical form)**: the block-top
co-isometry `C = blockTopRows r s` relates the Stinespring matrix of a Kraus
family `K : Fin r → M` with that of its append with another family
`L : Fin s → M`:
  `stinespringV K = (𝟙_D ⊗ C) * stinespringV (Fin.append K L)`. -/
theorem stinespringV_eq_kronecker_blockTopRows_mul_append
    {r s : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (L : Fin s → Matrix (Fin D) (Fin D) ℂ) :
    stinespringV K =
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
          (Matrix.blockTopRows r s)) *
        stinespringV (Fin.append K L) := by
  ext ⟨i, j₁⟩ k
  simp only [stinespringV_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.blockTopRows_apply]
  -- Reduce double sum to a single value.
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single (Fin.castAdd s j₁)]
    · simp [Fin.append_left, Matrix.one_apply_eq]
    · intro b _ hb
      simp [Matrix.one_apply_eq, hb]
    · intro hj; exact absurd (Finset.mem_univ (Fin.castAdd s j₁)) hj
  · intro b _ hb
    refine Finset.sum_eq_zero ?_
    intro j _
    have : ((1 : Matrix (Fin D) (Fin D) ℂ) i b) = 0 := Matrix.one_apply_ne (Ne.symm hb)
    simp [this]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ### Wolf Theorem 2.3: ordered CP-maps -/

/-- **Wolf Theorem 2.3 (ordered CP-maps, canonical form)**.

Let `T₁, T₂ : M_D(ℂ) →ₗ M_D(ℂ)` be CP maps with `T₁ ≤ T₂` in the CP partial
order (i.e. `T₂ - T₁` is CP). Then there exist an ancilla dimension `m`,
Heisenberg-form Stinespring matrices
`V₁ : Matrix (Fin D × Fin r₁) (Fin D) ℂ` and
`V₂ : Matrix (Fin D × Fin m) (Fin D) ℂ` realizing `Tᵢ(A) = Vᵢᴴ * (A ⊗ 𝟙) * Vᵢ`,
together with a **contraction** `C : Matrix (Fin r₁) (Fin m) ℂ` satisfying
`Cᴴ * C ≤ 𝟙` and the intertwining identity `V₁ = (𝟙_D ⊗ C) * V₂`.

In the canonical realization returned below, `m = r₁ + s` where `s` is a Kraus
length of `T₂ - T₁`, the two Stinespring matrices come from conjugated Kraus
families, and `C = blockTopRows r₁ s`. -/
theorem CPDominates.exists_stinespring_contraction
    {T₁ T₂ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT₁ : IsCPMap T₁) (hdom : CPDominates T₂ T₁) :
    ∃ (r₁ m : ℕ)
      (K₁ : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)
      (K₂ : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (C : Matrix (Fin r₁) (Fin m) ℂ),
      (∀ A, T₁ A =
        (stinespringV K₁)ᴴ * stinespringPi (r := r₁) A * stinespringV K₁) ∧
      (∀ A, T₂ A =
        (stinespringV K₂)ᴴ * stinespringPi (r := m) A * stinespringV K₂) ∧
      Cᴴ * C ≤ 1 ∧
      stinespringV K₁ =
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ) C) *
          stinespringV K₂ := by
  obtain ⟨r₁, K₁h, hK₁⟩ := exists_stinespring_dilation T₁ hT₁
  obtain ⟨s, L, hL⟩ := hdom
  let Lh : Fin s → Matrix (Fin D) (Fin D) ℂ := fun j => (L j)ᴴ
  let K₂ : Fin (r₁ + s) → Matrix (Fin D) (Fin D) ℂ := Fin.append K₁h Lh
  refine ⟨r₁, r₁ + s, K₁h, K₂, Matrix.blockTopRows r₁ s, hK₁, ?_, ?_, ?_⟩
  · -- T₂ Heisenberg identity.
    intro A
    have hsum : T₂ A = T₁ A + (T₂ - T₁) A := by
      simp [LinearMap.sub_apply]
    rw [hsum, hK₁, hL]
    have hLsum : ∑ j : Fin s, L j * A * (L j)ᴴ =
        ∑ j : Fin s, (Lh j)ᴴ * A * (Lh j) := by
      refine Finset.sum_congr rfl ?_
      intro j _; simp [Lh]
    rw [hLsum]
    have hStK₂ : ∑ j : Fin (r₁ + s), (K₂ j)ᴴ * A * (K₂ j) =
        (stinespringV K₂)ᴴ * stinespringPi (r := r₁ + s) A * stinespringV K₂ :=
      (stinespring_dual_representation (K := K₂) (A := A)).symm
    have hStK₁ : ∑ i : Fin r₁, (K₁h i)ᴴ * A * (K₁h i) =
        (stinespringV K₁h)ᴴ * stinespringPi (r := r₁) A * stinespringV K₁h :=
      (stinespring_dual_representation (K := K₁h) (A := A)).symm
    have hSplit : ∑ j : Fin (r₁ + s), (K₂ j)ᴴ * A * (K₂ j) =
        (∑ i : Fin r₁, (K₁h i)ᴴ * A * (K₁h i)) +
        (∑ j : Fin s, (Lh j)ᴴ * A * (Lh j)) := by
      rw [Fin.sum_univ_add]
      congr 1 <;>
      · refine Finset.sum_congr rfl ?_
        intro i _
        simp [K₂, Fin.append_left, Fin.append_right]
    rw [← hStK₁, ← hStK₂, hSplit]
  · exact Matrix.blockTopRows_conjTranspose_mul_le_one r₁ s
  · exact stinespringV_eq_kronecker_blockTopRows_mul_append K₁h Lh
