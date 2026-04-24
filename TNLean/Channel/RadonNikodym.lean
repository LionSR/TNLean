/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.OrderedCP

/-!
# Radon–Nikodym theorem for CP maps and open-system representation
(Wolf Ch. 2, Thm 2.4 and Thm 2.5)

This file formalizes the canonical Radon–Nikodym theorem for completely
positive maps (Wolf Thm 2.4) and the open-system representation theorem
(Wolf Thm 2.5).

The Radon–Nikodym theorem says: for CP maps `T₁, T₂`, there exist a
Stinespring matrix `V` for `T₁ + T₂` and PSD operators `P₁, P₂` on the
dilation space with `P₁ + P₂ = 𝟙` such that `Tᵢ(A) = V†(A ⊗ Pᵢ)V`. In our
canonical realization, `V` is built from concatenated Kraus families of
`T₁` and `T₂`, and `P₁, P₂` are the orthogonal block projectors.

The open-system representation says: every CPTP map `T` can be written as
`T(ρ) = tr_r(V ρ V†)` for an isometry `V`, i.e. as the reduced unitary
evolution on a system-plus-environment.

## Main definitions

* `Matrix.blockDiagTopProj r s` — the projector `Cᴴ C` onto the first `r`
  coordinates of `ℂ^{r+s}` (equals `(blockTopRows r s)ᴴ * blockTopRows r s`).
* `Matrix.blockDiagBotProj r s` — the complementary projector onto the last
  `s` coordinates (equals `𝟙 - blockDiagTopProj r s`).

## Main results

* `Matrix.blockDiagTopProj_add_blockDiagBotProj` — the two projectors sum to
  the identity: resolution of identity on the dilation space.
* `Matrix.blockDiagTopProj_posSemidef`,
  `Matrix.blockDiagBotProj_posSemidef` — both are PSD.
* `IsCPMap.exists_radon_nikodym` (Wolf Thm 2.4 binary form):
  for CP `T₁, T₂`, there exist a Stinespring matrix `V` and two PSD
  operators `P₁, P₂` with `P₁ + P₂ = 𝟙` such that `Tᵢ(A) = V†(A ⊗ Pᵢ)V`.
* `IsChannel.exists_stinespring_open_system` (Wolf Thm 2.5 reduced form):
  every CPTP map admits an isometric Stinespring dilation realizing it as
  the reduced dynamics `T(ρ) = tr_r(V ρ V†)`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thms 2.4, 2.5]
  [Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### Block-diagonal projectors on the dilation space -/

/-- The **top-block projector** on `ℂ^{r+s}`: projects onto the first `r`
coordinates. Equals `Cᴴ * C` where `C = blockTopRows r s`. -/
noncomputable def Matrix.blockDiagTopProj (r s : ℕ) :
    Matrix (Fin (r + s)) (Fin (r + s)) ℂ :=
  (Matrix.blockTopRows r s)ᴴ * (Matrix.blockTopRows r s)

/-- The **bottom-block projector** on `ℂ^{r+s}`: projects onto the last `s`
coordinates. Equals `𝟙 - blockDiagTopProj r s`. -/
noncomputable def Matrix.blockDiagBotProj (r s : ℕ) :
    Matrix (Fin (r + s)) (Fin (r + s)) ℂ :=
  1 - Matrix.blockDiagTopProj r s

/-- Resolution of identity: `P_top + P_bot = 𝟙`. -/
theorem Matrix.blockDiagTopProj_add_blockDiagBotProj (r s : ℕ) :
    Matrix.blockDiagTopProj r s + Matrix.blockDiagBotProj r s = 1 := by
  simp [Matrix.blockDiagBotProj]

/-- The top-block projector is PSD (it is `CᴴC` for some `C`). -/
theorem Matrix.blockDiagTopProj_posSemidef (r s : ℕ) :
    (Matrix.blockDiagTopProj r s).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self (Matrix.blockTopRows r s)

/-- The bottom-block projector is PSD: `𝟙 - CᴴC ≥ 0` since `CᴴC ≤ 𝟙`. -/
theorem Matrix.blockDiagBotProj_posSemidef (r s : ℕ) :
    (Matrix.blockDiagBotProj r s).PosSemidef := by
  have := Matrix.blockTopRows_conjTranspose_mul_le_one r s
  rw [Matrix.le_iff] at this
  exact this

/-! ### Entrywise formula for the top-block projector -/

theorem Matrix.blockDiagTopProj_apply (r s : ℕ) (j j' : Fin (r + s)) :
    Matrix.blockDiagTopProj r s j j' =
      if j = j' ∧ (j : ℕ) < r then 1 else 0 :=
  Matrix.blockTopRows_conjTranspose_mul_apply r s j j'

/-! ### The key Kronecker identity: `A ⊗ (CᴴC) = (𝟙 ⊗ C)ᴴ (A ⊗ 𝟙)(𝟙 ⊗ C)` -/

/-- For any matrix `C : Fin r → Fin m` and `A : Fin D → Fin D`,
  `A ⊗ (Cᴴ * C) = (𝟙 ⊗ C)ᴴ * (A ⊗ 𝟙) * (𝟙 ⊗ C)`.
This is the Kronecker identity used in the Radon–Nikodym construction: it
rewrites `V†(A ⊗ P)V` with `P = CᴴC` as `(C̃ V)† (A ⊗ 𝟙)(C̃ V)` with
`C̃ = 𝟙 ⊗ C`. -/
theorem Matrix.kroneckerMap_conjTranspose_mul_kroneckerMap
    {D r m : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (C : Matrix (Fin r) (Fin m) ℂ) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ) C)ᴴ *
        Matrix.kroneckerMap (· * ·) A (1 : Matrix (Fin r) (Fin r) ℂ) *
        Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ) C =
      Matrix.kroneckerMap (· * ·) A (Cᴴ * C) := by
  rw [Matrix.conjTranspose_kronecker]
  rw [show (1 : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 from Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul (A := (1 : Matrix (Fin D) (Fin D) ℂ)) (B := A)
      (A' := Cᴴ) (B' := (1 : Matrix (Fin r) (Fin r) ℂ))]
  rw [← Matrix.mul_kronecker_mul (A := (1 * A : Matrix (Fin D) (Fin D) ℂ))
      (B := (1 : Matrix (Fin D) (Fin D) ℂ)) (A' := Cᴴ * 1) (B' := C)]
  simp

/-! ### Wolf Theorem 2.4 (Radon–Nikodym, binary form) -/

/-- **Wolf Theorem 2.4 (Radon–Nikodym for CP maps, binary form)**.

For completely positive maps `T₁, T₂`, there exist:

* an ancilla dimension `m`,
* a Kraus family `K : Fin m → M_D(ℂ)` with associated Stinespring matrix
  `V = stinespringV K`,
* two **positive operators** `P₁, P₂ : M_m(ℂ)` on the dilation space,
* with `P₁ + P₂ = 𝟙_m`,

such that each `Tᵢ` is recovered by the weighted Stinespring formula
`Tᵢ(A) = V† (A ⊗ Pᵢ) V`.

In the canonical realization returned below, `K` is the append of the Kraus
families of `T₁` and `T₂`, and `P₁, P₂` are the orthogonal block projectors
onto the two halves of the dilation space. -/
theorem IsCPMap.exists_radon_nikodym
    {T₁ T₂ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT₁ : IsCPMap T₁) (hT₂ : IsCPMap T₂) :
    ∃ (m : ℕ) (K : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (P₁ P₂ : Matrix (Fin m) (Fin m) ℂ),
      P₁.PosSemidef ∧ P₂.PosSemidef ∧ P₁ + P₂ = 1 ∧
      (∀ A, T₁ A =
        (stinespringV K)ᴴ *
          Matrix.kroneckerMap (· * ·) A P₁ *
          stinespringV K) ∧
      (∀ A, T₂ A =
        (stinespringV K)ᴴ *
          Matrix.kroneckerMap (· * ·) A P₂ *
          stinespringV K) := by
  -- Heisenberg-form Kraus families for T₁ and T₂.
  obtain ⟨r₁, K₁, hK₁⟩ := exists_stinespring_dilation T₁ hT₁
  obtain ⟨s, L, hL⟩ := hT₂
  -- Convert L to Heisenberg orientation.
  let Lh : Fin s → Matrix (Fin D) (Fin D) ℂ := fun j => (L j)ᴴ
  let K : Fin (r₁ + s) → Matrix (Fin D) (Fin D) ℂ := Fin.append K₁ Lh
  refine ⟨r₁ + s, K, Matrix.blockDiagTopProj r₁ s, Matrix.blockDiagBotProj r₁ s,
    Matrix.blockDiagTopProj_posSemidef r₁ s,
    Matrix.blockDiagBotProj_posSemidef r₁ s,
    Matrix.blockDiagTopProj_add_blockDiagBotProj r₁ s, ?_, ?_⟩
  · -- T₁(A) = V†(A ⊗ P_top)V.
    intro A
    -- Use the Kronecker identity: A ⊗ P_top = (𝟙 ⊗ C)ᴴ (A ⊗ 𝟙)(𝟙 ⊗ C).
    rw [Matrix.blockDiagTopProj,
        ← Matrix.kroneckerMap_conjTranspose_mul_kroneckerMap A
          (Matrix.blockTopRows r₁ s)]
    -- Reassociate: Vᴴ * ((𝟙⊗C)ᴴ * (A⊗𝟙) * (𝟙⊗C)) * V = ((𝟙⊗C)V)ᴴ * (A⊗𝟙) * ((𝟙⊗C)V).
    rw [show (stinespringV K)ᴴ *
        ((Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
            (Matrix.blockTopRows r₁ s))ᴴ *
          Matrix.kroneckerMap (· * ·) A
            (1 : Matrix (Fin r₁) (Fin r₁) ℂ) *
          Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
            (Matrix.blockTopRows r₁ s)) *
        stinespringV K =
      ((Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
            (Matrix.blockTopRows r₁ s)) * stinespringV K)ᴴ *
        Matrix.kroneckerMap (· * ·) A (1 : Matrix (Fin r₁) (Fin r₁) ℂ) *
        ((Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
            (Matrix.blockTopRows r₁ s)) * stinespringV K) from by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]]
    rw [← stinespringV_eq_kronecker_blockTopRows_mul_append K₁ Lh]
    -- Now the goal is T₁(A) = (stinespringV K₁)ᴴ * (A ⊗ 𝟙) * (stinespringV K₁).
    have : (stinespringV K₁)ᴴ *
        Matrix.kroneckerMap (· * ·) A (1 : Matrix (Fin r₁) (Fin r₁) ℂ) *
        stinespringV K₁ =
        (stinespringV K₁)ᴴ * stinespringPi (r := r₁) A * stinespringV K₁ := rfl
    rw [this, ← hK₁]
  · -- T₂(A) = V†(A ⊗ P_bot)V.
    -- Strategy: decompose P_bot = CᴴC where C is the "bottom-block rows" matrix.
    -- Easier: use the identity A ⊗ P_bot = A ⊗ 𝟙 - A ⊗ P_top, so
    -- V†(A ⊗ P_bot)V = V†(A ⊗ 𝟙)V - V†(A ⊗ P_top)V = T(A) - T₁(A) = T₂(A).
    intro A
    have hT_decomp : ∀ A, T₁ A + T₂ A =
        (stinespringV K)ᴴ * stinespringPi (r := r₁ + s) A * stinespringV K := by
      intro A
      have hK₁_kraus : T₁ A = ∑ i : Fin r₁, (K₁ i)ᴴ * A * (K₁ i) := by
        rw [hK₁]
        exact stinespring_dual_representation (K := K₁) (A := A)
      rw [hK₁_kraus, hL]
      have hLsum : ∑ j : Fin s, L j * A * (L j)ᴴ =
          ∑ j : Fin s, (Lh j)ᴴ * A * (Lh j) := by
        refine Finset.sum_congr rfl ?_
        intro j _; simp [Lh]
      rw [hLsum]
      have hSplit : ∑ j : Fin (r₁ + s), (K j)ᴴ * A * (K j) =
          (∑ i : Fin r₁, (K₁ i)ᴴ * A * (K₁ i)) +
          (∑ j : Fin s, (Lh j)ᴴ * A * (Lh j)) := by
        rw [Fin.sum_univ_add]
        congr 1 <;>
        · refine Finset.sum_congr rfl ?_
          intro i _
          simp [K, Fin.append_left, Fin.append_right]
      rw [← hSplit, ← stinespring_dual_representation (K := K) (A := A)]
      rfl
    have hT₁_kron : T₁ A =
        (stinespringV K)ᴴ *
          Matrix.kroneckerMap (· * ·) A
            (Matrix.blockDiagTopProj r₁ s) *
          stinespringV K := by
      rw [Matrix.blockDiagTopProj,
          ← Matrix.kroneckerMap_conjTranspose_mul_kroneckerMap A
            (Matrix.blockTopRows r₁ s)]
      rw [show (stinespringV K)ᴴ *
          ((Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
              (Matrix.blockTopRows r₁ s))ᴴ *
            Matrix.kroneckerMap (· * ·) A
              (1 : Matrix (Fin r₁) (Fin r₁) ℂ) *
            Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
              (Matrix.blockTopRows r₁ s)) *
          stinespringV K =
        ((Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
              (Matrix.blockTopRows r₁ s)) * stinespringV K)ᴴ *
          Matrix.kroneckerMap (· * ·) A (1 : Matrix (Fin r₁) (Fin r₁) ℂ) *
          ((Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
              (Matrix.blockTopRows r₁ s)) * stinespringV K) from by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]]
      rw [← stinespringV_eq_kronecker_blockTopRows_mul_append K₁ Lh]
      have : (stinespringV K₁)ᴴ *
          Matrix.kroneckerMap (· * ·) A (1 : Matrix (Fin r₁) (Fin r₁) ℂ) *
          stinespringV K₁ =
          (stinespringV K₁)ᴴ * stinespringPi (r := r₁) A * stinespringV K₁ := rfl
      rw [this, ← hK₁]
    -- Now T₂(A) = (T₁+T₂)(A) - T₁(A), and decompose the Kronecker product.
    have h_bot_decomp :
        Matrix.kroneckerMap (· * ·) A
          (Matrix.blockDiagBotProj r₁ s) =
        Matrix.kroneckerMap (· * ·) A
          (1 : Matrix (Fin (r₁ + s)) (Fin (r₁ + s)) ℂ) -
        Matrix.kroneckerMap (· * ·) A
          (Matrix.blockDiagTopProj r₁ s) := by
      rw [Matrix.blockDiagBotProj]
      ext ⟨i, j⟩ ⟨i', j'⟩
      simp [Matrix.kroneckerMap, Matrix.sub_apply, mul_sub]
    calc T₂ A
        = (T₁ A + T₂ A) - T₁ A := by abel
      _ = (stinespringV K)ᴴ *
            stinespringPi (r := r₁ + s) A *
            stinespringV K - T₁ A := by rw [hT_decomp]
      _ = (stinespringV K)ᴴ *
            Matrix.kroneckerMap (· * ·) A
              (1 : Matrix (Fin (r₁ + s)) (Fin (r₁ + s)) ℂ) *
            stinespringV K -
          (stinespringV K)ᴴ *
            Matrix.kroneckerMap (· * ·) A
              (Matrix.blockDiagTopProj r₁ s) *
            stinespringV K := by
          rw [hT₁_kron]
          rfl
      _ = (stinespringV K)ᴴ *
            (Matrix.kroneckerMap (· * ·) A
              (1 : Matrix (Fin (r₁ + s)) (Fin (r₁ + s)) ℂ) -
             Matrix.kroneckerMap (· * ·) A
              (Matrix.blockDiagTopProj r₁ s)) *
            stinespringV K := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = (stinespringV K)ᴴ *
            Matrix.kroneckerMap (· * ·) A
              (Matrix.blockDiagBotProj r₁ s) *
            stinespringV K := by rw [← h_bot_decomp]

/-! ### Wolf Theorem 2.5 (open-system representation) -/

/-- **Wolf Theorem 2.5 (open-system representation, reduced form)**.

Every CPTP quantum channel `T` admits a Stinespring isometric dilation `V`
realizing `T` as the reduced dynamics
  `T(ρ)_{ij} = ∑ₖ (V ρ V†)_{(i,k),(j,k)}`
on a system-plus-environment Hilbert space. Equivalently `T(ρ) = tr_r(VρV†)`.

This is the "reduced" form of Wolf's Thm 2.5; the full system-plus-environment
unitary form follows by extending `V` to a unitary `U` on `ℂ^D ⊗ ℂ^r` and
writing `V = U(𝟙 ⊗ |0⟩)`, which requires an orthonormal basis extension.
The isometric form here already carries the essential physical content:
`T` arises from coupling the system to an environment and tracing it out. -/
theorem IsChannel.exists_stinespring_open_system
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsChannel T) :
    ∃ (r : ℕ) (V : Matrix (Fin D × Fin r) (Fin D) ℂ),
      Vᴴ * V = 1 ∧
      ∀ (ρ : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D),
        (T ρ) i j = ∑ k : Fin r, (V * ρ * Vᴴ) (i, k) (j, k) := by
  obtain ⟨r, K, hkSchr, hVisom⟩ := exists_stinespring_isometry_of_cptp T hT.cp hT.tp
  refine ⟨r, stinespringV K, hVisom, ?_⟩
  intro ρ i j
  exact hkSchr ρ i j

/-- **Wolf Theorem 2.5, partial-trace form**.

Equivalent reformulation of the open-system representation expressed via
`Matrix.traceRight`, matching Wolf's statement
`T(ρ) = tr_E[V ρ V†]`. -/
theorem IsChannel.exists_stinespring_open_system_traceRight
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsChannel T) :
    ∃ (r : ℕ) (V : Matrix (Fin D × Fin r) (Fin D) ℂ),
      Vᴴ * V = 1 ∧
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ, T ρ = (V * ρ * Vᴴ).traceRight := by
  obtain ⟨r, V, hiso, hschr⟩ := hT.exists_stinespring_open_system
  refine ⟨r, V, hiso, ?_⟩
  intro ρ
  ext i j
  rw [hschr ρ i j]
  simp [Matrix.traceRight]
