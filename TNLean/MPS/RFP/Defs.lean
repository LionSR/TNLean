/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.Core.Transfer
import TNLean.Channel.Stinespring
import TNLean.Channel.KrausFreedom

/-!
# Pure-state renormalization fixed point (RFP) — definitions

This file gives two equivalent descriptions of a **renormalization fixed point**
for a pure MPS tensor, following arXiv:1606.00608, Section 3.1
(Cirac–Pérez-García–Schuch–Verstraete).

The source definition is `HasPhysicalBlockingIsometry A`: multiplication of two
tensor letters is obtained from one tensor letter by an isometry on the physical
index. The equivalent predicate `IsTransferIdempotent A` says that the associated completely
positive transfer map is idempotent.
-/

open scoped Matrix BigOperators
open Matrix Finset

namespace MPSTensor

variable {d D : ℕ}

/-- An MPS tensor has a **physical blocking isometry** when multiplication of
two tensor letters can be reversed by an isometry on the physical index:
\[
  A^{i_1}A^{i_2}=\sum_j U_{(i_1,i_2),j}A^j,
  \qquad U^\dagger U=1.
\]

This is the renormalization fixed-point relation `AA=A` in arXiv:1606.00608,
equation `AA=A` and Definition `defRFP`, lines 398--424. -/
def HasPhysicalBlockingIsometry (A : MPSTensor d D) : Prop :=
  ∃ U : Matrix (Fin d × Fin d) (Fin d) ℂ,
    U.conjTranspose * U = 1 ∧
    ∀ i₁ i₂ : Fin d, A i₁ * A i₂ = ∑ j : Fin d, U (i₁, i₂) j • A j

/-- The transfer-map criterion for a pure-state renormalization fixed point:
the completely positive map associated to `A` is idempotent,
`E_A ∘ E_A = E_A`.

The source defines the fixed-point property by a physical blocking isometry.
Theorem `isTransferIdempotent_iff_hasPhysicalBlockingIsometry` proves that the two conditions
are equivalent. -/
def IsTransferIdempotent (A : MPSTensor d D) : Prop :=
  transferMap A ∘ₗ transferMap A = transferMap A

/-- If the product letters of an MPS tensor are obtained from its letters by a
rectangular isometry `V`, with `V†V = 1`, then the transfer map is idempotent.

This is the Kraus-family implication used in arXiv:1606.00608, lines 1205--1209.

See `isTransferIdempotent_iff_kraus_isometry` for the full equivalence (both directions). -/
theorem isTransferIdempotent_of_kraus_isometry (A : MPSTensor d D)
    (V : Matrix (Fin d × Fin d) (Fin d) ℂ)
    (hV : V.conjTranspose * V = 1)
    (hprod : ∀ i₁ i₂ : Fin d,
      A i₁ * A i₂ = ∑ j : Fin d, V (i₁, i₂) j • A j) :
    IsTransferIdempotent A := by
  -- Extract the orthogonality relation from V†V = 1.
  have hV_entry : ∀ j k : Fin d,
      ∑ x₁ : Fin d, ∑ x₂ : Fin d,
        V (x₁, x₂) j * star (V (x₁, x₂) k) =
        if k = j then 1 else 0 := by
    intro j k
    have h := congrFun (congrFun hV k) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_prod_type, RCLike.star_def] at h
    simp_rw [mul_comm] at h
    exact h
  change transferMap A ∘ₗ transferMap A = transferMap A
  apply LinearMap.ext; intro X
  simp only [LinearMap.comp_apply, transferMap_apply]
  -- Step 1: Distribute the outer sum and rewrite products using conjTranspose_mul.
  -- LHS = ∑ i₁ i₂, (A i₁ * A i₂) * X * (A i₁ * A i₂)†
  have step1 : ∀ (i₁ i₂ : Fin d),
      A i₁ * (A i₂ * X * (A i₂)ᴴ) * (A i₁)ᴴ =
      (A i₁ * A i₂) * X * (A i₁ * A i₂)ᴴ := by
    intro i₁ i₂; rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  -- Step 2: Substitute hprod and show both Kraus families give the same sum.
  -- This follows the pattern of `kraus_same_map_of_unitary_combination`.
  suffices h : ∑ i₁ : Fin d, ∑ i₂ : Fin d,
      (A i₁ * A i₂) * X * (A i₁ * A i₂)ᴴ =
      ∑ j : Fin d, A j * X * (A j)ᴴ by
    simp_rw [Finset.mul_sum, Finset.sum_mul, step1]; exact h
  -- Substitute hprod into LHS
  simp_rw [hprod]
  -- Expand the product of sums
  simp_rw [Matrix.sum_mul, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.mul_sum, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, smul_smul]
  -- Now LHS = ∑ i₁ i₂ j k, (V(i₁,i₂) j * star(V(i₁,i₂) k)) • (A j * (X * (A k)ᴴ))
  -- Rearrange sums: bring j, k outside and i₁, i₂ inside
  -- Step 1: Inside ∑ i₁, swap i₂ ↔ j
  conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  -- Step 2: Swap i₁ ↔ j at outermost level
  rw [Finset.sum_comm]
  -- Now: ∑ j i₁ i₂ k, ...
  -- Step 3: Inside ∑ j ∑ i₁, swap i₂ ↔ k
  conv_lhs => arg 2; ext; arg 2; ext; rw [Finset.sum_comm]
  -- Step 4: Inside ∑ j, swap i₁ ↔ k
  conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  -- Now: ∑ j k i₁ i₂, (V(i₁,i₂) j * star(V(i₁,i₂) k)) • (A j * (X * (A k)ᴴ))
  -- Inside ∑ j: factor scalar from i₁, i₂ sums, apply V†V = 1, simplify
  apply Finset.sum_congr rfl; intro j _
  simp_rw [← Finset.sum_smul]
  simp_rw [hV_entry j]
  simp only [ite_smul, one_smul, zero_smul, sum_ite_eq', mem_univ, ↓reduceIte]

/-- The RFP condition is equivalent to a Kraus-level condition: there exists
an isometry `V : Fin d × Fin d → Fin d → ℂ` (i.e. a `(d²×d)` matrix) such
that `A i₁ * A i₂ = ∑ j, V (i₁, i₂) j • A j` for all `i₁ i₂`.

**Forward direction**: `E² = E` means the product Kraus family `{Aᵢ₁ Aᵢ₂}`
and the single family `{Aⱼ}` define the same CPM. By rectangular Kraus freedom
(`kraus_rectangular_freedom'` from `KrausFreedom.lean`), they are related by a
rectangular isometry `V` with `V†V = 1`.

**Backward direction**: proved as `isTransferIdempotent_of_kraus_isometry`.

See arXiv:1606.00608, Definition `defRFP`, lines 420--424, and its Kraus-family
argument at lines 1205--1209; see also Wolf Theorem 2.1 item 4. -/
theorem isTransferIdempotent_iff_kraus_isometry (A : MPSTensor d D) :
    IsTransferIdempotent A ↔
      ∃ V : Matrix (Fin d × Fin d) (Fin d) ℂ,
        V.conjTranspose * V = 1 ∧
        ∀ i₁ i₂ : Fin d,
          A i₁ * A i₂ = ∑ j : Fin d, V (i₁, i₂) j • A j := by
  constructor
  · -- Forward direction: E² = E ⟹ product Kraus family = single Kraus family,
    -- then rectangular Kraus freedom gives the isometry V.
    intro hRFP
    -- Step 1: Extract the Kraus map equality from E² = E.
    -- LHS = ∑ i₁ i₂, (A i₁ * A i₂) * X * (A i₁ * A i₂)†
    -- RHS = ∑ j, A j * X * (A j)†
    have hmap : ∀ X : Matrix (Fin D) (Fin D) ℂ,
        ∑ p : Fin d × Fin d, (A p.1 * A p.2) * X * (A p.1 * A p.2)ᴴ =
        ∑ j : Fin d, A j * X * (A j)ᴴ := by
      intro X
      have h := congr_fun (congr_arg DFunLike.coe hRFP) X
      simp only [LinearMap.comp_apply, transferMap_apply] at h
      rw [← h]
      rw [show ∑ p : Fin d × Fin d, (A p.1 * A p.2) * X * (A p.1 * A p.2)ᴴ =
          ∑ i₁ : Fin d, ∑ i₂ : Fin d,
            (A i₁ * A i₂) * X * (A i₁ * A i₂)ᴴ from Fintype.sum_prod_type _]
      apply Finset.sum_congr rfl; intro i₁ _
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i₂ _
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    -- Step 2: Apply rectangular Kraus freedom (Wolf Theorem 2.1 item 4).
    obtain ⟨V, hV_iso, hV_decomp⟩ := kraus_rectangular_freedom'
      (fun p : Fin d × Fin d => A p.1 * A p.2) A hmap
      (by simp only [Fintype.card_fin, Fintype.card_prod]; exact Nat.le_mul_self d)
    exact ⟨V, hV_iso, fun i₁ i₂ => hV_decomp (i₁, i₂)⟩
  · -- Backward direction: proved as `isTransferIdempotent_of_kraus_isometry`
    rintro ⟨V, hV, hprod⟩
    exact isTransferIdempotent_of_kraus_isometry A V hV hprod

/-- Transfer-map idempotence is equivalent to the physical blocking-isometry
definition of a pure-state renormalization fixed point.

This identifies the transfer-map criterion with equation `AA=A` and Definition
`defRFP` in arXiv:1606.00608, lines 398--424. -/
theorem isTransferIdempotent_iff_hasPhysicalBlockingIsometry (A : MPSTensor d D) :
    IsTransferIdempotent A ↔ HasPhysicalBlockingIsometry A := by
  simpa only [HasPhysicalBlockingIsometry] using isTransferIdempotent_iff_kraus_isometry A

end MPSTensor
