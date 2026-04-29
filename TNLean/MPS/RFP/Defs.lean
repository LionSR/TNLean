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

This file defines the notion of a **renormalization fixed point** (RFP) for a
pure MPS tensor, following arXiv:1606.00608 §3.1
(Cirac–Pérez-García–Schuch–Verstraete).

The key definition is `IsRFP A`, which says that the completely positive map
(CPM) associated to the MPS tensor `A` is **idempotent**: composing the
transfer map with itself yields the same transfer map.
-/

open scoped Matrix BigOperators
open Matrix Finset

namespace MPSTensor

variable {d D : ℕ}

/-- An MPS tensor `A` is a **renormalization fixed point** (RFP) when its
transfer map is idempotent as a linear map, i.e. `E_A ∘ E_A = E_A`.
See arXiv:1606.00608, Definition 3.2. -/
def IsRFP (A : MPSTensor d D) : Prop :=
  transferMap A ∘ₗ transferMap A = transferMap A

/-- The idempotence equation expressed as a projection lemma. -/
theorem IsRFP.idempotent {A : MPSTensor d D} (h : IsRFP A) :
    transferMap A ∘ₗ transferMap A = transferMap A :=
  h

/-- The backward direction of the RFP ↔ Kraus-isometry characterisation
(arXiv:1606.00608, Theorem 3.1): if the Kraus operators of an MPS tensor
decompose via a rectangular isometry `V` (with `V†V = 1`), then the
transfer map is idempotent.

See `isRFP_iff_kraus_isometry` for the full equivalence (both directions). -/
theorem isRFP_of_kraus_isometry (A : MPSTensor d D)
    (V : Matrix (Fin d × Fin d) (Fin d) ℂ)
    (hV : V.conjTranspose * V = 1)
    (hprod : ∀ i₁ i₂ : Fin d,
      A i₁ * A i₂ = ∑ j : Fin d, V (i₁, i₂) j • A j) :
    IsRFP A := by
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

**Backward direction**: proved as `isRFP_of_kraus_isometry`.

See arXiv:1606.00608, Theorem 3.1 and Wolf Thm 2.1 item 4. -/
theorem isRFP_iff_kraus_isometry (A : MPSTensor d D) :
    IsRFP A ↔
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
    -- Step 2: Apply rectangular Kraus freedom (Wolf Thm 2.1 item 4).
    obtain ⟨V, hV_iso, hV_decomp⟩ := kraus_rectangular_freedom'
      (fun p : Fin d × Fin d => A p.1 * A p.2) A hmap
      (by simp only [Fintype.card_fin, Fintype.card_prod]; exact Nat.le_mul_self d)
    exact ⟨V, hV_iso, fun i₁ i₂ => hV_decomp (i₁, i₂)⟩
  · -- Backward direction: proved as `isRFP_of_kraus_isometry`
    rintro ⟨V, hV, hprod⟩
    exact isRFP_of_kraus_isometry A V hV hprod

/-- Backwards-compatible name for `isRFP_iff_kraus_isometry`. -/
theorem isRFP_iff_kraus (A : MPSTensor d D) :
    IsRFP A ↔
      ∃ V : Matrix (Fin d × Fin d) (Fin d) ℂ,
        V.conjTranspose * V = 1 ∧
        ∀ i₁ i₂ : Fin d,
          A i₁ * A i₂ = ∑ j : Fin d, V (i₁, i₂) j • A j :=
  isRFP_iff_kraus_isometry A

end MPSTensor
