/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Basic
import TNLean.Wielandt.RectangularSpan.Growth

/-!
# Rectangular span universality compatibility names

The rank-one and eigenvector statements hold for arbitrary finite matrix families.
This module retains their established names for matrix product tensors.
-/

open scoped Matrix

namespace MPSTensor

open Matrix

variable {d D : ℕ}

/-- Rank-one matrices whose left vector lies in the range of `P` belong to the
range of left multiplication by `P`. -/
theorem vecMulVec_mem_range_mulLeft_of_mem_range_toLin
    (P : Matrix (Fin D) (Fin D) ℂ) {φ : Fin D → ℂ}
    (hφ : φ ∈ LinearMap.range (Matrix.toLin' P)) (ψ : Fin D → ℂ) :
    vecMulVec φ ψ ∈ LinearMap.range (LinearMap.mulLeft ℂ P) :=
  Kraus.vecMulVec_mem_range_mulLeft_of_mem_range_toLin P hφ ψ

/-- Rank-one matrices from the range of `(A i₀) ^ D` belong to a stabilized
rectangular span. -/
theorem vecMulVec_mem_rectSpan_of_mem_range_of_rectSpan_eq_range
    (A : MPSTensor d D) (i₀ : Fin d) {n : ℕ}
    {φ : Fin D → ℂ}
    (hφ : φ ∈ LinearMap.range (Matrix.toLin' ((A i₀) ^ D)))
    (heq : rectSpan ((A i₀) ^ D) A n =
           LinearMap.range (LinearMap.mulLeft ℂ ((A i₀) ^ D))) :
    ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ rectSpan ((A i₀) ^ D) A n :=
  Kraus.vecMulVec_mem_rectSpan_of_mem_range_of_rectSpan_eq_range A i₀ hφ heq

/-- Rank-one matrices in a stabilized rectangular span belong to the
corresponding longer word span. -/
theorem vecMulVec_mem_wordSpan_of_rectSpan_eq_range
    (A : MPSTensor d D) (i₀ : Fin d) {m n : ℕ}
    (hPmem : (A i₀) ^ D ∈ wordSpan A m)
    (heq : rectSpan ((A i₀) ^ D) A n =
           LinearMap.range (LinearMap.mulLeft ℂ ((A i₀) ^ D)))
    {φ : Fin D → ℂ}
    (hφ : φ ∈ LinearMap.range (Matrix.toLin' ((A i₀) ^ D)))
    (ψ : Fin D → ℂ) :
    vecMulVec φ ψ ∈ wordSpan A (m + n) :=
  Kraus.vecMulVec_mem_wordSpan_of_rectSpan_eq_range A i₀ hPmem heq hφ ψ

/-- The `D`-th power of one matrix in a family belongs to its length-`D` word span. -/
theorem pow_mem_wordSpan (A : MPSTensor d D) (i₀ : Fin d) :
    (A i₀) ^ D ∈ wordSpan A D :=
  Kraus.pow_mem_wordSpan A i₀

/-- The `k`-th power of one matrix in a family belongs to its length-`k` word span. -/
theorem pow_mem_wordSpan' (A : MPSTensor d D) (i₀ : Fin d) (k : ℕ) :
    (A i₀) ^ k ∈ wordSpan A k :=
  Kraus.pow_mem_wordSpan' A i₀ k

/-- A nonzero-eigenvalue eigenvector belongs to the range of the `D`-th power. -/
theorem eigenvector_mem_range_toLin_pow
    (A : MPSTensor d D) (i₀ : Fin d)
    {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    φ ∈ LinearMap.range (Matrix.toLin' ((A i₀) ^ D)) :=
  Kraus.eigenvector_mem_range_toLin_pow A i₀ hμ heig

/-- A nonzero-eigenvalue eigenvector belongs to the range of every matrix power. -/
theorem eigenvector_mem_range_toLin_pow'
    (A : MPSTensor d D) (i₀ : Fin d) (k : ℕ)
    {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    φ ∈ LinearMap.range (Matrix.toLin' ((A i₀) ^ k)) :=
  Kraus.eigenvector_mem_range_toLin_pow' A i₀ k hμ heig

/-- A nonzero-eigenvalue eigenvector gives rank-one matrices in a bounded word span
once the corresponding rectangular span has stabilized. -/
theorem vecMulVec_eigenvector_mem_wordSpan
    (A : MPSTensor d D) (i₀ : Fin d) {n : ℕ}
    {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ)
    (hstab : rectSpan ((A i₀) ^ D) A n =
             LinearMap.range (LinearMap.mulLeft ℂ ((A i₀) ^ D)))
    (ψ : Fin D → ℂ) :
    vecMulVec φ ψ ∈ wordSpan A (D + n) :=
  Kraus.vecMulVec_eigenvector_mem_wordSpan A i₀ hμ heig hstab ψ

end MPSTensor
