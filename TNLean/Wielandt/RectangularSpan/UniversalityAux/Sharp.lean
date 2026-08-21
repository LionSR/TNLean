/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Sharp
import TNLean.Wielandt.RectangularSpan.UniversalityAux.Basic

/-!
# Sharp rectangular-span bounds for matrix product tensors

The sharp nilpotent-index estimates for arbitrary Kraus families imply the corresponding
rectangular-span bounds for matrix product tensors.
-/

open scoped Matrix

namespace MPSTensor

open Matrix Module Wielandt

variable {d D : ℕ}

/-- The ranks of the nilpotent-index and `D`-th powers agree. -/
theorem rank_pow_nilpIndex_eq (A : MPSTensor d D)
    (i₀ : Fin d) :
    ((A i₀) ^ nilpIndex (toLin' (A i₀))).rank =
      ((A i₀) ^ D).rank :=
  Kraus.rank_pow_nilpIndex_eq A i₀

/-- The rank of the `D`-th power and the generalized zero-eigenspace dimension sum to `D`. -/
theorem rank_pow_D_add_dimV0 (A : MPSTensor d D)
    (i₀ : Fin d) :
    ((A i₀) ^ D).rank +
      finrank ℂ ↥(End.maxGenEigenspace
        (toLin' (A i₀)) 0) = D :=
  Kraus.rank_pow_D_add_dimV0 A i₀

/-- Left multiplication by the nilpotent-index and `D`-th powers have equal ranges. -/
theorem range_mulLeft_pow_nilpIndex_eq
    (A : MPSTensor d D) (i₀ : Fin d) :
    LinearMap.range (LinearMap.mulLeft ℂ
      ((A i₀) ^ nilpIndex (toLin' (A i₀)))) =
    LinearMap.range
      (LinearMap.mulLeft ℂ ((A i₀) ^ D)) :=
  Kraus.range_mulLeft_pow_nilpIndex_eq A i₀

/-- A nonzero-eigenvalue eigenvector belongs to the range of the nilpotent-index power. -/
theorem eigenvector_mem_range_toLin_pow_nilpIndex
    (A : MPSTensor d D) (i₀ : Fin d)
    {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    φ ∈ LinearMap.range (toLin'
      ((A i₀) ^ nilpIndex (toLin' (A i₀)))) :=
  Kraus.eigenvector_mem_range_toLin_pow_nilpIndex A i₀ hμ heig

/-- Rank-one matrices from a nonzero-eigenvalue eigenvector belong to the
corresponding word span. -/
theorem vecMulVec_eigenvector_mem_wordSpan_nilpIndex
    (A : MPSTensor d D) (i₀ : Fin d) {n : ℕ}
    {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ)
    (hstab : rectSpan
      ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n =
      LinearMap.range (LinearMap.mulLeft ℂ
        ((A i₀) ^ nilpIndex (toLin' (A i₀))))) :
    ∀ ψ : Fin D → ℂ,
      vecMulVec φ ψ ∈ wordSpan A
        (nilpIndex (toLin' (A i₀)) + n) :=
  Kraus.vecMulVec_eigenvector_mem_wordSpan_nilpIndex A i₀ hμ heig hstab

/-- The nilpotent-index route satisfies the sharp bound `D² - D + 1`. -/
theorem sharp_bound_le (A : MPSTensor d D)
    (i₀ : Fin d)
    (hNotInv : ¬ IsUnit (toLin' (A i₀))) :
    D * ((A i₀) ^ D).rank +
      nilpIndex (toLin' (A i₀)) ≤
        D ^ 2 - D + 1 :=
  Kraus.sharp_bound_le A i₀ hNotInv

/-- Stabilization within the rank bound gives the sharp cumulative-span bound. -/
theorem vecMulVec_eigenvector_sharp_of_rectSpan
    (A : MPSTensor d D) (i₀ : Fin d)
    (hNotInv : ¬ IsUnit (toLin' (A i₀)))
    {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ)
    {n₀ : ℕ} (hn₀ : n₀ ≤ D * ((A i₀) ^ D).rank)
    (hstab : rectSpan
      ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n₀ =
      LinearMap.range (LinearMap.mulLeft ℂ
        ((A i₀) ^ nilpIndex (toLin' (A i₀))))) :
    ∀ ψ : Fin D → ℂ,
      vecMulVec φ ψ ∈
        cumulativeSpan A (D ^ 2 - D + 1) :=
  Kraus.vecMulVec_eigenvector_sharp_of_rectSpan A i₀ hNotInv hμ heig hn₀ hstab

end MPSTensor
