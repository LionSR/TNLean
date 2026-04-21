/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.Algebra

/-!
# Choi--Effros identities from fixed-point multiplicativity

In this file we prove a fixed-point-algebra form of the Choi--Effros projected-product
identities for an idempotent unital Kraus map whose adjoint map has a positive definite
fixed point.

## Main results

- `Kraus.choi_effros_left`: if the left factor is already projected, then projecting the
  right factor does not change the final projected product.
- `Kraus.choi_effros_right`: the symmetric statement for the right factor.
- `Kraus.choi_effros_sandwich`: the product of two projected factors is itself fixed.
- `Kraus.choi_effros_left_eq_right`: the left and right projected-product formulas agree.

The proof is short: idempotence makes `E(X)` and `E(Y)` fixed points, Wolf Theorem 6.12
places fixed points in the multiplicative domain, and the multiplicative-domain identities
from Chapter 5 give the projected-product formulas.

This is the version needed later for projected multiplications on ranges of idempotent
maps. The more general completely positive contractive projection theorem is not
formalized here.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private theorem map_fixes_range_of_idempotent
    (K : Fin d → Mat)
    (hIdem : mapLM K ∘ₗ mapLM K = mapLM K)
    (X : Mat) :
    map K (map K X) = map K X := by
  have h := congrArg (fun F : Mat →ₗ[ℂ] Mat => F X) hIdem
  simpa only [LinearMap.comp_apply, mapLM_apply] using h

/-- For an idempotent unital Kraus map with a positive definite adjoint fixed
point, every projected element lies in the multiplicative domain. -/
theorem map_mem_multiplicativeDomain_of_idempotent
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    (hIdem : mapLM K ∘ₗ mapLM K = mapLM K)
    (X : Mat) :
    map K X ∈ KadisonSchwarz.multiplicativeDomain K := by
  have hEX_fix : map K (map K X) = map K X :=
    map_fixes_range_of_idempotent (K := K) hIdem X
  have hEX_mem : map K X ∈ fixedPoints K := hEX_fix
  exact mem_multiplicativeDomain_of_mem_fixedPoints (K := K) h_unital hρ hρ_fix hEX_mem

/-- Left absorption for the projected product attached to an idempotent Kraus map. -/
theorem choi_effros_left
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    (hIdem : mapLM K ∘ₗ mapLM K = mapLM K)
    (X Y : Mat) :
    map K (map K X * Y) = map K (map K X * map K Y) := by
  have hEX_md : map K X ∈ KadisonSchwarz.multiplicativeDomain K :=
    map_mem_multiplicativeDomain_of_idempotent (K := K) h_unital hρ hρ_fix hIdem X
  calc
    map K (map K X * Y)
        = map K (map K X) * map K Y := by
          simpa only [map, KadisonSchwarz.krausMap] using
            (KadisonSchwarz.krausMap_mul_right_of_mem_multiplicativeDomain
              (K := K) hEX_md Y)
    _ = map K X * map K Y := by
          rw [map_fixes_range_of_idempotent (K := K) hIdem X]
    _ = map K (map K X * map K Y) := by
          symm
          rw [show map K (map K X * map K Y) =
              map K (map K X) * map K (map K Y) by
            simpa only [map, KadisonSchwarz.krausMap] using
              (KadisonSchwarz.krausMap_mul_right_of_mem_multiplicativeDomain
                (K := K) hEX_md (map K Y))]
          rw [map_fixes_range_of_idempotent (K := K) hIdem X,
            map_fixes_range_of_idempotent (K := K) hIdem Y]

/-- Right absorption for the projected product attached to an idempotent Kraus map. -/
theorem choi_effros_right
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    (hIdem : mapLM K ∘ₗ mapLM K = mapLM K)
    (X Y : Mat) :
    map K (X * map K Y) = map K (map K X * map K Y) := by
  have hEY_md : map K Y ∈ KadisonSchwarz.multiplicativeDomain K :=
    map_mem_multiplicativeDomain_of_idempotent (K := K) h_unital hρ hρ_fix hIdem Y
  calc
    map K (X * map K Y)
        = map K X * map K (map K Y) := by
          simpa only [map, KadisonSchwarz.krausMap] using
            (KadisonSchwarz.krausMap_mul_left_of_mem_multiplicativeDomain
              (K := K) hEY_md X)
    _ = map K X * map K Y := by
          rw [map_fixes_range_of_idempotent (K := K) hIdem Y]
    _ = map K (map K X * map K Y) := by
          symm
          rw [show map K (map K X * map K Y) =
              map K (map K X) * map K (map K Y) by
            simpa only [map, KadisonSchwarz.krausMap] using
              (KadisonSchwarz.krausMap_mul_left_of_mem_multiplicativeDomain
                (K := K) hEY_md (map K X))]
          rw [map_fixes_range_of_idempotent (K := K) hIdem X,
            map_fixes_range_of_idempotent (K := K) hIdem Y]

/-- The product of two projected factors is itself fixed. -/
theorem choi_effros_sandwich
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    (hIdem : mapLM K ∘ₗ mapLM K = mapLM K)
    (X Y : Mat) :
    map K (map K X * map K Y) = map K X * map K Y := by
  have hEX_md : map K X ∈ KadisonSchwarz.multiplicativeDomain K :=
    map_mem_multiplicativeDomain_of_idempotent (K := K) h_unital hρ hρ_fix hIdem X
  rw [show map K (map K X * map K Y) =
      map K (map K X) * map K (map K Y) by
    simpa only [map, KadisonSchwarz.krausMap] using
      (KadisonSchwarz.krausMap_mul_right_of_mem_multiplicativeDomain
        (K := K) hEX_md (map K Y))]
  rw [map_fixes_range_of_idempotent (K := K) hIdem X,
    map_fixes_range_of_idempotent (K := K) hIdem Y]

/-- The left and right projected-product identities agree. -/
theorem choi_effros_left_eq_right
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    (hIdem : mapLM K ∘ₗ mapLM K = mapLM K)
    (X Y : Mat) :
    map K (map K X * Y) = map K (X * map K Y) := by
  rw [choi_effros_left (K := K) h_unital hρ hρ_fix hIdem X Y,
    choi_effros_right (K := K) h_unital hρ hρ_fix hIdem X Y]

end Kraus
