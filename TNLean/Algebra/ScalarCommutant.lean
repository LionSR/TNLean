import TNLean.MPS.Defs

import Mathlib.Data.Matrix.Basis

/-!
# Scalar commutant lemma

If a matrix `Z` commutes with every element of a spanning set of `M_n(ℂ)`,
then `Z` is a scalar multiple of the identity.  This is the algebraic fact
that the center of `M_n(ℂ)` is `ℂ · 1`.

## Main results

* `commutant_of_span_top_is_scalar` – the abstract version for any spanning set.
* `MPSTensor.IsInjective.commutant_is_scalar` – the MPS corollary:  for an
  injective MPS tensor `A`, any `Z` commuting with every `A i` is scalar.
-/

open scoped Matrix

/-! ### Abstract scalar commutant lemma -/

/-- The set `{M | Z * M = M * Z}` is a submodule of `Matrix (Fin D) (Fin D) ℂ`. -/
private def commutantSubmodule {D : ℕ} (Z : Matrix (Fin D) (Fin D) ℂ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) where
  carrier := {M | Z * M = M * Z}
  add_mem' {a b} (ha : Z * a = a * Z) (hb : Z * b = b * Z) := by
    simp [mul_add, add_mul, ha, hb]
  zero_mem' := by simp
  smul_mem' c M (hM : Z * M = M * Z) := by
    change Z * (c • M) = (c • M) * Z
    simp [hM]

/-- If `Z` commutes with every element of a set `S` that spans `⊤`, then `Z`
commutes with every matrix. -/
private lemma commutes_of_span_top {D : ℕ}
    (Z : Matrix (Fin D) (Fin D) ℂ)
    {S : Set (Matrix (Fin D) (Fin D) ℂ)} (hS : Submodule.span ℂ S = ⊤)
    (hZ : ∀ M ∈ S, Z * M = M * Z) (M : Matrix (Fin D) (Fin D) ℂ) :
    Z * M = M * Z := by
  have hle : Submodule.span ℂ S ≤ commutantSubmodule Z :=
    Submodule.span_le.mpr (fun x hx => hZ x hx)
  exact hle (hS ▸ Submodule.mem_top)

/-- **Scalar commutant lemma**: if `Z` commutes with every element of a
spanning set of `M_n(ℂ)`, then `Z = c • 1` for some scalar `c : ℂ`. -/
lemma commutant_of_span_top_is_scalar [NeZero D]
    (Z : Matrix (Fin D) (Fin D) ℂ)
    {S : Set (Matrix (Fin D) (Fin D) ℂ)} (hS : Submodule.span ℂ S = ⊤)
    (hZ : ∀ M ∈ S, Z * M = M * Z) :
    ∃ c : ℂ, Z = c • 1 := by
  -- Z commutes with everything, so it is in the center.
  have hcomm : ∀ M, Z * M = M * Z := commutes_of_span_top Z hS hZ
  have hcenter : Z ∈ Set.center (Matrix (Fin D) (Fin D) ℂ) := by
    rw [Set.mem_center_iff]
    exact ⟨fun a => (hcomm a), fun _ _ => (Matrix.mul_assoc _ _ _).symm,
           fun _ _ => Matrix.mul_assoc _ _ _⟩
  -- For a commutative base ring, the center of M_n(R) is the range of `scalar`.
  rw [Matrix.center_eq_range] at hcenter
  obtain ⟨c, hc⟩ := hcenter
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

/-! ### MPS corollary -/

namespace MPSTensor

variable {d D : ℕ}

/-- For an injective MPS tensor `A` (whose matrices span `M_D(ℂ)`), any matrix
`Z` that commutes with every `A i` is a scalar multiple of the identity. -/
theorem IsInjective.commutant_is_scalar [NeZero D]
    {A : MPSTensor d D} (hA : IsInjective A) (Z : Matrix (Fin D) (Fin D) ℂ)
    (hZ : ∀ i : Fin d, Z * A i = A i * Z) :
    ∃ c : ℂ, Z = c • 1 := by
  apply commutant_of_span_top_is_scalar Z hA.span_eq_top
  intro M hM
  obtain ⟨i, rfl⟩ := hM
  exact hZ i

end MPSTensor
