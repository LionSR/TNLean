/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.MPDO.VerticalCF

/-!
# Distinguished reference corners for grouped vertical sectors

This file transports the distinguished physical corner of a vertical phase
class to the bond dimension of any chosen copy.  The construction depends only
on the grouped corner equations and is shared by the literal CPSV and
normalized BNT-refined Figure 8 arguments.

## Main result

* `MPOTensor.exists_distinguished_grouped_reference_corner`: the transported
  identity-gauge corner at the bond dimension of a chosen grouped copy.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1903--1919.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D m n : ℕ}

/-- Transporting a vertical corner along an equality of its bond dimensions
preserves its corner identity. -/
private theorem vertical_corner_cast (M : MPOTensor d D)
    (A : MPSTensor (D * D) m) (V : Matrix (Fin d) (Fin m) ℂ)
    (c : ℂ) (hcorner : ∀ v, Vᴴ * verticalTensor M v * V = c • A v)
    (h : m = n) (v : Fin (D * D)) :
    let A' := cast (congrArg (MPSTensor (D * D)) h) A
    let V' := cast (congrArg (fun k ↦ Matrix (Fin d) (Fin k) ℂ) h) V
    V'ᴴ * verticalTensor M v * V' = c • A' v := by
  cases h
  simpa using hcorner v

/-- Two successive transports from a common dimension agree with the direct
transport. -/
private theorem cast_via_common_dimension {k : ℕ} (F : ℕ → Type)
    (hmk : m = k) (hmn : m = n) (x : F m) :
    cast (congrArg F (hmk.symm.trans hmn))
        (cast (congrArg F hmk) x) =
      cast (congrArg F hmn) x := by
  subst k
  subst n
  rfl

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- Transport the distinguished physical corner of a grouped phase class to the
bond dimension of a chosen copy.

The construction uses only the grouped corner equations, positivity of their
effective coefficients, and the identity gauge at the distinguished copy.  It
is independent of the canonical-form hypothesis used later to compare the two
corners by Figure 8.

Source context: arXiv:1606.00608, proof of Proposition 4.13, lines
1903--1919. -/
theorem exists_distinguished_grouped_reference_corner
    {M : MPOTensor d D}
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (X : (j : Fin (C).g) → (q : Fin ((C).copies j)) →
      GL (Fin (dim ((C).enum j q))) ℂ)
    (ζ : (j : Fin (C).g) → Fin ((C).copies j) → ℂ)
    (hXDist : ∀ j, X j ⟨0, (C).copies_pos j⟩ = 1)
    (hCoeffPos : ∀ j q, (0 : ℂ) < μ ((C).enum j q) * ζ j q)
    (hCorner : ∀ j q v,
      (μ ((C).enum j q) * ζ j q) •
          ((X j q : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
      (blocks ((C).repr j))
    ∃ (W : Matrix (Fin d) (Fin (dim ((C).enum j q))) ℂ) (c0 : ℂ),
      (0 : ℂ) < c0 ∧ ∀ w, Wᴴ * verticalTensor M w * W = c0 • A w := by
  classical
  let q0 : Fin ((C).copies j) := ⟨0, (C).copies_pos j⟩
  let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
    (blocks ((C).repr j))
  let A0 := cast (congrArg (MPSTensor (D * D)) (hdim j q0))
    (blocks ((C).repr j))
  let h0q := (hdim j q0).symm.trans (hdim j q)
  let W := cast
    (congrArg (fun k ↦ Matrix (Fin d) (Fin k) ℂ) h0q)
    (V ((C).enum j q0))
  let c0 := μ ((C).repr j) * ζ j q0
  have hEnum0 : (C).enum j q0 = (C).repr j := by
    exact MPSTensor.mpvPhaseClassData_enum_zero_eq_repr blocks j
  have hc0 : (0 : ℂ) < c0 := by
    simpa [c0, q0, hEnum0] using hCoeffPos j q0
  have hcoeff0 : μ ((C).enum j q0) * ζ j q0 = c0 := by
    change μ ((C).enum j q0) * ζ j q0 = μ ((C).repr j) * ζ j q0
    rw [hEnum0]
  have hCorner0 : ∀ w,
      (V ((C).enum j q0))ᴴ * verticalTensor M w * V ((C).enum j q0) =
        c0 • A0 w := by
    intro w
    have h := (hCorner j q0 w).symm
    rw [hXDist j] at h
    rw [inv_one, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mul, Matrix.mul_one] at h
    rw [hcoeff0] at h
    simpa [A0, q0] using h
  have hAtransport :
      cast (congrArg (MPSTensor (D * D)) h0q) A0 = A := by
    exact cast_via_common_dimension (MPSTensor (D * D))
      (hdim j q0) (hdim j q) (blocks ((C).repr j))
  refine ⟨W, c0, hc0, ?_⟩
  intro w
  have h := vertical_corner_cast M A0 (V ((C).enum j q0))
    c0 hCorner0 h0q w
  simpa [W, hAtransport] using h

end GroupedSectors

end MPOTensor
