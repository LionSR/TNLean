/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.FigureEightPairwise
import TNLean.MPS.MPDO.VerticalBNT

/-!
# Figure 8 for grouped vertical sectors

This file applies the pairwise reflected form of Lemma L to the actual
vertical corners and gauges furnished by the grouped vertical decomposition
under normalized BNT-refined horizontal form.

## Main result

* `IsMPDO.grouped_sector_gram_conj_eq`: the Gram conjugation of each grouped
  copy fixes the transported representative tensor.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, Figures 7--8 and lines 1909--1919.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D m n : ℕ}

/-- Transporting a vertical corner along an equality of its bond dimensions
preserves its corner identity.

Source context: arXiv:1606.00608, proof of Proposition 4.13, lines
1898--1919. -/
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
transport.  This isolates the dependent cast used for the distinguished
sector in Figure 8.

Source context: arXiv:1606.00608, proof of Proposition 4.13, lines
1909--1919. -/
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

/-- **Figure 8 for an actual grouped sector and its distinguished copy.**

Assume the phase-class gauges, positive coefficients, and physical corner
identities furnished by `exists_verticalBNTGrouping_with_isometry`.  For each
copy `q`, transport the distinguished physical corner to the bond dimension
of `q` and apply the pairwise reflected form of Lemma L.  The resulting Gram
conjugation fixes the transported representative tensor.

No identity between an individual dressed tensor and its raw reflected
adjoint is used or asserted.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is the
normalized BNT-refined horizontal form, stronger than the literal CPSV
canonical form; see `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
theorem IsMPDO.grouped_sector_gram_conj_eq
    {M : MPOTensor d D} (hM : IsMPDO M)
    (hHorizontal : IsHorizontalCF M)
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
    (j : Fin (C).g) (q : Fin ((C).copies j))
    (v : Fin (D * D)) :
    let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
      (blocks ((C).repr j))
    let G := (X j q : Matrix (Fin (dim ((C).enum j q)))
      (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q
    G * A v * G⁻¹ = A v := by
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
  let cq := μ ((C).enum j q) * ζ j q
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
  have hCorner0cast : ∀ w,
      Wᴴ * verticalTensor M w * W = c0 • A w := by
    intro w
    have h := vertical_corner_cast M A0 (V ((C).enum j q0))
      c0 hCorner0 h0q w
    simpa [W, hAtransport] using h
  have hCornerq : ∀ w,
      (V ((C).enum j q))ᴴ * verticalTensor M w * V ((C).enum j q) =
        cq • ((X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ) * A w *
          (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ)) := by
    intro w
    simpa [cq, A] using (hCorner j q w).symm
  have hGram := hHorizontal.gramDressing_eq_of_two_grouped_corners
    M hM A (V ((C).enum j q)) W (X j q) 1 cq c0
    (hCoeffPos j q) hc0 hCornerq
    (by intro w; simpa using hCorner0cast w)
  simpa [gramDressing, A] using congrFun hGram v

end GroupedSectors

end MPOTensor
