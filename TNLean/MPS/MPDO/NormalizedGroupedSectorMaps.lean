/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixGramUnitary
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.MPDO.VerticalCF

/-!
# Normalized maps for grouped vertical sectors

This file absorbs each normalized grouped bond gauge into its physical sector
isometry.  The resulting maps have the representative bond dimensions, have
pairwise orthogonal isometric ranges, intertwine the vertical tensor with the
undressed representative tensors, and retain the literal reconstruction of
every vertical letter.

The final theorem takes the positive Gram scalar of each grouped gauge as
an abstract hypothesis, so both horizontal and literal canonical-form arguments
can use the same construction without importing one another.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1895--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

section LinearAlgebra

variable {m n : ℕ}

@[simp]
private theorem cast_MPSTensor_apply {s : ℕ} (h : m = n)
    (A : MPSTensor s m) (v : Fin s) :
    (cast (congrArg (MPSTensor s) h) A) v =
      cast (congrArg (fun k ↦ Matrix (Fin k) (Fin k) ℂ) h) (A v) := by
  cases h
  rfl

/-- Absorb the normalized square gauge into a rectangular physical sector map
and transport its column index to the representative bond dimension.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
noncomputable def normalizedGroupedSectorMap (h : m = n)
    (V : Matrix (Fin d) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (omega : ℝ) : Matrix (Fin d) (Fin m) ℂ :=
  cast (congrArg (fun k ↦ Matrix (Fin d) (Fin k) ℂ) h.symm)
    (V * (((Real.sqrt omega : ℂ))⁻¹ • X))

/-- Absorbing a normalized unitary gauge into an isometry preserves its
isometry relation.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem normalizedGroupedSectorMap_isometry (h : m = n)
    (V : Matrix (Fin d) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (omega : ℝ) (hV : Vᴴ * V = 1)
    (hQ : (((Real.sqrt omega : ℂ))⁻¹ • X) ∈
      Matrix.unitaryGroup (Fin n) ℂ) :
    (normalizedGroupedSectorMap h V X omega)ᴴ *
        normalizedGroupedSectorMap h V X omega = 1 := by
  cases h
  simp only [normalizedGroupedSectorMap, cast_eq, Matrix.conjTranspose_mul]
  calc
    ((((Real.sqrt omega : ℂ))⁻¹ • X)ᴴ * Vᴴ) *
        (V * (((Real.sqrt omega : ℂ))⁻¹ • X)) =
      (((Real.sqrt omega : ℂ))⁻¹ • X)ᴴ *
        (Vᴴ * V) * (((Real.sqrt omega : ℂ))⁻¹ • X) := by
          simp only [Matrix.mul_assoc]
    _ = (((Real.sqrt omega : ℂ))⁻¹ • X)ᴴ *
        (((Real.sqrt omega : ℂ))⁻¹ • X) := by rw [hV, Matrix.mul_one]
    _ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp hQ

/-- Absorbing normalized gauges into two orthogonal sector maps preserves
their orthogonality.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem normalizedGroupedSectorMap_orthogonal
    {m₁ n₁ m₂ n₂ : ℕ} (h₁ : m₁ = n₁) (h₂ : m₂ = n₂)
    (V₁ : Matrix (Fin d) (Fin n₁) ℂ) (V₂ : Matrix (Fin d) (Fin n₂) ℂ)
    (X₁ : Matrix (Fin n₁) (Fin n₁) ℂ)
    (X₂ : Matrix (Fin n₂) (Fin n₂) ℂ) (omega₁ omega₂ : ℝ)
    (hV : V₁ᴴ * V₂ = 0) :
    (normalizedGroupedSectorMap h₁ V₁ X₁ omega₁)ᴴ *
        normalizedGroupedSectorMap h₂ V₂ X₂ omega₂ = 0 := by
  cases h₁
  cases h₂
  simp only [normalizedGroupedSectorMap, cast_eq, Matrix.conjTranspose_mul]
  calc
    ((((Real.sqrt omega₁ : ℂ))⁻¹ • X₁)ᴴ * V₁ᴴ) *
        (V₂ * (((Real.sqrt omega₂ : ℂ))⁻¹ • X₂)) =
      (((Real.sqrt omega₁ : ℂ))⁻¹ • X₁)ᴴ *
        (V₁ᴴ * V₂) * (((Real.sqrt omega₂ : ℂ))⁻¹ • X₂) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hV, Matrix.mul_zero, Matrix.zero_mul]

private theorem normalized_gauge_intertwining
    (T : Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (V : Matrix (Fin d) (Fin n) ℂ) (X : GL (Fin n) ℂ)
    (c : ℂ) (omega : ℝ)
    (hinter : T * V = V *
      (c • ((X : Matrix (Fin n) (Fin n) ℂ) * A *
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ)))) :
    T * (V * (((Real.sqrt omega : ℂ))⁻¹ •
        (X : Matrix (Fin n) (Fin n) ℂ))) =
      (V * (((Real.sqrt omega : ℂ))⁻¹ •
        (X : Matrix (Fin n) (Fin n) ℂ))) * (c • A) := by
  rw [← Matrix.mul_assoc, hinter]
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
  rw [show (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ) *
      (X : Matrix (Fin n) (Fin n) ℂ) = 1 by exact X.inv_val]
  simp only [Matrix.mul_one, smul_smul]
  rw [mul_comm (((Real.sqrt omega : ℂ))⁻¹) c]

private theorem normalized_gauge_corner
    (A : Matrix (Fin n) (Fin n) ℂ) (X : GL (Fin n) ℂ)
    (c : ℂ) (omega : ℝ) (homega : 0 < omega)
    (hGram : (X : Matrix (Fin n) (Fin n) ℂ)ᴴ * X = (omega : ℂ) • 1) :
    (((Real.sqrt omega : ℂ))⁻¹ •
          (X : Matrix (Fin n) (Fin n) ℂ)) * (c • A) *
        (((Real.sqrt omega : ℂ))⁻¹ •
          (X : Matrix (Fin n) (Fin n) ℂ))ᴴ =
      c • ((X : Matrix (Fin n) (Fin n) ℂ) * A *
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ)) := by
  have hs_sq : Real.sqrt omega * Real.sqrt omega = omega :=
    Real.mul_self_sqrt homega.le
  have hconjs : star ((Real.sqrt omega : ℂ))⁻¹ =
      ((Real.sqrt omega : ℂ))⁻¹ := by
    rw [star_inv₀]
    congr 1
    exact Complex.conj_ofReal _
  have hscalar : ((Real.sqrt omega : ℂ))⁻¹ *
      ((Real.sqrt omega : ℂ))⁻¹ * (omega : ℂ) = 1 := by
    rw [show ((omega : ℝ) : ℂ) =
        (Real.sqrt omega : ℂ) * (Real.sqrt omega : ℂ) by
      rw [← Complex.ofReal_mul, hs_sq]]
    field_simp
  have hXstar : (X : Matrix (Fin n) (Fin n) ℂ)ᴴ =
      (omega : ℂ) • (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ) := by
    have hXinv : (X : Matrix (Fin n) (Fin n) ℂ) *
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      exact X.val_inv
    calc
      (X : Matrix (Fin n) (Fin n) ℂ)ᴴ =
          (X : Matrix (Fin n) (Fin n) ℂ)ᴴ *
            ((X : Matrix (Fin n) (Fin n) ℂ) *
              (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ)) := by
                rw [hXinv, Matrix.mul_one]
      _ = ((X : Matrix (Fin n) (Fin n) ℂ)ᴴ * X) *
          (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ) := by
            rw [Matrix.mul_assoc]
      _ = (omega : ℂ) • (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ) := by
            rw [hGram, Matrix.smul_mul, Matrix.one_mul]
  rw [Matrix.conjTranspose_smul, hconjs, hXstar]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [show ((Real.sqrt omega : ℂ))⁻¹ * (omega : ℂ) *
      (c * ((Real.sqrt omega : ℂ))⁻¹) = c by
    calc
      ((Real.sqrt omega : ℂ))⁻¹ * (omega : ℂ) *
          (c * ((Real.sqrt omega : ℂ))⁻¹) =
        c * (((Real.sqrt omega : ℂ))⁻¹ *
          ((Real.sqrt omega : ℂ))⁻¹ * (omega : ℂ)) := by ring
      _ = c := by rw [hscalar, mul_one]]

/-- The normalized sector map intertwines with the ungauged representative
tensor.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem normalizedGroupedSectorMap_intertwining (h : m = n)
    (T : Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (V : Matrix (Fin d) (Fin n) ℂ) (X : GL (Fin n) ℂ)
    (c : ℂ) (omega : ℝ)
    (hinter : T * V = V *
      (c • ((X : Matrix (Fin n) (Fin n) ℂ) *
        (cast (congrArg (fun k ↦ Matrix (Fin k) (Fin k) ℂ) h) A) *
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ)))) :
    T * normalizedGroupedSectorMap h V X omega =
      normalizedGroupedSectorMap h V X omega * (c • A) := by
  cases h
  exact normalized_gauge_intertwining T A V X c omega hinter

/-- Conjugation by the normalized sector map reproduces the original gauged
corner exactly.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem normalizedGroupedSectorMap_corner (h : m = n)
    (A : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin d) (Fin n) ℂ)
    (X : GL (Fin n) ℂ) (c : ℂ) (omega : ℝ) (homega : 0 < omega)
    (hGram : (X : Matrix (Fin n) (Fin n) ℂ)ᴴ * X = (omega : ℂ) • 1) :
    normalizedGroupedSectorMap h V X omega * (c • A) *
        (normalizedGroupedSectorMap h V X omega)ᴴ =
      V * (c • ((X : Matrix (Fin n) (Fin n) ℂ) *
        (cast (congrArg (fun k ↦ Matrix (Fin k) (Fin k) ℂ) h) A) *
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ))) * Vᴴ := by
  cases h
  simp only [normalizedGroupedSectorMap, cast_eq, Matrix.conjTranspose_mul]
  calc
    (V * (((Real.sqrt omega : ℂ))⁻¹ •
          (X : Matrix (Fin m) (Fin m) ℂ))) * (c • A) *
        ((((Real.sqrt omega : ℂ))⁻¹ •
          (X : Matrix (Fin m) (Fin m) ℂ))ᴴ * Vᴴ) =
      V * ((((Real.sqrt omega : ℂ))⁻¹ •
          (X : Matrix (Fin m) (Fin m) ℂ)) * (c • A) *
        (((Real.sqrt omega : ℂ))⁻¹ •
          (X : Matrix (Fin m) (Fin m) ℂ))ᴴ) * Vᴴ := by
            simp only [Matrix.mul_assoc]
    _ = V * (c • ((X : Matrix (Fin m) (Fin m) ℂ) * A *
        (↑(X⁻¹) : Matrix (Fin m) (Fin m) ℂ))) * Vᴴ := by
          rw [normalized_gauge_corner A X c omega homega hGram]

end LinearAlgebra

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- The normalized grouped gauges can be absorbed into the physical sector
maps without changing the literal vertical decomposition.

The new map for the copy $(j,q)$ is
$W_{j,q}=V_{j,q}\omega_{j,q}^{-1/2}X_{j,q}$, with its columns transported
from the copy bond space to the representative bond space.  These maps are
isometries with mutually orthogonal ranges and intertwine the vertical tensor
with the undressed representative tensors.

The Gram hypothesis is the sole canonical-form-specific input.  The remaining
hypotheses describe the grouped vertical sectors and their exact reconstruction.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1895--1921. -/
theorem exists_normalized_grouped_sector_maps_of_gram
    {M : MPOTensor d D}
    (mu : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (X : (j : Fin (C).g) → (q : Fin ((C).copies j)) →
      GL (Fin (dim ((C).enum j q))) ℂ)
    (zeta : (j : Fin (C).g) → Fin ((C).copies j) → ℂ)
    (hGram : ∀ j q, ∃ omega : ℝ, 0 < omega ∧
      (X j q : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q = (omega : ℂ) • 1)
    (hIso : ∀ j q, (V ((C).enum j q))ᴴ * V ((C).enum j q) = 1)
    (hOrth : ∀ j q l p, (C).enum j q ≠ (C).enum l p →
      (V ((C).enum j q))ᴴ * V ((C).enum l p) = 0)
    (hInter : ∀ j q v, verticalTensor M v * V ((C).enum j q) =
      V ((C).enum j q) *
        ((mu ((C).enum j q) * zeta j q) •
          ((X j q : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ))))
    (hReconstruct : ∀ v, verticalTensor M v =
      ∑ j : Fin (C).g, ∑ q : Fin ((C).copies j),
        V ((C).enum j q) *
          ((mu ((C).enum j q) * zeta j q) •
            ((X j q : Matrix (Fin (dim ((C).enum j q)))
                (Fin (dim ((C).enum j q))) ℂ) *
              (cast (congrArg (MPSTensor (D * D)) (hdim j q))
                (blocks ((C).repr j))) v *
              (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
                (Fin (dim ((C).enum j q))) ℂ))) *
          (V ((C).enum j q))ᴴ) :
    ∃ (omega : (j : Fin (C).g) → Fin ((C).copies j) → ℝ)
      (W : (p : (j : Fin (C).g) × Fin ((C).copies j)) →
        Matrix (Fin d) (Fin (dim ((C).repr p.1))) ℂ),
      (∀ j q, 0 < omega j q) ∧
      (∀ p, (W p)ᴴ * W p = 1) ∧
      (∀ p q, p ≠ q → (W p)ᴴ * W q = 0) ∧
      (∀ p v, verticalTensor M v * W p =
        W p * ((mu ((C).enum p.1 p.2) * zeta p.1 p.2) •
          blocks ((C).repr p.1) v)) ∧
      ∀ v, verticalTensor M v =
        ∑ j : Fin (C).g, ∑ q : Fin ((C).copies j),
          W ⟨j, q⟩ *
            ((mu ((C).enum j q) * zeta j q) • blocks ((C).repr j) v) *
            (W ⟨j, q⟩)ᴴ := by
  classical
  choose omega homega hGramEq using hGram
  let W : (p : (j : Fin (C).g) × Fin ((C).copies j)) →
      Matrix (Fin d) (Fin (dim ((C).repr p.1))) ℂ := fun p ↦
    normalizedGroupedSectorMap (hdim p.1 p.2) (V ((C).enum p.1 p.2))
      (X p.1 p.2) (omega p.1 p.2)
  have hQ : ∀ j q, (((Real.sqrt (omega j q) : ℂ))⁻¹ •
      (X j q : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ)) ∈
      Matrix.unitaryGroup (Fin (dim ((C).enum j q))) ℂ := by
    intro j q
    exact Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      (homega j q) (hGramEq j q)
  refine ⟨omega, W, homega, ?_, ?_, ?_, ?_⟩
  · intro p
    exact normalizedGroupedSectorMap_isometry (hdim p.1 p.2)
      (V ((C).enum p.1 p.2)) (X p.1 p.2) (omega p.1 p.2)
      (hIso p.1 p.2) (hQ p.1 p.2)
  · intro p q hpq
    have hEnum : (C).enum p.1 p.2 ≠ (C).enum q.1 q.2 := by
      intro h
      apply hpq
      apply (C).enumEquiv.injective
      change (C).enum p.1 p.2 = (C).enum q.1 q.2
      exact h
    exact normalizedGroupedSectorMap_orthogonal
      (hdim p.1 p.2) (hdim q.1 q.2)
      (V ((C).enum p.1 p.2)) (V ((C).enum q.1 q.2))
      (X p.1 p.2) (X q.1 q.2) (omega p.1 p.2) (omega q.1 q.2)
      (hOrth p.1 p.2 q.1 q.2 hEnum)
  · intro p v
    have h := hInter p.1 p.2 v
    rw [cast_MPSTensor_apply (hdim p.1 p.2)] at h
    exact normalizedGroupedSectorMap_intertwining (hdim p.1 p.2)
      (verticalTensor M v) (blocks ((C).repr p.1) v)
      (V ((C).enum p.1 p.2)) (X p.1 p.2)
      (mu ((C).enum p.1 p.2) * zeta p.1 p.2) (omega p.1 p.2) h
  · intro v
    rw [hReconstruct v]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro q _
    have h := normalizedGroupedSectorMap_corner (hdim j q)
      (blocks ((C).repr j) v) (V ((C).enum j q)) (X j q)
      (mu ((C).enum j q) * zeta j q) (omega j q)
      (homega j q) (hGramEq j q)
    rw [← cast_MPSTensor_apply (hdim j q)] at h
    exact h.symm

end GroupedSectors

end MPOTensor
