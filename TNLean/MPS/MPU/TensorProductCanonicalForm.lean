/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.Core.TensorProduct
import TNLean.MPS.MPU.TensorProduct
import TNLean.MPS.MPU.TransferMatrix

/-!
# Normalized flattening of an independent tensor product

This file identifies the normalized doubled-index MPS tensor of an independent
MPO tensor product with the independent tensor product of the two normalized
flattenings.  The physical coordinate is regrouped in the canonical
product-coordinate order
`((i, k), (j, l)) ↦ ((i, j), (k, l))`.

## Main statement

* `MPOTensor.normalizedFlattening_tensorProduct`: normalized flattening commutes
  with independent tensor products after the doubled-product coordinate change.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188], equation
  `eq:transfer-op`, lines 336--340, and the proof of Theorem `IndexTh` (ii),
  lines 824--845.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D e E : ℕ}

/-- Normalized flattening commutes with independent tensor products after the
doubled physical coordinate change
`((i, k), (j, l)) ↦ ((i, j), (k, l))`.

The scalar equality is
`(sqrt (d * e))⁻¹ = (sqrt d)⁻¹ * (sqrt e)⁻¹`; it holds without nonzero-dimension
hypotheses because inverses in `ℂ` are totalized.
This identity makes explicit the normalized-flattening compatibility
corresponding to the tensoring clause in arXiv:1703.09188, proof of Theorem
`IndexTh` (ii), lines 824--845; the paper does not state it separately. -/
theorem normalizedFlattening_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    (tensorProduct U V).normalizedFlattening =
      Kraus.reindexPhysical (finDoubledProdEquiv d e)
        (MPSTensor.tensorProduct U.normalizedFlattening V.normalizedFlattening) := by
  have hsqrt :
      (Real.sqrt ((d * e : ℕ) : ℝ) : ℂ) =
        (Real.sqrt d : ℂ) * (Real.sqrt e : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  funext q
  rcases finProdFinEquiv.surjective q with ⟨⟨ik, jl⟩, rfl⟩
  rcases finProdFinEquiv.surjective ik with ⟨⟨i, k⟩, rfl⟩
  rcases finProdFinEquiv.surjective jl with ⟨⟨j, l⟩, rfl⟩
  ext αγ βδ
  rcases finProdFinEquiv.surjective αγ with ⟨⟨α, γ⟩, rfl⟩
  rcases finProdFinEquiv.surjective βδ with ⟨⟨β, δ⟩, rfl⟩
  simp only [normalizedFlattening, Kraus.reindexPhysical,
    finDoubledProdEquiv_apply, MPSTensor.tensorProduct_apply,
    MPOTensor.tensorProduct_apply, toMPSTensor,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat,
    Matrix.smul_apply, smul_eq_mul]
  rw [hsqrt, mul_inv]
  ring

end MPOTensor
