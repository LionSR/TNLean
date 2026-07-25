/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalSectorRetractions
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Product spans of fixed points on vertical-sector algebras

This file defines the span of pointwise products of fixed points of a linear
endomorphism on a direct product of matrix algebras.

## Main declarations

* `MPOTensor.fixedPointProductSpan`: the span of fixed-point products of a
  prescribed length.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1980--1993.
-/

open scoped Matrix

noncomputable section

namespace MPOTensor

/-- The span of all $L$-fold products of fixed points of a linear
endomorphism of the vertical-sector algebra.

This is the space denoted by $C_L(\mathcal F)$ in the dimension argument of the
general MPDO renormalization fixed-point theorem.

Source: arXiv:1606.00608, Appendix C.4, lines 1980--1993. -/
def fixedPointProductSpan
    {g : ℕ} {dim : Fin g → ℕ} (L : ℕ)
    (F : VerticalSectorAlgebra dim →ₗ[ℂ] VerticalSectorAlgebra dim) :
    Submodule ℂ (VerticalSectorAlgebra dim) :=
  Submodule.span ℂ (Set.range fun X : Fin L → F.fixedSubmodule =>
    fun α => (List.ofFn fun t => (X t : VerticalSectorAlgebra dim) α).prod)

end MPOTensor
