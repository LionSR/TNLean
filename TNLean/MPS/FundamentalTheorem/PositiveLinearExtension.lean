/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.PositiveSkolemNoether
import TNLean.MPS.FundamentalTheorem.ProductAlgebra

/-!
# Positive per-block linear extensions

The linear extension between two matched injective matrix-product tensors is
already unital, multiplicative, and bijective.  If it is also positive, then
it is implemented by unitary conjugation.

## Main results

* `exists_unitary_conj_of_positive_perBlockLinearExtension`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 1955--1997
* [Wolf--Perez-Garcia 2010] arXiv:1005.4545, Theorem 8
-/

open scoped Matrix

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- A positive per-block linear extension between matched injective tensors
is implemented by unitary conjugation.

**Scope restriction (positive linear extension):** Positivity of the virtual
linear extension is assumed, not deduced from equality of closed chains or
from a tensor-attached BNT algebra clause.  The missing deduction is recorded
in `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Appendix C.4, lines 1955--1997,
together with Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8. -/
theorem exists_unitary_conj_of_positive_perBlockLinearExtension
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r)
    (hPos : IsPositiveMap (perBlockLinearExtension A B hA hSame k)) :
    ∃ U : Matrix.unitaryGroup (Fin (dim k)) ℂ,
      ∀ M : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
        perBlockLinearExtension A B hA hSame k M =
          (U : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * M *
            (U : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)ᴴ :=
  exists_unitary_conj_of_positive_bijective_multiplicative_matrix_linearMap
    (perBlockLinearExtension A B hA hSame k)
    (perBlockLinearExtension_mul A B hA hSame k)
    (perBlockLinearExtension_bijective A B hA hSame k)
    hPos

end MPSTensor
