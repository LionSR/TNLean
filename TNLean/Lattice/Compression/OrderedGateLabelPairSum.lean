/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod

/-! # Summation over ordered ket and bra gate labels

A ket-label function and a bra-label function are equivalent to a single
function assigning their ordered pair to each gate occurrence. Consequently,
a double matrix sum can be written as one sum over these ordered pairs.
The ket and bra coordinates are kept in their original order; no unordered
pair or extension of a partial choice is introduced. Empty gate families and
empty label types are included.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579.
-/

namespace TNLean.PEPS.Approximation
open scoped ComplexConjugate
variable {G : Type} [Fintype G] {Ket Bra : G → Type}
variable [∀ g, Fintype (Ket g)] [∀ g, Fintype (Bra g)] {m n : Type}

open Classical in
/-- Reindex a double matrix sum by the ordered ket and bra labels at each
original gate occurrence. The equivalence pairs the two labels pointwise.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579. -/
theorem sum_gateLabels_eq_sum_orderedGateLabelPairs
    (K : ((g : G) → Ket g) → ((g : G) → Bra g) → Matrix m n ℂ) :
    (∑ η, ∑ θ, K η θ) =
      ∑ ξζ : (g : G) → Ket g × Bra g,
        K (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) := by
  have hProd := (Fintype.sum_prod_type' K).symm
  have hPair := (Equiv.arrowProdEquivProdArrow G Ket Bra).sum_comp
    (fun t : ((g : G) → Ket g) × ((g : G) → Bra g) ↦ K t.1 t.2)
  exact hProd.trans hPair.symm

open Classical in
/-- Reindex the matrix sum with its original gatewise ket and conjugate bra
coefficients. No normalization or nonvanishing of these coefficients is needed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–579. -/
theorem sum_weighted_gateLabels_eq_sum_orderedGateLabelPairs
    (a : (g : G) → Ket g → ℂ) (b : (g : G) → Bra g → ℂ)
    (K : ((g : G) → Ket g) → ((g : G) → Bra g) → Matrix m n ℂ) :
    (∑ η, ∑ θ, (∏ g, a g (η g) * conj (b g (θ g))) • K η θ) =
      ∑ ξζ : (g : G) → Ket g × Bra g,
        (∏ g, a g (ξζ g).1 * conj (b g (ξζ g).2)) •
          K (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) := by
  exact sum_gateLabels_eq_sum_orderedGateLabelPairs
    (fun η θ ↦ (∏ g, a g (η g) * conj (b g (θ g))) • K η θ)

end TNLean.PEPS.Approximation
