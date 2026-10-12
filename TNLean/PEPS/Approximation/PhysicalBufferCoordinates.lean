/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SitewiseTensorSupport
import TNLean.PEPS.Approximation.EncodedFrame
import QICLean.Entropy.FiniteProductSplitting
import QICLean.Entropy.PhysicalBufferOverlap

/-!
# Buffer operators in paired physical coordinates

Split a physical configuration into two disjoint regions and their complement,
using the canonical finite enumerations of the two retained regions. After
doubling and regrouping, an identity on the retained coordinates tensored with
an arbitrary buffer operator is precisely the lift of that operator from the
complement to the paired physical sites.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 498–564,
`eq:info-operator-localization` and `eq:info-local-two-sided`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Kronecker

namespace TNLean.PEPS.EncodedFrame

/-- The actual grouped buffer operator is the lift from the same physical
complement after pairing the two copies at every site. The regional finite
enumerations are retained, and zero local dimension and empty regions are allowed.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 498–564,
`eq:info-operator-localization` and `eq:info-local-two-sided`. -/
theorem reindex_physicalBuffer_eq_siteLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (R C : Finset ι) (hRC : Disjoint R C) :
    let Q := (R ∪ C)ᶜ
    let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C → Fin q))
    let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : ι ↦ Fin q) R C hRC
    let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (Q → Fin q))
    let p := QuantumCircuit.sitePairConfigurationEquiv ι q q
    let pQ := QuantumCircuit.sitePairConfigurationEquiv Q q q
    let e := g.symm.trans p
    ∀ W : Matrix ((Q → Fin q) × (Q → Fin q)) ((Q → Fin q) × (Q → Fin q)) ℂ,
      Matrix.reindex e e ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W) =
        siteLift Q (Matrix.reindex pQ pQ W) := by
  classical
  intro Q P s g p pQ e W
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, siteLift, QuantumCircuit.embedOp_apply]
  have hcondition : (e.symm x).1 = (e.symm y).1 ↔
      QuantumCircuit.AgreeOff (Subtype.val : Q → ι) x y := by
    constructor
    · intro h i hi
      done
    · done
  done

end TNLean.PEPS.EncodedFrame
