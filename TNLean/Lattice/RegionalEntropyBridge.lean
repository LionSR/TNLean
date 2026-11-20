/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.MarginalTails
import QICLean.Entropy.RegionEntropy
import QICLean.Entropy.RegionUnion

/-!
# Regional data of the finite-domain model as QICLean regional data

The regional states and regional entropies of the finite-domain model are the QICLean
regional states and region entropies on the sites of the domain with constant local
dimension `q`. These identifications let the finite-dimensional entropy
results of QICLean, stated on an arbitrary finite set of sites, be read on lattice domains.

## Main results

* `reducedState_eq_regionState`, `regionalEntropy_eq_regionEntropy`, `card_regionConfig`.
* `reducedState_eq_finiteProduct`, `regionalEntropy_eq_finiteProduct`: the same
  identifications with QICLean's generic finite-product entropy.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 2 (`sec:prelim`), lines 10–25.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix

namespace TNLean.Lattice

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- The regional state of the finite-domain model is the QICLean regional state for constant
local dimension `q`. -/
theorem reducedState_eq_regionState (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    ManyBody.regionState Ω A = ManyBody.regionState (X := fun _ ↦ Fin q) Ω A :=
  (partialTraceRight_cutVector Ω A).symm

/-- The regional entropy of the finite-domain model is the QICLean regional entropy. -/
theorem regionalEntropy_eq_regionEntropy (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    ManyBody.regionEntropy Ω A = ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω A :=
  vonNeumannEntropy_congr (reducedState_eq_regionState Ω A) _ _

/-- The number of configurations of a region is `q ^ |A|`. -/
theorem card_regionConfig (A : Finset (Site Λ)) :
    Fintype.card (ManyBody.RegionConfig (fun _ ↦ Fin q) A) = q ^ A.card := by
  simp [Entropy.RegionConfig]

/-- The domain model's partial trace equals the generic finite-product reduction. -/
theorem reducedState_eq_finiteProduct (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    ManyBody.regionState Ω A = ManyBody.regionState Ω A := by
  classical
  let e : ({x : Site Λ // x ∉ A} → Fin q) ≃
      ManyBody.RegionConfig (fun _ : Site Λ ↦ Fin q) Aᶜ :=
    { toFun := fun f x ↦ f ⟨x, Finset.mem_compl.mp x.property⟩
      invFun := fun f x ↦ f ⟨x, Finset.mem_compl.mpr x.property⟩
      left_inv := fun f ↦ rfl
      right_inv := fun f ↦ rfl }
  ext a b
  unfold reducedState ManyBody.regionState
  simp only [Matrix.partialTraceRight_apply, Matrix.submatrix_apply,
    ManyBody.regionMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  have heq (a : {x : Site Λ // x ∈ A} → Fin q)
      (c : {x : Site Λ // x ∉ A} → Fin q) :
      (configurationSplit Λ q A).symm (a, c) =
        (ManyBody.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (a, e c) := by
    funext v
    by_cases hv : v ∈ A <;>
      simp [configurationSplit, Equiv.piEquivPiSubtypeProd, ManyBody.splitEquiv,
        ManyBody.complementEquiv, hv, e]
  simp_rw [heq]
  exact e.sum_comp (fun c ↦
    Ω ((ManyBody.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (a, c)) *
      star (Ω ((ManyBody.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (b, c))))

/-- The finite-domain regional entropy uses exactly the generic QICLean entropy. -/
theorem regionalEntropy_eq_finiteProduct (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    ManyBody.regionEntropy Ω A = ManyBody.regionEntropy Ω A := by
  apply vonNeumannEntropy_congr
  exact reducedState_eq_finiteProduct Λ q Ω A

end TNLean.Lattice
