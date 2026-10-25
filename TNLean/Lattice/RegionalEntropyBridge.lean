/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.MarginalTails
import QICLean.Entropy.FiniteProduct
import QICLean.Entropy.RegionEntropy
import QICLean.Entropy.RegionUnion

/-!
# Regional data of the finite-domain model as QICLean regional data

The regional states, regional entropies and local placements of the finite-domain model are
the QICLean regional states, region entropies and local lifts on the sites of the domain with
constant local dimension `q`. These identifications let the finite-dimensional entropy
results of QICLean, stated on an arbitrary finite set of sites, be read on lattice domains.

## Main results

* `reducedState_eq_regionState`, `regionalEntropy_eq_regionEntropy`,
  `localLift_eq_entropyLocalLift`, `card_regionConfig`.
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
    reducedState Λ q Ω A = Entropy.regionState (n := fun _ ↦ q) A Ω :=
  (partialTraceRight_cutVector Ω A).symm

/-- The regional entropy of the finite-domain model is the QICLean regional entropy. -/
theorem regionalEntropy_eq_regionEntropy (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    regionalEntropy Λ q Ω A = Entropy.regionEntropy (n := fun _ ↦ q) A Ω :=
  vonNeumannEntropy_congr (reducedState_eq_regionState Ω A) _ _

/-- The placement of a local matrix in the finite-domain model is the QICLean local lift. -/
theorem localLift_eq_entropyLocalLift (A : Finset (Site Λ))
    (K : Matrix (↥A → Fin q) (↥A → Fin q) ℂ) :
    localLift Λ q A K = Entropy.localLift (n := fun _ ↦ q) A K := by
  ext σ τ
  rw [Entropy.localLift_apply, localLift, QuantumCircuit.embedOp_apply]
  congr 1
  simp only [QuantumCircuit.AgreeOff, eq_iff_iff]
  constructor
  · intro h v hv
    exact h v fun w hw ↦ hv (hw ▸ w.2)
  · intro h v hv
    exact h v fun hvA ↦ hv ⟨v, hvA⟩ rfl

/-- The number of configurations of a region is `q ^ |A|`. -/
theorem card_regionConfig (A : Finset (Site Λ)) :
    Fintype.card (Entropy.RegionConfig (fun _ : Site Λ ↦ q) A) = q ^ A.card := by
  simp [Entropy.RegionConfig]

/-- The domain model's partial trace equals the generic finite-product reduction. -/
theorem reducedState_eq_finiteProduct (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    reducedState Λ q Ω A = FiniteProduct.reducedPure (fun _ : Site Λ ↦ Fin q) Ω A := by
  classical
  let e : ({x : Site Λ // x ∉ A} → Fin q) ≃
      FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) Aᶜ :=
    { toFun := fun f x ↦ f ⟨x, Finset.mem_compl.mp x.property⟩
      invFun := fun f x ↦ f ⟨x, Finset.mem_compl.mpr x.property⟩
      left_inv := fun f ↦ rfl
      right_inv := fun f ↦ rfl }
  ext a b
  unfold reducedState FiniteProduct.reducedPure
  simp only [Matrix.partialTraceRight_apply, Matrix.submatrix_apply,
    FiniteProduct.reducedMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  have heq (a : {x : Site Λ // x ∈ A} → Fin q)
      (c : {x : Site Λ // x ∉ A} → Fin q) :
      (configurationSplit Λ q A).symm (a, c) =
        (FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (a, e c) := by
    funext v
    by_cases hv : v ∈ A <;>
      simp [configurationSplit, Equiv.piEquivPiSubtypeProd, FiniteProduct.splitEquiv,
        FiniteProduct.complementEquiv, hv, e]
  simp_rw [heq]
  exact e.sum_comp (fun c ↦
    Ω ((FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (a, c)) *
      star (Ω ((FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) A).symm (b, c))))

/-- The finite-domain regional entropy uses exactly the generic QICLean entropy. -/
theorem regionalEntropy_eq_finiteProduct (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    regionalEntropy Λ q Ω A = FiniteProduct.entropy (fun _ : Site Λ ↦ Fin q) Ω A := by
  apply vonNeumannEntropy_congr
  exact reducedState_eq_finiteProduct Λ q Ω A

end TNLean.Lattice
