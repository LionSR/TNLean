import TNLean.PEPS.ParentHamiltonian.DependentRegionCoordinates
import Mathlib.Data.Fin.Rev

/-! Heterogeneous local alphabets, nontrivial basis relabelling, arbitrary complex
operators, and empty configurations for native-to-QIC coordinate transport. -/

open scoped Matrix
open Matrix TNLean.PEPS

namespace Heterogeneous

private abbrev Out (v : Fin 2) := ULift (Fin (v.val + 2))
private def basis (v : Fin 2) : Out v ≃ Fin (v.val + 2) :=
  Equiv.ulift.trans Fin.revPerm

example : Fintype.card (Out 0) = 2 ∧ Fintype.card (Out 1) = 3 := by
  norm_num [Out]

example : basis 0 ⟨0⟩ = 1 ∧ basis 1 ⟨0⟩ = 2 := by decide

example (R : Finset (Fin 2))
    (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ) :
    Matrix.reindex (dependentGlobalFinEquiv basis) (dependentGlobalFinEquiv basis)
        (dependentRegionOperatorLift R K) =
      Entropy.localLift R
        (Matrix.reindex (dependentRegionFinEquiv basis R) (dependentRegionFinEquiv basis R) K) :=
  reindex_dependentRegionOperatorLift basis R K

example (R : Finset (Fin 2))
    (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ)
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset (Fin 2))) → Out v.1)) :
    dependentGlobalFinIsometry basis (WithLp.toLp 2 (dependentRegionOperatorLift R K *ᵥ ξ)) =
      Matrix.toEuclideanLin (Entropy.localLift R
        (Matrix.reindex (dependentRegionFinEquiv basis R) (dependentRegionFinEquiv basis R) K))
          (dependentGlobalFinIsometry basis ξ) :=
  dependentGlobalFinIsometry_lift basis R K ξ

example (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset (Fin 2))) → Out v.1)) :
    Matrix.reindex (dependentRegionFinEquiv basis ∅) (dependentRegionFinEquiv basis ∅)
        (FiniteProduct.reducedPure Out (dependentGlobalConfigIsometry ξ) ∅) =
      Entropy.regionState ∅ (dependentGlobalFinIsometry basis ξ) :=
  reindex_reducedPure_eq_regionState basis ∅ ξ

end Heterogeneous

namespace EmptyAlphabet

private def basis (_ : Unit) : Empty ≃ Fin 0 := Equiv.equivOfIsEmpty _ _

example (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset Unit)) → Empty))
    (R : Finset Unit) :
    Matrix.reindex (dependentRegionFinEquiv basis R) (dependentRegionFinEquiv basis R)
        (FiniteProduct.reducedPure (fun _ : Unit ↦ Empty)
          (dependentGlobalConfigIsometry ξ) R) =
      Entropy.regionState R (dependentGlobalFinIsometry basis ξ) :=
  reindex_reducedPure_eq_regionState basis R ξ

example (K : Matrix ((v : (∅ : Finset Unit)) → Empty)
    ((v : (∅ : Finset Unit)) → Empty) ℂ) :
    Matrix.reindex (dependentGlobalFinEquiv basis) (dependentGlobalFinEquiv basis)
        (dependentRegionOperatorLift (Out := fun _ : Unit ↦ Empty) ∅ K) =
      Entropy.localLift ∅
        (Matrix.reindex (dependentRegionFinEquiv basis ∅) (dependentRegionFinEquiv basis ∅) K) :=
  reindex_dependentRegionOperatorLift basis ∅ K

end EmptyAlphabet

namespace EmptySites

private def basis (v : Fin 0) : Fin 0 ≃ Fin 0 := Fin.elim0 v

example (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset (Fin 0))) → Fin 0)) :
    Matrix.reindex (dependentRegionFinEquiv basis ∅) (dependentRegionFinEquiv basis ∅)
        (FiniteProduct.reducedPure (fun _ : Fin 0 ↦ Fin 0)
          (dependentGlobalConfigIsometry ξ) ∅) =
      Entropy.regionState ∅ (dependentGlobalFinIsometry basis ξ) :=
  reindex_reducedPure_eq_regionState basis ∅ ξ

end EmptySites
