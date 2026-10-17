/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PinnedNestedFilterCoordinates

/-! Regressions through the adapted original-grid filter interface. -/

noncomputable section

open Matrix

namespace TNLean.PEPS.Approximation

open Pinned Pinned.NestedFilter

-- The adapted lift is the existing local matrix action.
example {L q : ℕ} (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ) :
    liftLocal X A = Entropy.localLift (n := fun _ ↦ q) X A :=
  liftLocal_eq_localLift X A

-- Every feasible canonical competitor, with no omitted subclass, round-trips exactly.
example {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (K : CanonicalFamily q X)
    (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j)) :
    canonicalMatrices (fromCanonical K hK) = K ∧
      Admissible a (fromCanonical K hK) :=
  ⟨canonicalMatrices_fromCanonical K hK, admissible_fromCanonical a ha K hK⟩

-- Both directions of the source-shaped global maximum are usable independently.
example {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (Ω : State L q) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (F : FilterFamily q m X) (hF : IsMaximizer Ω a F)
    (K : CanonicalFamily q X) (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j)) :
    ‖toEuclideanLin (Entropy.liftProd
      (Entropy.chainList (canonicalRegions X) K fun _ ↦ True)) (squareAreaLawState Ω)‖ ≤
    ‖toEuclideanLin (Entropy.liftProd
      (Entropy.chainList (canonicalRegions X) (canonicalMatrices F) fun _ ↦ True))
      (squareAreaLawState Ω)‖ :=
  ((isMaximizer_iff Ω a ha F).mp hF).2 K hK

example {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (Ω : State L q) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (K : CanonicalFamily q X) (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j))
    (hmax : ∀ K' : CanonicalFamily q X,
      (∀ j, Entropy.IsFeasibleFilter 0 (a j) (K' j)) →
      ‖toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) K' fun _ ↦ True)) (squareAreaLawState Ω)‖ ≤
      ‖toEuclideanLin (Entropy.liftProd
        (Entropy.chainList (canonicalRegions X) K fun _ ↦ True)) (squareAreaLawState Ω)‖) :
    IsMaximizer Ω a (fromCanonical K hK) := by
  apply (isMaximizer_iff Ω a ha (fromCanonical K hK)).mpr
  simpa only [canonicalMatrices_fromCanonical] using And.intro hK hmax

-- The normalization identity tracks the supplied K exactly, even for a zero input.
example {L q m : ℕ} {X : Fin m → Finset (Vertex L)} {a : Fin m → ℝ}
    (K : CanonicalFamily q X) (hK : ∀ j, Entropy.IsFeasibleFilter 0 (a j) (K j))
    (Ω : State L q) :
    let ψ := toEuclideanLin (Entropy.liftProd
      (Entropy.chainList (canonicalRegions X) K fun _ ↦ True)) (squareAreaLawState Ω)
    squareAreaLawState (normalizedOutput (fromCanonical K hK) Ω) =
      ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ := by
  simpa only [canonicalMatrices_fromCanonical] using
    squareAreaLawState_normalizedOutput (fromCanonical K hK) Ω

-- Empty physical regions have one configuration, even at q = 0.
example : Fintype.card (RegionConfiguration 0 (∅ : Finset (Vertex 1))) = 1 := by
  simp [RegionConfiguration]

-- A nonempty region with q = 0 has no configurations and no trace-normalized filter.
example : ¬ ∃ F : FilterFamily 0 1 (fun _ ↦ (Finset.univ : Finset (Vertex 1))),
    Admissible (fun _ ↦ 1) F := by
  classical
  let : IsEmpty (RegionConfiguration 0 (Finset.univ : Finset (Vertex 1))) :=
    ⟨fun σ ↦ Fin.elim0 (σ ⟨(0, 0), Finset.mem_univ _⟩)⟩
  rintro ⟨F, hF⟩
  have h := hF (0 : Fin 1)
  simp [tracePower] at h

-- No region or tail data are needed for an empty family.
example {L q : ℕ} (X : Fin 0 → Finset (Vertex L))
    (F : FilterFamily q 0 X) (Ω : State L q) :
    output F Ω = Ω ∧ IsMaximizer Ω (fun _ ↦ 1) F := by
  simp [output, IsMaximizer, Admissible]

end TNLean.PEPS.Approximation
