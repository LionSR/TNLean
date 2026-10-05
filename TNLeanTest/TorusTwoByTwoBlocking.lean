/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoByTwoPhysicalBlocking

/-! # Geometric blocking retains small-period bonds and arbitrary alphabets -/

noncomputable section
open TNLean.PEPS
open scoped Matrix

namespace TorusTwoByTwoBlockingTest
local instance : Fact (2 < 3) := ⟨by decide⟩
local instance : Fact (1 < 3) := ⟨by decide⟩

-- Both coarse periods are one; this remains a bond-indexed 2×2 fine torus.
example (a : TorusVertex 2 2 → (Fin 4 → Fin 3) → Fin 5 → ℂ)
    (σ : TorusVertex 2 2 → Fin 5) :
    torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1 =
      torusBondNetwork (fun v c => twoByTwoTensor
        (fun i => a (kitaevPeriodicTilingEquiv (width := 1) (height := 1) (v, i)))
        ![c.1, c.2.1, c.2.2.1, c.2.2.2]
        (twoByTwoPhysicalEquiv (width := 1) (height := 1) σ v)) 1 1 :=
  torusBondNetwork_eq_twoByTwoBlocked (width := 1) (height := 1) a σ

-- At period two the two parallel geometric bonds are still separate variables.
example :
    Matrix.IsIsometry (twoByTwoPhysicalMatrix (width := 2) (height := 1) (P := Fin 3)) ∧
      Matrix.IsIsometry
        (twoByTwoPhysicalMatrix (width := 2) (height := 1) (P := Fin 3)).conjTranspose :=
  ⟨twoByTwoPhysicalMatrix_isIsometry, twoByTwoPhysicalMatrix_conjTranspose_isIsometry⟩

-- Every boundary coordinate is retained without an identification hypothesis.
example (α : Fin 4 → Fin 7 × Fin 7) :
    twoByTwoBoundaryEquiv.symm (twoByTwoBoundaryEquiv α) = α :=
  twoByTwoBoundaryEquiv.symm_apply_apply α

-- The crossing/internal virtual reindexing is a genuine two-sided inverse.
example (q : (TorusVertex 1 2 × Fin 4 → Fin 3) × (TorusVertex 1 2 × Fin 4 → Fin 3)) :
    twoByTwoTiledBondEquiv (twoByTwoTiledBondEquiv.symm q) = q :=
  twoByTwoTiledBondEquiv.apply_symm_apply q

-- The coarse canonical tensor has precisely the original physical support,
-- even when there are unused directions in its finite physical alphabet.
example {G P : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fintype P] [DecidableEq P]
    (a : (Fin 4 → G) → P → ℂ)
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a))
    (v : TorusVertex 3 3) :
    ∃ c : ℝ, 0 < c ∧
      Nonempty ((Matrix.toEuclideanLin (LinearMap.toMatrix'
        (regularSiteMap (torusIncidentFamily (fun _ : TorusVertex 3 3 => a) v)))).range ≃ₗᵢ[ℂ]
        (Matrix.toEuclideanLin (LinearMap.toMatrix'
          (regularSiteMap (graphAveragingSite (Γ := torusGraph 3 3)
            (leftRegularMatrix G) v)))).range) := by
  obtain ⟨c, hc, I, _, _⟩ := ha.exists_torusCanonicalSupportEquiv v
  exact ⟨c, hc, ⟨I⟩⟩

end TorusTwoByTwoBlockingTest

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.torusBondNetwork_eq_twoByTwoBlocked'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.torusBondNetwork_eq_twoByTwoBlocked

/--
info: 'TNLean.PEPS.twoByTwoPhysicalMatrix_mulVec_network'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.twoByTwoPhysicalMatrix_mulVec_network

/--
info: 'TNLean.PEPS.torusBondNetwork_eq_twoByTwoBundledGraphSite'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.torusBondNetwork_eq_twoByTwoBundledGraphSite

/--
info: 'TNLean.PEPS.twoByTwoFineState_mem_physicalSupport'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.twoByTwoFineState_mem_physicalSupport
