import TNLean.PEPS.ParentHamiltonian.SemiRegularFourierCanonicalParentTransport

/-! Regression: a proper region of a two-vertex graph retains an arbitrary
crossing label. Empty and whole regions use the same transport statement. -/
noncomputable section
open scoped Matrix
open TNLean.PEPS

namespace TNLeanTest
variable {G : Type*} [Group G] [Fintype G]

example (U : G →* Matrix (Fin 2) (Fin 2) ℂ)
    (θ : {e : Edge (⊤ : SimpleGraph (Fin 2)) // IsRegionBoundaryEdge {0} e} → Fin 2) :
    graphRegionCoordinateMatrix (Γ := (⊤ : SimpleGraph (Fin 2)))
      (1 : Matrix (Fin 2) (Fin 2) ℂ) {0} *ᵥ graphOpenBondCoordinates U 1 {0} θ =
      ∑ a, (∏ e, graphBoundaryCoordinateMatrix (1 : Matrix (Fin 2) (Fin 2) ℂ)
        {0} e (a e) (θ e)) • graphOpenBondCoordinates U 1 {0} a := by
  exact graphRegionCoordinateMatrix_open 1 (by simp) U U (fun _ => by simp) {0} θ

example (U : G →* Matrix (Fin 2) (Fin 2) ℂ) :
    (graphOpenBondSpace (Γ := (⊤ : SimpleGraph (Fin 2))) U 1 ∅).map
      (Matrix.mulVecLin (graphRegionCoordinateMatrix (1 : Matrix (Fin 2) (Fin 2) ℂ) ∅)) =
      graphOpenBondSpace U 1 ∅ :=
  graphRegionCoordinateMatrix_map_openBondSpace 1 (by simp) U U (fun _ => by simp) ∅

example (U : G →* Matrix (Fin 2) (Fin 2) ℂ) :
    (graphOpenBondSpace (Γ := (⊤ : SimpleGraph (Fin 2))) U 1 Finset.univ).map
      (Matrix.mulVecLin (graphRegionCoordinateMatrix
        (1 : Matrix (Fin 2) (Fin 2) ℂ) Finset.univ)) = graphOpenBondSpace U 1 Finset.univ :=
  graphRegionCoordinateMatrix_map_openBondSpace 1 (by simp) U U (fun _ => by simp) Finset.univ

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.graphRegionCoordinateMatrix_open'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.graphRegionCoordinateMatrix_open
/--
info: 'TNLean.PEPS.graphRegionCoordinateMatrix_map_openBondSpace'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.graphRegionCoordinateMatrix_map_openBondSpace
/--
info: 'TNLean.PEPS.canonicalCoordinateParentEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.canonicalCoordinateParentEquiv
/--
info: 'TNLean.PEPS.map_ker_regionParentHamiltonian_semiRegular_fourier_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.map_ker_regionParentHamiltonian_semiRegular_fourier_eq
/--
info: 'TNLean.PEPS.canonicalSemiRegularFourierParentEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.canonicalSemiRegularFourierParentEquiv
end TNLeanTest
