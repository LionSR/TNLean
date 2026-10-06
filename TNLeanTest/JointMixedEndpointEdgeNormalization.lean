import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointEdgeProjectors
import TNLean.MPS.ParentHamiltonian.Martingale.IsometricCompressionGap

/-! Regressions retain physically overlapping labels, unused physical
directions, vanishing second dimensions, empty labels, and rectangular
isometries with an ambient complement. -/

set_option linter.hashCommand false

open scoped Matrix BigOperators Kronecker
open MPSTensor MPSTensor.MPOSymmetry

private def overlappingEdgeEndpoint : Fin 2 → MPSTensor 3 1 :=
  fun x i => if i = 0 then 1 else if i = 1 ∧ x = 1 then 1 else 0

private theorem overlappingEdgeEndpoint_span :
    WordTupleSpanTop overlappingEdgeEndpoint 1 := by
  classical
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hzero : (fun x => overlappingEdgeEndpoint x 0) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingEdgeEndpoint x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hone : (fun x => overlappingEdgeEndpoint x 1) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingEdgeEndpoint x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hcomb := Submodule.add_mem _
    (Submodule.smul_mem _ (M 0 0 0) hzero)
    (Submodule.smul_mem _ (M 1 0 0 - M 0 0 0) hone)
  convert hcomb using 1
  funext x a b
  fin_cases x <;> fin_cases a <;> fin_cases b <;> simp [overlappingEdgeEndpoint]

private def emptySecondEndpoint : Fin 2 → MPSTensor 0 0 := fun _ i => Fin.elim0 i

private theorem emptySecondEndpoint_span : WordTupleSpanTop emptySecondEndpoint 1 := by
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hM : M = 0 := Subsingleton.elim _ _
  simp [hM]

-- The joint positive factor is not licensed to discard the off-diagonal
-- label entry, even when every second endpoint bond dimension vanishes.
example :
    ((jointMixedFirstBoundaryColumns overlappingEdgeEndpoint emptySecondEndpoint)ᴴ *
      jointMixedFirstBoundaryColumns overlappingEdgeEndpoint emptySecondEndpoint)
        ⟨0, Fin.castAdd 0 0, 0⟩ ⟨1, Fin.castAdd 0 0, 0⟩ = 1 := by
  rw [jointMixedFirstBoundaryColumns_gram_firstSector]
  norm_num [Fin.sum_univ_three, overlappingEdgeEndpoint]

-- Boundary normalization preserves the actual neighboring A₀ coefficient:
-- the second physical letter is zero for label 0 and nonzero for label 1.
example (X : (x : Fin 2) → Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) :
    (((Matrix.polarPos (jointMixedFirstBoundaryColumns
        overlappingEdgeEndpoint emptySecondEndpoint))⁻¹ ⊗ₖ
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ
        jointMixedFirstEdgeCompressedMap overlappingEdgeEndpoint emptySecondEndpoint X)
          (⟨0, 0, 0⟩, 1) = 0 := by
  rw [jointMixedFirstEdge_normalize_compressed _ _
    overlappingEdgeEndpoint_span emptySecondEndpoint_span]
  simp [jointEndpointFirstEdgeCoreMap, overlappingEdgeEndpoint]

example (X : (x : Fin 2) → Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) :
    (((Matrix.polarPos (jointMixedFirstBoundaryColumns
        overlappingEdgeEndpoint emptySecondEndpoint))⁻¹ ⊗ₖ
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ
        jointMixedFirstEdgeCompressedMap overlappingEdgeEndpoint emptySecondEndpoint X)
          (⟨1, 0, 0⟩, 1) = X 1 0 0 := by
  rw [jointMixedFirstEdge_normalize_compressed _ _
    overlappingEdgeEndpoint_span emptySecondEndpoint_span]
  simp [jointEndpointFirstEdgeCoreMap, overlappingEdgeEndpoint]

-- The right edge has the same unmodified neighboring letter.
example (X : (x : Fin 2) → Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) :
    (((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ
      (Matrix.polarPos (jointMixedLastBoundaryColumns
        overlappingEdgeEndpoint emptySecondEndpoint))⁻¹) *ᵥ
        jointMixedLastEdgeCompressedMap overlappingEdgeEndpoint emptySecondEndpoint X)
          (1, ⟨1, 0, 0⟩) = X 1 0 0 := by
  rw [jointMixedLastEdge_normalize_compressed _ _
    overlappingEdgeEndpoint_span emptySecondEndpoint_span]
  simp [jointEndpointLastEdgeCoreMap, overlappingEdgeEndpoint]

-- The unused third bulk direction remains present as a physical coordinate.
example (X : (x : Fin 2) → Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) :
    (((Matrix.polarPos (jointMixedFirstBoundaryColumns
        overlappingEdgeEndpoint emptySecondEndpoint))⁻¹ ⊗ₖ
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ
        jointMixedFirstEdgeCompressedMap overlappingEdgeEndpoint emptySecondEndpoint X)
          (⟨1, 0, 0⟩, 2) = 0 := by
  rw [jointMixedFirstEdge_normalize_compressed _ _
    overlappingEdgeEndpoint_span emptySecondEndpoint_span]
  simp [jointEndpointFirstEdgeCoreMap, overlappingEdgeEndpoint]

-- Core maps and virtual padding never introduce an inhabitant of the label type.
example {d : ℕ} {D E : Fin 0 → ℕ} (A : (x : Fin 0) → MPSTensor d (D x)) :
    jointEndpointFirstEdgeCoreMap A E = 0 := Subsingleton.elim _ _

example {r : ℕ} {D : Fin r → ℕ} :
    Function.Surjective (fun X : (x : Fin r) →
      Matrix (Fin (0 + D x)) (Fin (0 + D x)) ℂ =>
        fun x => (X x).submatrix (Fin.castAdd (D x)) id) :=
  jointMixedFirstBoundaryExtraction_surjective (D₀ := fun _ => 0) (D₁ := D)

private def rectangularFrame : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun z := PiLp.single 2 0 z
  map_add' z w := PiLp.single_add 2 0
  map_smul' z w := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  norm_map' z := PiLp.norm_single 2 (fun _ : Fin 2 => ℂ) 0 z

-- This is genuinely rectangular: the second ambient basis vector is absent.
example : ¬ Function.Surjective rectangularFrame := by
  intro h
  obtain ⟨z, hz⟩ := h (PiLp.single 2 (1 : Fin 2) (1 : ℂ))
  have := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) hz
  simp [rectangularFrame] at this

-- An identity gap restricts unchanged through this nonsurjective frame.
example : ∀ v ∈ (LinearMap.ker
    (rectangularFrame.compression (1 : Module.End ℂ (EuclideanSpace ℂ (Fin 2)))))ᗮ,
    1 * ‖v‖ ≤ ‖rectangularFrame.compression 1 v‖ := by
  apply rectangularFrame.norm_gap_compression_of_commute 1 (Commute.one_right _)
  intro w _
  simp

-- The domain may be zero-dimensional, with a nontrivial physical complement.
example : ∀ v ∈ (LinearMap.ker
    ((⊥ : Submodule ℂ ℂ).subtypeₗᵢ.compression (1 : Module.End ℂ ℂ)))ᗮ,
    1 * ‖v‖ ≤ ‖(⊥ : Submodule ℂ ℂ).subtypeₗᵢ.compression 1 v‖ := by
  apply (⊥ : Submodule ℂ ℂ).subtypeₗᵢ.norm_gap_compression_of_commute 1
    (Commute.one_right _)
  intro w _
  simp

/--
info: 'MPSTensor.MPOSymmetry.jointMixedFirstEdgeBoundaryMap_eq_columns_core'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedFirstEdgeBoundaryMap_eq_columns_core

/--
info: 'MPSTensor.MPOSymmetry.map_jointMixedLastEdgeCompressed_range_eq_core'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.map_jointMixedLastEdgeCompressed_range_eq_core

/--
info: 'MPSTensor.MPOSymmetry.jointMixedFirstEdgeNormalization_deformed_constraints'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedFirstEdgeNormalization_deformed_constraints

/--
info: 'LinearIsometry.norm_gap_compression_of_commute'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearIsometry.norm_gap_compression_of_commute
