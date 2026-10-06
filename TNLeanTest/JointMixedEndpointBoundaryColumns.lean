import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointBoundaryColumns

/-! Joint boundary regressions retain physical overlap between two distinct
scalar blocks. The actual first Gram matrix has a nonzero cross-label entry,
while both joint boundary maps are injective and their polar factors are
isometries. The empty block-label case is also admitted. -/

set_option linter.hashCommand false

open scoped Matrix BigOperators
open MPSTensor MPSTensor.MPOSymmetry

private def overlappingBoundaryEndpoints : Fin 2 → MPSTensor 2 1 :=
  fun x i => if i = 0 then 1 else if x = 1 then 1 else 0

private theorem overlappingBoundaryEndpoints_span :
    WordTupleSpanTop overlappingBoundaryEndpoints 1 := by
  classical
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hzero : (fun x => overlappingBoundaryEndpoints x 0) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingBoundaryEndpoints x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hone : (fun x => overlappingBoundaryEndpoints x 1) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingBoundaryEndpoints x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hcomb := Submodule.add_mem _
    (Submodule.smul_mem _ (M 0 0 0) hzero)
    (Submodule.smul_mem _ (M 1 0 0 - M 0 0 0) hone)
  convert hcomb using 1
  funext x a b
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    simp [overlappingBoundaryEndpoints]

-- The actual joint first-boundary Gram matrix mixes distinct labels.
example :
    ((jointMixedFirstBoundaryColumns overlappingBoundaryEndpoints
        overlappingBoundaryEndpoints)ᴴ *
      jointMixedFirstBoundaryColumns overlappingBoundaryEndpoints overlappingBoundaryEndpoints)
        ⟨0, Fin.castAdd 1 0, 0⟩ ⟨1, Fin.castAdd 1 0, 0⟩ = 1 := by
  rw [jointMixedFirstBoundaryColumns_gram_firstSector]
  norm_num [Fin.sum_univ_two, overlappingBoundaryEndpoints]

-- A single physical zero letter overlaps both labels, yet the entire joint map is injective.
example : Function.Injective
    (jointMixedFirstBoundaryColumns overlappingBoundaryEndpoints
      overlappingBoundaryEndpoints).mulVec :=
  jointMixedFirstBoundaryColumns_injective _ _
    overlappingBoundaryEndpoints_span overlappingBoundaryEndpoints_span

example : Function.Injective
    (jointMixedLastBoundaryColumns overlappingBoundaryEndpoints
      overlappingBoundaryEndpoints).mulVec :=
  jointMixedLastBoundaryColumns_injective _ _
    overlappingBoundaryEndpoints_span overlappingBoundaryEndpoints_span

example :
    (Matrix.polarIso (jointMixedFirstBoundaryColumns overlappingBoundaryEndpoints
      overlappingBoundaryEndpoints)).IsIsometry :=
  (jointMixedBoundaryColumns_polar _ _
    overlappingBoundaryEndpoints_span overlappingBoundaryEndpoints_span).1

example :
    (Matrix.polarPos (jointMixedLastBoundaryColumns overlappingBoundaryEndpoints
      overlappingBoundaryEndpoints)).PosDef :=
  (jointMixedBoundaryColumns_polar _ _
    overlappingBoundaryEndpoints_span overlappingBoundaryEndpoints_span).2.2.2

-- The empty interior is a single two-site edge. Its factorization does not
-- introduce a sum of separately counted first and last edge operators.
example {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (x : Fin r)
    (i j : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
    (a e : Fin (D₀ x + D₁ x)) :
    insertedEvalWord (jointMixedEndpointBase A₀ A₁ x)
        (bondInterpolationMatrix (D₀ x) (D₁ x) 0) [i, j] a e =
      ∑ b : Fin (D₀ x), jointMixedFirstBoundaryColumns A₀ A₁ i ⟨x, a, b⟩ *
        jointMixedLastBoundaryColumns A₀ A₁ j ⟨x, b, e⟩ := by
  classical
  simpa [Kraus.evalWord, Matrix.one_apply, mul_ite, Finset.sum_ite_eq] using
    jointMixedEndpoint_insertedEvalWord_originalBulk A₀ A₁ x i j [] a e

-- No inhabitant of the block-label type is introduced by the column proof.
example {d : ℕ} {D : Fin 0 → ℕ} (A : (x : Fin 0) → MPSTensor d (D x)) :
    Function.Injective (Matrix.mulVec
      (fun (i : Fin d) (p : (x : Fin 0) × (Fin (D x) × Fin (D x))) =>
        A p.1 i p.2.1 p.2.2)) := by
  apply injective_jointOneSiteColumns_of_wordTupleSpanTop
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hM : M = 0 := Subsingleton.elim _ _
  simp [hM]

/--
info: 'MPSTensor.injective_jointOneSiteColumns_of_wordTupleSpanTop'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.injective_jointOneSiteColumns_of_wordTupleSpanTop

/--
info: 'MPSTensor.MPOSymmetry.jointMixedBoundaryColumns_polar'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedBoundaryColumns_polar

/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_insertedEvalWord_originalBulk'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_insertedEvalWord_originalBulk
