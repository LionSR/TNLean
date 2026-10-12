import TNLean.MPS.Symmetry.MPOSymmetry.JointInsertedOpenKernel

/-! Joint-boundary regressions on an arbitrary common physical alphabet.
No physical block orthogonality, square alphabet, invertible insertion,
positive block count, or positive dimension is assumed. -/

-- These regression files intentionally audit axioms with guarded #print commands.
set_option linter.hashCommand false

open scoped Matrix BigOperators
open MPSTensor MPSTensor.MPOSymmetry

variable {d r N : ℕ} {dim : Fin r → ℕ}

example (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) (hN : 0 < N) :
    Function.Injective (blockInsertedGroundSpaceMap A W N) :=
  blockInsertedGroundSpaceMap_injective A hA W hW hN

example (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) (hN : 0 < N) :
    Submodule.span ℂ (Set.range fun σ : Cfg d N =>
      fun x => insertedEvalWord (A x) (W x) (List.ofFn σ)) = ⊤ :=
  span_range_blockInsertedEvalWord_eq_top A hA W hW hN

example (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) (hN : 1 < N) (ψ : NSiteSpace d (N + 1)) :
    ψ ∈ blockInsertedGroundSpace A W (N + 1) ↔
      (∀ j, restrictLast ψ j ∈ blockInsertedGroundSpace A W N) ∧
      (∀ i, restrictFirst ψ i ∈ blockInsertedGroundSpace A W N) :=
  blockInsertedGroundSpace_iff_left_right A hA W hW hN

example (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap A W 2).range.starProjection).toLinearMap N) =
      (blockInsertedBoundaryMap A W N).range :=
  ker_openInteractionHamiltonianES_blockInserted_eq A hA W hW hN

example (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap A W 2).range.starProjection).toLinearMap N)) =
      ∑ x, dim x * dim x :=
  finrank_ker_openInteractionHamiltonianES_blockInserted A hA W hW hN

-- A nonzero nilpotent insertion is allowed in every block.
example : (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) ^ 2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pow_two]

example (A : Fin r → MPSTensor d 2) (hA : WordTupleSpanTop A 1) (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap A
        (fun _ => Matrix.single 0 1 1) 2).range.starProjection).toLinearMap N) =
      (blockInsertedBoundaryMap A (fun _ => Matrix.single 0 1 1) N).range := by
  apply ker_openInteractionHamiltonianES_blockInserted_eq A hA _ _ hN
  intro x hx
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hx
  simp at hentry

example {X : Type*} [TopologicalSpace X]
    (A : X → (x : Fin r) → MPSTensor d (dim x))
    (hA : ∀ x, Continuous fun t => A t x)
    (W : X → (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, Continuous fun t => W t x)
    (hSpan : ∀ t, WordTupleSpanTop (A t) 1) (hne : ∀ t x, W t x ≠ 0) (hN : 2 ≤ N) :
    Continuous fun t => (LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap (A t) (W t) 2).range.starProjection).toLinearMap
        N)).starProjection :=
  continuous_ker_openInteractionHamiltonianES_blockInserted_starProjection
    A hA W hW hSpan hne hN

-- The block letters share a physical column: their coefficient vectors are (1, 0) and (1, 1).
private def overlappingScalarBlocks : Fin 2 → MPSTensor 2 1 :=
  fun x i => if i = 0 then 1 else if x = 1 then 1 else 0

private theorem overlappingScalarBlocks_span : WordTupleSpanTop overlappingScalarBlocks 1 := by
  classical
  unfold WordTupleSpanTop
  apply top_unique
  intro M _
  have hzero : wordTuple overlappingScalarBlocks 1 (fun _ => 0) ∈
      Submodule.span ℂ (Set.range (wordTuple overlappingScalarBlocks 1)) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hone : wordTuple overlappingScalarBlocks 1 (fun _ => 1) ∈
      Submodule.span ℂ (Set.range (wordTuple overlappingScalarBlocks 1)) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hcomb := Submodule.add_mem _
    (Submodule.smul_mem _ (M 0 0 0) hzero)
    (Submodule.smul_mem _ (M 1 0 0 - M 0 0 0) hone)
  convert hcomb using 1
  funext x a b
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    simp [wordTuple, overlappingScalarBlocks, List.ofFn_succ, Kraus.evalWord]

example (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap overlappingScalarBlocks
        (fun _ => 1) 2).range.starProjection).toLinearMap N)) = 2 := by
  simpa using finrank_ker_openInteractionHamiltonianES_blockInserted
    overlappingScalarBlocks overlappingScalarBlocks_span (fun _ => 1)
    (fun _ => one_ne_zero) hN

-- No block-count or physical-alphabet positivity assumption is needed.
example (A : (x : Fin 0) → MPSTensor 0 (Fin.elim0 x))
    (W : (x : Fin 0) → Matrix (Fin (Fin.elim0 x)) (Fin (Fin.elim0 x)) ℂ)
    (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap A W 2).range.starProjection).toLinearMap N) =
      (blockInsertedBoundaryMap A W N).range := by
  have hA : WordTupleSpanTop A 1 := by
    unfold WordTupleSpanTop
    apply top_unique
    intro X _
    have hX : X = 0 := funext fun x => x.elim0
    rw [hX]
    exact Submodule.zero_mem _
  exact ker_openInteractionHamiltonianES_blockInserted_eq A hA W (fun x => x.elim0) hN

/--
info: 'MPSTensor.MPOSymmetry.blockInsertedGroundSpaceMap_injective'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.blockInsertedGroundSpaceMap_injective
/--
info: 'MPSTensor.MPOSymmetry.span_range_blockInsertedEvalWord_eq_top'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.span_range_blockInsertedEvalWord_eq_top
/--
info: 'MPSTensor.MPOSymmetry.blockInsertedGroundSpace_iff_left_right'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.blockInsertedGroundSpace_iff_left_right
/--
info: 'MPSTensor.MPOSymmetry.ker_openInteractionHamiltonianES_blockInserted_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.ker_openInteractionHamiltonianES_blockInserted_eq
/--
info: 'MPSTensor.MPOSymmetry.finrank_ker_openInteractionHamiltonianES_blockInserted'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.finrank_ker_openInteractionHamiltonianES_blockInserted
/--
info: 'MPSTensor.MPOSymmetry.continuous_ker_openInteractionHamiltonianES_blockInserted_starProjection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms continuous_ker_openInteractionHamiltonianES_blockInserted_starProjection
