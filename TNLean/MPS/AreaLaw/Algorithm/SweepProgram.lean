/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.Query
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveConstruction

/-!
# The sweep as a program over the linear-algebra queries

The four steps of the algorithm of Landau, Vazirani and Vidick, extension, size trimming,
bond trimming and error reduction, are written as programs over the queries of
`LinearAlgebraQuery`, and the sweep as their iteration from the scalar singleton. Each
program, run with the honest oracle, computes the corresponding family of the mathematical
development: `extensionProgram` computes `extend`, `sizeTrimmingProgram` computes the
size-trimming selection, `bondTrimmingProgram` computes `bondTrimSet`,
`errorReductionProgram` computes `errorReductionSet`, `sweepStepProgram` computes
`lvvSweepStep` and `sweepProgram` computes `lvvSweep`. The viability, cardinality and bond
bounds of the sweep therefore transfer to the outputs of the programs.

The programs take the bond budget of the vectors they handle as an input, the paper's
polynomial `p₂(n)`, which the queries use to declare their costs; the honest oracle ignores
it. The cost model is recorded in `docs/paper-gaps/lvv13_cost_model.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, algorithm steps 1--4, lines 379--400,
456--487, 549--559 and 572--592, and the proof of Theorem 1, lines 652--668.
-/

open Matrix Cslib
open scoped ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

variable {q : ℕ}

/-- A program of the algorithm: a computation over the linear-algebra queries returning a
value of type `α`. -/
abbrev LVVProgram (q : ℕ) (α : Type) : Type 1 := FreeM (LinearAlgebraQuery q) α

open LinearAlgebraQuery

/-! ## Finite-set bookkeeping -/

/-- A finite union over the elements of a set satisfying a predicate, written as a union of
conditional sets. -/
theorem Finset.biUnion_ite_empty {α β : Type*} [DecidableEq β] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (g : α → Finset β) :
    (s.biUnion fun x ↦ if p x then g x else ∅) = (s.filter p).biUnion g := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, hv⟩
    split_ifs at hv with hp
    · exact ⟨x, ⟨hx, hp⟩, hv⟩
    · exact absurd hv (Finset.notMem_empty v)
  · rintro ⟨x, ⟨hx, hp⟩, hv⟩
    exact ⟨x, hx, by simpa only [hp, ↓reduceIte] using hv⟩

/-- The left columns, in the gluing coordinates, of one vector on the left block and a bond
of dimension `m`. LVV13, `algo53.tex`, lines 477--478. -/
noncomputable def leftColumnsOf {L q k m : ℕ}
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    Finset (LeftBlockVector L q k) :=
  open Classical in
  Finset.univ.image fun a : Fin m ↦ WithLp.toLp 2
    ((schmidtCoeffMatrix (WithLp.ofLp (gluingLeftCoordinates L q k m u))).col a)

/-- The family of left columns of an indexed family of vectors is the union of the columns
of its members. -/
theorem leftColumns_eq_biUnion {L q k m : ℕ} {ι : Type*} (I : Finset ι)
    (u : ι → EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    leftColumns I (fun x ↦ gluingLeftCoordinates L q k m (u x)) =
      I.biUnion fun x ↦ leftColumnsOf (u x) := by
  classical
  ext v
  simp only [leftColumns, leftColumnsOf, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
    and_true, true_and, Finset.mem_biUnion, Prod.exists]
  constructor
  · rintro ⟨x, a, hx, rfl⟩
    exact ⟨x, hx, a, rfl⟩
  · rintro ⟨x, hx, a, rfl⟩
    exact ⟨x, a, hx, rfl⟩

/-! ## Algorithm step 1: extension -/

/-- **Algorithm step 1.** Extend every member of the family on the first `i - 1` sites by
every one-site basis vector. LVV13, `algo53.tex`, lines 379--386. -/
noncomputable def extensionProgram (L i b : ℕ) (S : Finset (LeftBlockVector L q (i - 1))) :
    LVVProgram q (Finset (LeftBlockVector L q i)) :=
  unionOver S.toList fun v ↦ unionOver (List.finRange q) fun k ↦ do
    let w ← FreeM.lift (LinearAlgebraQuery.extendSite L i b k v)
    pure {w}

/-- With the honest oracle, step 1 computes the extended family. -/
theorem eval_extensionProgram (L i b : ℕ) (S : Finset (LeftBlockVector L q (i - 1))) :
    FreeM.eval honestOracle (extensionProgram L i b S) = AreaLaw.extend i S := by
  classical
  ext v
  simp only [extensionProgram, eval_unionOver, Finset.toList_toFinset, List.toFinset_finRange,
    FreeM.eval_liftBind, FreeM.eval_pure, honestOracle_extendSite, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_singleton, AreaLaw.extend, Finset.mem_image₂]
  constructor <;> rintro ⟨s, hs, k, hv⟩ <;> exact ⟨s, hs, k, hv.symm⟩

/-! ## Algorithm step 2: size trimming -/

/-- **Algorithm step 2.** For every bond dimension up to the uniform cut bound, enumerate
the net of boundary contractions, and at every feasible net point solve the size-trimming
convex program and keep the left columns of the leading eigenvector of its solution. The
family `S` consists of `b`-bounded matrix product states. LVV13, `algo53.tex`, lines
456--487. -/
noncomputable def sizeTrimmingProgram (L k b : ℕ) (h : ChainHamiltonian L q 1 1)
    (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k)) :
    LVVProgram q (Finset (LeftBlockVector L q k)) :=
  haveI : NeZero q := ⟨by omega⟩
  let c : ℝ := (Δ / 169) ^ 2
  let D := constantCutBond q 1 1 Δ c
  let η : ℝ := c / (2 * L)
  let HL := leftCutOperator k (h.cutLeftPart k)
  unionOver (List.finRange (D + 1)) fun m ↦ do
    let N ← FreeM.lift (LinearAlgebraQuery.boundaryNet L k m.val η)
    unionOver N.toList fun X ↦ do
      let ok ← FreeM.lift (LinearAlgebraQuery.feasible L k b S m.val η X)
      if ok then do
        let u ← FreeM.lift (LinearAlgebraQuery.leadingVector L k b S HL m.val η X)
        pure (leftColumnsOf u)
      else pure ∅

open Classical in
/-- With the honest oracle, the program at one net point returns the left columns of the
chosen leading vector when the point is feasible, and nothing otherwise. -/
theorem eval_feasible_ite (L k b m : ℕ) (S : Finset (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) (η : ℝ)
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    FreeM.eval honestOracle
      (if honestOracle (LinearAlgebraQuery.feasible L k b S m η X) = true then do
          let u ← FreeM.lift (LinearAlgebraQuery.leadingVector L k b S HL m η X)
          pure (leftColumnsOf u)
        else pure (∅ : Finset (LeftBlockVector L q k))) =
      if (feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) m η X).Nonempty then
        leftColumnsOf (boundaryLeadingVector (S : Set (LeftBlockVector L q k)) HL m η X)
      else ∅ := by
  by_cases hX : (feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) m η X).Nonempty
  · simp only [honestOracle_feasible, hX, decide_true, ↓reduceIte, FreeM.eval_liftBind,
      FreeM.eval_pure, honestOracle_leadingVector]
  · simp only [honestOracle_feasible, hX, decide_false, Bool.false_eq_true, ↓reduceIte,
      FreeM.eval_pure]

/-- With the honest oracle, step 2 computes the size-trimming selection. -/
theorem eval_sizeTrimmingProgram (L k b : ℕ) (h : ChainHamiltonian L q 1 1)
    (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k)) :
    FreeM.eval honestOracle (sizeTrimmingProgram L k b h hq Δ S) =
      h.sizeTrimmingSelection hq Δ S := by
  classical
  let : NeZero q := ⟨by omega⟩
  simp only [sizeTrimmingProgram, ChainHamiltonian.sizeTrimmingSelection, eval_unionOver,
    List.toFinset_finRange, FreeM.eval_liftBind, honestOracle_boundaryNet,
    Finset.toList_toFinset, boundaryMinimizerFamily, leftColumns_eq_biUnion]
  refine Finset.biUnion_congr rfl fun m _ ↦ ?_
  ext v
  simp only [Finset.mem_biUnion, mem_feasibleBoundaryPoints]
  constructor
  · rintro ⟨X, hX, hv⟩
    rw [eval_feasible_ite] at hv
    split_ifs at hv with hP
    · exact ⟨X, ⟨hX, hP⟩, hv⟩
    · exact absurd hv (Finset.notMem_empty v)
  · rintro ⟨X, ⟨hX, hP⟩, hv⟩
    exact ⟨X, hX, by rw [eval_feasible_ite]; simpa only [hP, ↓reduceIte] using hv⟩

/-! ## Algorithm step 3: bond trimming -/

/-- **Algorithm step 3.** Trim every member of the family, a `b`-bounded matrix product
state, to `m` terms at every internal bond. LVV13, `algo53.tex`, lines 549--559. -/
noncomputable def bondTrimmingProgram (L i : ℕ) (hi : i ≤ L) (b m : ℕ)
    (S : Finset (LeftBlockVector L q i)) : LVVProgram q (Finset (LeftBlockVector L q i)) :=
  unionOver S.toList fun u ↦ do
    let w ← FreeM.lift (LinearAlgebraQuery.schmidtTrim L i hi b m u)
    pure {w}

/-- With the honest oracle, step 3 computes the trimmed family. -/
theorem eval_bondTrimmingProgram (L i : ℕ) (hi : i ≤ L) (b m : ℕ)
    (S : Finset (LeftBlockVector L q i)) :
    FreeM.eval honestOracle (bondTrimmingProgram L i hi b m S) = bondTrimSet hi m S := by
  classical
  ext v
  simp only [bondTrimmingProgram, eval_unionOver, Finset.toList_toFinset, FreeM.eval_liftBind,
    FreeM.eval_pure, honestOracle_schmidtTrim, Finset.mem_biUnion, Finset.mem_singleton,
    bondTrimSet, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

/-! ## Algorithm step 4: error reduction -/

/-- **Algorithm step 4.** Apply every left factor of the error-reduction operator, of
operator-Schmidt rank at most `r`, to every member of the family, a `b`-bounded matrix
product state. LVV13, `algo53.tex`, lines 572--592. -/
noncomputable def errorReductionProgram (L i r b : ℕ) (F : Finset (LeftBlockMatrix L q i))
    (T : Finset (LeftBlockVector L q i)) : LVVProgram q (Finset (LeftBlockVector L q i)) :=
  unionOver F.toList fun A ↦ unionOver T.toList fun s ↦ do
    let w ← FreeM.lift (LinearAlgebraQuery.applyFactor L i r b A s)
    pure {w}

/-- With the honest oracle, step 4 computes the error-reduced family. -/
theorem eval_errorReductionProgram (L i r b : ℕ) (F : Finset (LeftBlockMatrix L q i))
    (T : Finset (LeftBlockVector L q i)) :
    FreeM.eval honestOracle (errorReductionProgram L i r b F T) =
      errorReductionSet F id T := by
  classical
  ext v
  simp only [errorReductionProgram, eval_unionOver, Finset.toList_toFinset, FreeM.eval_liftBind,
    FreeM.eval_pure, honestOracle_applyFactor, Finset.mem_biUnion, Finset.mem_singleton,
    errorReductionSet,
    Finset.mem_image₂, id]
  constructor
  · rintro ⟨A, hA, s, hs, rfl⟩
    exact ⟨A, hA, s, hs, rfl⟩
  · rintro ⟨A, hA, s, hs, rfl⟩
    exact ⟨A, hA, s, hs, rfl⟩

/-! ## One step of the sweep and the sweep -/

/-- **One step of the sweep as a program.** Extend, size-trim, bond-trim at the corrected
radius, and apply the Gaussian filter factors, with the bond budget `b_L` of the sweep
declared for the vectors handled. LVV13, `algo53.tex`, algorithm steps 1--4, lines
379--592, with Huang, Section 5.4, Lemmas 18--19 for the error-reduction operator. -/
noncomputable def sweepStepProgram {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Delta : ℝ) {i : ℕ} (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i)) :
    LVVProgram q (Finset (LeftBlockVector L q (i + 1))) :=
  let b := lvvSuccessiveBondBound q Delta L
  let m := bondTrimmingRadius L (lvvReferenceBond q Delta L)
  let c := lvvSuccessiveError Delta
  do
    let S₁ ← extensionProgram L (i + 1) b S
    let S₂ ← sizeTrimmingProgram L (i + 1) b
      (ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1) hq Delta S₁
    let S₃ ← bondTrimmingProgram L (i + 1) hi b m S₂
    let F ← FreeM.lift
      (LinearAlgebraQuery.gaussianFilterFactors L (i + 1) (Nat.le_of_lt hq) h h0 c Delta)
    errorReductionProgram L (i + 1) (huangFilterRankBound q c Delta L) (max 1 m) F S₃

/-- With the honest oracle, one step of the program computes one step of the sweep. -/
theorem eval_sweepStepProgram {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Delta : ℝ) {i : ℕ} (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i)) :
    FreeM.eval honestOracle (sweepStepProgram hq h hs h0 h1 Delta hi S) =
      lvvSweepStep hq h hs h0 h1 Delta hi S := by
  simp only [sweepStepProgram, FreeM.eval_bind, FreeM.eval_lift,
    honestOracle_gaussianFilterFactors, eval_extensionProgram, eval_sizeTrimmingProgram,
    eval_bondTrimmingProgram, eval_errorReductionProgram, lvvSweepStep, successiveStep]

/-- **The sweep as a program.** Start from the scalar singleton and apply the step at every
cut of the chain. LVV13, `algo53.tex`, proof of Theorem 1, lines 652--668. -/
noncomputable def sweepProgram {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Delta : ℝ) : (i : ℕ) → LVVProgram q (Finset (LeftBlockVector L q i))
  | 0 => pure {emptyLeftVector L q}
  | i + 1 =>
    if hi : i + 1 ≤ L then do
      let S ← sweepProgram hq h hs h0 h1 Delta i
      sweepStepProgram hq h hs h0 h1 Delta hi S
    else pure ∅

/-- With the honest oracle, the program computes the sweep at every cut. -/
theorem eval_sweepProgram {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Delta : ℝ) (i : ℕ) :
    FreeM.eval honestOracle (sweepProgram hq h hs h0 h1 Delta i) =
      lvvSweep hq h hs h0 h1 Delta i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    by_cases hi : i + 1 ≤ L
    · simp only [sweepProgram, hi, ↓reduceDIte, FreeM.eval_bind, ih, eval_sweepStepProgram,
        lvvSweep_succ hq h hs h0 h1 Delta hi]
    · simp only [sweepProgram, hi, ↓reduceDIte, FreeM.eval_pure, lvvSweep]

end TNLean.MPS.AreaLaw
