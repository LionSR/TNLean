/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Cslib.Algorithms.Lean.Query.Bounds
import TNLean.MPS.AreaLaw.ViableSet.SampledFactors
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveStep

/-!
# The linear-algebra queries of the ground-state algorithm

The algorithm of Landau, Vazirani and Vidick is a sequence of linear-algebra operations on
vectors given as matrix product states of polynomial bond dimension: one-site extensions,
the enumeration of a net of boundary contractions, the size-trimming convex programs and the
leading eigenvectors of their solutions, Schmidt trimmings, the left factors of the
error-reduction operators and their application, and the final convex program. The paper
counts each of these as one polynomial-time step on polynomial-dimensional data and does
not analyse the linear algebra further (arXiv:1307.5143v1, `algo53.tex`, lines 219 and
484--487: "The remaining steps rely on the singular value decomposition which can be
performed efficiently as well.").

This module fixes the cost model in which that count is made. The queries form the type
`LinearAlgebraQuery`, indexed by their answer types, in the query framework of CSLib. The
honest oracle `honestOracle` answers every query with the exact mathematical object that
the definitions of the sweep use, so that a program over these queries, run with the honest
oracle, computes the sweep itself. The declared cost `queryCost` of each query is a
polynomial in the dimensions of its arguments: the chain length, the local dimension, the
bond dimension of the vectors involved, the cardinality of the family, the bond of the
boundary contraction and the rank of the operator.

**Scope restriction (cost model):** The costs are declared, not derived. Arithmetic is
exact, a query is charged the cost of the textbook algorithm for it on data of the stated
dimensions, and nothing is proved about how a query is answered. Bit complexity and
floating-point error are outside the model, as they are outside the paper. The restriction
is recorded in `docs/paper-gaps/lvv13_cost_model.tex`; it applies to every program and cost
bound built on this query type.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 213--219 (Theorem 1), 379--400
(extension), 456--487 (the size-trimming convex program and its cost), 549--559 (bond
trimming), 572--592 (error reduction) and 652--678 (the final convex program).
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-! ## The energy minimizer of the final convex program -/

/-- A unit vector of least energy in a nonzero subspace exists.
LVV13, `algo53.tex`, lines 672--677: the final convex program has an optimal solution. -/
theorem exists_energy_minimizer {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (U : Submodule ℂ (EuclideanSpace ℂ n)) (hU : U ≠ ⊥) :
    ∃ v ∈ U, ‖v‖ = 1 ∧ ∀ w ∈ U, ‖w‖ = 1 →
      (⟪v, toEuclideanLin H v⟫_ℂ).re ≤ (⟪w, toEuclideanLin H w⟫_ℂ).re := by
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).mp hU
  have hK : IsCompact ((U : Set (EuclideanSpace ℂ n)) ∩ Metric.sphere 0 1) :=
    (isCompact_sphere (0 : EuclideanSpace ℂ n) 1).inter_left U.closed_of_finiteDimensional
  have hne : ((U : Set (EuclideanSpace ℂ n)) ∩ Metric.sphere 0 1).Nonempty :=
    ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, U.smul_mem _ hxU, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]⟩
  have hcont : Continuous fun w : EuclideanSpace ℂ n ↦ (⟪w, toEuclideanLin H w⟫_ℂ).re :=
    Complex.continuous_re.comp
      (continuous_id.inner (LinearMap.continuous_of_finiteDimensional (toEuclideanLin H)))
  obtain ⟨v, ⟨hvU, hv1⟩, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  exact ⟨v, hvU, mem_sphere_zero_iff_norm.mp hv1,
    fun w hwU hw1 ↦ hmin ⟨hwU, mem_sphere_zero_iff_norm.mpr hw1⟩⟩

open Classical in
/-- **The solution of the final convex program.** A chosen unit vector of least energy in the
span of the family `S`, and `0` when the span is trivial. This is the leading eigenvector of
an optimal solution of the program of LVV13, `algo53.tex`, lines 672--677, whose optimal
solutions include pure states. -/
noncomputable def energyMinimizer {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (S : Finset (EuclideanSpace ℂ n)) : EuclideanSpace ℂ n :=
  if hU : Submodule.span ℂ (S : Set (EuclideanSpace ℂ n)) ≠ ⊥ then
    Classical.choose (exists_energy_minimizer H _ hU)
  else 0

/-- When the span of `S` is nonzero, the chosen vector is a unit vector of the span of least
energy among the unit vectors of the span. LVV13, `algo53.tex`, lines 672--677. -/
theorem energyMinimizer_spec {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (S : Finset (EuclideanSpace ℂ n))
    (hU : Submodule.span ℂ (S : Set (EuclideanSpace ℂ n)) ≠ ⊥) :
    energyMinimizer H S ∈ Submodule.span ℂ (S : Set (EuclideanSpace ℂ n)) ∧
      ‖energyMinimizer H S‖ = 1 ∧
      ∀ w ∈ Submodule.span ℂ (S : Set (EuclideanSpace ℂ n)), ‖w‖ = 1 →
        (⟪energyMinimizer H S, toEuclideanLin H (energyMinimizer H S)⟫_ℂ).re ≤
          (⟪w, toEuclideanLin H w⟫_ℂ).re := by
  simp only [energyMinimizer, ne_eq, hU, not_false_eq_true, ↓reduceDIte]
  exact Classical.choose_spec (exists_energy_minimizer H _ hU)

/-! ## The query type -/

/-- **The linear-algebra queries of the algorithm**, indexed by their answer types. Every
query carries the chain length `L`; the natural-number arguments `b`, `s`, `m`, `r` that
the honest oracle ignores are the dimensions in which its cost is declared: the bond
dimension of the vectors involved, the cardinality of the family, the bond of the boundary
contraction and the rank of the operator. LVV13, `algo53.tex`, lines 379--400, 456--487,
549--559, 572--592 and 672--677. -/
inductive LinearAlgebraQuery (q : ℕ) : Type → Type
  /-- The one-site extension `v ⊗ |k⟩` of a vector `v` on the first `i - 1` sites, given as
  a matrix product state of bond dimension at most `b`. Algorithm step 1, lines 379--386. -/
  | extendSite (L i b : ℕ) (k : Fin q) (v : LeftBlockVector L q (i - 1)) :
      LinearAlgebraQuery q (LeftBlockVector L q i)
  /-- The trace-norm net of radius `η` on the boundary contractions at the cut after `k`
  sites with a bond of dimension `m`. Lemma 2.4, lines 451--460. -/
  | boundaryNet (L k m : ℕ) (η : ℝ) :
      LinearAlgebraQuery q
        (Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ))
  /-- Whether the size-trimming convex program over the span of `S`, a family of `s`
  matrix product states of bond dimension at most `b`, is feasible at the boundary point
  `X` with tolerance `η`. Equation `eq:conv`, lines 472--476. -/
  | feasible (L k b : ℕ) (S : Finset (LeftBlockVector L q k)) (m : ℕ) (η : ℝ)
      (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
      LinearAlgebraQuery q Bool
  /-- The leading eigenvector of an optimal solution of the size-trimming convex program
  over the span of `S` with left Hamiltonian `HL` at the boundary point `X`. Equation
  `eq:conv` and lines 477--478. -/
  | leadingVector (L k b : ℕ) (S : Finset (LeftBlockVector L q k))
      (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
      (m : ℕ) (η : ℝ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
      LinearAlgebraQuery q (EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
  /-- The Schmidt trimming of a vector on the first `i` sites, of bond dimension at most
  `b`, to `m` terms at every internal bond. Algorithm step 3, lines 549--559. -/
  | schmidtTrim (L i : ℕ) (hi : i ≤ L) (b m : ℕ) (u : LeftBlockVector L q i) :
      LinearAlgebraQuery q (LeftBlockVector L q i)
  /-- The left factors, at the cut after `i` sites, of the Gaussian filters of the chain
  with terms `h` at precision `c` for the gap parameter `Delta`. Huang, arXiv:1406.6355v6,
  Section 5.4; LVV13 algorithm step 4, lines 572--592. -/
  | gaussianFilterFactors (L i : ℕ) (hq : 1 ≤ q)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (h0 : ∀ j, 0 ≤ h j)
      (c Delta : ℝ) : LinearAlgebraQuery q (Finset (LeftBlockMatrix L q i))
  /-- The left factors, at the cut after `i` sites, of the sampled projector of the words
  `I`, `ℓ` words of length `m` whose factors have rank at most `D`, for the chain with
  terms `h` at ground energy `E₀`. Definition `d:sagsp`, line 611; algorithm step 4,
  lines 572--592. -/
  | sampledFactors (L i : ℕ) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (E₀ : ℝ) (ℓ m D : ℕ) (I : Fin ℓ → Fin m → Fin L) :
      LinearAlgebraQuery q (Finset (LeftBlockMatrix L q i))
  /-- The application of a left factor `A` of operator-Schmidt rank at most `r` to a
  vector `s` of bond dimension at most `b`. Algorithm step 4, line 572. -/
  | applyFactor (L i r b : ℕ) (A : LeftBlockMatrix L q i) (s : LeftBlockVector L q i) :
      LinearAlgebraQuery q (LeftBlockVector L q i)
  /-- A unit vector of least energy for `H` in the span of a family `S` of `s` matrix
  product states of bond dimension at most `b` on the whole chain: the final convex
  program. Lines 672--677. -/
  | energyMinimizer (L b : ℕ) (H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (S : Finset (EuclideanSpace ℂ (Fin L → Fin q))) :
      LinearAlgebraQuery q (EuclideanSpace ℂ (Fin L → Fin q))

variable {q : ℕ}

open Classical in
/-- **The honest oracle** answers every query with the exact object used by the definitions
of the sweep: the extension `extendSite`, the chosen net `rectangularTraceNormNet`,
feasibility of the convex program, the chosen leading vector `boundaryLeadingVector`, the
trimming `leftSchmidtTrim`, the Gaussian filter factors `gaussianFilterFactors`, the sampled factors
`sampledFactors`, the matrix action, and the chosen `energyMinimizer`. -/
noncomputable def LinearAlgebraQuery.honestOracle : {ι : Type} → LinearAlgebraQuery q ι → ι
  | _, .extendSite _ i _ k v => AreaLaw.extendSite i k v
  | _, .boundaryNet L k m η => rectangularTraceNormNet (CutSite L q k × Fin m) η
  | _, .feasible _ _ _ S m η X =>
      decide (feasibleBoundaryDensities (S : Set (LeftBlockVector _ q _)) m η X).Nonempty
  | _, .leadingVector _ _ _ S HL m η X =>
      boundaryLeadingVector (S : Set (LeftBlockVector _ q _)) HL m η X
  | _, .schmidtTrim _ _ hi _ m u => leftSchmidtTrim hi m u
  | _, .gaussianFilterFactors _ i hq h h0 c Delta =>
      AreaLaw.gaussianFilterFactors hq h h0 c Delta i
  | _, .sampledFactors _ i h E₀ _ _ _ I => AreaLaw.sampledFactors h E₀ I i
  | _, .applyFactor _ _ _ _ A s => toEuclideanLin A s
  | _, .energyMinimizer _ _ H S => AreaLaw.energyMinimizer H S

/-! ### The honest answers, one query at a time -/

@[simp]
theorem LinearAlgebraQuery.honestOracle_extendSite (L i b : ℕ) (k : Fin q)
    (v : LeftBlockVector L q (i - 1)) :
    honestOracle (LinearAlgebraQuery.extendSite L i b k v) = AreaLaw.extendSite i k v := rfl

@[simp]
theorem LinearAlgebraQuery.honestOracle_boundaryNet (L k m : ℕ) (η : ℝ) :
    honestOracle (LinearAlgebraQuery.boundaryNet (q := q) L k m η) =
      rectangularTraceNormNet (CutSite L q k × Fin m) η := rfl

open Classical in
@[simp]
theorem LinearAlgebraQuery.honestOracle_feasible (L k b : ℕ) (S : Finset (LeftBlockVector L q k))
    (m : ℕ) (η : ℝ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    honestOracle (LinearAlgebraQuery.feasible L k b S m η X) =
      decide (feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) m η X).Nonempty :=
  rfl

@[simp]
theorem LinearAlgebraQuery.honestOracle_leadingVector (L k b : ℕ)
    (S : Finset (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    honestOracle (LinearAlgebraQuery.leadingVector L k b S HL m η X) =
      boundaryLeadingVector (S : Set (LeftBlockVector L q k)) HL m η X := rfl

@[simp]
theorem LinearAlgebraQuery.honestOracle_schmidtTrim (L i : ℕ) (hi : i ≤ L) (b m : ℕ)
    (u : LeftBlockVector L q i) :
    honestOracle (LinearAlgebraQuery.schmidtTrim L i hi b m u) = leftSchmidtTrim hi m u := rfl

@[simp]
theorem LinearAlgebraQuery.honestOracle_gaussianFilterFactors (L i : ℕ) (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (h0 : ∀ j, 0 ≤ h j)
    (c Delta : ℝ) :
    honestOracle (LinearAlgebraQuery.gaussianFilterFactors L i hq h h0 c Delta) =
      AreaLaw.gaussianFilterFactors hq h h0 c Delta i := rfl

@[simp]
theorem LinearAlgebraQuery.honestOracle_sampledFactors (L i : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) (ℓ m D : ℕ)
    (I : Fin ℓ → Fin m → Fin L) :
    honestOracle (LinearAlgebraQuery.sampledFactors L i h E₀ ℓ m D I) =
      AreaLaw.sampledFactors h E₀ I i := rfl

@[simp]
theorem LinearAlgebraQuery.honestOracle_applyFactor (L i r b : ℕ) (A : LeftBlockMatrix L q i)
    (s : LeftBlockVector L q i) :
    honestOracle (LinearAlgebraQuery.applyFactor L i r b A s) = toEuclideanLin A s := rfl

@[simp]
theorem LinearAlgebraQuery.honestOracle_energyMinimizer (L b : ℕ)
    (H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (S : Finset (EuclideanSpace ℂ (Fin L → Fin q))) :
    honestOracle (LinearAlgebraQuery.energyMinimizer L b H S) = AreaLaw.energyMinimizer H S :=
  rfl

/-! ## The declared costs

Each cost is one unit for the query itself plus a polynomial in the dimensions carried by
the query. They are declared: the cost of the textbook algorithm on data of those
dimensions, in exact arithmetic. -/

/-- Declared cost of one one-site extension of a matrix product state of bond dimension at
most `b`: one new tensor with `q b²` entries. -/
def extensionCost (q b : ℕ) : ℕ := 1 + q * b ^ 2

/-- Declared cost of enumerating the trace-norm net of radius `η` on a boundary space of
dimension `q m`: its cardinality bound times the number of entries of one point. -/
noncomputable def netCost (q m : ℕ) (η : ℝ) : ℕ :=
  1 + (q * m) ^ 2 * (2 * ⌈((q * m : ℕ) : ℝ) ^ 2 / η⌉₊ + 1) ^ (2 * (q * m) ^ 2)

/-- Declared cost of the size-trimming convex program over the span of `s` matrix product
states of bond dimension at most `b` on a chain of length `L` with a bond of dimension
`m`: the matrix elements of the `L` terms in an orthonormal basis of the span, computed from
the matrix product states, and an interior-point solution in `(s m)²` variables. -/
def convexProgramCost (L q b s m : ℕ) : ℕ := 1 + L * q * b ^ 2 * (s * m) ^ 3

/-- Declared cost of trimming a matrix product state of bond dimension at most `b` on a
chain of length `L`: one singular value decomposition at each bond. -/
def schmidtTrimCost (L q b : ℕ) : ℕ := 1 + L * q * b ^ 3

/-- Declared cost of computing the left factors of `E` Gaussian filters of operator-Schmidt
rank at most `R` on a chain of length `L`. -/
def filterFactorsCost (L q E R : ℕ) : ℕ := 1 + E * R * L * q ^ 2

/-- Declared cost of applying a left factor of operator-Schmidt rank at most `r` to a matrix
product state of bond dimension at most `b` on a chain of length `L`. -/
def applyFactorCost (L q r b : ℕ) : ℕ := 1 + L * q ^ 2 * r ^ 2 * b ^ 2

/-- Declared cost of the final convex program over the span of `s` matrix product states of
bond dimension at most `b` on a chain of length `L`. -/
def energyMinimizerCost (L q b s : ℕ) : ℕ := 1 + L * q * b ^ 2 * s ^ 3

/-- **The declared cost of a query.** -/
noncomputable def LinearAlgebraQuery.queryCost : {ι : Type} → LinearAlgebraQuery q ι → ℕ
  | _, .extendSite _ _ b _ _ => extensionCost q b
  | _, .boundaryNet _ _ m η => netCost q m η
  | _, .feasible L _ b S m _ _ => convexProgramCost L q b S.card m
  | _, .leadingVector L _ b S _ m _ _ => convexProgramCost L q b S.card m
  | _, .schmidtTrim L _ _ b _ _ => schmidtTrimCost L q b
  | _, .gaussianFilterFactors L _ _ _ _ c Delta =>
      filterFactorsCost L q (huangEnergyCount c Delta L) (huangFilterRankBound q c Delta L)
  | _, .sampledFactors L _ _ _ ℓ _ D _ => filterFactorsCost L q ℓ D
  | _, .applyFactor L _ r b _ _ => applyFactorCost L q r b
  | _, .energyMinimizer L b _ S => energyMinimizerCost L q b S.card

/-! ### The declared costs, one query at a time -/

@[simp]
theorem LinearAlgebraQuery.queryCost_extendSite (L i b : ℕ) (k : Fin q)
    (v : LeftBlockVector L q (i - 1)) :
    queryCost (LinearAlgebraQuery.extendSite L i b k v) = extensionCost q b := rfl

@[simp]
theorem LinearAlgebraQuery.queryCost_boundaryNet (L k m : ℕ) (η : ℝ) :
    queryCost (LinearAlgebraQuery.boundaryNet (q := q) L k m η) = netCost q m η := rfl

@[simp]
theorem LinearAlgebraQuery.queryCost_feasible (L k b : ℕ) (S : Finset (LeftBlockVector L q k))
    (m : ℕ) (η : ℝ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    queryCost (LinearAlgebraQuery.feasible L k b S m η X) =
      convexProgramCost L q b S.card m := rfl

@[simp]
theorem LinearAlgebraQuery.queryCost_leadingVector (L k b : ℕ)
    (S : Finset (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    queryCost (LinearAlgebraQuery.leadingVector L k b S HL m η X) =
      convexProgramCost L q b S.card m := rfl

@[simp]
theorem LinearAlgebraQuery.queryCost_schmidtTrim (L i : ℕ) (hi : i ≤ L) (b m : ℕ)
    (u : LeftBlockVector L q i) :
    queryCost (LinearAlgebraQuery.schmidtTrim L i hi b m u) = schmidtTrimCost L q b := rfl

@[simp]
theorem LinearAlgebraQuery.queryCost_gaussianFilterFactors (L i : ℕ) (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (h0 : ∀ j, 0 ≤ h j)
    (c Delta : ℝ) :
    queryCost (LinearAlgebraQuery.gaussianFilterFactors L i hq h h0 c Delta) =
      filterFactorsCost L q (huangEnergyCount c Delta L) (huangFilterRankBound q c Delta L) :=
  rfl

@[simp]
theorem LinearAlgebraQuery.queryCost_sampledFactors (L i : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) (ℓ m D : ℕ)
    (I : Fin ℓ → Fin m → Fin L) :
    queryCost (LinearAlgebraQuery.sampledFactors L i h E₀ ℓ m D I) =
      filterFactorsCost L q ℓ D := rfl

@[simp]
theorem LinearAlgebraQuery.queryCost_applyFactor (L i r b : ℕ) (A : LeftBlockMatrix L q i)
    (s : LeftBlockVector L q i) :
    queryCost (LinearAlgebraQuery.applyFactor L i r b A s) = applyFactorCost L q r b := rfl

@[simp]
theorem LinearAlgebraQuery.queryCost_energyMinimizer (L b : ℕ)
    (H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (S : Finset (EuclideanSpace ℂ (Fin L → Fin q))) :
    queryCost (LinearAlgebraQuery.energyMinimizer L b H S) =
      energyMinimizerCost L q b S.card := rfl

/-- Every query costs at least one unit. -/
theorem LinearAlgebraQuery.one_le_queryCost {ι : Type} (op : LinearAlgebraQuery q ι) :
    1 ≤ queryCost op := by
  cases op <;> exact Nat.le_add_right 1 _

/-! ## Iterating a program over a finite family -/

namespace LinearAlgebraQuery

open Cslib

variable {Q : Type → Type} {α β : Type} [DecidableEq β]

/-- The number of queries is at most the cost when every query costs at least one unit. -/
theorem countQueries_le_cost (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → ℕ)
    (hw : ∀ {ι : Type} (op : Q ι), 1 ≤ weight op) (p : FreeM Q α) :
    FreeM.countQueries oracle p ≤ FreeM.cost oracle weight p := by
  induction p with
  | pure a => simp
  | lift_bind op cont ih =>
    rw [FreeM.bind_eq_bind, FreeM.countQueries_liftBind, FreeM.cost_liftBind]
    exact Nat.add_le_add (hw op) (ih _)

/-- Run a program at every element of a list and take the union of the finite sets it
returns. -/
def unionOver : List α → (α → FreeM Q (Finset β)) → FreeM Q (Finset β)
  | [], _ => pure ∅
  | x :: xs, f => do
    let s ← f x
    let t ← unionOver xs f
    pure (s ∪ t)

@[simp]
theorem unionOver_nil (f : α → FreeM Q (Finset β)) : unionOver [] f = pure ∅ := rfl

@[simp]
theorem unionOver_cons (x : α) (xs : List α) (f : α → FreeM Q (Finset β)) :
    unionOver (x :: xs) f = (do
      let s ← f x
      let t ← unionOver xs f
      pure (s ∪ t)) := rfl

/-- Evaluating the iteration gives the union of the evaluations over the elements of the
list. -/
theorem eval_unionOver [DecidableEq α] (oracle : {ι : Type} → Q ι → ι) (l : List α)
    (f : α → FreeM Q (Finset β)) :
    FreeM.eval oracle (unionOver l f) =
      l.toFinset.biUnion fun x ↦ FreeM.eval oracle (f x) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [unionOver_cons, FreeM.eval_bind, FreeM.eval_pure, ih, List.toFinset_cons,
      Finset.biUnion_insert]

/-- The cost of the iteration is the sum of the costs over the list. -/
theorem cost_unionOver {T : Type} [AddCommMonoid T] (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T) (l : List α) (f : α → FreeM Q (Finset β)) :
    FreeM.cost oracle weight (unionOver l f) =
      (l.map fun x ↦ FreeM.cost oracle weight (f x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [unionOver_cons, FreeM.cost_bind, FreeM.cost_pure, add_zero, ih, List.map_cons,
      List.sum_cons]

/-- The number of queries of the iteration is the sum over the list. -/
theorem countQueries_unionOver (oracle : {ι : Type} → Q ι → ι) (l : List α)
    (f : α → FreeM Q (Finset β)) :
    FreeM.countQueries oracle (unionOver l f) =
      (l.map fun x ↦ FreeM.countQueries oracle (f x)).sum :=
  cost_unionOver oracle (fun _ ↦ 1) l f

end LinearAlgebraQuery

end TNLean.MPS.AreaLaw
