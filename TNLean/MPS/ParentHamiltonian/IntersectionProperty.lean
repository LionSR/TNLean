/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.Chain.OneSidedInverse

/-!
# Intersection and closure properties of MPS ground spaces

For an injective MPS tensor `A`, we establish:

1. **Injectivity of the ground-space map**: `groundSpaceMap A L` is injective for `L ≥ 1`,
   yielding `dim G_L(A) = D²`.

2. **Restriction to ground spaces**: An element of `G_{L+1}(A)` restricts to elements of
   `G_L(A)` on both the left `L`-site window (fixing the last index) and the right
   `L`-site window (fixing the first index).

3. **Intersection property** (the "invert-and-regrow" step): conversely, a state on `L+1`
   sites whose left and right restrictions both lie in `G_L(A)` is itself in `G_{L+1}(A)`.

The intersection property is the key ingredient for proving uniqueness of the ground state
of the parent Hamiltonian (see `UniqueGroundState.lean`).

## Main results

* `MPSTensor.groundSpace_inLeftGround` — forward direction, left window
* `MPSTensor.groundSpace_inRightGround` — forward direction, right window
* `MPSTensor.groundSpaceMap_injective` — injectivity for injective tensors
* `MPSTensor.groundSpace_finrank_eq` — dimension equals `D²`
* `MPSTensor.groundSpace_intersection` — the intersection property

## References

* [CPGSV21] arXiv:2011.12127, parent Hamiltonian section (lines 2013–2094)
* [MPGSC18] arXiv:1804.04964, Section 3 (one-sided inverse)
* [FNW92] Sections 3–4
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Helper lemmas for `List.ofFn` with `Fin.snoc` and `Fin.cons` -/

/-- `List.ofFn` distributes over `Fin.snoc`: appending one element to a function
yields the corresponding list concatenation. -/
theorem list_ofFn_snoc {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) :
    List.ofFn (Fin.snoc f x) = List.ofFn f ++ [x] := by
  conv_lhs => rw [List.ofFn_succ' (Fin.snoc f x)]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Evaluating a word obtained by snoc: peel off the last letter. -/
theorem evalWord_ofFn_snoc (A : MPSTensor d D) {L : ℕ}
    (σ : Fin L → Fin d) (j : Fin d) :
    evalWord A (List.ofFn (Fin.snoc σ j)) =
      evalWord A (List.ofFn σ) * A j := by
  rw [list_ofFn_snoc, evalWord_append]
  simp [evalWord]

/-- Evaluating a word obtained by cons: peel off the first letter. -/
theorem evalWord_ofFn_cons (A : MPSTensor d D) {L : ℕ}
    (i : Fin d) (σ : Fin L → Fin d) :
    evalWord A (List.ofFn (Fin.cons i σ)) =
      A i * evalWord A (List.ofFn σ) := by
  rw [List.ofFn_cons]
  simp [evalWord]

/-! ### Restriction maps between site spaces -/

/-- Restrict an `(L+1)`-site state to the first `L` sites by fixing the last
physical index to `j` (using `Fin.snoc`). -/
def restrictLast {d L : ℕ} (ψ : NSiteSpace d (L + 1)) (j : Fin d) : NSiteSpace d L :=
  fun σ => ψ (Fin.snoc σ j)

/-- Restrict an `(L+1)`-site state to the last `L` sites by fixing the first
physical index to `i` (using `Fin.cons`). -/
def restrictFirst {d L : ℕ} (ψ : NSiteSpace d (L + 1)) (i : Fin d) : NSiteSpace d L :=
  fun σ => ψ (Fin.cons i σ)

@[simp] theorem restrictLast_apply {d L : ℕ} (ψ : NSiteSpace d (L + 1))
    (j : Fin d) (σ : Fin L → Fin d) :
    restrictLast ψ j σ = ψ (Fin.snoc σ j) := rfl

@[simp] theorem restrictFirst_apply {d L : ℕ} (ψ : NSiteSpace d (L + 1))
    (i : Fin d) (σ : Fin L → Fin d) :
    restrictFirst ψ i σ = ψ (Fin.cons i σ) := rfl

/-- `restrictLast` is linear in `ψ`. -/
theorem restrictLast_add {d L : ℕ} (ψ₁ ψ₂ : NSiteSpace d (L + 1)) (j : Fin d) :
    restrictLast (ψ₁ + ψ₂) j = restrictLast ψ₁ j + restrictLast ψ₂ j := by
  ext σ; simp [restrictLast]

/-- `restrictLast` respects scalar multiplication. -/
theorem restrictLast_smul {d L : ℕ} (c : ℂ) (ψ : NSiteSpace d (L + 1)) (j : Fin d) :
    restrictLast (c • ψ) j = c • restrictLast ψ j := by
  ext σ; simp [restrictLast]

/-- `restrictFirst` is linear in `ψ`. -/
theorem restrictFirst_add {d L : ℕ} (ψ₁ ψ₂ : NSiteSpace d (L + 1)) (i : Fin d) :
    restrictFirst (ψ₁ + ψ₂) i = restrictFirst ψ₁ i + restrictFirst ψ₂ i := by
  ext σ; simp [restrictFirst]

/-- `restrictFirst` respects scalar multiplication. -/
theorem restrictFirst_smul {d L : ℕ} (c : ℂ) (ψ : NSiteSpace d (L + 1)) (i : Fin d) :
    restrictFirst (c • ψ) i = c • restrictFirst ψ i := by
  ext σ; simp [restrictFirst]

/-! ### Ground space membership via restrictions -/

/-- A state on `L+1` sites has its left restriction in `G_L(A)`: for each value of the
last physical index, the resulting `L`-site state lies in the ground space. -/
def InLeftGround (A : MPSTensor d D) (L : ℕ) (ψ : NSiteSpace d (L + 1)) : Prop :=
  ∀ j : Fin d, restrictLast ψ j ∈ groundSpace A L

/-- A state on `L+1` sites has its right restriction in `G_L(A)`: for each value of the
first physical index, the resulting `L`-site state lies in the ground space. -/
def InRightGround (A : MPSTensor d D) (L : ℕ) (ψ : NSiteSpace d (L + 1)) : Prop :=
  ∀ i : Fin d, restrictFirst ψ i ∈ groundSpace A L

/-! ### Forward direction: ground-space elements restrict to ground-space elements

If `ψ ∈ G_{L+1}(A)`, i.e. `ψ(σ) = tr(A^σ · X)` for some boundary matrix `X`,
then fixing the last index `j` gives `ψ(σ, j) = tr(A^σ · (A^j · X))`, which lies
in `G_L(A)` with boundary matrix `A^j · X`. Similarly, fixing the first index `i`
gives `ψ(i, σ) = tr(A^σ · (X · A^i))` by trace cyclicity. -/

/-- An element of `G_{L+1}(A)` restricts to `G_L(A)` on the first `L` sites
(left window, fixing the last index). -/
theorem groundSpace_inLeftGround (A : MPSTensor d D) (L : ℕ)
    {ψ : NSiteSpace d (L + 1)} (hψ : ψ ∈ groundSpace A (L + 1)) :
    InLeftGround A L ψ := by
  intro j
  rw [groundSpace, LinearMap.mem_range] at hψ ⊢
  obtain ⟨X, rfl⟩ := hψ
  refine ⟨A j * X, ?_⟩
  ext σ
  simp only [restrictLast_apply, groundSpaceMap_apply, evalWord_ofFn_snoc, Matrix.mul_assoc]

/-- An element of `G_{L+1}(A)` restricts to `G_L(A)` on the last `L` sites
(right window, fixing the first index). -/
theorem groundSpace_inRightGround (A : MPSTensor d D) (L : ℕ)
    {ψ : NSiteSpace d (L + 1)} (hψ : ψ ∈ groundSpace A (L + 1)) :
    InRightGround A L ψ := by
  intro i
  rw [groundSpace, LinearMap.mem_range] at hψ ⊢
  obtain ⟨X, rfl⟩ := hψ
  refine ⟨X * A i, ?_⟩
  ext σ
  simp only [restrictFirst_apply, groundSpaceMap_apply, evalWord_ofFn_cons, Matrix.mul_assoc]
  -- Goal: tr(evalWord * (X * A i)) = tr(A i * (evalWord * X))
  -- Use: tr(M * N) = tr(N * M) twice, plus associativity
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]

/-! ### Injectivity of the ground-space map -/

/-- For an injective tensor, `groundSpaceMap A L` is injective for any `L ≥ 1`.

**Proof sketch**: It suffices to show `groundSpaceMap A L X = 0 → X = 0`.
If `tr(A^σ · X) = 0` for all words `σ` of length `L`, and the set `{A^σ}`
spans `M_D(ℂ)` (which holds for `L ≥ 1` by the injectivity hypothesis),
then nondegeneracy of the trace pairing gives `X = 0`. -/
theorem groundSpaceMap_injective {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 0 < L) :
    Function.Injective (groundSpaceMap A L) := by
  sorry

/-- For an injective tensor, the ground space has dimension exactly `D²` for `L ≥ 1`.

This follows from injectivity of `groundSpaceMap` (which has domain `M_D(ℂ)` of
dimension `D²`) together with the dimension upper bound `dim G_L(A) ≤ D²`. -/
theorem groundSpace_finrank_eq {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 0 < L) :
    Module.finrank ℂ ↥(groundSpace A L) = D ^ 2 := by
  sorry

/-! ### The intersection property -/

/-- **Intersection property** for injective MPS: a state on `L+1` sites that restricts
to ground-space elements on both the left and right `L`-site windows is itself
in `G_{L+1}(A)`.

This is the "invert-and-regrow" step. The proof proceeds as follows:

1. From `InRightGround`: for each `i`, ∃ unique `Y_i` with `ψ(i, σ) = tr(A^σ · Y_i)`.
2. From `InLeftGround`: for each `j`, ∃ unique `Z_j` with `ψ(σ, j) = tr(A^σ · Z_j)`.
3. Matching on the overlap and using trace-pairing nondegeneracy:
   `A^j · Y_i = Z_j · A^i` for all `i, j`.
4. Apply the decomposition map (one-sided inverse from `OneSidedInverse.lean`):
   sum over `i` with decomposition coefficients of the identity to get
   `Y_i = X' · A^i` for a single matrix `X' = ∑ⱼ (Ψ(I))ⱼ · Z_j`.
5. By trace cyclicity, `ψ(σ) = tr(A^σ · X')`, so `ψ ∈ G_{L+1}(A)`. -/
theorem groundSpace_intersection {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 0 < L) {ψ : NSiteSpace d (L + 1)}
    (hLeft : InLeftGround A L ψ) (hRight : InRightGround A L ψ) :
    ψ ∈ groundSpace A (L + 1) := by
  sorry

/-- The ground space on `L+1` sites is characterized by the intersection property:
`ψ ∈ G_{L+1}(A)` iff both the left and right `L`-site restrictions lie in `G_L(A)`. -/
theorem groundSpace_iff_left_right {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 0 < L) {ψ : NSiteSpace d (L + 1)} :
    ψ ∈ groundSpace A (L + 1) ↔ InLeftGround A L ψ ∧ InRightGround A L ψ :=
  ⟨fun h => ⟨groundSpace_inLeftGround A L h, groundSpace_inRightGround A L h⟩,
   fun ⟨hL', hR'⟩ => groundSpace_intersection hA hL hL' hR'⟩

end MPSTensor
