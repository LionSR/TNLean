/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.Algebra.TracePairing
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan

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
* `MPSTensor.groundSpaceMap_injective_of_wordSpan_eq_top` — injectivity from
  full word span at length `L`
* `MPSTensor.groundSpaceMap_injective` — injectivity for injective tensors
* `MPSTensor.groundSpace_finrank_eq` — dimension equals `D²`
* `MPSTensor.groundSpace_intersection` — the intersection property

## References

* [CPGSV21] arXiv:2011.12127, parent Hamiltonian section (lines 2013–2094)
* [MPGSC18] arXiv:1804.04964, Section 3 (one-sided inverse)
* [FNW92] Sections 3–4
-/

open scoped Matrix BigOperators

namespace List

/-- `List.ofFn` distributes over `Fin.snoc`: appending one element to a function
yields the corresponding list concatenation. -/
theorem ofFn_snoc {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) :
    List.ofFn (Fin.snoc f x) = List.ofFn f ++ [x] := by
  conv_lhs => rw [List.ofFn_succ' (Fin.snoc f x)]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

end List

namespace MPSTensor

variable {d D : ℕ}

/-! ### Helper lemmas for `List.ofFn` with `Fin.snoc` and `Fin.cons` -/

/-- Evaluating a word obtained by snoc: peel off the last letter. -/
theorem evalWord_ofFn_snoc (A : MPSTensor d D) {L : ℕ}
    (σ : Fin L → Fin d) (j : Fin d) :
    evalWord A (List.ofFn (Fin.snoc σ j)) =
      evalWord A (List.ofFn σ) * A j := by
  rw [List.ofFn_snoc, evalWord_append]
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
def restrictLastₗ {d L : ℕ} (j : Fin d) : NSiteSpace d (L + 1) →ₗ[ℂ] NSiteSpace d L where
  toFun ψ := fun σ => ψ (Fin.snoc σ j)
  map_add' ψ₁ ψ₂ := by
    ext σ
    simp
  map_smul' c ψ := by
    ext σ
    simp

/-- Restrict an `(L+1)`-site state to the first `L` sites by fixing the last
physical index to `j` (using `Fin.snoc`). -/
noncomputable def restrictLast {d L : ℕ} (ψ : NSiteSpace d (L + 1)) (j : Fin d) :
    NSiteSpace d L :=
  restrictLastₗ j ψ

/-- Restrict an `(L+1)`-site state to the last `L` sites by fixing the first
physical index to `i` (using `Fin.cons`). -/
def restrictFirstₗ {d L : ℕ} (i : Fin d) : NSiteSpace d (L + 1) →ₗ[ℂ] NSiteSpace d L where
  toFun ψ := fun σ => ψ (Fin.cons i σ)
  map_add' ψ₁ ψ₂ := by
    ext σ
    simp
  map_smul' c ψ := by
    ext σ
    simp

/-- Restrict an `(L+1)`-site state to the last `L` sites by fixing the first
physical index to `i` (using `Fin.cons`). -/
noncomputable def restrictFirst {d L : ℕ} (ψ : NSiteSpace d (L + 1)) (i : Fin d) :
    NSiteSpace d L :=
  restrictFirstₗ i ψ

@[simp] theorem restrictLast_apply {d L : ℕ} (ψ : NSiteSpace d (L + 1))
    (j : Fin d) (σ : Fin L → Fin d) :
    restrictLast ψ j σ = ψ (Fin.snoc σ j) := rfl

@[simp] theorem restrictFirst_apply {d L : ℕ} (ψ : NSiteSpace d (L + 1))
    (i : Fin d) (σ : Fin L → Fin d) :
    restrictFirst ψ i σ = ψ (Fin.cons i σ) := rfl

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
  -- Cycle the leading `A i` to the end of the product under the trace.
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]

/-! ### Injectivity of the ground-space map -/

/-- If the length-`L` word span is all of `M_D(ℂ)`, then `groundSpaceMap A L`
is injective. -/
theorem groundSpaceMap_injective_of_wordSpan_eq_top {A : MPSTensor d D} {L : ℕ}
    (hwordL : wordSpan A L = ⊤) :
    Function.Injective (groundSpaceMap A L) := by
  have hker : (groundSpaceMap A L).ker = ⊥ := by
    apply (LinearMap.ker_eq_bot').2
    intro X hX
    have hφ :
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulRight ℂ X) = 0 := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin L → Fin d => evalWord A (List.ofFn σ))
      · simpa [wordSpan] using hwordL
      · intro σ
        simpa [groundSpaceMap_apply, Matrix.traceLinearMap_apply] using
          congrArg (fun ψ => ψ σ) hX
    exact trace_mul_right_eq_zero fun N => by
      have hNX : Matrix.trace (N * X) = 0 := by
        simpa [Matrix.traceLinearMap_apply] using congrArg (fun f => f N) hφ
      calc
        Matrix.trace (X * N) = Matrix.trace (N * X) := Matrix.trace_mul_comm X N
        _ = 0 := hNX
  exact LinearMap.ker_eq_bot.mp hker

/-- For an injective tensor, `groundSpaceMap A L` is injective for any `L ≥ 1`.

**Proof sketch**: injectivity gives `wordSpan A 1 = ⊤`; since `1 ∈ wordSpan A 1`,
monotonicity of word spans yields `wordSpan A L = ⊤` for all `L ≥ 1`, and the
previous theorem applies. -/
theorem groundSpaceMap_injective {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 0 < L) :
    Function.Injective (groundSpaceMap A L) := by
  have hword1 : wordSpan A 1 = ⊤ := by
    have hRange :
        Set.range (fun σ : Fin 1 → Fin d => evalWord A (List.ofFn σ)) = Set.range A := by
      ext M
      constructor
      · rintro ⟨σ, rfl⟩
        exact ⟨σ 0, by simp [evalWord]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨fun _ => i, by simp [evalWord]⟩
    change Submodule.span ℂ (Set.range fun σ : Fin 1 → Fin d => evalWord A (List.ofFn σ)) = ⊤
    rw [hRange]
    exact hA
  have hone : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1 := by
    rw [hword1]
    exact Submodule.mem_top
  have hwordL : wordSpan A L = ⊤ := by
    have hmono : wordSpan A 1 ≤ wordSpan A L :=
      wordSpan_mono'_of_one_mem_wordSpan_one A hone (by omega)
    exact eq_top_iff.mpr (by simpa [hword1] using hmono)
  exact groundSpaceMap_injective_of_wordSpan_eq_top hwordL

/-- For an injective tensor, the ground space has dimension exactly `D²` for `L ≥ 1`.

This follows from injectivity of `groundSpaceMap` (which has domain `M_D(ℂ)` of
dimension `D²`) together with the dimension upper bound `dim G_L(A) ≤ D²`. -/
theorem groundSpace_finrank_eq {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 0 < L) :
    Module.finrank ℂ ↥(groundSpace A L) = D ^ 2 := by
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] groundSpace A L :=
    LinearEquiv.ofInjective (groundSpaceMap A L) (groundSpaceMap_injective hA hL)
  calc
    Module.finrank ℂ ↥(groundSpace A L)
        = Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) := by
            simpa [groundSpace] using (LinearEquiv.finrank_eq e).symm
    _ = (Fintype.card (Fin D) * Fintype.card (Fin D)) * Module.finrank ℂ ℂ := by
          simpa using (Module.finrank_matrix ℂ ℂ (Fin D) (Fin D))
    _ = D * D := by simp
    _ = D ^ 2 := by simp [pow_two]

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
5. By trace cyclicity, `ψ(σ) = tr(A^σ · X')`, so `ψ ∈ G_{L+1}(A)`.

The formal overlap argument uses the `(L - 1)`-site intersection, so we record
the theorem with the honest hypothesis `1 < L`. -/
theorem groundSpace_intersection {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 1 < L) {ψ : NSiteSpace d (L + 1)}
    (hLeft : InLeftGround A L ψ) (hRight : InRightGround A L ψ) :
    ψ ∈ groundSpace A (L + 1) := by
  classical
  have hL0 : 0 < L := by omega
  obtain ⟨K, hKeq⟩ := Nat.exists_eq_add_of_lt hL0
  rw [zero_add] at hKeq
  subst hKeq
  have hK : 0 < K := by omega
  have hRight' :
      ∀ i : Fin d, ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        restrictFirst ψ i = groundSpaceMap A (K + 1) Y := by
    intro i
    have hi := hRight i
    rw [groundSpace, LinearMap.mem_range] at hi
    rcases hi with ⟨Y, hY⟩
    exact ⟨Y, hY.symm⟩
  choose Y hY using hRight'
  have hLeft' :
      ∀ j : Fin d, ∃ Z : Matrix (Fin D) (Fin D) ℂ,
        restrictLast ψ j = groundSpaceMap A (K + 1) Z := by
    intro j
    have hj := hLeft j
    rw [groundSpace, LinearMap.mem_range] at hj
    rcases hj with ⟨Z, hZ⟩
    exact ⟨Z, hZ.symm⟩
  choose Z hZ using hLeft'
  have hCompat : ∀ i j, A j * Y i = Z j * A i := by
    intro i j
    apply groundSpaceMap_injective hA hK
    ext σ
    have hYi :
        groundSpaceMap A K (A j * Y i) σ = ψ (Fin.cons i (Fin.snoc σ j)) := by
      calc
        groundSpaceMap A K (A j * Y i) σ
            = Matrix.trace (evalWord A (List.ofFn σ) * (A j * Y i)) := by
                simp [groundSpaceMap_apply]
        _ = Matrix.trace (evalWord A (List.ofFn (Fin.snoc σ j)) * Y i) := by
              rw [evalWord_ofFn_snoc]
              simp [Matrix.mul_assoc]
        _ = ψ (Fin.cons i (Fin.snoc σ j)) := by
              simpa [restrictFirst_apply, groundSpaceMap_apply] using
                (congrArg (fun φ => φ (Fin.snoc σ j)) (hY i)).symm
    have hZj :
        groundSpaceMap A K (Z j * A i) σ = ψ (Fin.snoc (Fin.cons i σ) j) := by
      calc
        groundSpaceMap A K (Z j * A i) σ
            = Matrix.trace (evalWord A (List.ofFn σ) * (Z j * A i)) := by
                simp [groundSpaceMap_apply]
        _ = Matrix.trace (evalWord A (List.ofFn (Fin.cons i σ)) * Z j) := by
              simpa [evalWord_ofFn_cons, Matrix.mul_assoc] using
                Matrix.trace_mul_cycle' (evalWord A (List.ofFn σ)) (Z j) (A i)
        _ = ψ (Fin.snoc (Fin.cons i σ) j) := by
              simpa [restrictLast_apply, groundSpaceMap_apply] using
                (congrArg (fun φ => φ (Fin.cons i σ)) (hZ j)).symm
    have hψeq :
        ψ (Fin.cons i (Fin.snoc σ j)) = ψ (Fin.snoc (Fin.cons i σ) j) := by
      rw [Fin.cons_snoc_eq_snoc_cons]
    exact hYi.trans (hψeq.trans hZj.symm)
  let X : Matrix (Fin D) (Fin D) ℂ := ∑ j, decompositionMap hA 1 j • Z j
  have hY_eq : ∀ i, Y i = X * A i := by
    intro i
    calc
      Y i = (1 : Matrix (Fin D) (Fin D) ℂ) * Y i := by simp
      _ = (∑ j, decompositionMap hA 1 j • A j) * Y i := by
            rw [decompositionMap_sum hA 1]
      _ = ∑ j, (decompositionMap hA 1 j • A j) * Y i := by
            rw [Finset.sum_mul]
      _ = ∑ j, decompositionMap hA 1 j • (A j * Y i) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [smul_mul_assoc]
      _ = ∑ j, decompositionMap hA 1 j • (Z j * A i) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hCompat i j]
      _ = (∑ j, decompositionMap hA 1 j • Z j) * A i := by
            symm
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [smul_mul_assoc]
      _ = X * A i := rfl
  rw [groundSpace, LinearMap.mem_range]
  refine ⟨X, ?_⟩
  ext τ
  have hτ :
      ψ (Fin.cons (τ 0) (Fin.tail τ)) =
        Matrix.trace (evalWord A (List.ofFn (Fin.tail τ)) * Y (τ 0)) := by
    simpa [restrictFirst_apply, groundSpaceMap_apply] using
      congrArg (fun φ => φ (Fin.tail τ)) (hY (τ 0))
  calc
    groundSpaceMap A (K + 2) X τ
        = Matrix.trace (evalWord A (List.ofFn (Fin.cons (τ 0) (Fin.tail τ))) * X) := by
            rw [← Fin.cons_self_tail τ]
            simp [groundSpaceMap_apply]
    _ = Matrix.trace (A (τ 0) * evalWord A (List.ofFn (Fin.tail τ)) * X) := by
          rw [evalWord_ofFn_cons, Matrix.mul_assoc]
    _ = Matrix.trace (evalWord A (List.ofFn (Fin.tail τ)) * (X * A (τ 0))) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle' (evalWord A (List.ofFn (Fin.tail τ))) X (A (τ 0))).symm
    _ = Matrix.trace (evalWord A (List.ofFn (Fin.tail τ)) * Y (τ 0)) := by
          rw [hY_eq (τ 0)]
    _ = ψ (Fin.cons (τ 0) (Fin.tail τ)) := hτ.symm
    _ = ψ τ := by
          rw [Fin.cons_self_tail τ]

/-- The ground space on `L+1` sites is characterized by the intersection property:
`ψ ∈ G_{L+1}(A)` iff both the left and right `L`-site restrictions lie in `G_L(A)`. -/
theorem groundSpace_iff_left_right {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 1 < L) {ψ : NSiteSpace d (L + 1)} :
    ψ ∈ groundSpace A (L + 1) ↔ InLeftGround A L ψ ∧ InRightGround A L ψ :=
  ⟨fun h => ⟨groundSpace_inLeftGround A L h, groundSpace_inRightGround A L h⟩,
   fun ⟨hL', hR'⟩ => groundSpace_intersection hA hL hL' hR'⟩

end MPSTensor
