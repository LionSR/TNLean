/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.Algebra.TracePairing
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan

/-!
# Intersection property of MPS ground spaces

For an injective MPS tensor \(A\), we establish:

1. **Injectivity of the ground-space map**: `groundSpaceMap A L` is injective for
   \(L \geq 1\), yielding \(\dim G_L(A) = D^2\).

2. **Restriction to ground spaces**: An element of \(G_{L+1}(A)\) restricts to
   elements of \(G_L(A)\) on both the left \(L\)-site window (fixing the last
   index) and the right \(L\)-site window (fixing the first index).

3. **Intersection property** (the "inverting and growing back" step): conversely,
   a state on \(L+1\) sites whose left and right restrictions both lie in
   \(G_L(A)\) is itself in \(G_{L+1}(A)\).

The intersection property is the inductive step used in `UniqueGroundState.lean`
to characterize \(G_{L+1}(A)\) and prove uniqueness of the periodic-chain ground
state of the parent Hamiltonian.

## Main results

* `MPSTensor.groundSpace_inLeftGround` — forward direction, left window
* `MPSTensor.groundSpace_inRightGround` — forward direction, right window
* `MPSTensor.groundSpaceMap_injective` — injectivity for injective tensors
* `MPSTensor.groundSpace_finrank_eq` — dimension equals \(D^2\)
* `MPSTensor.groundSpace_intersection` — the intersection property

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2021] arXiv:2011.12127,
  Section IV.C (see in particular lines 1976--2000 for the parent Hamiltonian
  definition, lines 2013--2078 for the intersection property)
* [MPGSC18] arXiv:1804.04964, Section 3 (one-sided inverse)
* [FNW92] Sections 3–4

## External input: cumulative and exact word spans

This file imports `TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan`, which supplies
the connection from the cumulative Wielandt bound to a concrete word-span theorem:

> **Cumulative-to-word-span connection (Wielandt chain, Lemma 2(b) of arXiv:0909.5347).**
> The cumulative span \(S_n(A)\) is the linear span of all word products of length
> \(≤ n\).  `CumulativeToWordSpan` converts the statement "\(S_n(A)\) reaches the
> full matrix algebra" into exact-length fullness, namely that the
> word products of exactly length \(n\) (not just up to \(n\)) span \(M_D(ℂ)\).

In the intersection property proof: the injectivity of `groundSpaceMap A L`
(for \(L ≥ 1\)) requires the products \(A^\sigma\), with \(|\sigma| = L\), to
span the full matrix algebra.  The Wielandt machinery
supplies this conclusion from the injectivity hypothesis `IsInjective A`:
injectivity at length 1 implies word-span fullness at all positive lengths
via the cumulative span chain, and `CumulativeToWordSpan` upgrades the
cumulative conclusion to an exact-length word-span theorem.

Under the aperiodicity hypothesis
\[
  I\in\operatorname{span}\{A^i: i\in[d]\},
\]
which follows here from injectivity at length one, the equivalence
\[
  S_n(A)=M_D(\mathbb C)
  \quad\Longleftrightarrow\quad
  \operatorname{span}\{A^w: |w|=n\}=M_D(\mathbb C)
\]
for \(n\ge 1\) is the cumulative-to-exact-length equivalence used to prove
injectivity of the ground-space map.
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

/-! ### Auxiliary lemmas for `List.ofFn` with `Fin.snoc` and `Fin.cons` -/

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

/-- Restrict an \((L+1)\)-site state to the first \(L\) sites by fixing the last
physical index to \(j\) (using `Fin.snoc`). -/
def restrictLastₗ {d L : ℕ} (j : Fin d) : NSiteSpace d (L + 1) →ₗ[ℂ] NSiteSpace d L where
  toFun ψ := fun σ => ψ (Fin.snoc σ j)
  map_add' ψ₁ ψ₂ := by
    ext σ
    simp
  map_smul' c ψ := by
    ext σ
    simp

/-- Restrict an \((L+1)\)-site state to the first \(L\) sites by fixing the last
physical index to \(j\) (using `Fin.snoc`). -/
noncomputable def restrictLast {d L : ℕ} (ψ : NSiteSpace d (L + 1)) (j : Fin d) :
    NSiteSpace d L :=
  restrictLastₗ j ψ

/-- Restrict an \((L+1)\)-site state to the last \(L\) sites by fixing the first
physical index to \(i\) (using `Fin.cons`). -/
def restrictFirstₗ {d L : ℕ} (i : Fin d) : NSiteSpace d (L + 1) →ₗ[ℂ] NSiteSpace d L where
  toFun ψ := fun σ => ψ (Fin.cons i σ)
  map_add' ψ₁ ψ₂ := by
    ext σ
    simp
  map_smul' c ψ := by
    ext σ
    simp

/-- Restrict an \((L+1)\)-site state to the last \(L\) sites by fixing the first
physical index to \(i\) (using `Fin.cons`). -/
noncomputable def restrictFirst {d L : ℕ} (ψ : NSiteSpace d (L + 1)) (i : Fin d) :
    NSiteSpace d L :=
  restrictFirstₗ i ψ

@[simp] theorem restrictLast_apply {d L : ℕ} (ψ : NSiteSpace d (L + 1))
    (j : Fin d) (σ : Fin L → Fin d) :
    restrictLast ψ j σ = ψ (Fin.snoc σ j) := rfl

@[simp] theorem restrictFirst_apply {d L : ℕ} (ψ : NSiteSpace d (L + 1))
    (i : Fin d) (σ : Fin L → Fin d) :
    restrictFirst ψ i σ = ψ (Fin.cons i σ) := rfl

/-- A vector on \(L + 1\) sites is determined by all restrictions obtained by
fixing its first physical index. -/
theorem eq_of_forall_restrictFirst_eq {d L : ℕ} {ψ φ : NSiteSpace d (L + 1)}
    (h : ∀ i : Fin d, restrictFirst ψ i = restrictFirst φ i) :
    ψ = φ := by
  ext σ
  have hσ := congr_fun (h (σ 0)) (Fin.tail σ)
  simpa [restrictFirst_apply, Fin.cons_self_tail σ] using hσ

/-! ### Ground space membership via restrictions -/

/-- A state on \(L+1\) sites has its left restriction in \(G_L(A)\): for each value of the
last physical index, the resulting \(L\)-site state lies in the ground space. -/
def InLeftGround (A : MPSTensor d D) (L : ℕ) (ψ : NSiteSpace d (L + 1)) : Prop :=
  ∀ j : Fin d, restrictLast ψ j ∈ groundSpace A L

/-- A state on \(L+1\) sites has its right restriction in \(G_L(A)\): for each value of the
first physical index, the resulting \(L\)-site state lies in the ground space. -/
def InRightGround (A : MPSTensor d D) (L : ℕ) (ψ : NSiteSpace d (L + 1)) : Prop :=
  ∀ i : Fin d, restrictFirst ψ i ∈ groundSpace A L

/-! ### Forward direction: ground-space elements restrict to ground-space elements

If \(\psi \in G_{L+1}(A)\), i.e. \(\psi(\sigma)=\tr(A^\sigma X)\) for some
boundary matrix \(X\), then fixing the last index \(j\) gives
\(\psi(\sigma,j)=\tr(A^\sigma A^jX)\), which lies in \(G_L(A)\) with boundary
matrix \(A^jX\). Similarly, fixing the first index \(i\) gives
\(\psi(i,\sigma)=\tr(A^\sigma XA^i)\) by trace cyclicity. -/

/-- An element of \(G_{L+1}(A)\) restricts to \(G_L(A)\) on the first \(L\) sites
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

/-- An element of \(G_{L+1}(A)\) restricts to \(G_L(A)\) on the last \(L\) sites
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

/-- For an injective tensor, the ground-space map is injective for any \(L ≥ 1\).

**Proof sketch**: It suffices to show \(Γ_L(X)=0 → X=0\).
If \(\operatorname{tr}(A^σ X) = 0\) for all words \(σ\) of length \(L\), and the set
\(\{A^σ\}\) spans \(M_D(ℂ)\) (which holds for \(L ≥ 1\) by the injectivity hypothesis),
then nondegeneracy of the trace pairing gives \(X = 0\). -/
theorem groundSpaceMap_injective {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 0 < L) :
    Function.Injective (groundSpaceMap A L) := by
  have hker : (groundSpaceMap A L).ker = ⊥ := by
    apply (LinearMap.ker_eq_bot').2
    intro X hX
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
    have hφ :
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulRight ℂ X) = 0 := by
      apply LinearMap.ext_on_range
        (v := fun σ : Fin L → Fin d => evalWord A (List.ofFn σ))
      · simpa [wordSpan] using hwordL
      · intro σ
        simpa [groundSpaceMap_apply, Matrix.traceLinearMap_apply] using
          congrArg (fun ψ => ψ σ) hX
    exact (Matrix.trace_mul_right_eq_zero_iff (n := Fin D) X).1 fun N => by
      have hNX : Matrix.trace (N * X) = 0 := by
        simpa [Matrix.traceLinearMap_apply] using congrArg (fun f => f N) hφ
      calc
        Matrix.trace (X * N) = Matrix.trace (N * X) := Matrix.trace_mul_comm X N
        _ = 0 := hNX
  exact LinearMap.ker_eq_bot.mp hker

/-- For an injective tensor, the ground space has dimension exactly \(D^2\) for
\(L \geq 1\).

This follows from injectivity of `groundSpaceMap` (which has domain \(M_D(ℂ)\) of
dimension \(D^2\)) together with the dimension upper bound
\(\dim G_L(A) \leq D^2\). -/
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

/-- Nontrivial direction of the intersection property for injective MPS: a state
on \(L+1\) sites that restricts to ground-space elements on both the left and right
\(L\)-site windows is itself in \(G_{L+1}(A)\).

This is the "inverting and growing back" step. The proof proceeds as follows:

1. From `InRightGround`: for each \(i\), ∃ unique \(Y_i\) with
   \(ψ(i, σ) = \operatorname{tr}(A^σ · Y_i)\).
2. From `InLeftGround`: for each \(j\), ∃ unique \(Z_j\) with
   \(ψ(σ, j) = \operatorname{tr}(A^σ · Z_j)\).
3. Matching on the overlap and using trace-pairing nondegeneracy:
   \(A^j · Y_i = Z_j · A^i\) for all \(i, j\).
4. Apply the decomposition map (one-sided inverse from `OneSidedInverse.lean`):
   sum over \(i\) with decomposition coefficients of the identity to get
   \(Y_i = X' · A^i\) for a single matrix \(X' = ∑ⱼ (Ψ(I))ⱼ · Z_j\).
5. By trace cyclicity, \(ψ(σ) = \operatorname{tr}(A^σ · X')\), so \(ψ ∈ G_{L+1}(A)\).

The formal overlap argument uses the \((L - 1)\)-site intersection, so we state
the theorem with the exact hypothesis \(1 < L\). -/
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

/-- The ground space on \(L+1\) sites is characterized by the intersection property:
\(ψ ∈ G_{L+1}(A)\) iff both the left and right \(L\)-site restrictions lie in \(G_L(A)\). -/
theorem groundSpace_iff_left_right {A : MPSTensor d D} (hA : IsInjective A)
    {L : ℕ} (hL : 1 < L) {ψ : NSiteSpace d (L + 1)} :
    ψ ∈ groundSpace A (L + 1) ↔ InLeftGround A L ψ ∧ InRightGround A L ψ :=
  ⟨fun h => ⟨groundSpace_inLeftGround A L h, groundSpace_inRightGround A L h⟩,
   fun ⟨hL', hR'⟩ => groundSpace_intersection hA hL hL' hR'⟩

end MPSTensor
