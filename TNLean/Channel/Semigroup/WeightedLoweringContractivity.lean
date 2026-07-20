/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Semigroup.RelaxationConditions

/-!
# Algebraic obstruction for weighted lowering operators

This file formalizes the new finite-dimensional algebraic step in the solution of
`Notes/OpenProblemsQC/problems/q1_weighted_lowering_arbitrary_drive.tex`.  It does **not**
formalize relaxed-control compactness, trace-norm differentiation, or the full analytic
Hamiltonian-independent contractivity statement.

The abstract part proves that a nilpotent endomorphism whose kernel is one-dimensional forces
all nonzero invariant subspaces to contain the same kernel line.  Consequently, it admits no
two nonzero disjoint—and hence no two nonzero orthogonal—invariant subspaces.  The concrete
part defines the weighted lowering operator on `Fin (n + 1) → ℂ`, proves its nilpotency and
identifies its kernel with the span of the ground basis vector when every edge weight is
nonzero, and then instantiates the abstract obstruction.

## Main declarations

- `exists_ne_zero_mem_ker_of_map_le_of_pow_eq_zero`: a nilpotent restriction to a nonzero
  invariant subspace has a nonzero kernel vector.
- `ker_le_invariant_of_pow_eq_zero_of_ker_eq_span`: every nonzero invariant subspace contains
  the one-dimensional kernel.
- `WeightedLowering.operator`: the weighted shift sending basis vector `i.succ` to a nonzero
  multiple of basis vector `i`.
- `WeightedLowering.operator_pow_dimension_eq_zero`: the shift is nilpotent.
- `WeightedLowering.ker_operator`: its kernel is exactly the ground-state line.
- `WeightedLowering.not_disjoint_invariant`: two nonzero invariant subspaces cannot be disjoint.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- If a nilpotent endomorphism preserves a nonzero submodule, its kernel meets that submodule
nontrivially.  This statement does not require finite dimensionality. -/
theorem exists_ne_zero_mem_ker_of_map_le_of_pow_eq_zero
    (f : Module.End K V) (W : Submodule K V) (hW : W.map f ≤ W) (hW0 : W ≠ ⊥)
    {n : ℕ} (hn : f ^ n = 0) :
    ∃ y : V, y ≠ 0 ∧ y ∈ W ∧ y ∈ LinearMap.ker f := by
  classical
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hex : ∃ k : ℕ, (f ^ k) x = 0 := by
    refine ⟨n, ?_⟩
    rw [hn]
    rfl
  let k := Nat.find hex
  have hk : (f ^ k) x = 0 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hkzero
    apply hx0
    have hk' := hk
    rw [hkzero] at hk'
    simpa using hk'
  let y := (f ^ (k - 1)) x
  have hW' : W ≤ W.comap f := Submodule.map_le_iff_le_comap.mp hW
  refine ⟨y, ?_, W.le_comap_pow_of_le_comap hW' (k - 1) hxW, ?_⟩
  · intro hy
    have hlt : k - 1 < k := Nat.sub_lt (Nat.zero_lt_of_ne_zero hk0) (by decide)
    exact (Nat.find_min hex hlt) hy
  · rw [LinearMap.mem_ker]
    have hksucc : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk0)
    rw [show f y = (f ^ (k - 1 + 1)) x by
      simp [y, pow_succ', Module.End.mul_apply]]
    simpa [hksucc] using hk

/-- If a nilpotent endomorphism has kernel `span K {v}`, every nonzero invariant submodule
contains `v`. -/
theorem mem_invariant_of_pow_eq_zero_of_ker_eq_span
    (f : Module.End K V) (v : V) (W : Submodule K V)
    (hW : W.map f ≤ W) (hW0 : W ≠ ⊥) {n : ℕ} (hn : f ^ n = 0)
    (hker : LinearMap.ker f = K ∙ v) : v ∈ W := by
  obtain ⟨y, hy0, hyW, hyker⟩ :=
    exists_ne_zero_mem_ker_of_map_le_of_pow_eq_zero f W hW hW0 hn
  rw [hker, Submodule.mem_span_singleton] at hyker
  obtain ⟨c, rfl⟩ := hyker
  have hc : c ≠ 0 := by
    intro hc
    subst c
    simp at hy0
  convert W.smul_mem (c⁻¹) hyW using 1
  simp [hc]

/-- Under the same hypotheses, the whole kernel line lies in every nonzero invariant
submodule. -/
theorem ker_le_invariant_of_pow_eq_zero_of_ker_eq_span
    (f : Module.End K V) (v : V) (W : Submodule K V)
    (hW : W.map f ≤ W) (hW0 : W ≠ ⊥) {n : ℕ} (hn : f ^ n = 0)
    (hker : LinearMap.ker f = K ∙ v) : LinearMap.ker f ≤ W := by
  rw [hker]
  apply Submodule.span_le.2
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact mem_invariant_of_pow_eq_zero_of_ker_eq_span f v W hW hW0 hn hker

/-- A nilpotent endomorphism with one-dimensional kernel has no two nonzero disjoint invariant
submodules.  Orthogonal subspaces are disjoint, so this is the exact algebraic obstruction used
in the weighted-lowering argument. -/
theorem not_disjoint_invariant_of_pow_eq_zero_of_ker_eq_span
    (f : Module.End K V) (v : V) (hv : v ≠ 0) {W₁ W₂ : Submodule K V}
    (hW₁ : W₁.map f ≤ W₁) (hW₂ : W₂.map f ≤ W₂) (hW₁0 : W₁ ≠ ⊥)
    (hW₂0 : W₂ ≠ ⊥) {n : ℕ} (hn : f ^ n = 0)
    (hker : LinearMap.ker f = K ∙ v) : ¬Disjoint W₁ W₂ := by
  intro hdisj
  have hv₁ : v ∈ W₁ :=
    mem_invariant_of_pow_eq_zero_of_ker_eq_span f v W₁ hW₁ hW₁0 hn hker
  have hv₂ : v ∈ W₂ :=
    mem_invariant_of_pow_eq_zero_of_ker_eq_span f v W₂ hW₂ hW₂0 hn hker
  have : v ∈ (⊥ : Submodule K V) := by
    rw [← hdisj.eq_bot]
    exact ⟨hv₁, hv₂⟩
  exact hv this

namespace WeightedLowering

/-- The ground basis vector in `Fin (n + 1) → ℂ`. -/
def ground (n : ℕ) : Fin (n + 1) → ℂ := Pi.single 0 1

/-- The weighted lowering endomorphism with edge weights `w i`: its coordinate formula is
`(operator w x) i.castSucc = w i * x i.succ`, while its last coordinate is zero.  Thus it sends
the basis vector indexed by `i.succ` to `w i` times the basis vector indexed by `i.castSucc`.
For Q1 one may take `w i = sqrt (γ_{i+1})`; positivity of the rates is used only through
`w i ≠ 0`. -/
def operator {n : ℕ} (w : Fin n → ℂ) : Module.End ℂ (Fin (n + 1) → ℂ) where
  toFun x := Fin.snoc (fun i => w i * x i.succ) 0
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [mul_add]
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [mul_left_comm]

@[simp]
theorem operator_apply_castSucc {n : ℕ} (w : Fin n → ℂ) (x : Fin (n + 1) → ℂ)
    (i : Fin n) : operator w x i.castSucc = w i * x i.succ := by
  simp [operator]

@[simp]
theorem operator_apply_last {n : ℕ} (w : Fin n → ℂ) (x : Fin (n + 1) → ℂ) :
    operator w x (Fin.last n) = 0 := by
  simp [operator]

private theorem pow_apply_eq_zero_of_dimension_le {n k : ℕ} (w : Fin n → ℂ)
    (x : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (h : n + 1 ≤ i.val + k) :
    ((operator w) ^ k) x i = 0 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      revert h
      refine Fin.lastCases ?_ (fun j h => ?_) i
      · intro _
        exact operator_apply_last w ((operator w ^ k) x)
      · rw [operator_apply_castSucc]
        have h' : n + 1 ≤ (j.succ : Fin (n + 1)).val + k := by
          simp only [Fin.val_castSucc, Fin.val_succ] at h ⊢
          omega
        rw [ih j.succ h', mul_zero]

/-- In dimension `n + 1`, every weighted lowering operator has `(n + 1)`st power zero. -/
theorem operator_pow_dimension_eq_zero {n : ℕ} (w : Fin n → ℂ) :
    operator w ^ (n + 1) = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  apply pow_apply_eq_zero_of_dimension_le
  omega

/-- A vector is killed by the weighted lowering operator with nonzero edge weights exactly when
it is a scalar multiple of the ground basis vector. -/
theorem operator_apply_eq_zero_iff {n : ℕ} (w : Fin n → ℂ)
    (hw : ∀ i : Fin n, w i ≠ 0) (x : Fin (n + 1) → ℂ) :
    operator w x = 0 ↔ ∃ c : ℂ, x = c • ground n := by
  constructor
  · intro hx
    refine ⟨x 0, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ground]
    · have hij := congrFun hx j.castSucc
      rw [operator_apply_castSucc] at hij
      have hxj : x j.succ = 0 := (mul_eq_zero.mp hij).resolve_left (hw j)
      simp [ground, hxj]
  · rintro ⟨c, rfl⟩
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [ground]

/-- With nonzero edge weights, the kernel of the weighted lowering operator is exactly the
one-dimensional ground-state line. -/
theorem ker_operator {n : ℕ} (w : Fin n → ℂ) (hw : ∀ i : Fin n, w i ≠ 0) :
    LinearMap.ker (operator w) = ℂ ∙ ground n := by
  ext x
  rw [LinearMap.mem_ker, operator_apply_eq_zero_iff w hw x,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

/-- The ground basis vector is nonzero. -/
theorem ground_ne_zero (n : ℕ) : ground n ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [ground] at this

/-- Every nonzero subspace invariant under a weighted lowering operator with nonzero edge
weights contains the ground basis vector. -/
theorem ground_mem_invariant {n : ℕ} (w : Fin n → ℂ) (hw : ∀ i : Fin n, w i ≠ 0)
    (W : Submodule ℂ (Fin (n + 1) → ℂ)) (hW : W.map (operator w) ≤ W)
    (hW0 : W ≠ ⊥) : ground n ∈ W :=
  mem_invariant_of_pow_eq_zero_of_ker_eq_span (operator w) (ground n) W hW hW0
    (operator_pow_dimension_eq_zero w) (ker_operator w hw)

/-- Two nonzero invariant subspaces of a weighted lowering operator with nonzero edge weights
cannot be disjoint.  In particular, there are no two nonzero orthogonal invariant subspaces. -/
theorem not_disjoint_invariant {n : ℕ} (w : Fin n → ℂ) (hw : ∀ i : Fin n, w i ≠ 0)
    {W₁ W₂ : Submodule ℂ (Fin (n + 1) → ℂ)} (hW₁ : W₁.map (operator w) ≤ W₁)
    (hW₂ : W₂.map (operator w) ≤ W₂) (hW₁0 : W₁ ≠ ⊥) (hW₂0 : W₂ ≠ ⊥) :
    ¬Disjoint W₁ W₂ :=
  not_disjoint_invariant_of_pow_eq_zero_of_ker_eq_span (operator w) (ground n)
    (ground_ne_zero n) hW₁ hW₂ hW₁0 hW₂0 (operator_pow_dimension_eq_zero w)
    (ker_operator w hw)

/-- Two subspaces of the coordinate space are orthogonal for the standard Hermitian inner
product when every vector in the first is orthogonal to every vector in the second.  This
coordinate definition avoids imposing an unrelated norm topology on the algebraic function
space used above. -/
def AreOrthogonal {n : ℕ} (W₁ W₂ : Submodule ℂ (Fin (n + 1) → ℂ)) : Prop :=
  ∀ x ∈ W₁, ∀ y ∈ W₂, ∑ i, star (x i) * y i = 0

/-- A weighted lowering operator with nonzero edge weights has no two nonzero orthogonal
invariant subspaces.  This is the concrete Q1 obstruction needed after the analytic
constant-trace-norm argument produces positive and negative invariant support spaces. -/
theorem not_orthogonal_invariant {n : ℕ} (w : Fin n → ℂ)
    (hw : ∀ i : Fin n, w i ≠ 0) {W₁ W₂ : Submodule ℂ (Fin (n + 1) → ℂ)}
    (hW₁ : W₁.map (operator w) ≤ W₁) (hW₂ : W₂.map (operator w) ≤ W₂)
    (hW₁0 : W₁ ≠ ⊥) (hW₂0 : W₂ ≠ ⊥) : ¬AreOrthogonal W₁ W₂ := by
  intro hOrtho
  have hv₁ : ground n ∈ W₁ := ground_mem_invariant w hw W₁ hW₁ hW₁0
  have hv₂ : ground n ∈ W₂ := ground_mem_invariant w hw W₂ hW₂ hW₂0
  have hzero := hOrtho (ground n) hv₁ (ground n) hv₂
  simp [ground, Fin.sum_univ_succ] at hzero

end WeightedLowering

end
