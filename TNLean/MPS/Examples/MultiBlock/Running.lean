/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.FlagVectors
import TNLean.MPS.Examples.MultiBlock.Periodic

/-!
# The running example

The tensor `B = diag(1, 2)` with one letter (*The asymmetric fundamental theorem of matrix product
states*, Examples 1.2, 3.4, 4.4 and 6.14) has the two one-dimensional blocks `C₁ = (1)` and
`C₂ = (2)`. Its invariant subspaces are `0`, `ℂ e₁`, `ℂ e₂`, `ℂ²`, so every reduction onto
`(C₁, C₂)` without zero block has the flag `0 ⊂ ℂ e₁ ⊂ ℂ²` and the order `(1, 2)`, or the flag
`0 ⊂ ℂ e₂ ⊂ ℂ²` and the order `(2, 1)`. The reductions with the first flag are the upper triangular
gauges `h = [[α, β], [0, δ]]`, those with the second flag the gauges `g̃ = [[β̃, α̃], [δ̃, 0]]`.
Against `g = 1` the gauge `g̃` matches block `1` with block `1` at the other position, with scalars
`λ₁ = δ̃`, `λ₂ = α̃`, and `g̃ = 𝔄̃ P_X 𝔄⁻¹` with `𝔄 = 1`.

This file sets up the example and determines all its reductions; the matching, the intertwiners,
the factorization and the density theorem for one letter are in
`TNLean.MPS.Examples.MultiBlock.RunningFactorization`.

## Main results

* `MultiBlockExamples.Running.exists_multiBlockCompression_gauge_one`,
  `exists_multiBlockCompression_gauge_unipotent`, `unipotent_conj_tensorB`, `left_mul_pow_ne_smul`,
  `remainder_pow_ne_zero`, `isInvariantSubmodule_tensorB_iff`, `ord_flagVec_cases_of_z_eq_zero`,
  `exists_multiBlockCompression_each_order`: Examples 1.2 and 3.4.
* `MultiBlockExamples.Running.exists_multiBlockCompression_upper`, `exists_left_eq_upper_of_ord_lt`,
  `exists_multiBlockCompression_swap`, `exists_left_eq_swap_of_ord_gt`: the reductions of
  Example 6.14.

## References

*The asymmetric fundamental theorem of matrix product states*, Examples 1.2, 3.4 and 6.14; blueprint
`thm:asym_uniq_all`, *The set of all compressions*.
-/

open scoped Matrix

namespace MultiBlockExamples

open MPSTensor

namespace Running

/-- **The running example** `B = diag(1, 2)`, one letter (*The asymmetric fundamental theorem of
matrix product states*, Example 1.2). -/
noncomputable def tensorB : MPSTensor 1 2 := fun _ => !![1, 0; 0, 2]

/-- Labels of the two blocks. -/
abbrev labels : Finset (Fin 2) := Finset.univ

/-- Both blocks are one-dimensional. -/
abbrev dims : Fin 2 → ℕ := fun _ => 1

/-- The blocks `C₁ = (1)`, `C₂ = (2)` (labels `0`, `1`). -/
noncomputable def blocks : ∀ s : Fin 2, MPSTensor 1 (dims s) := fun s _ => !![(s.val + 1 : ℂ)]

/-- The slot of `C₁`. -/
abbrev slot0 : {s // s ∈ labels} := ⟨0, Finset.mem_univ _⟩

/-- The slot of `C₂`. -/
abbrev slot1 : {s // s ∈ labels} := ⟨1, Finset.mem_univ _⟩

/-- The order `(1, 2)`. -/
def ord12 : BlockIndex labels 0 ≃ Fin 2 where
  toFun
    | Sum.inl s => s.1
    | Sum.inr t => t.elim0
  invFun n := Sum.inl ⟨n, Finset.mem_univ n⟩
  left_inv := by decide
  right_inv := by decide

/-- The order `(2, 1)`. -/
def ord21 : BlockIndex labels 0 ≃ Fin 2 where
  toFun
    | Sum.inl s => 1 - s.1
    | Sum.inr t => t.elim0
  invFun n := Sum.inl ⟨1 - n, Finset.mem_univ _⟩
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates in the order `(1, 2)`. -/
def tau12 : BlockSpace dims labels 0 ≃ Fin 2 where
  toFun x := ord12 x.1
  invFun n := ⟨Sum.inl ⟨n, Finset.mem_univ n⟩, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates in the order `(2, 1)`. -/
def tau21 : BlockSpace dims labels 0 ≃ Fin 2 where
  toFun x := ord21 x.1
  invFun n := ⟨Sum.inl ⟨1 - n, Finset.mem_univ _⟩, 0⟩
  left_inv := by decide
  right_inv := by decide

theorem tensorB_apply (i : Fin 1) : tensorB i = !![1, 0; 0, 2] := rfl

/-- A reduction of the running example from an explicit complex gauge `G` (blueprint
`thm:asym_multiblock`, *Multi-block asymmetric compression theorem*, clauses (i)–(iii)): `G B G⁻¹`
is upper triangular with the block of the slot at position `p` on the diagonal entry `p`. -/
noncomputable def red (ord : BlockIndex labels 0 ≃ Fin 2) (τ : BlockSpace dims labels 0 ≃ Fin 2)
    (hτ : ∀ x, τ x = ord x.1) (G Ginv : Matrix (Fin 2) (Fin 2) ℂ) (hG : G * Ginv = 1)
    (hG' : Ginv * G = 1) (h10 : (G * tensorB 0 * Ginv) 1 0 = 0)
    (hdiag : ∀ s : {s // s ∈ labels},
      (G * tensorB 0 * Ginv) (ord (Sum.inl s)) (ord (Sum.inl s)) = s.1.val + 1) :
    MultiBlockCompression tensorB labels blocks where
  z := 0
  ord := ord
  gauge := gaugeOfMatrix τ G Ginv hG hG'
  triangular i x y hxy := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hτ, hτ]
    have key : ∀ a b : Fin 2, b < a → (G * tensorB 0 * Ginv) a b = 0 := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | exact h10
    exact key _ _ hxy
  matched i s := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    ext p q
    obtain rfl : p = 0 := Subsingleton.elim p 0
    obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hτ]
    simpa [blocks] using hdiag s
  unmatched _ t := t.elim0

section RedMaps

variable (ord : BlockIndex labels 0 ≃ Fin 2) (τ : BlockSpace dims labels 0 ≃ Fin 2)
  (hτ : ∀ x, τ x = ord x.1) (G Ginv : Matrix (Fin 2) (Fin 2) ℂ) (hG : G * Ginv = 1)
  (hG' : Ginv * G = 1) (h10 : (G * tensorB 0 * Ginv) 1 0 = 0)
  (hdiag : ∀ s : {s // s ∈ labels},
    (G * tensorB 0 * Ginv) (ord (Sum.inl s)) (ord (Sum.inl s)) = s.1.val + 1)

theorem red_z : (red ord τ hτ G Ginv hG hG' h10 hdiag).z = 0 := rfl

theorem red_left (s : {s // s ∈ labels}) :
    (red ord τ hτ G Ginv hG hG' h10 hdiag).left s =
      Matrix.of fun (_ : Fin 1) j => G (ord (Sum.inl s)) j := by
  rw [MultiBlockCompression.left_gaugeOfMatrix _ (τ := τ) (hG := hG) (hG' := hG') rfl s]
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
  exact congrArg (fun r => G r j) (hτ ⟨Sum.inl s, 0⟩)

theorem red_right (s : {s // s ∈ labels}) :
    (red ord τ hτ G Ginv hG hG' h10 hdiag).right s =
      Matrix.of fun i (_ : Fin 1) => Ginv i (ord (Sum.inl s)) := by
  rw [MultiBlockCompression.right_gaugeOfMatrix _ (τ := τ) (hG := hG) (hG' := hG') rfl s]
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
  exact congrArg (fun c => Ginv i c) (hτ ⟨Sum.inl s, 0⟩)

end RedMaps

theorem tau12_eq_ord12 : ∀ x, tau12 x = ord12 x.1 := fun _ => rfl

theorem tau21_eq_ord21 : ∀ x, tau21 x = ord21 x.1 := fun _ => rfl

/-- The gauge `h = [[α, β], [0, δ]]` and its inverse. -/
theorem upper_mul_inv {α β δ : ℂ} (h : α * δ ≠ 0) :
    !![α, β; 0, δ] * !![α⁻¹, -β / (α * δ); 0, δ⁻¹] = 1 ∧
      !![α⁻¹, -β / (α * δ); 0, δ⁻¹] * !![α, β; 0, δ] = 1 := by
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, mul_zero, zero_mul, add_zero, zero_add] <;>
    (try field_simp) <;> ring_nf

/-- The gauge `g̃ = [[β̃, α̃], [δ̃, 0]]` and its inverse. -/
theorem swap_mul_inv {α β δ : ℂ} (h : α * δ ≠ 0) :
    !![β, α; δ, 0] * !![0, δ⁻¹; α⁻¹, -β / (α * δ)] = 1 ∧
      !![0, δ⁻¹; α⁻¹, -β / (α * δ)] * !![β, α; δ, 0] = 1 := by
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, mul_zero, zero_mul, add_zero, zero_add] <;>
    (try field_simp) <;> ring_nf

/-- The conjugated letter of the upper triangular gauge. -/
theorem upper_conj {α β δ : ℂ} (h : α * δ ≠ 0) :
    !![α, β; 0, δ] * tensorB 0 * !![α⁻¹, -β / (α * δ); 0, δ⁻¹] = !![1, β / δ; 0, 2] := by
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  rw [tensorB_apply, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring

/-- The conjugated letter of the swapped gauge. -/
theorem swap_conj {α β δ : ℂ} (h : α * δ ≠ 0) :
    !![β, α; δ, 0] * tensorB 0 * !![0, δ⁻¹; α⁻¹, -β / (α * δ)] = !![2, -β / δ; 0, 1] := by
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  rw [tensorB_apply, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring

/-- The reduction `h = [[α, β], [0, δ]]` in the order `(1, 2)` (*The asymmetric fundamental theorem
of matrix product states*, Example 6.14, (6.14)). -/
noncomputable def redUpper (α β δ : ℂ) (h : α * δ ≠ 0) :
    MultiBlockCompression tensorB labels blocks :=
  red ord12 tau12 tau12_eq_ord12 !![α, β; 0, δ] !![α⁻¹, -β / (α * δ); 0, δ⁻¹] (upper_mul_inv h).1
    (upper_mul_inv h).2 (by rw [upper_conj h]; simp)
    (fun s => by
      rw [upper_conj h]
      obtain ⟨s, hs⟩ := s
      fin_cases s <;> simp [ord12]
      norm_num)

/-- The reduction `g̃ = [[β̃, α̃], [δ̃, 0]]` in the order `(2, 1)` (*The asymmetric fundamental
theorem of matrix product states*, Example 6.14, (6.15)). -/
noncomputable def redSwap (α β δ : ℂ) (h : α * δ ≠ 0) :
    MultiBlockCompression tensorB labels blocks :=
  red ord21 tau21 tau21_eq_ord21 !![β, α; δ, 0] !![0, δ⁻¹; α⁻¹, -β / (α * δ)] (swap_mul_inv h).1
    (swap_mul_inv h).2 (by rw [swap_conj h]; simp)
    (fun s => by
      rw [swap_conj h]
      obtain ⟨s, hs⟩ := s
      fin_cases s <;> simp [ord21]
      norm_num)

/-! ### Two reductions with the same flag -/

/-- **The reduction `g = 1`** (*The asymmetric fundamental theorem of matrix product states*,
Examples 1.2 and 3.4): `g = 1` is a reduction in the order `(1, 2)`, with `W₁ = (1, 0)`,
`W₂ = (0, 1)`. -/
theorem exists_multiBlockCompression_gauge_one :
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
    P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1) ∧
    P.left slot0 = !![1, 0] ∧ P.left slot1 = !![0, 1] := by
  refine ⟨redUpper 1 0 1 (by norm_num), rfl, ?_, ?_, ?_⟩
  · change ord12 (Sum.inl slot0) < ord12 (Sum.inl slot1)
    decide
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]

/-- **The reduction `h`** (*The asymmetric fundamental theorem of matrix product states*, Examples
1.2 and 3.4): `g̃ = h = [[1, 1], [0, 1]]` is a reduction in the order `(1, 2)` with `W̃₁ = (1, 1)`,
`W̃₂ = (0, 1)`, `Ṽ₁ = e₁`, `Ṽ₂ = (-1, 1)ᵀ`. -/
theorem exists_multiBlockCompression_gauge_unipotent :
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
    P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1) ∧
    P.left slot0 = !![1, 1] ∧ P.left slot1 = !![0, 1] ∧
    P.right slot0 = !![1; 0] ∧ P.right slot1 = !![-1; 1] := by
  refine ⟨redUpper 1 1 1 (by norm_num), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change ord12 (Sum.inl slot0) < ord12 (Sum.inl slot1)
    decide
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]

/-- **The conjugated letter** (*The asymmetric fundamental theorem of matrix product states*,
Example 3.4): `h B h⁻¹ = [[1, 1], [0, 2]]`. -/
theorem unipotent_conj_tensorB :
    !![(1 : ℂ), 1; 0, 1] * tensorB 0 * !![1, -1; 0, 1] = !![1, 1; 0, 2] := by
  rw [tensorB_apply, Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

theorem tensorB_pow (n : ℕ) : tensorB 0 ^ n = !![1, 0; 0, (2 : ℂ) ^ n] := by
  induction n with
  | zero => rw [pow_zero, Matrix.one_fin_two]; simp
  | succ n ih =>
    rw [pow_succ, ih, tensorB_apply, Matrix.mul_fin_two]
    simp [pow_succ]

/-- **The reading maps after words** (*The asymmetric fundamental theorem of matrix product states*,
Example 3.4): `W₁ Bⁿ = (1, 0)` and `W̃₁ Bⁿ = (1, 2ⁿ)` for every `n ≥ 0`, and these are never
proportional. -/
theorem left_mul_pow_ne_smul (n : ℕ) :
    !![(1 : ℂ), 0] * tensorB 0 ^ n = !![1, 0] ∧ !![(1 : ℂ), 1] * tensorB 0 ^ n = !![1, 2 ^ n] ∧
    ¬ ∃ c : ℂ, !![(1 : ℂ), 1] * tensorB 0 ^ n = c • (!![(1 : ℂ), 0] * tensorB 0 ^ n) := by
  have h1 : !![(1 : ℂ), 0] * tensorB 0 ^ n = !![1, 0] := by
    rw [tensorB_pow]; ext i j; fin_cases i; fin_cases j <;> simp [Matrix.mul_apply]
  have h2 : !![(1 : ℂ), 1] * tensorB 0 ^ n = !![1, 2 ^ n] := by
    rw [tensorB_pow]; ext i j; fin_cases i; fin_cases j <;> simp [Matrix.mul_apply]
  refine ⟨h1, h2, ?_⟩
  rintro ⟨c, hc⟩
  rw [h1, h2] at hc
  have := congrFun (congrFun hc 0) 1
  simp at this

/-- **The remainder is not nilpotent** (*The asymmetric fundamental theorem of matrix product
states*, Example 1.2): the remainder `B - V₁ C₁ W₁ = diag(0, 2)` has no vanishing power. -/
theorem remainder_pow_ne_zero :
    tensorB 0 - !![(1 : ℂ); 0] * blocks 0 0 * !![(1 : ℂ), 0] = !![0, 0; 0, 2] ∧
    ∀ n : ℕ, (!![(0 : ℂ), 0; 0, 2]) ^ n ≠ 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [tensorB_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [blocks]
  · have hpow : ∀ m : ℕ, ((!![(0 : ℂ), 0; 0, 2]) ^ m) 1 1 = 2 ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, ih]
        simp [pow_succ]
    have := hpow n
    rw [hn] at this
    exact absurd this.symm (pow_ne_zero _ two_ne_zero)

/-- The line `ℂ e₁` is invariant. -/
theorem isInvariant_span_e0 : Matrix.IsInvariantSubmodule tensorB (Submodule.span ℂ {e 0}) :=
  (isInvariantSubmodule_span_singleton_iff _ _).2 fun i =>
    ⟨1, by ext j; fin_cases j <;> simp [tensorB, Matrix.mulVec, dotProduct]⟩

/-- The line `ℂ e₂` is invariant. -/
theorem isInvariant_span_e1 : Matrix.IsInvariantSubmodule tensorB (Submodule.span ℂ {e 1}) :=
  (isInvariantSubmodule_span_singleton_iff _ _).2 fun i =>
    ⟨2, by ext j; fin_cases j <;> simp [tensorB, Matrix.mulVec, dotProduct]⟩

/-- **The invariant subspaces** (*The asymmetric fundamental theorem of matrix product states*,
Example 3.4): the subspaces invariant under `B` are `0`, `ℂ e₁`, `ℂ e₂`, `ℂ²`. -/
theorem isInvariantSubmodule_tensorB_iff (W : Submodule ℂ (Fin 2 → ℂ)) :
    Matrix.IsInvariantSubmodule tensorB W ↔
      W = ⊥ ∨ W = Submodule.span ℂ {e 0} ∨ W = Submodule.span ℂ {e 1} ∨ W = ⊤ := by
  constructor
  · intro hW
    have hle : Module.finrank ℂ W ≤ 2 := by
      simpa using Submodule.finrank_le W
    interval_cases h : Module.finrank ℂ W
    · exact Or.inl (Submodule.finrank_eq_zero.1 h)
    · obtain ⟨v, hv, rfl⟩ := exists_eq_span_singleton_of_finrank_eq_one W h
      obtain ⟨c, hc⟩ := (isInvariantSubmodule_span_singleton_iff _ _).1 hW 0
      have a0 : v 0 = c * v 0 := by
        simpa [tensorB, Matrix.mulVec, dotProduct] using congrFun hc 0
      have a1 : 2 * v 1 = c * v 1 := by
        simpa [tensorB, Matrix.mulVec, dotProduct] using congrFun hc 1
      by_cases hv0 : v 0 = 0
      · have hv1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [hv0, h1])
        refine Or.inr (Or.inr (Or.inl (span_singleton_eq_of_eq_smul hv1 ?_)))
        ext i; fin_cases i <;> simp [hv0]
      · have hc : c = 1 := by
          have h' : (c - 1) * v 0 = 0 := by linear_combination -a0
          exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hv0)
        have hv1 : v 1 = 0 := by
          rw [hc] at a1
          linear_combination a1
        refine Or.inr (Or.inl (span_singleton_eq_of_eq_smul hv0 ?_))
        ext i; fin_cases i <;> simp [hv1]
    · refine Or.inr (Or.inr (Or.inr (Submodule.eq_top_of_finrank_eq ?_)))
      simpa using h
  · rintro (rfl | rfl | rfl | rfl)
    · intro i v hv
      rw [Submodule.mem_bot] at hv ⊢
      simp [hv]
    · exact isInvariant_span_e0
    · exact isInvariant_span_e1
    · intro i v _
      exact Submodule.mem_top

/-- The member `M₁` of the flag of a reduction whose positions `0`, `1` carry the slots `s`, `s'`
is the eigenline `ℂ e_s` of the block `C_s`. -/
theorem flagVec_eq_of_ord (P : MultiBlockCompression tensorB labels blocks)
    (s s' : {s // s ∈ labels}) (hs : (P.ord (Sum.inl s)).val = 0)
    (hs' : (P.ord (Sum.inl s')).val = 1) (k : Fin (labels.card + P.z + 1)) (hk : k.val = 1) :
    flagVec P k = Submodule.span ℂ {e s.1} := by
  have hks : (P.ord (Sum.inl s)).succ = k := Fin.ext (by rw [Fin.val_succ, hs, hk])
  have hks' : (P.ord (Sum.inl s')).castSucc = k := Fin.ext (by rw [Fin.val_castSucc, hs', hk])
  set u := P.rightCol (Sum.inl s) *ᵥ (fun _ => (1 : ℂ)) with hu_def
  have hu : u ∈ flagVec P k := hks ▸ rightCol_mulVec_mem_flagVec P (Sum.inl s) _
  have hWu : P.leftRow (Sum.inl s) *ᵥ u = fun _ => 1 := by
    rw [hu_def, Matrix.mulVec_mulVec, P.leftRow_mul_rightCol_self, Matrix.one_mulVec]
  have hu0 : u ≠ 0 := fun h0 => by
    have := congrFun hWu 0
    rw [h0, Matrix.mulVec_zero] at this
    simp at this
  have hu' : P.rightCol (Sum.inl s') *ᵥ (fun _ => (1 : ℂ)) ∉ flagVec P k := fun hin => by
    have h0 := leftRow_mulVec_eq_zero_of_mem_flagVec P (b := Sum.inl s') (hks'.symm ▸ hin)
    rw [Matrix.mulVec_mulVec, P.leftRow_mul_rightCol_self, Matrix.one_mulVec] at h0
    simpa using congrFun h0 0
  have hinv : Matrix.IsInvariantSubmodule tensorB (flagVec P k) :=
    fun i v hv => mulVec_mem_flagVec P k i hv
  have heig : ∀ j : Fin 2, flagVec P k = Submodule.span ℂ {e j} → j = s.1 := by
    intro j hj
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hj ▸ hu)
    have hBu : tensorB 0 *ᵥ u = ((j.val : ℂ) + 1) • u := by
      rw [← ha]
      ext i; fin_cases i <;> fin_cases j <;>
        simp only [tensorB, Matrix.mulVec, dotProduct, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
          Matrix.cons_val_one, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero, zero_mul, one_mul, zero_add, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          CharP.cast_eq_zero, Nat.cast_one, zero_ne_one, one_ne_zero, mul_eq_mul_right_iff]
      first | ring1 | (left; norm_num)
    have hW := leftRow_mulVec_mulVec_of_mem_flagVec P (b := Sum.inl s) 0 (hks.symm ▸ hu)
    rw [hBu, Matrix.mulVec_smul, hWu] at hW
    have h0 : (j.val : ℂ) + 1 = (s.1.val : ℂ) + 1 := by
      have := congrFun hW 0
      simpa [blockOf, blocks, Matrix.mulVec, dotProduct] using this
    have : (j.val : ℂ) = s.1.val := by linear_combination h0
    exact Fin.ext (by exact_mod_cast this)
  rcases (isInvariantSubmodule_tensorB_iff _).1 hinv with h | h | h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hu)) hu0
  · rw [h, heig 0 h]
  · rw [h, heig 1 h]
  · exact absurd (h ▸ Submodule.mem_top) hu'

/-- **The two flags** (*The asymmetric fundamental theorem of matrix product states*, Example 3.4):
a reduction without zero block has the flag `0 ⊂ ℂ e₁ ⊂ ℂ²` and the order `(1, 2)`, or the flag
`0 ⊂ ℂ e₂ ⊂ ℂ²` and the order `(2, 1)`. -/
theorem ord_flagVec_cases_of_z_eq_zero (P : MultiBlockCompression tensorB labels blocks)
    (hz : P.z = 0) :
    (P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1) ∧
      ∀ k : Fin (labels.card + P.z + 1), k.val = 1 → flagVec P k = Submodule.span ℂ {e 0}) ∨
    (P.ord (Sum.inl slot1) < P.ord (Sum.inl slot0) ∧
      ∀ k : Fin (labels.card + P.z + 1), k.val = 1 → flagVec P k = Submodule.span ℂ {e 1}) := by
  have hn : labels.card + P.z = 2 := by rw [hz]; rfl
  have h0 : (P.ord (Sum.inl slot0)).val < 2 := lt_of_lt_of_eq (P.ord _).isLt hn
  have h1 : (P.ord (Sum.inl slot1)).val < 2 := lt_of_lt_of_eq (P.ord _).isLt hn
  have hne : (P.ord (Sum.inl slot0)).val ≠ (P.ord (Sum.inl slot1)).val := fun h =>
    absurd (P.ord.injective (Fin.ext h)) (by simp)
  rcases (show (P.ord (Sum.inl slot0)).val = 0 ∧ (P.ord (Sum.inl slot1)).val = 1 ∨
      (P.ord (Sum.inl slot0)).val = 1 ∧ (P.ord (Sum.inl slot1)).val = 0 by omega) with
    ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨Fin.lt_def.2 (by omega), fun k hk => flagVec_eq_of_ord P slot0 slot1 ha hb k hk⟩
  · exact Or.inr ⟨Fin.lt_def.2 (by omega), fun k hk => flagVec_eq_of_ord P slot1 slot0 hb ha k hk⟩

/-- **Both orders occur** (*The asymmetric fundamental theorem of matrix product states*, Example
3.4): both cases occur. -/
theorem exists_multiBlockCompression_each_order :
    (∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
      P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1)) ∧
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
      P.ord (Sum.inl slot1) < P.ord (Sum.inl slot0) := by
  refine ⟨⟨redUpper 1 0 1 (by norm_num), rfl, ?_⟩, ⟨redSwap 1 0 1 (by norm_num), rfl, ?_⟩⟩
  · change ord12 (Sum.inl slot0) < ord12 (Sum.inl slot1)
    decide
  · change ord21 (Sum.inl slot1) < ord21 (Sum.inl slot0)
    decide

/-! ### All reductions -/

/-- A vector read as zero by both reading maps of a reduction without zero block is zero. -/
theorem eq_zero_of_left_mulVec_eq_zero (P : MultiBlockCompression tensorB labels blocks)
    (hz : P.z = 0) {v : Fin 2 → ℂ} (h : ∀ s, P.left s *ᵥ v = 0) : v = 0 := by
  have hg : P.gauge v = 0 := by
    funext y
    obtain ⟨b, j⟩ := y
    rcases b with s | t
    · have := congrFun (h s) j
      rw [← MultiBlockCompression.leftRow_inl, MultiBlockCompression.leftRow_mulVec] at this
      exact this
    · exact absurd t.isLt (by omega)
  exact P.gauge.map_eq_zero_iff.1 hg

theorem left_mulVec_e (P : MultiBlockCompression tensorB labels blocks) (s : {s // s ∈ labels})
    (j : Fin 2) : (P.left s *ᵥ e j) 0 = P.left s 0 j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The entry of `W_s V_s = 1`. -/
theorem left_mul_right_apply (P : MultiBlockCompression tensorB labels blocks)
    (s : {s // s ∈ labels}) :
    P.left s 0 0 * P.right s 0 0 + P.left s 0 1 * P.right s 1 0 = 1 := by
  have := congrFun (congrFun (P.left_mul_right_self s) 0) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using this

/-- **The reductions with the first flag** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.14, (6.14)): `h = [[α, β], [0, δ]]` with `αδ ≠ 0` is a reduction in the order
`(1, 2)`, with `W₁ = (α, β)`, `W₂ = (0, δ)`, `V₁ = (α⁻¹, 0)ᵀ`, `V₂ = (-β/(αδ), δ⁻¹)ᵀ`. -/
theorem exists_multiBlockCompression_upper (α β δ : ℂ) (h : α * δ ≠ 0) :
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
      P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1) ∧
      P.left slot0 = !![α, β] ∧ P.left slot1 = !![0, δ] ∧
      P.right slot0 = !![α⁻¹; 0] ∧ P.right slot1 = !![-β / (α * δ); δ⁻¹] := by
  refine ⟨redUpper α β δ h, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change ord12 (Sum.inl slot0) < ord12 (Sum.inl slot1)
    decide
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]

/-- **Every reduction with the first flag** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.14): every reduction with the first flag (no zero block, order `(1, 2)`) has
`W₁ = (α, β)`, `W₂ = (0, δ)` with `αδ ≠ 0`, that is the gauge `[[α, β], [0, δ]]`. -/
theorem exists_left_eq_upper_of_ord_lt (P : MultiBlockCompression tensorB labels blocks)
    (hz : P.z = 0) (hord : P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1)) :
    ∃ α β δ : ℂ, α * δ ≠ 0 ∧ P.left slot0 = !![α, β] ∧ P.left slot1 = !![0, δ] := by
  have hflag : ∀ k : Fin (labels.card + P.z + 1), k.val = 1 →
      flagVec P k = Submodule.span ℂ {e 0} := by
    rcases ord_flagVec_cases_of_z_eq_zero P hz with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd hord (lt_asymm h)
  have hn : labels.card + P.z = 2 := by rw [hz]; rfl
  have h1 : (P.ord (Sum.inl slot1)).val = 1 := by
    have := lt_of_lt_of_eq (P.ord (Sum.inl slot1)).isLt hn
    have := Fin.lt_def.1 hord
    omega
  have hW : P.left slot1 *ᵥ e 0 = 0 := by
    rw [← MultiBlockCompression.leftRow_inl]
    refine leftRow_mulVec_eq_zero_of_mem_flagVec P ?_
    rw [hflag _ (by rw [Fin.val_castSucc]; exact h1)]
    exact Submodule.mem_span_singleton_self _
  have h10 : P.left slot1 0 0 = 0 := by rw [← left_mulVec_e, hW]; rfl
  refine ⟨P.left slot0 0 0, P.left slot0 0 1, P.left slot1 0 1, mul_ne_zero ?_ ?_, ?_, ?_⟩
  · intro hα
    refine absurd (eq_zero_of_left_mulVec_eq_zero P hz (v := e 0) fun s => ?_) (by simp)
    obtain ⟨s, hs⟩ := s
    ext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    fin_cases s
    · rw [left_mulVec_e]; exact hα
    · rw [left_mulVec_e]; exact h10
  · intro hδ
    have := left_mul_right_apply P slot1
    rw [h10, hδ] at this
    simp at this
  · ext i j; fin_cases i; fin_cases j <;> rfl
  · ext i j; fin_cases i; fin_cases j
    · exact h10
    · rfl

/-- **The reductions with the second flag** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.14, (6.15)): `g̃ = [[β̃, α̃], [δ̃, 0]]` with `α̃δ̃ ≠ 0` is a reduction in the
order `(2, 1)`, with `W̃₂ = (β̃, α̃)`, `W̃₁ = (δ̃, 0)`, `Ṽ₂ = (0, α̃⁻¹)ᵀ`,
`Ṽ₁ = (δ̃⁻¹, -β̃/(α̃δ̃))ᵀ`. -/
theorem exists_multiBlockCompression_swap (α β δ : ℂ) (h : α * δ ≠ 0) :
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
      P.ord (Sum.inl slot1) < P.ord (Sum.inl slot0) ∧
      P.left slot1 = !![β, α] ∧ P.left slot0 = !![δ, 0] ∧
      P.right slot1 = !![0; α⁻¹] ∧ P.right slot0 = !![δ⁻¹; -β / (α * δ)] := by
  refine ⟨redSwap α β δ h, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change ord21 (Sum.inl slot1) < ord21 (Sum.inl slot0)
    decide
  · rw [redSwap, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord21]
  · rw [redSwap, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord21]
  · rw [redSwap, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord21]
  · rw [redSwap, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord21]

/-- **Every reduction with the second flag** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.14): every reduction with the second flag (no zero block, order `(2, 1)`) has
`W̃₂ = (β̃, α̃)`, `W̃₁ = (δ̃, 0)` with `α̃δ̃ ≠ 0`, that is the gauge `[[β̃, α̃], [δ̃, 0]]`. -/
theorem exists_left_eq_swap_of_ord_gt (P : MultiBlockCompression tensorB labels blocks)
    (hz : P.z = 0) (hord : P.ord (Sum.inl slot1) < P.ord (Sum.inl slot0)) :
    ∃ α β δ : ℂ, α * δ ≠ 0 ∧ P.left slot1 = !![β, α] ∧ P.left slot0 = !![δ, 0] := by
  have hflag : ∀ k : Fin (labels.card + P.z + 1), k.val = 1 →
      flagVec P k = Submodule.span ℂ {e 1} := by
    rcases ord_flagVec_cases_of_z_eq_zero P hz with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd hord (lt_asymm h)
    · exact h
  have hn : labels.card + P.z = 2 := by rw [hz]; rfl
  have h0 : (P.ord (Sum.inl slot0)).val = 1 := by
    have := lt_of_lt_of_eq (P.ord (Sum.inl slot0)).isLt hn
    have := Fin.lt_def.1 hord
    omega
  have hW : P.left slot0 *ᵥ e 1 = 0 := by
    rw [← MultiBlockCompression.leftRow_inl]
    refine leftRow_mulVec_eq_zero_of_mem_flagVec P ?_
    rw [hflag _ (by rw [Fin.val_castSucc]; exact h0)]
    exact Submodule.mem_span_singleton_self _
  have h01 : P.left slot0 0 1 = 0 := by rw [← left_mulVec_e, hW]; rfl
  refine ⟨P.left slot1 0 1, P.left slot1 0 0, P.left slot0 0 0, mul_ne_zero ?_ ?_, ?_, ?_⟩
  · intro hα
    refine absurd (eq_zero_of_left_mulVec_eq_zero P hz (v := e 1) fun s => ?_) (by simp)
    obtain ⟨s, hs⟩ := s
    ext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    fin_cases s
    · rw [left_mulVec_e]; exact h01
    · rw [left_mulVec_e]; exact hα
  · intro hδ
    have := left_mul_right_apply P slot0
    rw [h01, hδ] at this
    simp at this
  · ext i j; fin_cases i; fin_cases j <;> rfl
  · ext i j; fin_cases i; fin_cases j
    · rfl
    · exact h01

end Running

end MultiBlockExamples
