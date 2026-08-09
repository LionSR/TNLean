/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ResidualAlgebra

/-!
# Three-form span for the second MPU blocking

This file formalizes the ordered-word step in arXiv:1703.09188, Proposition
`blockingsimple`, lines 415--425.  Once residual products of length `D²` vanish,
a product of letters `c E + S` has, after removal of its all-`E` term, only the
basis-independent span of the forms `E A`, `A E`, and `A E A`.

No assertion is made that a coefficient in an arbitrary physical basis has one
exclusive type.  The invariant conclusion is membership in the sum of the
three submodules.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

section ThreeFormSubmodules

variable {R : Type*} [CommRing R]
variable {B : Type*} [Ring B] [Algebra R B]

/-- The span of products `E * A` with `A` in a residual nonunital algebra.

Source: arXiv:1703.09188, equation `sprimeforms`, type 1, lines 415--424. -/
def projectorMulResidualSubmodule (E : B) (A : NonUnitalSubalgebra R B) :
    Submodule R B :=
  Submodule.span R {x | ∃ a : A, x = E * (a : B)}

/-- The span of products `A * E` with `A` in a residual nonunital algebra.

Source: arXiv:1703.09188, equation `sprimeforms`, type 2, lines 415--424. -/
def residualMulProjectorSubmodule (E : B) (A : NonUnitalSubalgebra R B) :
    Submodule R B :=
  Submodule.span R {x | ∃ a : A, x = (a : B) * E}

/-- The span of products `A * E * B` with `A` and `B` in a residual
nonunital algebra.

Source: arXiv:1703.09188, equation `sprimeforms`, type 3, lines 415--424. -/
def residualMulProjectorMulResidualSubmodule
    (E : B) (A : NonUnitalSubalgebra R B) : Submodule R B :=
  Submodule.span R {x | ∃ a b : A, x = (a : B) * E * (b : B)}

/-- The basis-invariant sum of the three source forms `E A`, `A E`, and
`A E A`.

Source: arXiv:1703.09188, equation `sprimeforms`, lines 415--424. -/
def threeFormSubmodule (E : B) (A : NonUnitalSubalgebra R B) : Submodule R B :=
  projectorMulResidualSubmodule E A ⊔
    residualMulProjectorSubmodule E A ⊔
      residualMulProjectorMulResidualSubmodule E A

private def HasThreeForm (E : B) (A : NonUnitalSubalgebra R B) (x : B) : Prop :=
  (∃ a : A, x = E * (a : B)) ∨
    (∃ a : A, x = (a : B) * E) ∨
      ∃ a b : A, x = (a : B) * E * (b : B)

private theorem HasThreeForm.mem_threeFormSubmodule
    {E : B} {A : NonUnitalSubalgebra R B} {x : B}
    (hx : HasThreeForm E A x) : x ∈ threeFormSubmodule E A := by
  rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · apply Submodule.mem_sup_left
    apply Submodule.mem_sup_left
    exact Submodule.subset_span ⟨a, rfl⟩
  · apply Submodule.mem_sup_left
    apply Submodule.mem_sup_right
    exact Submodule.subset_span ⟨a, rfl⟩
  · apply Submodule.mem_sup_right
    exact Submodule.subset_span ⟨a, b, rfl⟩

private theorem HasThreeForm.zero (E : B) (A : NonUnitalSubalgebra R B) :
    HasThreeForm E A 0 := by
  left
  exact ⟨0, by simp⟩

private theorem HasThreeForm.projector_mul
    {E : B} {A : NonUnitalSubalgebra R B} (hE : E * E = E)
    (hEAE : ∀ a : A, E * (a : B) * E = 0)
    {x : B} (hx : HasThreeForm E A x) : HasThreeForm E A (E * x) := by
  rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · left
    exact ⟨a, by simp [← mul_assoc, hE]⟩
  · rw [← mul_assoc, hEAE a]
    exact HasThreeForm.zero E A
  · rw [← mul_assoc, ← mul_assoc, hEAE a, zero_mul]
    exact HasThreeForm.zero E A

private theorem HasThreeForm.residual_mul
    {E : B} {A : NonUnitalSubalgebra R B} (a : A)
    {x : B} (hx : HasThreeForm E A x) : HasThreeForm E A ((a : B) * x) := by
  rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, c, rfl⟩
  · right; right
    exact ⟨a, b, by simp [mul_assoc]⟩
  · right; left
    exact ⟨⟨(a : B) * b, A.mul_mem a.property b.property⟩, by simp [mul_assoc]⟩
  · right; right
    exact ⟨⟨(a : B) * b, A.mul_mem a.property b.property⟩, c, by simp [mul_assoc]⟩

private theorem pow_eq_self_of_pos {E : B} (hE : E * E = E)
    {N : ℕ} (hN : 0 < N) : E ^ N = E := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, ih (by omega), hE]


private theorem list_prod_mem_of_ne_nil
    (A : NonUnitalSubalgebra R B) (l : List B) (hne : l ≠ [])
    (hl : ∀ x ∈ l, x ∈ A) : l.prod ∈ A := by
  induction l with
  | nil => simp at hne
  | cons x l ih =>
      by_cases hl_nil : l = []
      · subst l
        simpa using hl x (by simp)
      · rw [List.prod_cons]
        exact A.mul_mem (hl x (by simp))
          (ih hl_nil (fun y hy ↦ hl y (List.mem_cons_of_mem x hy)))

private theorem ordered_option_word_classification
    (E : B) (A : NonUnitalSubalgebra R B) (hE : E * E = E)
    (hEAE : ∀ a : A, E * (a : B) * E = 0)
    (l : List (Option A)) :
    ((∀ o ∈ l, o = none) ∧
        (l.map (fun o ↦ o.elim E (fun a ↦ (a : B)))).prod = E ^ l.length) ∨
      (∃ la : List A, l = la.map some ∧
        (l.map (fun o ↦ o.elim E (fun a ↦ (a : B)))).prod =
          (la.map ((↑) : A → B)).prod) ∨
      HasThreeForm E A (l.map (fun o ↦ o.elim E (fun a ↦ (a : B)))).prod := by
  induction l with
  | nil => exact Or.inl ⟨by simp, by simp⟩
  | cons o l ih =>
      rcases o with _ | a
      · rcases ih with ⟨hnone, hprod⟩ | ⟨la, rfl, hprod⟩ | hthree
        · left
          exact ⟨by simpa using hnone, by simp [hprod, pow_succ']⟩
        · by_cases hla : la = []
          · subst la
            left
            simp
          · right; right
            have hpos : 0 < la.length := List.length_pos_iff.mpr hla
            rw [show (none :: List.map some la).map
                (fun o ↦ o.elim E (fun a ↦ (a : B))) =
                E :: la.map ((↑) : A → B) by simp,
              List.prod_cons]
            left
            exact ⟨⟨(la.map ((↑) : A → B)).prod,
              list_prod_mem_of_ne_nil A _
                (fun h ↦ hla (List.map_eq_nil_iff.mp h)) (fun b hb ↦ by
                obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
                exact a.property)⟩, rfl⟩
        · right; right
          simpa using hthree.projector_mul hE hEAE
      · rcases ih with ⟨hnone, hprod⟩ | ⟨la, rfl, hprod⟩ | hthree
        · by_cases hl : l = []
          · subst l
            right; left
            exact ⟨[a], by simp, by simp⟩
          · right; right
            have hpos : 0 < l.length := List.length_pos_iff.mpr hl
            have hpow : E ^ l.length = E := pow_eq_self_of_pos hE hpos
            rw [List.map_cons, List.prod_cons, hprod, hpow]
            right; left
            exact ⟨a, rfl⟩
        · right; left
          refine ⟨a :: la, by simp, ?_⟩
          simp
        · right; right
          simpa using hthree.residual_mul a

/-- Ordered noncommutative product-of-sums classification.  Removing the
all-projector term from a product of `N` letters `cₖ E + Sₖ` leaves the
three-form submodule, provided length-`N` residual products vanish.

Source: arXiv:1703.09188, equations `Sprime=0` and `sprimeforms`, lines 410--424. -/
theorem ordered_prod_smul_projector_add_sub_mem_threeFormSubmodule
    (E : B) (A : NonUnitalSubalgebra R B) (hE : E * E = E)
    (hEAE : ∀ a : A, E * (a : B) * E = 0)
    {N : ℕ} (hN : 0 < N)
    (hvanish : ∀ l : List B, (∀ x ∈ l, x ∈ A) → l.length = N → l.prod = 0)
    (c : Fin N → R) (S : Fin N → A) :
    (List.ofFn (fun k ↦ c k • E + (S k : B))).prod - (∏ k, c k) • E ∈
      threeFormSubmodule E A := by
  classical
  let f : Fin N → Bool → B := fun k b ↦ if b then (S k : B) else c k • E
  have hexpand := List.prod_ofFn_sum f
  have hsum (k : Fin N) : ∑ b : Bool, f k b = c k • E + (S k : B) := by
    simp [f, add_comm]
  simp_rw [hsum] at hexpand
  rw [hexpand]
  let eChoice : Fin N → Bool := fun _ ↦ false
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ eChoice)]
  have heword : (List.ofFn fun k ↦ f k (eChoice k)).prod = (∏ k, c k) • E := by
    change (List.ofFn fun k ↦ c k • E).prod = _
    calc
      _ = (∏ k, c k) • (List.ofFn fun _ : Fin N ↦ E).prod :=
        List.prod_ofFn_smul c (fun _ ↦ E)
      _ = (∏ k, c k) • E := by
        rw [List.ofFn_const, List.prod_replicate, pow_eq_self_of_pos hE hN]
  rw [heword, add_sub_cancel_left]
  apply Submodule.sum_mem
  intro choice hchoice
  have hne : choice ≠ eChoice := by
    simpa using hchoice
  let options : List (Option A) :=
    List.ofFn (fun k ↦ if choice k then some (S k) else none)
  let coeff : Fin N → R := fun k ↦ if choice k then 1 else c k
  let base : Fin N → B := fun k ↦ if choice k then (S k : B) else E
  have hfactor (k : Fin N) : f k (choice k) = coeff k • base k := by
    by_cases hk : choice k = true <;> simp [f, coeff, base, hk]
  have hbase : List.ofFn base =
      options.map (fun o ↦ o.elim E (fun a ↦ (a : B))) := by
    simp only [options, List.map_ofFn]
    apply congrArg List.ofFn
    funext k
    by_cases hk : choice k = true <;> simp [base, hk]
  have hword : (List.ofFn fun k ↦ f k (choice k)).prod =
      (∏ k, if choice k then (1 : R) else c k) •
        (options.map (fun o ↦ o.elim E (fun a ↦ (a : B)))).prod := by
    simp_rw [hfactor]
    calc
      _ = (∏ k, coeff k) • (List.ofFn base).prod :=
        List.prod_ofFn_smul coeff base
      _ = (∏ k, if choice k then (1 : R) else c k) •
          (options.map (fun o ↦ o.elim E (fun a ↦ (a : B)))).prod := by
        rw [hbase]
  rw [hword]
  apply Submodule.smul_mem
  rcases ordered_option_word_classification E A hE hEAE options with
      ⟨hallE, _⟩ | ⟨la, hla, hprod⟩ | hthree
  · exfalso
    apply hne
    funext k
    have hk := hallE (if choice k then some (S k) else none)
      (List.mem_ofFn.mpr ⟨k, by simp⟩)
    simpa using hk
  · have hlen : la.length = N := by
      rw [← List.length_map some, ← hla]
      simp [options]
    have hmem : ∀ x ∈ la.map ((↑) : A → B), x ∈ A := by
      intro x hx
      obtain ⟨a, _, hax⟩ := List.mem_map.mp hx
      rw [← hax]
      exact a.property
    rw [hprod, hvanish _ hmem (by simpa using hlen)]
    exact (threeFormSubmodule E A).zero_mem
  · exact hthree.mem_threeFormSubmodule

end ThreeFormSubmodules

section ResidualThreeForms

private theorem exists_nonempty_residual_word_of_mem_closure
    {U : MPOTensor d D}
    {x : Matrix (Fin (D * D)) (Fin (D * D)) ℂ}
    (hx : x ∈ Subsemigroup.closure (residualGeneratorSet U)) :
    ∃ l : List (Matrix (Fin (D * D)) (Fin (D * D)) ℂ),
      l ≠ [] ∧ (∀ a ∈ l, a ∈ residualGeneratorSet U) ∧ l.prod = x := by
  induction hx using Subsemigroup.closure_induction with
  | mem x hx => exact ⟨[x], by simp, by simpa, by simp⟩
  | mul x y _ _ hx hy =>
      obtain ⟨lx, hlx, hlxs, hxl⟩ := hx
      obtain ⟨ly, hly, hlys, hyl⟩ := hy
      refine ⟨lx ++ ly, ?_, ?_, ?_⟩
      · simp [hlx]
      · intro a ha
        exact List.mem_append.mp ha |>.elim (hlxs a) (hlys a)
      · rw [List.prod_append, hxl, hyl]

/-- The rank-one normalized diagonal annihilates every element of the residual
algebra when placed on both sides.

Source: arXiv:1703.09188, equation `ESE=0`, lines 405--410. -/
theorem IsMPU.normalizedDiagonal_mul_mem_residualAlgebra_mul_normalizedDiagonal_eq_zero
    [NeZero d] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ Φ : Fin (D * D) → ℂ)
    (hE : normalizedDiagonal (doubleLayerTensor U) = Matrix.vecMulVec ρ Φ)
    (A : residualAlgebra U) :
    normalizedDiagonal (doubleLayerTensor U) * (A : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) *
      normalizedDiagonal (doubleLayerTensor U) = 0 := by
  let E := normalizedDiagonal (doubleLayerTensor U)
  change E * (A : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) * E = 0
  have hA := A.property
  change (A : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) ∈
    (NonUnitalAlgebra.adjoin ℂ (residualGeneratorSet U)).toSubmodule at hA
  rw [NonUnitalAlgebra.adjoin_eq_span] at hA
  have hspan : ∀ x : Matrix (Fin (D * D)) (Fin (D * D)) ℂ,
      x ∈ Submodule.span ℂ (Subsemigroup.closure (residualGeneratorSet U)) →
        E * x * E = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨l, hne, hl, rfl⟩ := exists_nonempty_residual_word_of_mem_closure hx
        have hX : ∀ a ∈ l, ∃ X, a = residualSlice (doubleLayerTensor U) X := by
          intro a ha
          obtain ⟨X, hX⟩ := hl a ha
          exact ⟨X, hX.symm⟩
        let X' : Fin l.length → Matrix (Fin d) (Fin d) ℂ := fun k ↦
          Classical.choose (hX l[k] (List.get_mem l k))
        have hlword : l = List.ofFn
            (fun k ↦ residualSlice (doubleLayerTensor U) (X' k)) := by
          calc
            l = List.ofFn (fun k ↦ l[k]) := (List.ofFn_get l).symm
            _ = _ := by
              congr 1
              funext k
              exact Classical.choose_spec (hX l[k] (List.get_mem l k))
        have hpos : 0 < l.length := List.length_pos_iff.mpr hne
        rw [hlword]
        exact hU.normalizedDiagonal_mul_prod_residualSlice_mul_normalizedDiagonal_eq_zero
          hpos X' ρ Φ hE
    | zero => simp
    | add x y _ _ hx hy => simp [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul c x _ hx => simp [hx]
  exact hspan _ hA

private theorem doubleLayer_entry_eq_diagonal_add_residual
    [NeZero d] (U : MPOTensor d D) (i j : Fin d) :
    doubleLayerTensor U i j =
      (if i = j then (1 : ℂ) else 0) • normalizedDiagonal (doubleLayerTensor U) +
        residualSlice (doubleLayerTensor U) (Matrix.single j i 1) := by
  rw [residualSlice, contractPhysical_single]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Matrix.trace_single_eq_same]
    simp
  · rw [if_neg hij, Matrix.trace_single_eq_of_ne j i (1 : ℂ) (Ne.symm hij)]
    simp

private theorem diagonal_coeff_prod_eq
    {N d : ℕ} (I J : Fin (MPSTensor.blockPhysDim d N)) :
    (∏ k : Fin N, if MPSTensor.decodeBlock d N I k = MPSTensor.decodeBlock d N J k
      then (1 : ℂ) else 0) = if I = J then 1 else 0 := by
  classical
  by_cases hIJ : I = J
  · subst J
    simp
  · rw [if_neg hIJ]
    have hdiff : ∃ k : Fin N,
        MPSTensor.decodeBlock d N I k ≠ MPSTensor.decodeBlock d N J k := by
      by_contra h
      push Not at h
      apply hIJ
      exact (MPSTensor.decodeBlockEquiv d N).injective (funext h)
    obtain ⟨k, hk⟩ := hdiff
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- Every matrix-unit residual coefficient after the second, length-`D²`
blocking belongs to the basis-invariant sum of the forms `E A`, `A E`, and
`A E A`.

Source: arXiv:1703.09188, equation `sprimeforms`, lines 415--424. -/
theorem IsMPU.residualSlice_doubleLayerTensor_blockTensor_single_mem_threeFormSubmodule
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ Φ : Fin (D * D) → ℂ)
    (hE : normalizedDiagonal (doubleLayerTensor U) = Matrix.vecMulVec ρ Φ)
    (hEidem : normalizedDiagonal (doubleLayerTensor U) *
      normalizedDiagonal (doubleLayerTensor U) = normalizedDiagonal (doubleLayerTensor U))
    (I J : Fin (MPSTensor.blockPhysDim d (D * D))) :
    residualSlice
        (doubleLayerTensor (MPOTensor.blockTensor U (D * D))) (Matrix.single J I 1) ∈
      threeFormSubmodule (normalizedDiagonal (doubleLayerTensor U)) (residualAlgebra U) := by
  classical
  let E := normalizedDiagonal (doubleLayerTensor U)
  let σ := MPSTensor.decodeBlock d (D * D) I
  let τ := MPSTensor.decodeBlock d (D * D) J
  let c : Fin (D * D) → ℂ := fun k ↦ if σ k = τ k then 1 else 0
  let S : Fin (D * D) → residualAlgebra U := fun k ↦
    ⟨residualSlice (doubleLayerTensor U) (Matrix.single (τ k) (σ k) 1),
      residualSlice_mem_residualAlgebra U _⟩
  have hN : 0 < D * D := Nat.mul_pos (NeZero.pos D) (NeZero.pos D)
  have hword := ordered_prod_smul_projector_add_sub_mem_threeFormSubmodule
    E (residualAlgebra U) hEidem
    (hU.normalizedDiagonal_mul_mem_residualAlgebra_mul_normalizedDiagonal_eq_zero ρ Φ hE)
    hN (fun l hl hlen ↦ hU.residualAlgebra_list_prod_eq_zero l hl hlen) c S
  have hentry : MPOTensor.blockTensor (doubleLayerTensor U) (D * D) I J =
      (List.ofFn (fun k ↦ c k • E + (S k : Matrix (Fin (D * D)) (Fin (D * D)) ℂ))).prod := by
    simp only [blockTensor_apply, MPSTensor.wordOfBlock, evalWord_ofFn]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext k
    simpa [E, c, S, σ, τ] using
      doubleLayer_entry_eq_diagonal_add_residual U (σ k) (τ k)
  have hc : (∏ k, c k) = if I = J then 1 else 0 :=
    diagonal_coeff_prod_eq I J
  have htrace : Matrix.trace (Matrix.single J I (1 : ℂ)) =
      if I = J then 1 else 0 := by
    by_cases hIJ : I = J
    · subst J
      rw [if_pos rfl, Matrix.trace_single_eq_same]
    · rw [if_neg hIJ,
        Matrix.trace_single_eq_of_ne J I (1 : ℂ) (Ne.symm hIJ)]
  rw [doubleLayerTensor_blockTensor, residualSlice, contractPhysical_single,
    normalizedDiagonal_blockTensor, hentry, htrace, ← hc]
  change _ - (∏ k, c k) • E ^ (D * D) ∈ _
  rw [pow_eq_self_of_pos hEidem hN]
  exact hword

/-- Residual slicing is linear in the physical argument.

Source: arXiv:1703.09188, equation `WIsom`, lines 390--395. -/
private noncomputable def residualSliceLinear (W : MPOTensor d D) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun := residualSlice W
  map_add' X Y := by
    simp only [residualSlice, ← contractPhysicalLinear_apply, map_add, Matrix.trace_add,
      add_smul]
    module
  map_smul' c X := by
    simp only [residualSlice, ← contractPhysicalLinear_apply, map_smul, Matrix.trace_smul,
      RingHom.id_apply]
    module

/-- Evaluation of the residual-slice linear map.

Source: arXiv:1703.09188, equation `WIsom`, lines 390--395. -/
@[simp] private theorem residualSliceLinear_apply (W : MPOTensor d D)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    residualSliceLinear W X = residualSlice W X := rfl

/-- Every residual coefficient after the second, length-`D²` blocking belongs
to the basis-invariant sum of the forms `E A`, `A E`, and `A E A`.

This is a span statement, not an exclusive type assignment to coefficients in
an arbitrary physical basis.

Source: arXiv:1703.09188, equation `sprimeforms`, lines 415--424. -/
theorem IsMPU.residualSlice_doubleLayerTensor_blockTensor_mem_threeFormSubmodule
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ Φ : Fin (D * D) → ℂ)
    (hE : normalizedDiagonal (doubleLayerTensor U) = Matrix.vecMulVec ρ Φ)
    (hEidem : normalizedDiagonal (doubleLayerTensor U) *
      normalizedDiagonal (doubleLayerTensor U) = normalizedDiagonal (doubleLayerTensor U))
    (X : Matrix (Fin (MPSTensor.blockPhysDim d (D * D)))
      (Fin (MPSTensor.blockPhysDim d (D * D))) ℂ) :
    residualSlice (doubleLayerTensor (MPOTensor.blockTensor U (D * D))) X ∈
      threeFormSubmodule (normalizedDiagonal (doubleLayerTensor U)) (residualAlgebra U) := by
  classical
  let W := doubleLayerTensor (MPOTensor.blockTensor U (D * D))
  change residualSliceLinear W X ∈ _
  rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, residualSliceLinear_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  have hsingle : Matrix.single i j (X i j) =
      (X i j) • Matrix.single i j (1 : ℂ) := by
    ext a b
    simp [Matrix.single]
  rw [hsingle, ← residualSliceLinear_apply, map_smul, residualSliceLinear_apply]
  apply Submodule.smul_mem
  exact hU.residualSlice_doubleLayerTensor_blockTensor_single_mem_threeFormSubmodule
    ρ Φ hE hEidem j i

end ResidualThreeForms

end MPOTensor
