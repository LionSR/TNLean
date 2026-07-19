/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.ProjectionGeometry

/-!
# Products of complementary commuting projections

For a finite commuting family of orthogonal projections, the ordered product
of the complementary projections has range equal to the kernel of their sum.
The order of the product is retained in the statement, so the result applies
directly to cyclic chains of local operators.
-/

open scoped BigOperators

namespace Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
  {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The trace of a matrix whose entries are dependent products of matrix
entries is the product of the traces of its factors. -/
theorem trace_piProduct (P : (i : ι) → Matrix (α i) (α i) R) :
    trace (fun (x y : ∀ i, α i) ↦ ∏ i, P i (x i) (y i)) =
      ∏ i, trace (P i) := by
  simp only [trace, diag]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum (fun _ ↦ Finset.univ) fun i x ↦ P i x x]

end Matrix

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem apply_list_prod_one_sub_eq_self
    (P : List (E →ₗ[𝕜] E)) (v : E) (hP : ∀ p ∈ P, p v = 0) :
    (P.map fun p ↦ (1 : E →ₗ[𝕜] E) - p).prod v = v := by
  induction P with
  | nil => simp
  | cons p P ih =>
      simp only [List.map_cons, List.prod_cons]
      change (1 - p) ((P.map fun q ↦ (1 : E →ₗ[𝕜] E) - q).prod v) = v
      rw [ih (fun q hq ↦ hP q (List.mem_cons_of_mem p hq))]
      simp [hP p (List.mem_cons_self)]

private theorem mul_list_prod_one_sub_eq_zero
    (P : List (E →ₗ[𝕜] E)) (hcomm : P.Pairwise fun p q ↦ Commute p q)
    (hidem : ∀ p ∈ P, IsIdempotentElem p) {p : E →ₗ[𝕜] E} (hp : p ∈ P) :
    p * (P.map fun q ↦ (1 : E →ₗ[𝕜] E) - q).prod = 0 := by
  induction P with
  | nil => simp at hp
  | cons q P ih =>
      rw [List.pairwise_cons] at hcomm
      simp only [List.map_cons, List.prod_cons]
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        rw [← mul_assoc, (hidem q (List.mem_cons_self)).mul_one_sub_self, zero_mul]
      · have hpq : Commute p q :=
          (hcomm.1 p hp).symm
        rw [← mul_assoc, ((Commute.one_right p).sub_right hpq).eq, mul_assoc,
          ih hcomm.2 (fun r hr ↦ hidem r (List.mem_cons_of_mem q hr)) hp, mul_zero]

private theorem list_prod_one_sub_isIdempotentElem
    (P : List (E →ₗ[𝕜] E)) (hcomm : P.Pairwise fun p q ↦ Commute p q)
    (hidem : ∀ p ∈ P, IsIdempotentElem p) :
    IsIdempotentElem (P.map fun p ↦ (1 : E →ₗ[𝕜] E) - p).prod := by
  induction P with
  | nil => exact IsIdempotentElem.one
  | cons p P ih =>
      rw [List.pairwise_cons] at hcomm
      simp only [List.map_cons, List.prod_cons]
      have hhead : IsIdempotentElem ((1 : E →ₗ[𝕜] E) - p) :=
        (hidem p List.mem_cons_self).one_sub
      have htail := ih hcomm.2 (fun q hq ↦ hidem q (List.mem_cons_of_mem p hq))
      apply hhead.mul_of_commute _ htail
      apply Commute.list_prod_right
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact (Commute.one_left ((1 : E →ₗ[𝕜] E) - r)).sub_left
        ((Commute.one_right p).sub_right (hcomm.1 r hr))

/-- For a finite commuting family of symmetric projections, the ordered
product of their complements has range equal to the kernel of their sum. -/
theorem range_listProd_one_sub_eq_ker_sum
    {N : ℕ} (P : Fin N → E →ₗ[𝕜] E)
    (hP : ∀ i, (P i).IsSymmetricProjection)
    (hcomm : ∀ i j, Commute (P i) (P j)) :
    range ((List.ofFn fun i ↦ 1 - P i).prod) = ker (∑ i, P i) := by
  classical
  let Ps : List (E →ₗ[𝕜] E) := List.ofFn P
  have hpair : Ps.Pairwise fun p q ↦ Commute p q := by
    simp only [Ps, List.pairwise_ofFn]
    intro i j _
    exact hcomm i j
  have hidem : ∀ p ∈ Ps, IsIdempotentElem p := by
    intro p hp
    simp only [Ps, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact (hP i).isIdempotentElem
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    rw [mem_ker]
    simp only [sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hkill := mul_list_prod_one_sub_eq_zero Ps hpair hidem
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
    change P i ((List.ofFn ((fun q ↦ (1 : E →ₗ[𝕜] E) - q) ∘ P)).prod x) = 0
    simpa [Ps] using LinearMap.congr_fun hkill x
  · intro v hv
    rw [mem_ker] at hv
    have heach : ∀ i, P i v = 0 := fun i ↦
      ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero P hP hv i
    refine ⟨v, ?_⟩
    change (List.ofFn ((fun p ↦ (1 : E →ₗ[𝕜] E) - p) ∘ P)).prod v = v
    simpa [Ps] using apply_list_prod_one_sub_eq_self Ps v (by
      intro p hp
      simp only [Ps, List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact heach i)

/-- The ordered product of the complementary members of a finite commuting
family of symmetric projections is the projection onto the kernel of their
sum. -/
theorem isProj_ker_sum_listProd_one_sub
    {N : ℕ} (P : Fin N → E →ₗ[𝕜] E)
    (hP : ∀ i, (P i).IsSymmetricProjection)
    (hcomm : ∀ i j, Commute (P i) (P j)) :
    IsProj (ker (∑ i, P i)) ((List.ofFn fun i ↦ 1 - P i).prod) := by
  classical
  rw [← range_listProd_one_sub_eq_ker_sum P hP hcomm,
    isProj_range_iff_isIdempotentElem]
  simpa only [List.map_ofFn, Function.comp_def] using
    list_prod_one_sub_isIdempotentElem (List.ofFn P) (by
      rw [List.pairwise_ofFn]
      exact fun _ _ _ ↦ hcomm _ _) (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact (hP i).isIdempotentElem)

end LinearMap
