import MPSLean.MPS.BlockPermutation
import MPSLean.MPS.SkolemNoether

import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Decomposition of algebra automorphisms of products of matrix algebras

This file bridges `BlockPermutation.lean` to the MPS gauge-equivalence machinery.

Given a ℂ-algebra automorphism `T` of `∏_i M_{D_i}(ℂ)`, we decompose it as:
1. A block permutation `σ : ι ≃ ι`
2. A proof that `σ` preserves dimensions: `D (σ i) = D i`
3. Per-block inner automorphisms (Skolem–Noether)

## Main results

* `mem_blockIdeal_iff` — block ideal membership characterisation
* `componentMap` — the per-block map extracted from T
* `algEquiv_pi_matrix_decomposition` — the main decomposition theorem
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.show false

open scoped Matrix

namespace MPSTensor

/-! ### Block ideal membership -/
section BlockIdealMembership

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]

/-- An element belongs to the block ideal at `i` iff all other components vanish. -/
theorem mem_blockIdeal_iff {i : ι} {x : ∀ j, R j} :
    x ∈ blockIdeal R i ↔ ∀ j, j ≠ i → x j = 0 := by
  classical
  have h_eq : blockIdeal R i =
      (Ideal.pi fun j =>
        ((Function.update (⊥ : ∀ k, TwoSidedIdeal (R k)) i ⊤) j).asIdeal).toTwoSided := by
    simp only [blockIdeal, twoSidedIdealPiOrderIso]; rfl
  rw [h_eq, Ideal.mem_toTwoSided, Ideal.mem_pi]
  constructor
  · intro h j hj
    have := h j; rw [Function.update_of_ne hj] at this
    exact TwoSidedIdeal.mem_asIdeal.mp this
  · intro h j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact TwoSidedIdeal.mem_asIdeal.mpr trivial
    · rw [Function.update_of_ne hj]
      exact TwoSidedIdeal.mem_asIdeal.mpr (h j hj ▸ (⊥ : TwoSidedIdeal (R j)).asIdeal.zero_mem)

/-- `Pi.single i M` belongs to the block ideal at `i`. -/
theorem pi_single_mem_blockIdeal {i : ι} (M : R i) :
    Pi.single i M ∈ blockIdeal R i :=
  mem_blockIdeal_iff.mpr (fun _ hj => Pi.single_eq_of_ne hj M)

theorem ringEquiv_maps_single_support
    (T : (∀ j, R j) ≃+* (∀ j, R j)) (σ : ι ≃ ι)
    (hσ : ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R (σ i))
    {i : ι} (M : R i) (j : ι) (hj : j ≠ σ i) :
    T (Pi.single i M) j = 0 := by
  have : T (Pi.single i M) ∈ blockIdeal R (σ i) := by
    rw [← hσ i, RingEquiv.mapTwoSidedIdeal_apply, TwoSidedIdeal.mem_comap]
    simp [pi_single_mem_blockIdeal M]
  exact (mem_blockIdeal_iff.mp this) j hj

theorem ringEquiv_symm_maps_blockIdeal
    (T : (∀ j, R j) ≃+* (∀ j, R j)) (σ : ι ≃ ι)
    (hσ : ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R (σ i)) (i : ι) :
    T.symm.mapTwoSidedIdeal (blockIdeal R (σ i)) = blockIdeal R i := by
  rw [← hσ i]; ext x
  simp [RingEquiv.mapTwoSidedIdeal_apply, TwoSidedIdeal.mem_comap]

end BlockIdealMembership

/-! ### T maps Pi.single i 1 to Pi.single (σ i) 1 -/
section PiSingleOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]

/-- A ring automorphism maps `Pi.single i 1` to `Pi.single (σ i) 1`. -/
theorem ringEquiv_single_one_eq
    (T : (∀ j, R j) ≃+* (∀ j, R j)) (σ : ι ≃ ι)
    (hσ : ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R (σ i)) (i : ι) :
    T (Pi.single i (1 : R i)) = Pi.single (σ i) (1 : R (σ i)) := by
  have h_support : ∀ j, j ≠ σ i → T (Pi.single i (1 : R i)) j = 0 :=
    fun j hj => ringEquiv_maps_single_support T σ hσ 1 j hj
  have h_eq_single : T (Pi.single i (1 : R i)) =
      Pi.single (σ i) (T (Pi.single i (1 : R i)) (σ i)) := by
    ext j; by_cases hj : j = σ i
    · subst hj; simp
    · rw [h_support j hj, Pi.single_eq_of_ne hj]
  have h_eval : T (Pi.single i (1 : R i)) (σ i) = 1 := by
    have h_T_sum : ∑ j : ι, T (Pi.single j (1 : R j)) = 1 := by
      rw [← map_sum, show ∑ j : ι, Pi.single j (1 : R j) = 1 from by
        simpa using Finset.univ_sum_single (1 : ∀ i, R i), map_one]
    have h_at : (∑ j : ι, T (Pi.single j (1 : R j))) (σ i) =
        T (Pi.single i (1 : R i)) (σ i) := by
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single i (fun j _ hj =>
        ringEquiv_maps_single_support T σ hσ 1 (σ i) (fun h => hj (σ.injective h.symm)))
        (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [h_T_sum] at h_at; simpa using h_at.symm
  rw [h_eq_single, h_eval]

end PiSingleOne

/-! ### Component map -/
section ComponentMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : ι → ℕ} [∀ i, NeZero (D i)]

noncomputable instance instSimple (i : ι) :
    IsSimpleRing (Matrix (Fin (D i)) (Fin (D i)) ℂ) := by
  have : Nonempty (Fin (D i)) := Fin.pos_iff_nonempty.mp (NeZero.pos (D i))
  exact IsSimpleRing.matrix (Fin (D i)) ℂ

/-- The per-block map: `M ↦ T(Pi.single i M)(σ i)`. -/
noncomputable def componentMap
    (T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+*
         (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ))
    (σ : ι ≃ ι) (i : ι)
    (M : Matrix (Fin (D i)) (Fin (D i)) ℂ) :
    Matrix (Fin (D (σ i))) (Fin (D (σ i))) ℂ :=
  T (Pi.single i M) (σ i)

private theorem componentMap_map_zero
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι} {i : ι} :
    componentMap T σ i 0 = 0 := by
  simp [componentMap, Pi.single_zero, map_zero]

private theorem componentMap_map_add
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι} {i : ι}
    (M N : Matrix (Fin (D i)) (Fin (D i)) ℂ) :
    componentMap T σ i (M + N) = componentMap T σ i M + componentMap T σ i N := by
  simp [componentMap, Pi.single_add, map_add, Pi.add_apply]

theorem componentMap_map_mul
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι} {i : ι}
    (M N : Matrix (Fin (D i)) (Fin (D i)) ℂ) :
    componentMap T σ i (M * N) = componentMap T σ i M * componentMap T σ i N := by
  show T (Pi.single i (M * N)) (σ i) =
    T (Pi.single i M) (σ i) * T (Pi.single i N) (σ i)
  rw [Pi.single_mul, map_mul, Pi.mul_apply]

theorem componentMap_map_one
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι}
    (hσ : ∀ i, T.mapTwoSidedIdeal
        (blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) i) =
      blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) (σ i))
    (i : ι) :
    componentMap T σ i 1 = 1 := by
  show T (Pi.single i 1) (σ i) = 1
  rw [ringEquiv_single_one_eq T σ hσ i, Pi.single_eq_same]

private theorem componentMap_map_sub
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι} {i : ι}
    (M N : Matrix (Fin (D i)) (Fin (D i)) ℂ) :
    componentMap T σ i (M - N) = componentMap T σ i M - componentMap T σ i N := by
  show T (Pi.single i (M - N)) (σ i) =
    T (Pi.single i M) (σ i) - T (Pi.single i N) (σ i)
  have : (Pi.single i (M - N) : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) =
      Pi.single i M - Pi.single i N := by
    funext j; simp only [Pi.sub_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [this, map_sub, Pi.sub_apply]

/-- The component map commutes with ℂ-scalar multiplication when T is a ℂ-algebra map. -/
theorem componentMap_map_smul_of_algEquiv
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃ₐ[ℂ] _} {σ : ι ≃ ι} {i : ι}
    (c : ℂ) (M : Matrix (Fin (D i)) (Fin (D i)) ℂ) :
    componentMap T.toRingEquiv σ i (c • M) = c • componentMap T.toRingEquiv σ i M := by
  show T (Pi.single i (c • M)) (σ i) = c • T (Pi.single i M) (σ i)
  have h : Pi.single i (c • M) =
      (algebraMap ℂ (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) c) * Pi.single i M := by
    funext j; simp only [Pi.mul_apply, Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj, mul_zero]
  rw [h, map_mul, T.commutes, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
      Pi.smul_apply, Pi.one_apply, smul_mul_assoc, one_mul]

private noncomputable def componentMapRingHom
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι}
    (hσ : ∀ i, T.mapTwoSidedIdeal
        (blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) i) =
      blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) (σ i))
    (i : ι) : Matrix (Fin (D i)) (Fin (D i)) ℂ →+* Matrix (Fin (D (σ i))) (Fin (D (σ i))) ℂ where
  toFun := componentMap T σ i
  map_one' := componentMap_map_one hσ i
  map_mul' := componentMap_map_mul
  map_zero' := componentMap_map_zero
  map_add' := componentMap_map_add

theorem componentMap_injective
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι}
    (hσ : ∀ i, T.mapTwoSidedIdeal
        (blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) i) =
      blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) (σ i))
    (i : ι) : Function.Injective (componentMap T σ i) := by
  let f := componentMapRingHom hσ i
  have hker : TwoSidedIdeal.ker (f : Matrix _ _ ℂ →+* Matrix _ _ ℂ) = ⊥ := by
    rcases eq_bot_or_eq_top (TwoSidedIdeal.ker (f : Matrix _ _ ℂ →+* Matrix _ _ ℂ)) with h | h
    · exact h
    · exfalso
      have h1 : (1 : Matrix (Fin (D i)) (Fin (D i)) ℂ) ∈ (⊤ : TwoSidedIdeal _) := trivial
      rw [← h] at h1; rw [TwoSidedIdeal.mem_ker] at h1
      change componentMap T σ i 1 = 0 at h1
      rw [componentMap_map_one hσ i] at h1; exact one_ne_zero h1
  intro x y hxy
  have hsub : x - y ∈ TwoSidedIdeal.ker (f : Matrix _ _ ℂ →+* Matrix _ _ ℂ) := by
    rw [TwoSidedIdeal.mem_ker]; change componentMap T σ i (x - y) = 0
    rw [componentMap_map_sub, sub_eq_zero]; exact hxy
  rw [hker, TwoSidedIdeal.mem_bot] at hsub; exact sub_eq_zero.mp hsub

theorem componentMap_surjective
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι}
    (hσ : ∀ i, T.mapTwoSidedIdeal
        (blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) i) =
      blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) (σ i))
    (i : ι) : Function.Surjective (componentMap T σ i) := by
  intro N
  haveI : Finite ι := Finite.of_fintype ι
  have h_symm_support : ∀ j, j ≠ i → T.symm (Pi.single (σ i) N) j = 0 := by
    intro j hj
    exact (mem_blockIdeal_iff.mp (by
      rw [← ringEquiv_symm_maps_blockIdeal T σ hσ i,
          RingEquiv.mapTwoSidedIdeal_apply, TwoSidedIdeal.mem_comap]
      simp only [RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
      exact @pi_single_mem_blockIdeal ι _ _
        (fun k => Matrix (Fin (D k)) (Fin (D k)) ℂ) _ _ (σ i) N)) j hj
  have h_eq : T.symm (Pi.single (σ i) N) =
      Pi.single i (T.symm (Pi.single (σ i) N) i) := by
    ext j; by_cases hj : j = i
    · subst hj; simp
    · rw [h_symm_support j hj, Pi.single_eq_of_ne hj]
  refine ⟨T.symm (Pi.single (σ i) N) i, ?_⟩
  show T (Pi.single i (T.symm (Pi.single (σ i) N) i)) (σ i) = N
  rw [← h_eq, T.apply_symm_apply, Pi.single_eq_same]

theorem componentMap_bijective
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃+* _} {σ : ι ≃ ι}
    (hσ : ∀ i, T.mapTwoSidedIdeal
        (blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) i) =
      blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) (σ i))
    (i : ι) : Function.Bijective (componentMap T σ i) :=
  ⟨componentMap_injective hσ i, componentMap_surjective hσ i⟩

end ComponentMap

/-! ### Dimension preservation -/
section DimPreservation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- The permutation preserves block dimensions. -/
theorem dim_preserved
    {T : (∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) ≃ₐ[ℂ] _} {σ : ι ≃ ι}
    (hσ : ∀ i, T.toRingEquiv.mapTwoSidedIdeal
        (blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) i) =
      blockIdeal (fun j => Matrix (Fin (D j)) (Fin (D j)) ℂ) (σ i))
    (i : ι) : D (σ i) = D i := by
  let φ : Matrix (Fin (D i)) (Fin (D i)) ℂ →ₗ[ℂ] Matrix (Fin (D (σ i))) (Fin (D (σ i))) ℂ :=
    { toFun := componentMap T.toRingEquiv σ i
      map_add' := componentMap_map_add
      map_smul' := componentMap_map_smul_of_algEquiv }
  have h := (LinearEquiv.ofBijective φ (componentMap_bijective hσ i)).finrank_eq
  rw [Module.finrank_matrix, Module.finrank_matrix] at h
  simp only [Module.finrank_self, Fintype.card_fin, mul_one] at h
  exact (Nat.mul_self_inj.mp h).symm

end DimPreservation

/-! ### Main decomposition -/
section MainDecomposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- **Main theorem**: Any ℂ-algebra automorphism of `∏_i M_{D_i}(ℂ)` decomposes as a block
permutation composed with per-block inner automorphisms (Skolem–Noether). -/
theorem algEquiv_pi_matrix_decomposition
    (T : (∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ) ≃ₐ[ℂ]
         (∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)) :
    ∃ (σ : ι ≃ ι) (hDeq : ∀ i, D (σ i) = D i)
      (X : ∀ i, GL (Fin (D i)) ℂ),
    ∀ (i : ι) (M : Matrix (Fin (D i)) (Fin (D i)) ℂ),
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i)))
        (componentMap T.toRingEquiv σ i M) =
        (X i : Matrix (Fin (D i)) (Fin (D i)) ℂ) * M *
          ((X i)⁻¹ : GL (Fin (D i)) ℂ) := by
  obtain ⟨σ, hσ⟩ := ringEquiv_pi_simple_permutes_blockIdeals T.toRingEquiv
  have hDeq : ∀ i, D (σ i) = D i := fun i => dim_preserved hσ i
  let reind (i : ι) := Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i))
  let castMap (i : ι) : Matrix (Fin (D i)) (Fin (D i)) ℂ →ₐ[ℂ] _ :=
    (reind i).toAlgHom.comp
    { toFun := componentMap T.toRingEquiv σ i
      map_one' := componentMap_map_one hσ i
      map_mul' := componentMap_map_mul
      map_zero' := componentMap_map_zero
      map_add' := componentMap_map_add
      commutes' := fun c => by
        simp only [Algebra.algebraMap_eq_smul_one]
        rw [componentMap_map_smul_of_algEquiv, componentMap_map_one hσ i] }
  have castMap_bij : ∀ i, Function.Bijective (castMap i) :=
    fun i => (reind i).bijective.comp (componentMap_bijective hσ i)
  choose X hX using fun i =>
    skolemNoether_matrix (AlgEquiv.ofBijective (castMap i) (castMap_bij i))
  exact ⟨σ, hDeq, X, fun i M => hX i M⟩

end MainDecomposition

end MPSTensor
