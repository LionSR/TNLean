/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import QICLean.Algebra.OperatorSchmidt.PrescribedFactors
import QICLean.Algebra.OperatorSchmidt.Realignment
import QICLean.Algebra.OperatorSchmidt.Reindex
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.ManyBody.Sites.Placement
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector

/-!
# Matrix-entry slices over the complement of a region

Fix two configurations of the complement of a region `J`. The corresponding matrix entries of
an operator `X` on the whole chain form an operator on `J`, its slice. Two facts make slices
the right family for the improving operators of ALVV, arXiv:1602.08828v2, Theorem `t:aisff`,
lines 1580–1609.

* An operator of operator Schmidt rank `N` across `(J, Jᶜ)` is a sum of `N` products whose
  factors on `J` are slices of the operator itself: a basis of the span of all slices can be
  chosen among the slices.
* A slice has, at every cut inside `J`, operator Schmidt rank at most that of `X` at the
  corresponding cut of the whole chain. The bond dimensions of the improving operators of
  `t:aisff`, line 1586, are therefore controlled by the ranks of the filter itself.
-/

open Matrix
open scoped Kronecker

namespace TNLean.MPS.AreaLaw

variable {V : Type*} [DecidableEq V] {q : ℕ}

/-- The matrix entries of `X` between two fixed configurations of the complement of `J`,
viewed as an operator on `J`. -/
def regionalSlice (J : Finset V) (X : Matrix (V → Fin q) (V → Fin q) ℂ)
    (x y : {v // v ∉ J} → Fin q) : Matrix (J → Fin q) (J → Fin q) ℂ :=
  Matrix.of fun σ τ ↦ X ((ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm (σ, x))
      ((ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm (τ, y))

/-- **Slice decomposition.** An operator of operator Schmidt rank `N` across `(J, Jᶜ)` is a sum
of `N` products whose factors on `J` are slices of the operator. This is the decomposition
`K = ∑ A_i ⊗ B_i` behind the improving family of ALVV, arXiv:1602.08828v2, Theorem `t:aisff`,
lines 1606–1607, with every `A_i` chosen among the slices of `K`. -/
theorem exists_regionalSlice_decomposition [Finite V] (J : Finset V)
    (X : Matrix (V → Fin q) (V → Fin q) ℂ) :
    ∃ (N : ℕ) (e : Fin N → ({v // v ∉ J} → Fin q) × ({v // v ∉ J} → Fin q))
      (M : Fin N → Matrix ({v // v ∉ J} → Fin q) ({v // v ∉ J} → Fin q) ℂ),
      N = operatorSchmidtRank
          (X.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) J) (ManyBody.cutEquiv (fun _ ↦ Fin q) J)) ∧
      X = (∑ r, M r ⊗ₖ regionalSlice J X (e r).1 (e r).2).submatrix
        ((ManyBody.cutEquiv (fun _ ↦ Fin q) J).trans (Equiv.prodComm _ _))
        ((ManyBody.cutEquiv (fun _ ↦ Fin q) J).trans (Equiv.prodComm _ _)) := by
  classical
  have := Fintype.ofFinite V
  let τ := (ManyBody.cutEquiv (fun _ ↦ Fin q) J).trans
      (Equiv.prodComm (J → Fin q) ({v // v ∉ J} → Fin q))
  let ρ : Matrix (({v // v ∉ J} → Fin q) × (J → Fin q))
      (({v // v ∉ J} → Fin q) × (J → Fin q)) ℂ :=
    X.reindex τ τ
  let v : ({v // v ∉ J} → Fin q) × ({v // v ∉ J} → Fin q) →
      Matrix (J → Fin q) (J → Fin q) ℂ :=
    fun ij ↦ operatorBlock ρ ij.1 ij.2
  have hrank : operatorSchmidtRank ρ =
      operatorSchmidtRank (X.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) J)
          (ManyBody.cutEquiv (fun _ ↦ Fin q) J)) :=
    operatorSchmidtRank_reindex_prodComm
        (X.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) J) (ManyBody.cutEquiv (fun _ ↦ Fin q) J))
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ v
  have : Finite κ := hli.finite
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = operatorSchmidtRank ρ := by
    rw [operatorSchmidtRank_eq_finrank_operatorBlockSpan, ← finrank_span_eq_card hli, hspan]
    rfl
  let eq := Fintype.equivFin κ
  obtain ⟨M, hM⟩ := exists_left_factors_of_operatorBlock_mem_span ρ ((v ∘ a) ∘ eq.symm)
    fun i j ↦ by
      rw [EquivLike.range_comp, hspan]
      exact Submodule.subset_span ⟨(i, j), rfl⟩
  refine ⟨Fintype.card κ, fun r ↦ a (eq.symm r), M, hcard.trans hrank, ?_⟩
  calc X = ρ.submatrix τ τ := by ext z z'; simp [ρ]
    _ = _ := by rw [hM]; rfl

/-- **Slices keep interior ranks.** At every cut of `J`, a slice of `X` has operator Schmidt
rank at most that of `X` at the corresponding cut of the whole chain. Supporting the
bond-dimension clause of ALVV, arXiv:1602.08828v2, Theorem `t:aisff`, line 1586: the minimal
open-boundary matrix product operator bond dimension at a cut is the operator Schmidt rank. -/
theorem operatorSchmidtRank_regionalSlice_le [Finite V] (J C : Finset V)
    (X : Matrix (V → Fin q) (V → Fin q) ℂ) (x y : {v // v ∉ J} → Fin q) :
    operatorSchmidtRank ((regionalSlice J X x y).reindex
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (Finset.univ.filter fun v : J ↦ (v : V) ∈ C))
        (ManyBody.cutEquiv (fun _ ↦ Fin q) (Finset.univ.filter fun v : J ↦ (v : V) ∈ C))) ≤
      operatorSchmidtRank (X.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) C)
          (ManyBody.cutEquiv (fun _ ↦ Fin q) C)) := by
  classical
  have := Fintype.ofFinite V
  set C' : Finset ↥J := Finset.univ.filter fun v : J ↦ (v : V) ∈ C with hC'
  obtain ⟨A, B, hX⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank
    (X.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) C) (ManyBody.cutEquiv (fun _ ↦ Fin q) C))
  have hL (c : ↥C) (hc : (c : V) ∈ J) : (⟨c, hc⟩ : ↥J) ∈ C' := by
    simp [hC', c.2]
  have hR (c : {v // v ∉ C}) (hc : (c : V) ∈ J) : (⟨c, hc⟩ : ↥J) ∉ C' := by
    simpa [hC'] using c.2
  let fL : ({v // v ∉ J} → Fin q) → (↥C' → Fin q) → (↥C → Fin q) := fun z α c ↦
    if hc : (c : V) ∈ J then α ⟨⟨c, hc⟩, hL c hc⟩ else z ⟨c, hc⟩
  let fR : ({v // v ∉ J} → Fin q) → ({v // v ∉ C'} → Fin q) → ({v // v ∉ C} → Fin q) :=
    fun z β c ↦ if hc : (c : V) ∈ J then β ⟨⟨c, hc⟩, hR c hc⟩ else z ⟨c, hc⟩
  have hsplit (z : {v // v ∉ J} → Fin q) (α : ↥C' → Fin q) (β : {v // v ∉ C'} → Fin q) :
      ManyBody.cutEquiv (fun _ ↦ Fin q) C
          ((ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm
          ((ManyBody.cutEquiv (fun _ ↦ Fin q) C').symm (α, β), z)) =
        (fL z α, fR z β) := by
    refine Prod.ext (funext fun c ↦ ?_) (funext fun c ↦ ?_)
    · simp only [Equiv.piEquivPiSubtypeProd_apply]
      by_cases hc : (c : V) ∈ J
      · rw [ManyBody.cutEquiv_symm_apply_mem _ _ hc,
          ManyBody.cutEquiv_symm_apply_mem _ _ (hL c hc)]
        simp [fL, hc]
      · rw [ManyBody.cutEquiv_symm_apply_not_mem _ _ hc]
        simp [fL, hc]
    · simp only [Equiv.piEquivPiSubtypeProd_apply]
      by_cases hc : (c : V) ∈ J
      · rw [ManyBody.cutEquiv_symm_apply_mem _ _ hc,
          ManyBody.cutEquiv_symm_apply_not_mem _ _ (hR c hc)]
        simp [fR, hc]
      · rw [ManyBody.cutEquiv_symm_apply_not_mem _ _ hc]
        simp [fR, hc]
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨fun t ↦ Matrix.of fun α α' ↦ A t (fL x α) (fL y α'),
    fun t ↦ Matrix.of fun β β' ↦ B t (fR x β) (fR y β'), ?_⟩
  ext ⟨α, β⟩ ⟨α', β'⟩
  have hentry : X ((ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm
      ((ManyBody.cutEquiv (fun _ ↦ Fin q) C').symm (α, β), x))
      ((ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm
          ((ManyBody.cutEquiv (fun _ ↦ Fin q) C').symm (α', β'), y)) =
      (X.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) C) (ManyBody.cutEquiv (fun _ ↦ Fin q) C))
          (fL x α, fR x β) (fL y α', fR y β') := by
    rw [← hsplit x α β, ← hsplit y α' β']
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rw [hX] at hentry
  simp only [reindex_apply, submatrix_apply, regionalSlice, of_apply, hentry,
    Matrix.sum_apply, kroneckerMap_apply]

/-- Every bipartite operator has operator Schmidt rank at most the square of the dimension of
its first factor. -/
theorem operatorSchmidtRank_le_card_sq {m n : Type*} [Fintype m] [Finite n]
    (ρ : Matrix (m × n) (m × n) ℂ) : operatorSchmidtRank ρ ≤ Fintype.card m ^ 2 := by
  simpa only [Fintype.card_prod, sq] using operatorSchmidtRank_le_card_of_blocks_mem_span ρ
    (fun ij : m × m ↦ operatorBlock ρ ij.1 ij.2)
    (fun i j ↦ Submodule.subset_span ⟨(i, j), rfl⟩)

/-- The cut coordinates of `ManyBody.cutOperator` and of `sheetSplit` give the same operator
Schmidt rank. -/
theorem operatorSchmidtRank_cutOperator_eq [Finite V] (B : Finset V)
    (X : Matrix (V → Fin q) (V → Fin q) ℂ) :
    operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q) B X) =
      operatorSchmidtRank (X.reindex (ManyBody.cutEquiv (fun _ ↦ Fin q) B)
          (ManyBody.cutEquiv (fun _ ↦ Fin q) B)) := by
  have := Fintype.ofFinite V
  rfl

end TNLean.MPS.AreaLaw
