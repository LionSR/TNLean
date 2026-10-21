/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SitewiseTensorSupport
import TNLean.Lattice.RegionalSwap
import TNLean.Lattice.SiteRelabelEntropy

/-!
# Two replicas as paired sites, and the exchange of replicas on a region

Two replicas of a finite set `ι` of sites are the sites `ι ⊕ ι`, and their configurations are
the paired configurations of local dimension `q * q`. An operator on paired sites acts on both
replicas of the same sites. The regional swap `F_R` of the two replicas reads the doubled vector
`Ω ⊗ Ω` through the exchange of the replicas on `R`, so in `F_R (Ω ⊗ Ω)` a core inside `R` and
a core disjoint from `R` come from different replicas and have no mutual information. Nothing
here depends on a geometry of the sites.

## Main statements

* `QuantumCircuit.reindex_sumArrow_sitePair_embedOp`,
  `QuantumCircuit.reindex_sumArrow_sitePair_mem_supportedOperators`: an operator on paired
  sites acts on both replicas of the same sites.
* `TNLean.Lattice.sheetSwapOp_mulVec_comp_sumArrow`: the exchanged vector relabels the
  replicas.
* `TNLean.Lattice.mutualInformation_relabelSites_replicaSwap_eq_zero`: the cores of the
  exchanged vector are uncorrelated.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 355–365,
  416–424 and 597–616. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace QuantumCircuit

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

/-- The configurations of two replicas of the sites `ι`, as paired configurations. -/
def sumArrowSitePair (ι : Type*) (q : ℕ) : (ι ⊕ ι → Fin q) ≃ (ι → Fin (q * q)) :=
  (Equiv.sumArrowEquivProdArrow ι ι (Fin q)).trans (sitePairConfigurationEquiv ι q q)

omit [Fintype ι] [DecidableEq ι] in
theorem sumArrowSitePair_apply (q : ℕ) (x : ι ⊕ ι → Fin q) (i : ι) :
    sumArrowSitePair ι q x i = finProdFinEquiv (x (Sum.inl i), x (Sum.inr i)) :=
  rfl

/-- An operator placed on paired sites along `e` is the operator placed on both replicas
along `e ⊕ e`. -/
theorem reindex_sumArrow_sitePair_embedOp (q : ℕ) (e : κ → ι)
    (X : Matrix (κ → Fin (q * q)) (κ → Fin (q * q)) ℂ) :
    reindex (sumArrowSitePair ι q).symm (sumArrowSitePair ι q).symm (embedOp e X) =
      embedOp (Sum.map e e)
        (reindex (sumArrowSitePair κ q).symm (sumArrowSitePair κ q).symm X) := by
  ext x y
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, embedOp_apply]
  have hcomp (z : ι ⊕ ι → Fin q) :
      sumArrowSitePair ι q z ∘ e = sumArrowSitePair κ q (z ∘ Sum.map e e) := rfl
  have hagree : AgreeOff e (sumArrowSitePair ι q x) (sumArrowSitePair ι q y) ↔
      AgreeOff (Sum.map e e) x y := by
    constructor
    · intro h i hi
      rcases i with i | i
      · have h' := congrArg finProdFinEquiv.symm
          (h i fun j hj ↦ hi (Sum.inl j) (by simp [hj]))
        simpa [sumArrowSitePair_apply] using congrArg Prod.fst h'
      · have h' := congrArg finProdFinEquiv.symm
          (h i fun j hj ↦ hi (Sum.inr j) (by simp [hj]))
        simpa [sumArrowSitePair_apply] using congrArg Prod.snd h'
    · intro h i hi
      rw [sumArrowSitePair_apply, sumArrowSitePair_apply,
        h (Sum.inl i) (fun j hj ↦ by
          rcases j with j | j
          · exact hi j (Sum.inl_injective hj)
          · simp at hj),
        h (Sum.inr i) (fun j hj ↦ by
          rcases j with j | j
          · simp at hj
          · exact hi j (Sum.inr_injective hj))]
  simp only [hagree, hcomp]

omit [DecidableEq ι] in
/-- **An operator on paired sites acts on both replicas of the same sites.**
Source: `02-information.tex`, lines 416–424 and 597–609. -/
theorem reindex_sumArrow_sitePair_mem_supportedOperators (q : ℕ) {S : Finset ι}
    {A : Matrix (ι → Fin (q * q)) (ι → Fin (q * q)) ℂ}
    (hA : A ∈ supportedOperators (q * q) (S : Set ι)) :
    reindex (sumArrowSitePair ι q).symm (sumArrowSitePair ι q).symm A ∈
      supportedOperators q ((S.disjSum S : Finset (ι ⊕ ι)) : Set (ι ⊕ ι)) := by
  classical
  obtain ⟨A', hA'⟩ := TNLean.Lattice.exists_kronecker_one_of_mem_supportedOperators hA
  have hAeq : A = embedOp (fun x : S ↦ x.val) A' := by
    rw [embedOp_val_eq_kronecker_one_submatrix, ← hA']
    simp
  rw [hAeq, reindex_sumArrow_sitePair_embedOp q Subtype.val]
  have hrange : Set.range (Sum.map (fun x : S ↦ x.val) (fun x : S ↦ x.val)) =
      ((S.disjSum S : Finset (ι ⊕ ι)) : Set (ι ⊕ ι)) := by
    ext z
    rcases z with z | z <;> simp
  rw [← hrange]
  exact embedOp_mem_supportedOperators (Sum.map_injective.mpr
    ⟨Subtype.val_injective, Subtype.val_injective⟩) _

/-- Placing along a bijection of sites is the transport of configurations. -/
theorem embedOp_equiv_eq_reindex {q : ℕ} (σ : κ ≃ ι)
    (X : Matrix (κ → Fin q) (κ → Fin q) ℂ) :
    embedOp σ X = reindex (Equiv.arrowCongr σ (Equiv.refl (Fin q)))
      (Equiv.arrowCongr σ (Equiv.refl (Fin q))) X := by
  ext x y
  have hag : AgreeOff σ x y := fun i hi ↦ absurd (σ.apply_symm_apply i) (hi (σ.symm i))
  simp only [embedOp_apply, hag, ite_true]
  rfl

end QuantumCircuit

namespace TNLean.Lattice

section Replicas

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

/-- The exchange of the two replicas at the sites of `R`, as a permutation of `V ⊕ V`. -/
def replicaSwapFun (R : Finset V) : V ⊕ V → V ⊕ V
  | Sum.inl v => if v ∈ R then Sum.inr v else Sum.inl v
  | Sum.inr v => if v ∈ R then Sum.inl v else Sum.inr v

omit [Fintype V] in
theorem replicaSwapFun_involutive (R : Finset V) : Function.Involutive (replicaSwapFun R) := by
  intro x
  rcases x with v | v <;> by_cases hv : v ∈ R <;> simp [replicaSwapFun, hv]

/-- The exchange of the two replicas at the sites of `R`. -/
def replicaSwap (R : Finset V) : Equiv.Perm (V ⊕ V) :=
  (replicaSwapFun_involutive R).toPerm _

omit [Fintype V] [DecidableEq V] in
/-- In the doubled vector, the two replicas carry the product `Ω ⊗ Ω`.
Source: `02-information.tex`, lines 356–360. -/
theorem doubledVector_comp_sumArrow {N : Type*} (t : (V → Fin q) × (V → Fin q) ≃ N)
    (Ω : EuclideanSpace ℂ (V → Fin q)) :
    (fun c ↦ Ω (t.symm c).1 * Ω (t.symm c).2) ∘
        ((Equiv.sumArrowEquivProdArrow V V (Fin q)).trans t) =
      WithLp.ofLp (FiniteProduct.sumSitesProduct Ω Ω) := by
  funext x
  simp [FiniteProduct.sumSitesProduct]
  rfl

/-- **The exchanged vector relabels the replicas.** `F_R (Ω ⊗ Ω)` is `Ω ⊗ Ω` read through the
exchange of the replicas on `R`.
Source: `02-information.tex`, lines 356–365 and 612–616. -/
theorem sheetSwapOp_mulVec_comp_sumArrow {N : Type*} [Fintype N]
    (t : (V → Fin q) × (V → Fin q) ≃ N) (R : Finset V) (Ω : EuclideanSpace ℂ (V → Fin q)) :
    (reindex t t (sheetSwapOp q R) *ᵥ
        fun c ↦ Ω (t.symm c).1 * Ω (t.symm c).2) ∘
        ((Equiv.sumArrowEquivProdArrow V V (Fin q)).trans t) =
      WithLp.ofLp (FiniteProduct.relabelSites (replicaSwap R)
        (FiniteProduct.sumSitesProduct Ω Ω)) := by
  funext x
  rw [reindex_apply, submatrix_mulVec_equiv, sheetSwapOp,
    PEquiv.toMatrix_toPEquiv_mulVec]
  have h₁ : (sheetSwap q R (x ∘ Sum.inl, x ∘ Sum.inr)).1 =
      (x ∘ (replicaSwap R).symm) ∘ Sum.inl := by
    funext v
    by_cases hv : v ∈ R <;>
      simp [sheetSwap, replicaSwap, replicaSwapFun, hv]
  have h₂ : (sheetSwap q R (x ∘ Sum.inl, x ∘ Sum.inr)).2 =
      (x ∘ (replicaSwap R).symm) ∘ Sum.inr := by
    funext v
    by_cases hv : v ∈ R <;>
      simp [sheetSwap, replicaSwap, replicaSwapFun, hv]
  simp [FiniteProduct.relabelSites, FiniteProduct.sumSitesProduct, ← h₁, ← h₂]
  rfl

/-- **The cores of the exchanged vector are uncorrelated.** In `F_R (Ω ⊗ Ω)` the core
`R₀ ⊆ R` of the first replica comes from the second replica, and the core `C₀`, disjoint from
`R`, comes from the first replica.
Source: `02-information.tex`, lines 612–616. -/
theorem mutualInformation_relabelSites_replicaSwap_eq_zero {Ω : EuclideanSpace ℂ (V → Fin q)}
    (hΩ : ‖Ω‖ = 1) {R R₀ C₀ : Finset V} (hR₀ : R₀ ⊆ R) (hC₀ : Disjoint C₀ R) :
    FiniteProduct.mutualInformation (fun _ : V ⊕ V ↦ Fin q)
      (FiniteProduct.relabelSites (replicaSwap R) (FiniteProduct.sumSitesProduct Ω Ω))
      (R₀.disjSum ∅) (C₀.disjSum ∅) = 0 := by
  rw [FiniteProduct.mutualInformation_relabelSites]
  have hs : (replicaSwap R).symm = replicaSwap R := Equiv.ext fun _ ↦ rfl
  have hX : (R₀.disjSum (∅ : Finset V)).map (replicaSwap R).toEmbedding =
      (∅ : Finset V).disjSum R₀ := by
    ext z
    rw [Finset.mem_map_equiv, hs]
    rcases z with v | v <;> by_cases hv : v ∈ R
    · simp [replicaSwap, replicaSwapFun, hv]
    · have hv₀ : v ∉ R₀ := fun h ↦ hv (hR₀ h)
      simp [replicaSwap, replicaSwapFun, hv, hv₀]
    · simp [replicaSwap, replicaSwapFun, hv]
    · have hv₀ : v ∉ R₀ := fun h ↦ hv (hR₀ h)
      simp [replicaSwap, replicaSwapFun, hv, hv₀]
  have hJ : (C₀.disjSum (∅ : Finset V)).map (replicaSwap R).toEmbedding =
      C₀.disjSum ∅ := by
    ext z
    rw [Finset.mem_map_equiv, hs]
    rcases z with v | v <;> by_cases hv : v ∈ R <;>
      simp [replicaSwap, replicaSwapFun, hv, Finset.disjoint_right.mp hC₀]
  rw [hX, hJ]
  exact FiniteProduct.mutualInformation_sumSitesProduct_inr_inl hΩ hΩ R₀ C₀

end Replicas

end TNLean.Lattice
