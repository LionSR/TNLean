/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Chain.Basic
import TNLean.PEPS.AreaLaw.Chain.OpenMPS
import TNLean.PEPS.AreaLaw.RegionalEntropyBridge
import QICLean.Analysis.SurprisalMoment

/-!
# Transport between the chain domain and the sites `Fin L`

The chain of `L` sites is a lattice domain, whose configurations are indexed by its
sites, while the open-boundary matrix product state development indexes configurations
by `Fin L`. The order-preserving enumeration of the chain sites relabels one state space
onto the other by a linear isometry, carries the left block of the first `k` sites onto
the initial interval of the chain, and identifies the regional states, regional entropies
and surprisal tails of the two pictures.

## Main definitions

* `chainTransport L q`: the relabeling of a chain state along the enumeration of sites.
* `leftBlockSiteEquiv L k`: the left block of `k` sites as the initial interval.
* `leftBlockConfigEquiv L q k`: the induced relabeling of regional configurations.

## Main results

* `regionState_chainTransport`: the regional state of the transported vector on a left
  block is the reindexed reduced state of the chain on the initial interval.
* `regionEntropy_chainTransport`, `surprisalTail_chainTransport`: the regional entropy
  and surprisal tail agree.
* `Matrix.IsHermitian.sum_eigenvalues_reindex`: a sum of a function of the eigenvalues of
  a Hermitian matrix is invariant under reindexing.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), Section 7, Theorem B.
-/

open Matrix

namespace Matrix.IsHermitian

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A sum of a function of the eigenvalues of a Hermitian matrix is the corresponding sum
over the roots of its characteristic polynomial. -/
theorem sum_eigenvalues_eq_roots_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hA.eigenvalues i) = (A.charpoly.roots.map fun z : ℂ ↦ g z.re).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- A sum of a function of the eigenvalues of a Hermitian matrix is invariant under
reindexing. -/
theorem sum_eigenvalues_reindex {A : Matrix n n ℂ} (hA : A.IsHermitian) (e : n ≃ m)
    (g : ℝ → ℝ) :
    ∑ i, g ((hA.reindex e).eigenvalues i) = ∑ i, g (hA.eigenvalues i) := by
  rw [sum_eigenvalues_eq_roots_sum, sum_eigenvalues_eq_roots_sum, charpoly_reindex]

/-- Sums of a function of the eigenvalues of equal Hermitian matrices agree. -/
theorem sum_eigenvalues_congr {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) (g : ℝ → ℝ) : ∑ i, g (hA.eigenvalues i) = ∑ i, g (hB.eigenvalues i) := by
  subst h
  rfl

end Matrix.IsHermitian

namespace TNLean.PEPS.AreaLaw.Chain

/-- The relabeling of configurations of the chain of `L` sites along the enumeration of
its sites. -/
noncomputable def chainConfigEquiv (L q : ℕ) :
    Configuration (chainDomain L) q ≃ (Fin L → Fin q) :=
  Equiv.arrowCongr (chainSiteEquiv L).symm (Equiv.refl _)

/-- The relabeling of a chain state onto a vector on `L` sites, as a linear isometry. -/
noncomputable def chainTransport (L q : ℕ) :
    StateSpace (chainDomain L) q ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (chainConfigEquiv L q)

/-- The transported vector at a configuration on `Fin L`. -/
@[simp]
theorem chainTransport_apply {L q : ℕ} (Ω : StateSpace (chainDomain L) q) (x : Fin L → Fin q) :
    chainTransport L q Ω x = Ω (x ∘ (chainSiteEquiv L).symm) :=
  rfl

/-- The inverse transport at a chain configuration. -/
@[simp]
theorem chainTransport_symm_apply {L q : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (σ : Configuration (chainDomain L) q) :
    (chainTransport L q).symm ψ σ = ψ (σ ∘ chainSiteEquiv L) := by
  rw [chainTransport, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- The left block of `k` sites corresponds to the initial interval `[0, k - 1]`. -/
theorem chainSiteEquiv_mem_leftBlock_iff {L : ℕ} (k : ℕ) (i : Fin L) :
    chainSiteEquiv L i ∈ interval (chainDomain L) 0 ((k : ℤ) - 1) ↔ i ∈ leftBlock L k := by
  simp only [mem_interval, chainSiteEquiv_apply_fst, mem_leftBlock]
  omega

/-- The sites of the left block of `k` sites as the sites of the initial interval. -/
noncomputable def leftBlockSiteEquiv (L k : ℕ) :
    {i : Fin L // i ∈ leftBlock L k} ≃
      {x : Site (chainDomain L) // x ∈ interval (chainDomain L) 0 ((k : ℤ) - 1)} :=
  Equiv.subtypeEquiv (chainSiteEquiv L) fun i ↦ (chainSiteEquiv_mem_leftBlock_iff k i).symm

/-- The sites outside the left block of `k` sites as the sites outside the initial
interval. -/
noncomputable def leftBlockComplementSiteEquiv (L k : ℕ) :
    {i : Fin L // i ∉ leftBlock L k} ≃
      {x : Site (chainDomain L) // x ∉ interval (chainDomain L) 0 ((k : ℤ) - 1)} :=
  Equiv.subtypeEquiv (chainSiteEquiv L) fun i ↦
    not_congr (chainSiteEquiv_mem_leftBlock_iff k i).symm

/-- The relabeling of configurations of the left block of `k` sites onto configurations
of the initial interval. -/
noncomputable def leftBlockConfigEquiv (L q k : ℕ) :
    ((i : {i : Fin L // i ∈ leftBlock L k}) → Fin q) ≃
      ({x : Site (chainDomain L) // x ∈ interval (chainDomain L) 0 ((k : ℤ) - 1)} → Fin q) :=
  Equiv.arrowCongr (leftBlockSiteEquiv L k) (Equiv.refl _)

/-- The relabeling of configurations outside the left block of `k` sites onto
configurations outside the initial interval. -/
noncomputable def leftBlockComplementConfigEquiv (L q k : ℕ) :
    ((i : {i : Fin L // i ∉ leftBlock L k}) → Fin q) ≃
      ({x : Site (chainDomain L) // x ∉ interval (chainDomain L) 0 ((k : ℤ) - 1)} → Fin q) :=
  Equiv.arrowCongr (leftBlockComplementSiteEquiv L k) (Equiv.refl _)

/-- A configuration glued from its parts on the left block and its complement, read on
the chain, is the configuration glued from the relabeled parts. -/
theorem cutEquiv_symm_comp_chainSiteEquiv_symm {L q : ℕ} (k : ℕ)
    (a : (i : {i : Fin L // i ∈ leftBlock L k}) → Fin q)
    (c : (i : {i : Fin L // i ∉ leftBlock L k}) → Fin q) :
    (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm (a, c) ∘
        (chainSiteEquiv L).symm =
      (configurationSplit (chainDomain L) q (interval (chainDomain L) 0 ((k : ℤ) - 1))).symm
        (leftBlockConfigEquiv L q k a, leftBlockComplementConfigEquiv L q k c) := by
  funext v
  obtain ⟨i, rfl⟩ := (chainSiteEquiv L).surjective v
  rw [Function.comp_apply, Equiv.symm_apply_apply]
  by_cases hi : i ∈ leftBlock L k
  · have hv := (chainSiteEquiv_mem_leftBlock_iff k i).mpr hi
    rw [Entropy.cutEquiv_symm_apply_mem _ _ hi]
    simp [configurationSplit, Equiv.piEquivPiSubtypeProd, hv, leftBlockConfigEquiv,
      leftBlockSiteEquiv]
  · have hv := (not_congr (chainSiteEquiv_mem_leftBlock_iff k i)).mpr hi
    rw [Entropy.cutEquiv_symm_apply_not_mem _ _ hi]
    simp [configurationSplit, Equiv.piEquivPiSubtypeProd, hv, leftBlockComplementConfigEquiv,
      leftBlockComplementSiteEquiv]

/-- The regional state of the transported vector on the left block of `k` sites is the
reduced state of the chain on the initial interval, reindexed along the relabeling of
configurations. -/
theorem regionState_chainTransport {L q : ℕ} (Ω : StateSpace (chainDomain L) q) (k : ℕ) :
    Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) (chainTransport L q Ω) =
      Matrix.reindex (leftBlockConfigEquiv L q k).symm (leftBlockConfigEquiv L q k).symm
        (reducedState (chainDomain L) q Ω (interval (chainDomain L) 0 ((k : ℤ) - 1))) := by
  ext a b
  simp only [Entropy.regionState, reducedState, Matrix.reindex_apply, Matrix.submatrix_apply,
    partialTraceRight_apply, vecMulVec_apply, Equiv.symm_symm, Pi.star_apply]
  refine Fintype.sum_equiv (leftBlockComplementConfigEquiv L q k) _ _ fun c ↦ ?_
  simp only [chainTransport_apply, cutEquiv_symm_comp_chainSiteEquiv_symm]

/-- The regional entropy of the transported vector on the left block of `k` sites is the
regional entropy of the chain on the initial interval. -/
theorem regionEntropy_chainTransport {L q : ℕ} (Ω : StateSpace (chainDomain L) q) (k : ℕ) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) (chainTransport L q Ω) =
      regionalEntropy (chainDomain L) q Ω (interval (chainDomain L) 0 ((k : ℤ) - 1)) := by
  rw [Entropy.regionEntropy, regionalEntropy,
    vonNeumannEntropy_congr (regionState_chainTransport Ω k) _
      ((reducedState_isHermitian _ _ _ _).reindex _)]
  exact vonNeumannEntropy_submatrix_equiv _ _ _

/-- The surprisal tail of the regional state of the transported vector on the left block
of `k` sites is that of the reduced state of the chain on the initial interval. -/
theorem surprisalTail_chainTransport {L q : ℕ} (Ω : StateSpace (chainDomain L) q) (k : ℕ)
    (S w : ℝ) :
    Entropy.surprisalTail
        (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
          (chainTransport L q Ω)).eigenvalues S w =
      Entropy.surprisalTail
        (reducedState_isHermitian (chainDomain L) q Ω
          (interval (chainDomain L) 0 ((k : ℤ) - 1))).eigenvalues S w := by
  unfold Entropy.surprisalTail
  exact (Matrix.IsHermitian.sum_eigenvalues_congr _
    ((reducedState_isHermitian _ _ _ _).reindex (leftBlockConfigEquiv L q k).symm)
    (regionState_chainTransport Ω k) fun p ↦ if w < |-Real.log p - S| then p else 0).trans
    (Matrix.IsHermitian.sum_eigenvalues_reindex (reducedState_isHermitian _ _ _ _)
      (leftBlockConfigEquiv L q k).symm fun p ↦ if w < |-Real.log p - S| then p else 0)

end TNLean.PEPS.AreaLaw.Chain
