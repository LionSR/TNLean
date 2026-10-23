/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Splitting
import TNLean.Circuit.EntropySupport
import QICLean.Algebra.OperatorSchmidt
import QICLean.Entropy.SupportedMarginalTails

/-!
# A supported operator at the right boundary of a three-region partition

An operator supported disjointly from the first region has an associated
right factor whose operator Schmidt rank is bounded by the square of the
configuration dimension of the support inside the middle region. The same
product decomposition at the global middle-region cut is restricted at one
actual first-region configuration. No tensor factor is cancelled.

Supporting locality algebra for AKLV, arXiv:1301.1162v1, Lemma 4.2
(`l:agsp`), lines 646–654, and ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 806–821, and Proposition 5.7
(`prop:Cheby-AGSP-eff`), lines 1324–1332. Physical variable counts,
frequency selection, cut displacement and matrix product operator
constructions are separate assertions.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.Lattice.Sheet

/-- A supported right factor has the sharp support-intersection rank bound.
This is an algebraic auxiliary to the source passages cited in the module
documentation; no positivity, state or positive-dimension premise is imposed. -/
theorem exists_threeSplit_eq_reindex_one_kronecker_rank_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {T E D : Finset ι} (hTE : Disjoint T E) (hDT : Disjoint D T)
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q (D : Set ι)) :
    ∃ V : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
        ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ,
      A.submatrix (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ V).reindex
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm ∧
        operatorSchmidtRank V ≤ q ^ (2 * (D ∩ E).card) := by
  classical
  by_cases hconfig : Nonempty (ι → Fin q)
  · let σ₀ : ι → Fin q := Classical.choice hconfig
    let t₀ : T → Fin q := fun v ↦ σ₀ v
    let e₀ : E → Fin q := fun v ↦ σ₀ v
    have hDTset : Disjoint (D : Set ι) (T : Set ι) := by
      rw [Set.disjoint_left]
      exact fun _ hvD hvT ↦ Finset.disjoint_left.mp hDT hvD hvT
    obtain ⟨V, hV⟩ :=
      exists_threeSplit_eq_reindex_one_kronecker hTE hDTset hA
    let γ : (↥(T ∪ E)ᶜ → Fin q) → ((v : {v // v ∉ E}) → Fin q) :=
      fun u v ↦ (threeSplit q T E hTE).symm ((t₀, e₀), u) v
    have houtside (e : E → Fin q) (u : ↥(T ∪ E)ᶜ → Fin q)
        (v : {v // v ∉ E}) :
        (threeSplit q T E hTE).symm ((t₀, e), u) v = γ u v := by
      dsimp only [γ]
      by_cases hvT : v.val ∈ T
      · rw [threeSplit_symm_apply_of_mem_left hTE t₀ e u hvT,
          threeSplit_symm_apply_of_mem_left hTE t₀ e₀ u hvT]
      · have hvU : v.val ∉ T ∪ E := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hvT, v.property⟩
        rw [threeSplit_symm_apply_of_notMem hTE t₀ e u hvU,
          threeSplit_symm_apply_of_notMem hTE t₀ e₀ u hvU]
    have hcut (e : E → Fin q) (u : ↥(T ∪ E)ᶜ → Fin q) :
        Entropy.cutEquiv (fun _ : ι ↦ q) E
            ((threeSplit q T E hTE).symm ((t₀, e), u)) = (e, γ u) := by
      apply Prod.ext
      · funext v
        change (threeSplit q T E hTE).symm ((t₀, e), u) v = e v
        exact threeSplit_symm_apply_of_mem_right hTE t₀ e u v.property
      · funext v
        change (threeSplit q T E hTE).symm ((t₀, e), u) v = γ u v
        exact houtside e u v
    have hglue (e : E → Fin q) (u : ↥(T ∪ E)ᶜ → Fin q) :
        (Entropy.cutEquiv (fun _ : ι ↦ q) E).symm (e, γ u) =
          (threeSplit q T E hTE).symm ((t₀, e), u) := by
      apply (Entropy.cutEquiv (fun _ : ι ↦ q) E).injective
      rw [Equiv.apply_symm_apply, hcut]
    have hslice (e e' : E → Fin q)
        (u u' : ↥(T ∪ E)ᶜ → Fin q) :
        A ((threeSplit q T E hTE).symm ((t₀, e), u))
            ((threeSplit q T E hTE).symm ((t₀, e'), u')) =
          V (e, u) (e', u') := by
      have hentry := congrFun (congrFun hV ((t₀, e), u)) ((t₀, e'), u')
      change A ((threeSplit q T E hTE).symm ((t₀, e), u))
          ((threeSplit q T E hTE).symm ((t₀, e'), u')) =
        (1 : Matrix (T → Fin q) (T → Fin q) ℂ) t₀ t₀ *
          V (e, u) (e', u') at hentry
      simpa only [Matrix.one_apply_eq, one_mul] using hentry
    have hsupp : Entropy.IsSupportedOn (n := fun _ : ι ↦ q) A D :=
      isSupportedOn_of_mem_supportedOperators hA
    obtain ⟨M, L, R, hM, hdec, _⟩ :=
      hsupp.hasProductDecomposition_inner (B := E) σ₀ (c₀ := ‖A‖) le_rfl
    have hVdec : HasOperatorSchmidtDecomposition V M := by
      refine ⟨L, fun s ↦ (R s).submatrix γ γ, ?_⟩
      ext ⟨e, u⟩ ⟨e', u'⟩
      have hentry := congrFun (congrFun hdec (e, γ u)) (e', γ u')
      change A ((Entropy.cutEquiv (fun _ : ι ↦ q) E).symm (e, γ u))
          ((Entropy.cutEquiv (fun _ : ι ↦ q) E).symm (e', γ u')) = _ at hentry
      rw [hglue e u, hglue e' u', hslice e e' u u'] at hentry
      simpa only [Matrix.sum_apply, Matrix.kronecker_apply,
        Matrix.submatrix_apply] using hentry
    have hcard : Fintype.card (Entropy.InnerConfig (fun _ : ι ↦ q) E D) =
        q ^ (D ∩ E).card := by
      rw [Entropy.card_innerConfig]
      simp only [Finset.prod_const]
    refine ⟨V, hV,
      (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition hVdec).trans ?_⟩
    calc
      M ≤ Fintype.card (Entropy.InnerConfig (fun _ : ι ↦ q) E D) ^ 2 := hM
      _ = q ^ (2 * (D ∩ E).card) := by
        rw [hcard, ← pow_mul, Nat.mul_comm (D ∩ E).card 2]
  · letI : IsEmpty (ι → Fin q) := ⟨fun σ ↦ hconfig ⟨σ⟩⟩
    have hzero : A = 0 := Subsingleton.elim _ _
    refine ⟨0, ?_, ?_⟩
    · simp [hzero]
    · have hrank : operatorSchmidtRank
          (0 : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
            ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ) ≤ 0 :=
        operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
          ⟨Fin.elim0, Fin.elim0, by simp⟩
      exact hrank.trans (Nat.zero_le _)

end TNLean.Lattice.Sheet
