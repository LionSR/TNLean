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
# A supported left factor at a three-region partition

An operator supported in T ∪ E has a factor B on T × E in the three-region
coordinates. Its operator Schmidt rank is bounded using the existing global
T-cut matrix-unit decomposition, restricted at one actual configuration of U.
No identity on an empty spectator space is cancelled.

This is supporting locality algebra for AKLV, arXiv:1301.1162v1, Lemma 4.2
(l:agsp), lines 646–654, and ALVV, arXiv:1602.08828v2, eq:H-mid-cut,
lines 810–821, and prop:Cheby-AGSP-eff, lines 1324–1332. It does not
assert the physical coefficient identifications, frequency counts, cut movement,
or matrix product operator construction in those passages.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.Lattice.Sheet

/-- A supported left factor has the sharp support-intersection rank bound.
This is an algebraic auxiliary to the passages cited above; it assumes no state,
positivity, or positive local dimension. -/
theorem exists_threeSplit_eq_kronecker_one_rank_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {T E D : Finset ι} (hTE : Disjoint T E) (hD : D ⊆ T ∪ E)
    {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q (D : Set ι)) :
    ∃ B : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ,
      A.submatrix (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
        B ⊗ₖ (1 : Matrix (↥(T ∪ E)ᶜ → Fin q)
          (↥(T ∪ E)ᶜ → Fin q) ℂ) ∧
      operatorSchmidtRank B ≤ q ^ (2 * (D ∩ T).card) := by
  classical
  by_cases hconfig : Nonempty (ι → Fin q)
  · let σ₀ : ι → Fin q := Classical.choice hconfig
    let t₀ : T → Fin q := fun v ↦ σ₀ v
    let u₀ : ↥(T ∪ E)ᶜ → Fin q := fun v ↦ σ₀ v
    have hDset : (D : Set ι) ⊆ (↑(T ∪ E) : Set ι) := Finset.coe_subset.mpr hD
    obtain ⟨B, hB⟩ := exists_threeSplit_eq_kronecker_one hTE
      (supportedOperators_mono hDset hA)
    let γ : (E → Fin q) → ((v : {v // v ∉ T}) → Fin q) :=
      fun e v ↦ (threeSplit q T E hTE).symm ((t₀, e), u₀) v
    have houtside (t : T → Fin q) (e : E → Fin q)
        (v : {v // v ∉ T}) :
        (threeSplit q T E hTE).symm ((t, e), u₀) v = γ e v := by
      dsimp only [γ]
      by_cases hvE : v.val ∈ E
      · rw [threeSplit_symm_apply_of_mem_right hTE t e u₀ hvE,
          threeSplit_symm_apply_of_mem_right hTE t₀ e u₀ hvE]
      · have hvU : v.val ∉ T ∪ E := by
          simp only [Finset.mem_union, not_or]
          exact ⟨v.property, hvE⟩
        rw [threeSplit_symm_apply_of_notMem hTE t e u₀ hvU,
          threeSplit_symm_apply_of_notMem hTE t₀ e u₀ hvU]
    have hcut (t : T → Fin q) (e : E → Fin q) :
        Entropy.cutEquiv (fun _ : ι ↦ q) T
            ((threeSplit q T E hTE).symm ((t, e), u₀)) = (t, γ e) := by
      apply Prod.ext
      · funext v
        change (threeSplit q T E hTE).symm ((t, e), u₀) v = t v
        exact threeSplit_symm_apply_of_mem_left hTE t e u₀ v.property
      · funext v
        change (threeSplit q T E hTE).symm ((t, e), u₀) v = γ e v
        exact houtside t e v
    have hglue (t : T → Fin q) (e : E → Fin q) :
        (Entropy.cutEquiv (fun _ : ι ↦ q) T).symm (t, γ e) =
          (threeSplit q T E hTE).symm ((t, e), u₀) := by
      apply (Entropy.cutEquiv (fun _ : ι ↦ q) T).injective
      rw [Equiv.apply_symm_apply, hcut]
    have hslice (t t' : T → Fin q) (e e' : E → Fin q) :
        A ((threeSplit q T E hTE).symm ((t, e), u₀))
            ((threeSplit q T E hTE).symm ((t', e'), u₀)) =
          B (t, e) (t', e') := by
      have hentry := congrFun (congrFun hB ((t, e), u₀)) ((t', e'), u₀)
      change A ((threeSplit q T E hTE).symm ((t, e), u₀))
          ((threeSplit q T E hTE).symm ((t', e'), u₀)) =
        B (t, e) (t', e') *
          (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) u₀ u₀ at hentry
      simpa only [Matrix.one_apply_eq, mul_one] using hentry
    have hsupp : Entropy.IsSupportedOn (n := fun _ : ι ↦ q) A D :=
      isSupportedOn_of_mem_supportedOperators hA
    obtain ⟨M, L, R, hM, hdec, _⟩ :=
      hsupp.hasProductDecomposition_inner (B := T) σ₀ (c₀ := ‖A‖) le_rfl
    have hBdec : HasOperatorSchmidtDecomposition B M := by
      refine ⟨L, fun s ↦ (R s).submatrix γ γ, ?_⟩
      ext ⟨t, e⟩ ⟨t', e'⟩
      have hentry := congrFun (congrFun hdec (t, γ e)) (t', γ e')
      change A ((Entropy.cutEquiv (fun _ : ι ↦ q) T).symm (t, γ e))
          ((Entropy.cutEquiv (fun _ : ι ↦ q) T).symm (t', γ e')) = _ at hentry
      rw [hglue t e, hglue t' e', hslice t t' e e'] at hentry
      simpa only [Matrix.sum_apply, Matrix.kronecker_apply,
        Matrix.submatrix_apply] using hentry
    have hcard : Fintype.card (Entropy.InnerConfig (fun _ : ι ↦ q) T D) =
        q ^ (D ∩ T).card := by
      rw [Entropy.card_innerConfig]
      simp only [Finset.prod_const]
    refine ⟨B, hB,
      (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition hBdec).trans ?_⟩
    calc
      M ≤ Fintype.card (Entropy.InnerConfig (fun _ : ι ↦ q) T D) ^ 2 := hM
      _ = q ^ (2 * (D ∩ T).card) := by
        rw [hcard, ← pow_mul, Nat.mul_comm (D ∩ T).card 2]
  · let : IsEmpty (ι → Fin q) := ⟨fun σ ↦ hconfig ⟨σ⟩⟩
    have hzero : A = 0 := Subsingleton.elim _ _
    refine ⟨0, ?_, ?_⟩
    · simp [hzero]
    · have hrank : operatorSchmidtRank
          (0 : Matrix ((T → Fin q) × (E → Fin q))
            ((T → Fin q) × (E → Fin q)) ℂ) ≤ 0 :=
        operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
          ⟨Fin.elim0, Fin.elim0, by simp⟩
      exact hrank.trans (Nat.zero_le _)

end TNLean.Lattice.Sheet
