/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.ScalarCommutant
import TNLean.QCA.DisjointSupport

/-!
# Relative commutants of finite-region observable algebras

Inside the observable algebra of a finite region, the commutant of the full matrix algebra on a
complementary subregion is exactly the matrix algebra on the retained subregion. The corresponding
statement in the algebraic local algebra characterizes finite support by commutation with every
observable supported in a disjoint finite region.

These are source-independent finite-dimensional and algebraic-local facts. They are not statements
of Schumacher--Werner.

## Main results

* `SpinChain.mem_range_localInclusion_iff_commute_complement` identifies the finite relative
  commutant.
* `SpinChain.supportedIn_iff_commute_disjoint` characterizes algebraic-local support by
  commutation with all observables having disjoint finite support.
-/

open scoped Kronecker

namespace SpinChain

namespace Config

private lemma splitComplement_snd_eq_iff {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (x y : Config d Γ) :
    (splitEquiv (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) x).2 =
        (splitEquiv (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) y).2 ↔
      restrict h x = restrict h y := by
  constructor
  · intro hxy
    funext i
    exact congrFun hxy ⟨i, Finset.mem_sdiff.mpr ⟨h i.2, by simp [i.2]⟩⟩
  · intro hxy
    funext i
    have hiΛ : (i : ℤ) ∈ Λ := by
      by_contra hi
      exact (Finset.mem_sdiff.mp i.2).2
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp i.2).1, hi⟩)
    exact congrFun hxy ⟨i, hiΛ⟩

private lemma restrict_sdiff_splitEquiv_symm {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (p : Config d Λ × Config d (Γ \ Λ)) :
    restrict (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) ((splitEquiv h).symm p) = p.2 := by
  have hp := congrArg Prod.snd ((splitEquiv h).apply_symm_apply p)
  exact hp

end Config

section Finite

variable {d : ℕ} {Λ Γ : Finset ℤ}

private lemma reindex_localInclusion (h : Λ ⊆ Γ) (A : LocalAlgebra d Λ) :
    CStarMatrix.reindexₐ ℂ ℂ (Config.splitEquiv h) (localInclusion h A) =
      CStarMatrix.leftKroneckerEmbed (n := Config d (Γ \ Λ)) A := by
  rw [localInclusion]
  simp

private lemma reindex_localInclusion_sdiff (h : Λ ⊆ Γ)
    (B : LocalAlgebra d (Γ \ Λ)) :
    CStarMatrix.reindexₐ ℂ ℂ (Config.splitEquiv h)
        (localInclusion (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) B) =
      CStarMatrix.ofMatrix
        (Matrix.rightKroneckerEmbed (m := Config d Λ) (CStarMatrix.ofMatrix.symm B)) := by
  ext p q
  rw [CStarMatrix.reindexₐ_apply]
  change localInclusion (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) B
      ((Config.splitEquiv h).symm p) ((Config.splitEquiv h).symm q) = _
  rw [localInclusion_apply]
  rw [Config.restrict_sdiff_splitEquiv_symm h,
    Config.restrict_sdiff_splitEquiv_symm h]
  simp only [CStarMatrix.ofMatrix_apply, Matrix.rightKroneckerEmbed_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  have hp : Config.restrict h ((Config.splitEquiv h).symm p) = p.1 :=
    congrArg Prod.fst ((Config.splitEquiv h).apply_symm_apply p)
  have hq : Config.restrict h ((Config.splitEquiv h).symm q) = q.1 :=
    congrArg Prod.fst ((Config.splitEquiv h).apply_symm_apply q)
  have heq :
      (Config.splitEquiv (Finset.sdiff_subset : Γ \ Λ ⊆ Γ)
          ((Config.splitEquiv h).symm p)).2 =
        (Config.splitEquiv (Finset.sdiff_subset : Γ \ Λ ⊆ Γ)
          ((Config.splitEquiv h).symm q)).2 ↔ p.1 = q.1 := by
    rw [Config.splitComplement_snd_eq_iff h, hp, hq]
  by_cases hpq : p.1 = q.1
  · have hsnd := heq.mpr hpq
    simp [hpq, hsnd]
  · have hsnd := mt heq.mp hpq
    simp [hpq, hsnd]

/-- In a finite-region observable algebra, the commutant of the full algebra on the complement
of a retained region is exactly the image of the retained-region inclusion.

This is elementary finite tensor-factor infrastructure and is not a separately named theorem of
arXiv:1703.09188 or Schumacher--Werner. -/
theorem mem_range_localInclusion_iff_commute_complement (h : Λ ⊆ Γ)
    (A : LocalAlgebra d Γ) :
    A ∈ Set.range (localInclusion (d := d) h) ↔
      ∀ B : LocalAlgebra d (Γ \ Λ),
        Commute A (localInclusion (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) B) := by
  constructor
  · rintro ⟨AΛ, rfl⟩ B
    rw [commute_iff_eq]
    let e := CStarMatrix.reindexₐ ℂ ℂ (Config.splitEquiv (d := d) h)
    apply e.injective
    rw [map_mul, map_mul]
    have hleft : e.toRingEquiv (localInclusion h AΛ) =
        CStarMatrix.leftKroneckerEmbed (n := Config d (Γ \ Λ)) AΛ :=
      reindex_localInclusion h AΛ
    have hright : e.toRingEquiv
        (localInclusion (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) B) =
        CStarMatrix.ofMatrix
          (Matrix.rightKroneckerEmbed (m := Config d Λ) (CStarMatrix.ofMatrix.symm B)) :=
      reindex_localInclusion_sdiff h B
    rw [hleft, hright]
    apply CStarMatrix.ext
    intro p q
    change ((CStarMatrix.ofMatrix.symm AΛ ⊗ₖ
        (1 : Matrix (Config d (Γ \ Λ)) (Config d (Γ \ Λ)) ℂ)) *
      ((1 : Matrix (Config d Λ) (Config d Λ) ℂ) ⊗ₖ
        CStarMatrix.ofMatrix.symm B)) p q =
      (((1 : Matrix (Config d Λ) (Config d Λ) ℂ) ⊗ₖ
        CStarMatrix.ofMatrix.symm B) *
      (CStarMatrix.ofMatrix.symm AΛ ⊗ₖ
        (1 : Matrix (Config d (Γ \ Λ)) (Config d (Γ \ Λ)) ℂ))) p q
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  · intro hcomm
    let e := CStarMatrix.reindexₐ ℂ ℂ (Config.splitEquiv (d := d) h)
    let C : Matrix (Config d Λ × Config d (Γ \ Λ))
        (Config d Λ × Config d (Γ \ Λ)) ℂ := CStarMatrix.ofMatrix.symm (e A)
    have hC (B : Matrix (Config d (Γ \ Λ)) (Config d (Γ \ Λ)) ℂ) :
        ((1 : Matrix (Config d Λ) (Config d Λ) ℂ) ⊗ₖ B) * C =
          C * ((1 : Matrix (Config d Λ) (Config d Λ) ℂ) ⊗ₖ B) := by
      let B' : LocalAlgebra d (Γ \ Λ) := CStarMatrix.ofMatrix B
      have hmapped := (hcomm B').map e
      rw [reindex_localInclusion_sdiff] at hmapped
      exact hmapped.eq.symm
    obtain ⟨AΛ, hAΛ⟩ :=
      Matrix.exists_eq_kronecker_one_of_intertwines_span_eq_top
        (A := fun B : Matrix (Config d (Γ \ Λ)) (Config d (Γ \ Λ)) ℂ => B)
        (C := C)
        (by rw [Set.range_id', Submodule.span_univ])
        hC
    refine ⟨CStarMatrix.ofMatrix AΛ, ?_⟩
    apply e.injective
    change CStarMatrix.reindexₐ ℂ ℂ (Config.splitEquiv h)
        (localInclusion h (CStarMatrix.ofMatrix AΛ)) = e A
    rw [reindex_localInclusion]
    exact congrArg CStarMatrix.ofMatrix hAΛ.symm

end Finite

section Algebraic

variable {d : ℕ} [NeZero d] {x : AlgebraicLocalAlgebra d} {Λ : Finset ℤ}

/-- An algebraic-local observable is supported in a finite region exactly when it commutes with
every algebraic-local observable supported in a disjoint finite region.

This is an algebraic-local consequence of the finite relative-commutant theorem. It is not stated
by Schumacher--Werner. Their Theorem 6 gives the generalized Margolus structure, and Corollary 7
says that the inverse of a nearest-neighbor QCA exists and is a nearest-neighbor QCA. -/
theorem supportedIn_iff_commute_disjoint :
    SupportedIn x Λ ↔
      ∀ Γ, Disjoint Γ Λ →
        ∀ y, SupportedIn y Γ → Commute x y := by
  constructor
  · intro hx Γ hΓΛ y hy
    exact hx.commute_of_disjoint hy hΓΛ.symm
  · intro hcomm
    obtain ⟨Δ, AΔ, rfl⟩ := exists_supportedIn x
    let A := localInclusion (d := d) (Finset.subset_union_right : Δ ⊆ Λ ∪ Δ) AΔ
    have hA : localObservable d (Λ ∪ Δ) A = localObservable d Δ AΔ :=
      localObservable_localInclusion d Finset.subset_union_right AΔ
    rw [← hA] at hcomm ⊢
    let hΛ : Λ ⊆ Λ ∪ Δ := Finset.subset_union_left
    rw [show SupportedIn (localObservable d (Λ ∪ Δ) A) Λ ↔
        A ∈ Set.range (localInclusion (d := d) hΛ) by
      constructor
      · rintro ⟨AΛ, hAΛ⟩
        refine ⟨AΛ, (localObservable_injective d (Λ ∪ Δ)) ?_⟩
        rw [localObservable_localInclusion]
        exact hAΛ
      · rintro ⟨AΛ, hAΛ⟩
        refine ⟨AΛ, ?_⟩
        rw [← hAΛ, localObservable_localInclusion]]
    rw [mem_range_localInclusion_iff_commute_complement]
    intro B
    rw [commute_iff_eq]
    apply localObservable_injective d (Λ ∪ Δ)
    rw [map_mul, map_mul]
    have hB := localObservable_localInclusion d
      (Finset.sdiff_subset : (Λ ∪ Δ) \ Λ ⊆ Λ ∪ Δ) B
    rw [hB]
    exact (hcomm ((Λ ∪ Δ) \ Λ) Finset.sdiff_disjoint
      (localObservable d ((Λ ∪ Δ) \ Λ) B) ⟨B, rfl⟩).eq

end Algebraic

end SpinChain
