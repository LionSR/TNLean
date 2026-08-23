/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.Blocking
import TNLean.QCA.LocalNorm

/-!
# Blocking algebraic-local observables

Finite-region site blocking commutes with the canonical identity-tensor inclusions.  It therefore
extends from finite local algebras to an equivalence of algebraic local algebras.  For the reverse
map, an arbitrary original region is enlarged to the expansion of its finite block hull; an
original region need not itself be the expansion of a blocked region.

This file concerns the algebraic local algebra only.  It does not extend blocking to the
quasi-local completion or transport translations, propagation conditions, or quantum cellular
automata.

## Main definitions

* `SpinChain.blockHull` — the finite set of blocks meeting an original finite region.
* `SpinChain.algebraicLocalBlocking` — site blocking as an algebraic-local star-algebra
  equivalence.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2308 and
  2313--2320.
-/

open scoped ComplexOrder

namespace SpinChain

attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

/-- The finite set of blocks that meet an original finite region. -/
def blockHull (L : ℕ) [NeZero L] (Δ : Finset ℤ) : Finset ℤ :=
  Δ.image fun z ↦ (Int.divModEquiv L z).1

/-- An original region is contained in the expansion of its block hull. -/
lemma subset_expandedRegion_blockHull (L : ℕ) [NeZero L] (Δ : Finset ℤ) :
    Δ ⊆ expandedRegion L (blockHull L Δ) := by
  intro z hz
  rw [mem_expandedRegion]
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

/-- Taking the block hull is monotone. -/
lemma blockHull_mono {L : ℕ} [NeZero L] {Δ Θ : Finset ℤ} (h : Δ ⊆ Θ) :
    blockHull L Δ ⊆ blockHull L Θ :=
  Finset.image_mono _ h

/-- The block hull of an expanded blocked region is the original blocked region. -/
@[simp]
lemma blockHull_expandedRegion (L : ℕ) [NeZero L] (Λ : Finset ℤ) :
    blockHull L (expandedRegion L Λ) = Λ := by
  ext x
  simp only [blockHull, Finset.mem_image, mem_expandedRegion]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    refine ⟨(Int.divModEquiv L).symm (x, 0), ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using hx
    · exact congrArg Prod.fst ((Int.divModEquiv L).apply_symm_apply (x, 0))

private lemma restrict_blocking_symm {d L : ℕ} [NeZero L] {Λ Γ : Finset ℤ}
    (h : Λ ⊆ Γ) (x : Config d (expandedRegion L Γ)) :
    Config.restrict h ((Config.blocking d L Γ).symm x) =
      (Config.blocking d L Λ).symm (Config.restrict (expandedRegion_mono h) x) := by
  apply (Config.blocking d L Λ).injective
  simpa only [Equiv.apply_symm_apply] using
    (Config.restrict_blocking h ((Config.blocking d L Γ).symm x)).symm

private lemma blocking_complement_eq_iff {d L : ℕ} [NeZero L] {Λ Γ : Finset ℤ}
    (h : Λ ⊆ Γ) (x y : Config d (expandedRegion L Γ)) :
    (Config.splitEquiv h ((Config.blocking d L Γ).symm x)).2 =
        (Config.splitEquiv h ((Config.blocking d L Γ).symm y)).2 ↔
      (Config.splitEquiv (expandedRegion_mono h) x).2 =
        (Config.splitEquiv (expandedRegion_mono h) y).2 := by
  constructor
  · intro hxy
    funext z
    let q : Γ := ⟨(Int.divModEquiv L z).1,
      (mem_expandedRegion L Γ z).mp (Finset.mem_sdiff.mp z.2).1⟩
    have hq : (q : ℤ) ∉ Λ := by
      intro hqΛ
      exact (Finset.mem_sdiff.mp z.2).2 ((mem_expandedRegion L Λ z).mpr hqΛ)
    have hz := congrFun hxy ⟨q, Finset.mem_sdiff.mpr ⟨q.2, hq⟩⟩
    let zΓ : expandedRegion L Γ := ⟨z, (Finset.mem_sdiff.mp z.2).1⟩
    calc
      x zΓ = Config.blocking d L Γ ((Config.blocking d L Γ).symm x) zΓ := by
        rw [Equiv.apply_symm_apply]
      _ = MPSTensor.decodeBlockEquiv d L
          (((Config.blocking d L Γ).symm x) q) (Int.divModEquiv L z).2 := by
        rw [Config.blocking_apply]
        congr 2
      _ = MPSTensor.decodeBlockEquiv d L
          (((Config.blocking d L Γ).symm y) q) (Int.divModEquiv L z).2 := by
        exact congrArg
          (fun w ↦ MPSTensor.decodeBlockEquiv d L w (Int.divModEquiv L z).2) hz
      _ = Config.blocking d L Γ ((Config.blocking d L Γ).symm y) zΓ := by
        rw [Config.blocking_apply]
        congr 2
      _ = y zΓ := by rw [Equiv.apply_symm_apply]
  · intro hxy
    funext q
    apply (MPSTensor.decodeBlockEquiv d L).injective
    funext r
    let qΓ : Γ := ⟨q, (Finset.mem_sdiff.mp q.2).1⟩
    let z : expandedRegion L Γ :=
      ⟨(Int.divModEquiv L).symm ((qΓ : ℤ), r),
        mem_expandedRegion_blockSite L Γ qΓ r⟩
    have hzΛ : (z : ℤ) ∉ expandedRegion L Λ := by
      rw [mem_expandedRegion]
      have hzq : (Int.divModEquiv L (z : ℤ)).1 = (qΓ : ℤ) := by
        exact congrArg Prod.fst ((Int.divModEquiv L).apply_symm_apply ((qΓ : ℤ), r))
      rw [hzq]
      exact (Finset.mem_sdiff.mp q.2).2
    have hz := congrFun hxy ⟨z, Finset.mem_sdiff.mpr ⟨z.2, hzΛ⟩⟩
    change MPSTensor.decodeBlockEquiv d L ((Config.blocking d L Γ).symm x qΓ) r =
      MPSTensor.decodeBlockEquiv d L ((Config.blocking d L Γ).symm y qΓ) r
    calc
      _ = x ((blockSiteEquiv L Γ).symm (qΓ, r)) := by
        rw [Config.blocking_symm_apply, Equiv.apply_symm_apply]
      _ = x z := by congr 1
      _ = y z := hz
      _ = y ((blockSiteEquiv L Γ).symm (qΓ, r)) := by congr 1
      _ = _ := by rw [Config.blocking_symm_apply, Equiv.apply_symm_apply]

/-- Finite-region blocking commutes with canonical local inclusions. -/
lemma localBlocking_localInclusion {d L : ℕ} [NeZero L] {Λ Γ : Finset ℤ}
    (h : Λ ⊆ Γ) (A : LocalAlgebra (MPSTensor.blockPhysDim d L) Λ) :
    localBlocking d L Γ (localInclusion h A) =
      localInclusion (expandedRegion_mono h) (localBlocking d L Λ A) := by
  ext x y
  rw [localBlocking_apply, localInclusion_apply, localInclusion_apply, localBlocking_apply,
    restrict_blocking_symm h x, restrict_blocking_symm h y]
  by_cases hxy :
      (Config.splitEquiv h ((Config.blocking d L Γ).symm x)).2 =
        (Config.splitEquiv h ((Config.blocking d L Γ).symm y)).2
  · simp only [hxy, ite_true, mul_one]
    rw [blocking_complement_eq_iff h x y] at hxy
    simp only [hxy, ite_true, mul_one]
  · simp only [hxy, ite_false, mul_zero]
    rw [blocking_complement_eq_iff h x y] at hxy
    simp only [hxy, ite_false, mul_zero]

/-- Forward blocking of finite representatives induces a star-algebra homomorphism on the
algebraic local algebra. -/
noncomputable def algebraicLocalBlockingHom (d L : ℕ) [NeZero L] :
    AlgebraicLocalAlgebra (MPSTensor.blockPhysDim d L) →⋆ₐ[ℂ]
      AlgebraicLocalAlgebra d :=
  algebraicLocalAlgebraLift
    (fun Λ ↦ (localObservable d (expandedRegion L Λ)).comp
      (localBlocking d L Λ).toStarAlgHom)
    (by
      intro Λ Γ h A
      change localObservable d (expandedRegion L Γ)
          (localBlocking d L Γ (localInclusion h A)) =
        localObservable d (expandedRegion L Λ) (localBlocking d L Λ A)
      rw [localBlocking_localInclusion]
      exact localObservable_localInclusion d (expandedRegion_mono h) _)

/-- Forward algebraic-local blocking evaluates by finite blocking on every local
representative. -/
@[simp]
lemma algebraicLocalBlockingHom_localObservable (d L : ℕ) [NeZero L]
    (Λ : Finset ℤ) (A : LocalAlgebra (MPSTensor.blockPhysDim d L) Λ) :
    algebraicLocalBlockingHom d L (localObservable _ Λ A) =
      localObservable d (expandedRegion L Λ) (localBlocking d L Λ A) :=
  rfl

/-- Enlarging to the block hull and then undoing finite blocking induces the reverse
algebraic-local homomorphism. -/
noncomputable def algebraicLocalUnblockingHom (d L : ℕ) [NeZero L] :
    AlgebraicLocalAlgebra d →⋆ₐ[ℂ]
      AlgebraicLocalAlgebra (MPSTensor.blockPhysDim d L) :=
  algebraicLocalAlgebraLift
    (fun Δ ↦ (localObservable (MPSTensor.blockPhysDim d L) (blockHull L Δ)).comp
      ((localBlocking d L (blockHull L Δ)).symm.toStarAlgHom.comp
        (localInclusion (subset_expandedRegion_blockHull L Δ))))
    (by
      intro Δ Θ h A
      let hHull : blockHull L Δ ⊆ blockHull L Θ := blockHull_mono h
      let hΔ : Δ ⊆ expandedRegion L (blockHull L Δ) := subset_expandedRegion_blockHull L Δ
      let hΘ : Θ ⊆ expandedRegion L (blockHull L Θ) := subset_expandedRegion_blockHull L Θ
      have horiginal :
          localInclusion hΘ (localInclusion h A) =
            localInclusion (expandedRegion_mono hHull) (localInclusion hΔ A) := by
        rw [← StarAlgHom.comp_apply, localInclusion_trans,
          ← StarAlgHom.comp_apply, localInclusion_trans]
      have hblocked :
          (localBlocking d L (blockHull L Θ)).symm
              (localInclusion hΘ (localInclusion h A)) =
            localInclusion hHull
              ((localBlocking d L (blockHull L Δ)).symm (localInclusion hΔ A)) := by
        apply (localBlocking d L (blockHull L Θ)).injective
        calc
          localBlocking d L (blockHull L Θ)
              ((localBlocking d L (blockHull L Θ)).symm
                (localInclusion hΘ (localInclusion h A))) =
              localInclusion hΘ (localInclusion h A) := Equiv.apply_symm_apply _ _
          _ = localInclusion (expandedRegion_mono hHull) (localInclusion hΔ A) := horiginal
          _ = localBlocking d L (blockHull L Θ)
              (localInclusion hHull
                ((localBlocking d L (blockHull L Δ)).symm (localInclusion hΔ A))) := by
            rw [localBlocking_localInclusion]
            exact congrArg (localInclusion (expandedRegion_mono hHull))
              (Equiv.apply_symm_apply (localBlocking d L (blockHull L Δ)).toEquiv
                (localInclusion hΔ A)).symm
      change localObservable _ (blockHull L Θ)
          ((localBlocking d L (blockHull L Θ)).symm
            (localInclusion hΘ (localInclusion h A))) =
        localObservable _ (blockHull L Δ)
          ((localBlocking d L (blockHull L Δ)).symm (localInclusion hΔ A))
      rw [hblocked]
      exact localObservable_localInclusion _ hHull _)

/-- Reverse algebraic-local blocking evaluates by enlarging a finite region to its block hull and
undoing finite blocking. -/
@[simp]
lemma algebraicLocalUnblockingHom_localObservable (d L : ℕ) [NeZero L]
    (Δ : Finset ℤ) (A : LocalAlgebra d Δ) :
    algebraicLocalUnblockingHom d L (localObservable d Δ A) =
      localObservable (MPSTensor.blockPhysDim d L) (blockHull L Δ)
        ((localBlocking d L (blockHull L Δ)).symm
          (localInclusion (subset_expandedRegion_blockHull L Δ) A)) :=
  rfl

private lemma algebraicLocalBlockingHom_injective (d L : ℕ) [NeZero d] [NeZero L] :
    Function.Injective (algebraicLocalBlockingHom d L) := by
  intro X Y hXY
  obtain ⟨Λ, A, rfl⟩ := DirectLimit.exists_eq_mk
    (localAlgebraMap (MPSTensor.blockPhysDim d L)) X
  obtain ⟨Γ, B, rfl⟩ := DirectLimit.exists_eq_mk
    (localAlgebraMap (MPSTensor.blockPhysDim d L)) Y
  let Ω := Λ ∪ Γ
  let hΛ : Λ ⊆ Ω := Finset.subset_union_left
  let hΓ : Γ ⊆ Ω := Finset.subset_union_right
  have hExpanded :
      localInclusion (expandedRegion_mono hΛ) (localBlocking d L Λ A) =
        localInclusion (expandedRegion_mono hΓ) (localBlocking d L Γ B) := by
    apply localObservable_injective d (expandedRegion L Ω)
    calc
      localObservable d (expandedRegion L Ω)
          (localInclusion (expandedRegion_mono hΛ) (localBlocking d L Λ A)) =
        localObservable d (expandedRegion L Λ) (localBlocking d L Λ A) :=
          localObservable_localInclusion d (expandedRegion_mono hΛ) _
      _ = localObservable d (expandedRegion L Γ) (localBlocking d L Γ B) := hXY
      _ = localObservable d (expandedRegion L Ω)
          (localInclusion (expandedRegion_mono hΓ) (localBlocking d L Γ B)) :=
          (localObservable_localInclusion d (expandedRegion_mono hΓ) _).symm
  have hFinite : localInclusion hΛ A = localInclusion hΓ B := by
    apply (localBlocking d L Ω).injective
    calc
      localBlocking d L Ω (localInclusion hΛ A) =
          localInclusion (expandedRegion_mono hΛ) (localBlocking d L Λ A) :=
        localBlocking_localInclusion hΛ A
      _ = localInclusion (expandedRegion_mono hΓ) (localBlocking d L Γ B) := hExpanded
      _ = localBlocking d L Ω (localInclusion hΓ B) :=
        (localBlocking_localInclusion hΓ B).symm
  calc
    localObservable _ Λ A = localObservable _ Ω (localInclusion hΛ A) :=
      (localObservable_localInclusion _ hΛ A).symm
    _ = localObservable _ Ω (localInclusion hΓ B) := congrArg (localObservable _ Ω) hFinite
    _ = localObservable _ Γ B := localObservable_localInclusion _ hΓ B

/-- Forward blocking after block-hull unblocking is the identity on original algebraic-local
observables. -/
lemma algebraicLocalBlockingHom_comp_unblockingHom (d L : ℕ) [NeZero L] :
    (algebraicLocalBlockingHom d L).comp (algebraicLocalUnblockingHom d L) =
      StarAlgHom.id ℂ (AlgebraicLocalAlgebra d) := by
  apply algebraicLocalAlgebra_starAlgHom_ext
  intro Δ
  ext A
  change algebraicLocalBlockingHom d L
      (algebraicLocalUnblockingHom d L (localObservable d Δ A)) = localObservable d Δ A
  rw [algebraicLocalUnblockingHom_localObservable,
    algebraicLocalBlockingHom_localObservable]
  let B := localInclusion (subset_expandedRegion_blockHull L Δ) A
  calc
    localObservable d (expandedRegion L (blockHull L Δ))
        (localBlocking d L (blockHull L Δ)
          ((localBlocking d L (blockHull L Δ)).symm B)) =
      localObservable d (expandedRegion L (blockHull L Δ)) B := by
        exact congrArg (localObservable d (expandedRegion L (blockHull L Δ)))
          (Equiv.apply_symm_apply (localBlocking d L (blockHull L Δ)).toEquiv B)
    _ = localObservable d Δ A :=
      localObservable_localInclusion d (subset_expandedRegion_blockHull L Δ) A

/-- Block-hull unblocking after forward blocking is the identity on blocked algebraic-local
observables. -/
lemma algebraicLocalUnblockingHom_comp_blockingHom (d L : ℕ) [NeZero d] [NeZero L] :
    (algebraicLocalUnblockingHom d L).comp (algebraicLocalBlockingHom d L) =
      StarAlgHom.id ℂ (AlgebraicLocalAlgebra (MPSTensor.blockPhysDim d L)) := by
  apply algebraicLocalAlgebra_starAlgHom_ext
  intro Λ
  ext A
  apply algebraicLocalBlockingHom_injective d L
  change algebraicLocalBlockingHom d L
      (algebraicLocalUnblockingHom d L
        (algebraicLocalBlockingHom d L (localObservable _ Λ A))) =
    algebraicLocalBlockingHom d L (localObservable _ Λ A)
  rw [← StarAlgHom.comp_apply, algebraicLocalBlockingHom_comp_unblockingHom]
  rfl

/-- Blocking consecutive groups of `L` sites gives an equivalence between the blocked and
original algebraic local algebras.

This is the site-grouping operation used in Cirac--Perez-Garcia--Schuch--Verstraete,
arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
noncomputable def algebraicLocalBlocking (d L : ℕ) [NeZero d] [NeZero L] :
    AlgebraicLocalAlgebra (MPSTensor.blockPhysDim d L) ≃⋆ₐ[ℂ]
      AlgebraicLocalAlgebra d :=
  StarAlgEquiv.ofBijective (algebraicLocalBlockingHom d L) ⟨
    algebraicLocalBlockingHom_injective d L,
    fun A ↦ ⟨algebraicLocalUnblockingHom d L A, by
      rw [← StarAlgHom.comp_apply, algebraicLocalBlockingHom_comp_unblockingHom]
      rfl⟩⟩

/-- Algebraic-local blocking has the same underlying map as its forward lift. -/
@[simp]
lemma algebraicLocalBlocking_apply (d L : ℕ) [NeZero d] [NeZero L]
    (A : AlgebraicLocalAlgebra (MPSTensor.blockPhysDim d L)) :
    algebraicLocalBlocking d L A = algebraicLocalBlockingHom d L A :=
  StarAlgEquiv.ofBijective_apply _ _

/-- Algebraic-local blocking sends a finite blocked representative to its expanded original
representative. -/
lemma algebraicLocalBlocking_localObservable (d L : ℕ) [NeZero d] [NeZero L]
    (Λ : Finset ℤ) (A : LocalAlgebra (MPSTensor.blockPhysDim d L) Λ) :
    algebraicLocalBlocking d L (localObservable _ Λ A) =
      localObservable d (expandedRegion L Λ) (localBlocking d L Λ A) := by
  rw [algebraicLocalBlocking_apply]
  exact algebraicLocalBlockingHom_localObservable d L Λ A

/-- The inverse algebraic-local blocking equivalence is the block-hull unblocking homomorphism. -/
@[simp]
lemma algebraicLocalBlocking_symm_apply (d L : ℕ) [NeZero d] [NeZero L]
    (A : AlgebraicLocalAlgebra d) :
    (algebraicLocalBlocking d L).symm A = algebraicLocalUnblockingHom d L A := by
  rw [StarAlgEquiv.symm_apply_eq, algebraicLocalBlocking_apply,
    ← StarAlgHom.comp_apply, algebraicLocalBlockingHom_comp_unblockingHom]
  rfl

/-- Inverse algebraic-local blocking enlarges an arbitrary original finite region to its block hull
and then applies inverse finite blocking. -/
lemma algebraicLocalBlocking_symm_localObservable (d L : ℕ) [NeZero d] [NeZero L]
    (Δ : Finset ℤ) (A : LocalAlgebra d Δ) :
    (algebraicLocalBlocking d L).symm (localObservable d Δ A) =
      localObservable (MPSTensor.blockPhysDim d L) (blockHull L Δ)
        ((localBlocking d L (blockHull L Δ)).symm
          (localInclusion (subset_expandedRegion_blockHull L Δ) A)) := by
  rw [algebraicLocalBlocking_symm_apply,
    algebraicLocalUnblockingHom_localObservable]

/-- On an expanded region, inverse algebraic-local blocking has the exact inverse finite-blocking
formula, with no block-hull enlargement remaining. -/
lemma algebraicLocalBlocking_symm_localObservable_expandedRegion
    (d L : ℕ) [NeZero d] [NeZero L] (Λ : Finset ℤ)
    (A : LocalAlgebra d (expandedRegion L Λ)) :
    (algebraicLocalBlocking d L).symm (localObservable d (expandedRegion L Λ) A) =
      localObservable (MPSTensor.blockPhysDim d L) Λ ((localBlocking d L Λ).symm A) := by
  apply (algebraicLocalBlocking d L).injective
  change algebraicLocalBlocking d L
      ((algebraicLocalBlocking d L).symm (localObservable d (expandedRegion L Λ) A)) =
    algebraicLocalBlocking d L
      (localObservable (MPSTensor.blockPhysDim d L) Λ ((localBlocking d L Λ).symm A))
  rw [StarAlgEquiv.apply_symm_apply, algebraicLocalBlocking_localObservable,
    StarAlgEquiv.apply_symm_apply]

/-- Algebraic-local blocking preserves the operator norm. -/
lemma algebraicLocalBlocking_norm (d L : ℕ) [NeZero d] [NeZero L]
    (A : AlgebraicLocalAlgebra (MPSTensor.blockPhysDim d L)) :
    ‖algebraicLocalBlocking d L A‖ = ‖A‖ := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      change ‖algebraicLocalBlocking d L (localObservable _ Λ A)‖ =
        ‖localObservable _ Λ A‖
      rw [algebraicLocalBlocking_localObservable, norm_localObservable,
        localBlocking_norm, norm_localObservable]

/-- Algebraic-local blocking is an operator-norm isometry. -/
lemma algebraicLocalBlocking_isometry (d L : ℕ) [NeZero d] [NeZero L] :
    Isometry (algebraicLocalBlocking d L) := by
  rw [isometry_iff_dist_eq]
  intro A B
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact algebraicLocalBlocking_norm d L (A - B)

/-- Inverse algebraic-local blocking is an operator-norm isometry. -/
lemma algebraicLocalBlocking_symm_isometry (d L : ℕ) [NeZero d] [NeZero L] :
    Isometry ((algebraicLocalBlocking d L).symm) :=
  (algebraicLocalBlocking_isometry d L).right_inv
    (algebraicLocalBlocking d L).apply_symm_apply

end SpinChain
