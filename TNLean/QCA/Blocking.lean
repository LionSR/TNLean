/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Logic.Equiv.Fin.Basic
import TNLean.MPS.Core.Blocking
import TNLean.QCA.LocalAlgebra

/-!
# Blocking sites in a one-dimensional spin chain

For a positive block length `L`, this file groups the consecutive original sites
`L * x, ..., L * x + L - 1` into the blocked site `x`.  It constructs the expanded original
region, the corresponding equivalence of configurations, and the induced equivalence of finite
local observable algebras.

The compatibility with local inclusions, the algebraic-local and quasi-local extensions, and
transport of QCA predicates are deliberately left to the next layer.

## Main definitions

* `SpinChain.expandedRegion` — the original sites belonging to a finite blocked region.
* `SpinChain.blockSiteEquiv` — block coordinates `x, r` for an expanded original site.
* `SpinChain.Config.blocking` — blocked configurations as configurations on the expanded region.
* `SpinChain.localBlocking` — the induced finite local star-algebra equivalence.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2308 and
  2313--2320.
-/

namespace SpinChain

/-- The original sites obtained by expanding every blocked site `x` into the consecutive sites
`L * x, ..., L * x + L - 1`.

The inverse of `Int.divModEquiv L` fixes the order: the residue `r : Fin L` labels the site
`L * x + r` inside block `x`.
Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
def expandedRegion (L : ℕ) [NeZero L] (Λ : Finset ℤ) : Finset ℤ :=
  (Λ.product (Finset.univ : Finset (Fin L))).map (Int.divModEquiv L).symm.toEmbedding

/-- Membership in an expanded region is membership of the quotient block coordinate in the
blocked region.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
@[simp]
lemma mem_expandedRegion (L : ℕ) [NeZero L] (Λ : Finset ℤ) (z : ℤ) :
    z ∈ expandedRegion L Λ ↔ (Int.divModEquiv L z).1 ∈ Λ := by
  simp [expandedRegion]

/-- Expanding regions is monotone. -/
lemma expandedRegion_mono {L : ℕ} [NeZero L] {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) :
    expandedRegion L Λ ⊆ expandedRegion L Γ := by
  intro z hz
  simpa only [mem_expandedRegion] using h (mem_expandedRegion L Λ z |>.mp hz)

/-- The expanded site with block coordinate `x` and residue `r` is `L * x + r`. -/
@[simp]
lemma mem_expandedRegion_blockSite (L : ℕ) [NeZero L] (Λ : Finset ℤ)
    (x : Λ) (r : Fin L) :
    (Int.divModEquiv L).symm ((x : ℤ), r) ∈ expandedRegion L Λ := by
  simpa only [mem_expandedRegion, Equiv.apply_symm_apply] using x.2

/-- Expanded original sites are equivalent to a blocked site together with a residue inside that
block.  Residues increase in the source's consecutive-site order.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
def blockSiteEquiv (L : ℕ) [NeZero L] (Λ : Finset ℤ) :
    expandedRegion L Λ ≃ Λ × Fin L where
  toFun z :=
    (⟨(Int.divModEquiv L z).1, (mem_expandedRegion L Λ z).mp z.2⟩,
      (Int.divModEquiv L z).2)
  invFun p :=
    ⟨(Int.divModEquiv L).symm ((p.1 : ℤ), p.2), mem_expandedRegion_blockSite L Λ p.1 p.2⟩
  left_inv z := by
    apply Subtype.ext
    exact (Int.divModEquiv L).symm_apply_apply z
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((Int.divModEquiv L).apply_symm_apply ((p.1 : ℤ), p.2))
    · apply Fin.ext
      exact congrArg (fun q : ℤ × Fin L ↦ q.2.val)
        ((Int.divModEquiv L).apply_symm_apply ((p.1 : ℤ), p.2))

/-- The first block coordinate of an expanded site is its quotient by the block length. -/
@[simp]
lemma blockSiteEquiv_apply_fst_val (L : ℕ) [NeZero L] (Λ : Finset ℤ)
    (z : expandedRegion L Λ) :
    ((blockSiteEquiv L Λ z).1 : ℤ) = (Int.divModEquiv L z).1 := rfl

/-- The second block coordinate of an expanded site is its residue modulo the block length. -/
@[simp]
lemma blockSiteEquiv_apply_snd (L : ℕ) [NeZero L] (Λ : Finset ℤ)
    (z : expandedRegion L Λ) :
    (blockSiteEquiv L Λ z).2 = (Int.divModEquiv L z).2 := rfl

/-- The site with block coordinates `(x, r)` has integer coordinate `x * L + r`. -/
@[simp]
lemma blockSiteEquiv_symm_apply_val (L : ℕ) [NeZero L] (Λ : Finset ℤ)
    (p : Λ × Fin L) :
    ((blockSiteEquiv L Λ).symm p : ℤ) = (p.1 : ℤ) * L + p.2 := rfl

namespace Config

/-- A blocked configuration is equivalent to a configuration on the consecutively expanded
original region.  A blocked spin is decoded from `Fin (d^L)` into its length-`L` word using
`MPSTensor.decodeBlockEquiv`.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
noncomputable def blocking (d L : ℕ) [NeZero L] (Λ : Finset ℤ) :
    Config (MPSTensor.blockPhysDim d L) Λ ≃ Config d (expandedRegion L Λ) :=
  ((Equiv.refl Λ).arrowCongr (MPSTensor.decodeBlockEquiv d L)).trans
    ((Equiv.curry Λ (Fin L) (Fin d)).symm.trans
      ((blockSiteEquiv L Λ).symm.arrowCongr (Equiv.refl (Fin d))))

/-- Evaluation of an expanded configuration reads the corresponding residue of the decoded
blocked spin. -/
@[simp]
lemma blocking_apply (d L : ℕ) [NeZero L] (Λ : Finset ℤ)
    (x : Config (MPSTensor.blockPhysDim d L) Λ) (z : expandedRegion L Λ) :
    blocking d L Λ x z =
      MPSTensor.decodeBlockEquiv d L (x (blockSiteEquiv L Λ z).1)
        (blockSiteEquiv L Λ z).2 := rfl

/-- Re-encoding an expanded configuration at a blocked site collects its `L` consecutive
residues in increasing order. -/
@[simp]
lemma blocking_symm_apply (d L : ℕ) [NeZero L] (Λ : Finset ℤ)
    (x : Config d (expandedRegion L Λ)) (i : Λ) :
    (blocking d L Λ).symm x i =
      (MPSTensor.decodeBlockEquiv d L).symm
        (fun r ↦ x ((blockSiteEquiv L Λ).symm (i, r))) := rfl

/-- Decoding blocked configurations commutes with restriction to a smaller blocked region. -/
lemma restrict_blocking {d L : ℕ} [NeZero L] {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (x : Config (MPSTensor.blockPhysDim d L) Γ) :
    restrict (expandedRegion_mono h) (blocking d L Γ x) =
      blocking d L Λ (restrict h x) := by
  funext z
  rfl

end Config

/-- Blocking sites induces a star-algebra equivalence from observables on a finite blocked region
to observables on its consecutively expanded original region.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
noncomputable def localBlocking (d L : ℕ) [NeZero L] (Λ : Finset ℤ) :
    LocalAlgebra (MPSTensor.blockPhysDim d L) Λ ≃⋆ₐ[ℂ]
      LocalAlgebra d (expandedRegion L Λ) :=
  CStarMatrix.reindexₐ ℂ ℂ (Config.blocking d L Λ)

/-- Entrywise evaluation of finite-region blocking. -/
@[simp]
lemma localBlocking_apply (d L : ℕ) [NeZero L] (Λ : Finset ℤ)
    (A : LocalAlgebra (MPSTensor.blockPhysDim d L) Λ)
    (x y : Config d (expandedRegion L Λ)) :
    localBlocking d L Λ A x y =
      A ((Config.blocking d L Λ).symm x) ((Config.blocking d L Λ).symm y) := rfl

open scoped ComplexOrder in
/-- Finite-region blocking preserves the C-star operator norm. -/
@[simp]
lemma localBlocking_norm (d L : ℕ) [NeZero L] (Λ : Finset ℤ)
    (A : LocalAlgebra (MPSTensor.blockPhysDim d L) Λ) :
    ‖localBlocking d L Λ A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (localBlocking d L Λ) A

open scoped ComplexOrder in
/-- Finite-region blocking is an operator-norm isometry. -/
lemma localBlocking_isometry (d L : ℕ) [NeZero L] (Λ : Finset ℤ) :
    Isometry (localBlocking d L Λ) :=
  StarAlgEquiv.isometry (localBlocking d L Λ)

end SpinChain
