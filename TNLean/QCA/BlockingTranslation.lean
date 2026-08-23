/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.QuasiLocalBlocking
import TNLean.QCA.QuasiLocalTranslation
import TNLean.QCA.RegionSumset

/-!
# Translation geometry for blocked spin chains

Grouping `L` consecutive original sites into one blocked site scales a blocked displacement `a`
to the original displacement `a * L`.  An original displacement can also cross a block boundary,
with the resulting blocked displacement depending on the residue of the starting site.  This file
packages all such carries in `blockedNeighborhood` and proves the exact finite-region identity
needed to transport propagation bounds through blocking.

## Main definitions

* `SpinChain.blockedNeighborhood` — the carry-aware neighborhood on the blocked lattice.

## Main results

* `SpinChain.expandedRegion_translateRegion` — blocked translations scale by `L`.
* `SpinChain.algebraicLocalBlocking_translation` — algebraic blocking intertwines scaled
  translations.
* `SpinChain.quasiLocalBlocking_translation` — quasi-local blocking intertwines scaled
  translations.
* `SpinChain.mem_blockedNeighborhood` — quotient/remainder characterization of all carries.
* `SpinChain.blockHull_regionSumset_expandedRegion` — exact carry-aware block-hull identity.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2308 and
  2313--2320.
-/

namespace SpinChain

private lemma divModEquiv_fst_sub_mul (L : ℕ) [NeZero L] (z a : ℤ) :
    (Int.divModEquiv L (z - a * L)).1 = (Int.divModEquiv L z).1 - a := by
  simp only [Int.divModEquiv_apply]
  rw [show z - a * (L : ℤ) = z + (-a) * L by ring,
    Int.add_mul_ediv_right]
  · ring
  · exact_mod_cast NeZero.ne L

/-- Expanding a blocked region translated by `a` gives the original expanded region translated by
`a * L`.  This includes negative block coordinates and negative displacements.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
lemma expandedRegion_translateRegion (L : ℕ) [NeZero L] (a : ℤ) (Λ : Finset ℤ) :
    expandedRegion L (translateRegion a Λ) =
      translateRegion (a * L) (expandedRegion L Λ) := by
  ext z
  simp only [mem_expandedRegion, mem_translateRegion]
  rw [divModEquiv_fst_sub_mul]

/-- The blocked-lattice neighborhood induced by an original-lattice neighborhood `𝓝`.

The starting residue ranges over the full reference block `expandedRegion L {0}`.  Thus the block
hull records every possible carry of `r + n`, where `r` is a residue and `n ∈ 𝓝`; using only
`blockHull L 𝓝` would miss boundary-crossing carries.
Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
def blockedNeighborhood (L : ℕ) [NeZero L] (𝓝 : Finset ℤ) : Finset ℤ :=
  blockHull L (regionSumset (expandedRegion L {0}) 𝓝)

/-- Membership in the carry-aware blocked neighborhood is characterized by a starting residue and
an original displacement whose sum has the given quotient block coordinate.  Since
`Int.divModEquiv` uses Euclidean division, this statement applies without a sign restriction.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
lemma mem_blockedNeighborhood (L : ℕ) [NeZero L] (𝓝 : Finset ℤ) (b : ℤ) :
    b ∈ blockedNeighborhood L 𝓝 ↔
      ∃ r : Fin L, ∃ n ∈ 𝓝, (Int.divModEquiv L ((r : ℤ) + n)).1 = b := by
  simp only [blockedNeighborhood, blockHull, Finset.mem_image, mem_regionSumset,
    mem_expandedRegion, Finset.mem_singleton]
  constructor
  · rintro ⟨z, ⟨i, hi, n, hn, rfl⟩, rfl⟩
    have hi0 : (Int.divModEquiv L i).1 = 0 := hi
    let r := (Int.divModEquiv L i).2
    refine ⟨r, n, hn, ?_⟩
    have hi_repr := (Int.divModEquiv L).symm_apply_apply i
    rw [Int.divModEquiv_symm_apply] at hi_repr
    change (Int.divModEquiv L ((r : ℤ) + n)).1 = _
    rw [← hi_repr]
    simp only [hi0, zero_mul, zero_add]
    rfl
  · rintro ⟨r, n, hn, hbn⟩
    let i : ℤ := (Int.divModEquiv L).symm (0, r)
    refine ⟨i + n, ?_, ?_⟩
    · refine ⟨i, ?_, n, hn, rfl⟩
      simp only [i, Equiv.apply_symm_apply]
    · simpa only [i, Int.divModEquiv_symm_apply, zero_mul, zero_add] using hbn

/-- Equivalently, a blocked displacement belongs to `blockedNeighborhood L 𝓝` exactly when some
input residue and displacement decompose into that quotient and an output residue.  The two
residues expose the within-block carry explicitly, including for negative displacements.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
lemma mem_blockedNeighborhood_iff_exists_eq
    (L : ℕ) [NeZero L] (𝓝 : Finset ℤ) (b : ℤ) :
    b ∈ blockedNeighborhood L 𝓝 ↔
      ∃ r s : Fin L, ∃ n ∈ 𝓝, (r : ℤ) + n = b * L + s := by
  rw [mem_blockedNeighborhood]
  constructor
  · rintro ⟨r, n, hn, hq⟩
    let s := (Int.divModEquiv L ((r : ℤ) + n)).2
    refine ⟨r, s, n, hn, ?_⟩
    have hrepr := (Int.divModEquiv L).symm_apply_apply ((r : ℤ) + n)
    rw [Int.divModEquiv_symm_apply, hq] at hrepr
    exact hrepr.symm
  · rintro ⟨r, s, n, hn, hrs⟩
    refine ⟨r, n, hn, ?_⟩
    have hpair : Int.divModEquiv L ((r : ℤ) + n) = (b, s) := by
      apply (Int.divModEquiv L).symm.injective
      rw [Equiv.symm_apply_apply, Int.divModEquiv_symm_apply, hrs]
    exact congrArg Prod.fst hpair

private lemma divModEquiv_fst_add_block (L : ℕ) [NeZero L] (x z : ℤ) :
    (Int.divModEquiv L (x * L + z)).1 = x + (Int.divModEquiv L z).1 := by
  simp only [Int.divModEquiv_apply]
  rw [add_comm, Int.add_mul_ediv_right]
  · ring
  · exact_mod_cast NeZero.ne L

/-- Taking the block hull after adding an original neighborhood to an expanded blocked region is
exactly addition by the carry-aware blocked neighborhood.

For an expanded site `x * L + r` and displacement `n`, the output block is
`x + ((r + n) / L)`; ranging over all residues gives precisely `blockedNeighborhood L 𝓝`.
Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
lemma blockHull_regionSumset_expandedRegion (L : ℕ) [NeZero L]
    (Λ 𝓝 : Finset ℤ) :
    blockHull L (regionSumset (expandedRegion L Λ) 𝓝) =
      regionSumset Λ (blockedNeighborhood L 𝓝) := by
  ext b
  simp only [blockHull, Finset.mem_image, mem_regionSumset, mem_expandedRegion,
    mem_blockedNeighborhood]
  constructor
  · rintro ⟨z, ⟨i, hi, n, hn, rfl⟩, rfl⟩
    let x := (Int.divModEquiv L i).1
    let r := (Int.divModEquiv L i).2
    have hi_repr := (Int.divModEquiv L).symm_apply_apply i
    rw [Int.divModEquiv_symm_apply] at hi_repr
    refine ⟨x, hi, (Int.divModEquiv L ((r : ℤ) + n)).1, ?_, ?_⟩
    · exact ⟨r, n, hn, rfl⟩
    · rw [← hi_repr]
      change x + (Int.divModEquiv L ((r : ℤ) + n)).1 =
        (Int.divModEquiv L (x * L + (r : ℤ) + n)).1
      rw [show x * (L : ℤ) + (r : ℤ) + n = x * L + ((r : ℤ) + n) by ring,
        divModEquiv_fst_add_block]
  · rintro ⟨x, hx, q, ⟨r, n, hn, hq⟩, rfl⟩
    let i : ℤ := (Int.divModEquiv L).symm (x, r)
    refine ⟨i + n, ?_, ?_⟩
    · refine ⟨i, ?_, n, hn, rfl⟩
      simpa only [i, Equiv.apply_symm_apply] using hx
    · rw [show i = x * L + (r : ℤ) by simp [i, Int.divModEquiv_symm_apply]]
      rw [show x * (L : ℤ) + (r : ℤ) + n = x * L + ((r : ℤ) + n) by ring,
        divModEquiv_fst_add_block, hq]

/-- Adding an original neighborhood to an expanded blocked region is contained in the expansion
of the exact carry-aware blocked sumset.  This is the support-transport form of
`blockHull_regionSumset_expandedRegion`. -/
lemma regionSumset_expandedRegion_subset (L : ℕ) [NeZero L] (Λ 𝓝 : Finset ℤ) :
    regionSumset (expandedRegion L Λ) 𝓝 ⊆
      expandedRegion L (regionSumset Λ (blockedNeighborhood L 𝓝)) := by
  rw [← blockHull_regionSumset_expandedRegion]
  exact subset_expandedRegion_blockHull L _

private lemma expandedRegion_translateRegion_subset (L : ℕ) [NeZero L]
    (a : ℤ) (Λ : Finset ℤ) :
    expandedRegion L (translateRegion a Λ) ⊆
      translateRegion (a * L) (expandedRegion L Λ) := by
  rw [expandedRegion_translateRegion]

private lemma localBlocking_translation (d L : ℕ) [NeZero L] (a : ℤ)
    (Λ : Finset ℤ) (A : LocalAlgebra (MPSTensor.blockPhysDim d L) Λ) :
    localInclusion (expandedRegion_translateRegion_subset L a Λ)
        (localBlocking d L (translateRegion a Λ)
          (localTranslation (MPSTensor.blockPhysDim d L) a Λ A)) =
      localTranslation d (a * L) (expandedRegion L Λ) (localBlocking d L Λ A) := by
  ext x y
  rw [localInclusion_apply]
  have hreverse : translateRegion (a * L) (expandedRegion L Λ) ⊆
      expandedRegion L (translateRegion a Λ) := by
    rw [expandedRegion_translateRegion]
  have hcomp :
      (Config.splitEquiv (expandedRegion_translateRegion_subset L a Λ) x).2 =
        (Config.splitEquiv (expandedRegion_translateRegion_subset L a Λ) y).2 := by
    funext i
    exact False.elim ((Finset.mem_sdiff.mp i.2).2
      (hreverse (Finset.mem_sdiff.mp i.2).1))
  rw [ite_eq_left hcomp, mul_one, localBlocking_apply, localTranslation_apply,
    localTranslation_apply, localBlocking_apply]
  have hconfig (w : Config d (translateRegion (a * L) (expandedRegion L Λ))) :
      (Config.translation (MPSTensor.blockPhysDim d L) a Λ).symm
          ((Config.blocking d L (translateRegion a Λ)).symm
            (Config.restrict (expandedRegion_translateRegion_subset L a Λ) w)) =
        (Config.blocking d L Λ).symm
          ((Config.translation d (a * L) (expandedRegion L Λ)).symm w) := by
    funext i
    apply (MPSTensor.decodeBlockEquiv d L).injective
    funext r
    rw [Config.translation_symm_apply, Config.blocking_symm_apply,
      Config.blocking_symm_apply]
    simp only [Equiv.apply_symm_apply]
    rw [Config.translation_symm_apply]
    change w _ = w _
    congr 1
    apply Subtype.ext
    simp only [siteTranslation_apply_val, blockSiteEquiv_symm_apply_val]
    ring
  rw [hconfig x, hconfig y]

/-- Algebraic-local blocking intertwines blocked translation by `a` with original translation by
`a * L`.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
lemma algebraicLocalBlocking_translation (d L : ℕ) [NeZero d] [NeZero L] (a : ℤ)
    (A : AlgebraicLocalAlgebra (MPSTensor.blockPhysDim d L)) :
    algebraicLocalBlocking d L (algebraicLocalTranslation _ a A) =
      algebraicLocalTranslation d (a * L) (algebraicLocalBlocking d L A) := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      change algebraicLocalBlocking d L
          (algebraicLocalTranslation _ a (localObservable _ Λ A)) =
        algebraicLocalTranslation d (a * L)
          (algebraicLocalBlocking d L (localObservable _ Λ A))
      rw [algebraicLocalTranslation_localObservable,
        algebraicLocalBlocking_localObservable,
        algebraicLocalBlocking_localObservable,
        algebraicLocalTranslation_localObservable]
      rw [← localObservable_localInclusion d
        (expandedRegion_translateRegion_subset L a Λ)]
      exact congrArg (localObservable d (translateRegion (a * L) (expandedRegion L Λ)))
        (localBlocking_translation d L a Λ A)

/-- Quasi-local blocking intertwines blocked translation by `a` with original translation by
`a * L`.

Source: arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
lemma quasiLocalBlocking_translation (d L : ℕ) [NeZero d] [NeZero L] (a : ℤ)
    (A : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L)) :
    quasiLocalBlocking d L (quasiLocalTranslation _ a A) =
      quasiLocalTranslation d (a * L) (quasiLocalBlocking d L A) := by
  induction A using UniformSpace.Completion.induction_on with
  | hp =>
      change IsClosed {A : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) |
        quasiLocalBlocking d L (quasiLocalTranslation _ a A) =
          quasiLocalTranslation d (a * L) (quasiLocalBlocking d L A)}
      exact isClosed_eq
        ((quasiLocalBlocking_isometry d L).continuous.comp
          (quasiLocalTranslation_isometry _ a).continuous)
        ((quasiLocalTranslation_isometry d (a * L)).continuous.comp
          (quasiLocalBlocking_isometry d L).continuous)
  | ih A =>
      change quasiLocalBlocking d L
          (quasiLocalTranslation _ a (algebraicToQuasiLocal _ A)) =
        quasiLocalTranslation d (a * L)
          (quasiLocalBlocking d L (algebraicToQuasiLocal _ A))
      rw [quasiLocalTranslation_algebraicToQuasiLocal,
        quasiLocalBlocking_algebraicToQuasiLocal,
        quasiLocalBlocking_algebraicToQuasiLocal,
        quasiLocalTranslation_algebraicToQuasiLocal,
        algebraicLocalBlocking_translation]

end SpinChain
