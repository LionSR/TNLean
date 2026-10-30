/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.IntervalCoordinates
import TNLean.QCA.QuasiLocalTranslation

/-!
# Translation in consecutive interval coordinates

Translating an interval observable shifts its integer anchor and preserves
its matrix in consecutive coordinates. This identity compares actual local
observables, without choosing a transport between equal matrix types.

Source context: arXiv:1703.09188, Appendix local observables and lattice
translations, lines 2292--2306.
-/

namespace SpinChain

/-- Translating a consecutive interval shifts its left endpoint and preserves
its length. Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
integer interval convention. -/
theorem translateRegion_finiteChainRegion (a b : ℤ) (N : ℕ) :
    translateRegion b (finiteChainRegion a N) = finiteChainRegion (a + b) N := by
  ext x
  simp only [mem_translateRegion, finiteChainRegion, Finset.mem_Ico]
  omega

private theorem translated_interval_config (d N : ℕ) (t b : ℤ)
    (x : Config d (finiteChainRegion (b + t) N)) :
    (Config.translation d t (finiteChainRegion b N)).symm
      (Config.restrict (translateRegion_finiteChainRegion b t N).le x) =
      finiteChainConfigEquiv d N b ((finiteChainConfigEquiv d N (b + t)).symm x) := by
  funext i
  change x _ = x _
  congr 1
  apply Subtype.ext
  change (Finset.equivMap (Equiv.addRight t).toEmbedding (finiteChainRegion b N) i : ℤ) =
    (finiteChainSiteEquiv (b + t) N ((finiteChainSiteEquiv b N).symm i) : ℤ)
  rw [siteTranslation_apply_val, finiteChainSiteEquiv_val]
  have h := congrArg Subtype.val ((finiteChainSiteEquiv b N).apply_symm_apply i)
  simp only [finiteChainSiteEquiv_val] at h
  omega

/-- Actual algebraic-local translation shifts the interval anchor and
leaves its consecutive-coordinate matrix unchanged.
Source context: arXiv:1703.09188, Appendix lines 2292--2306. -/
theorem algebraicLocalTranslation_intervalCoordinates (d N : ℕ) (t b : ℤ)
    (A : LocalAlgebra d (finiteChainRegion b N)) :
    algebraicLocalTranslation d t (localObservable d (finiteChainRegion b N) A) =
      localObservable d (finiteChainRegion (b + t) N)
        ((intervalCoordinates d (b + t) N).symm (intervalCoordinates d b N A)) := by
  classical
  let h := (translateRegion_finiteChainRegion b t N).le
  rw [algebraicLocalTranslation_localObservable,
    ← localObservable_localInclusion d h]
  congr 1
  apply CStarMatrix.ext
  intro x y
  rw [localInclusion_apply]
  have hcomp : (Config.splitEquiv h x).2 = (Config.splitEquiv h y).2 := by
    funext i
    exact False.elim ((Finset.mem_sdiff.mp i.2).2
      ((translateRegion_finiteChainRegion b t N).ge (Finset.mem_sdiff.mp i.2).1))
  rw [if_pos hcomp, mul_one, localTranslation_apply,
    translated_interval_config, translated_interval_config]
  rfl

/-- Actual quasi-local translation shifts the anchor of a finite interval
representative without changing its consecutive-coordinate matrix.
Source context: arXiv:1703.09188, Appendix lines 2292--2306. -/
theorem quasiLocalTranslation_intervalCoordinates (d N : ℕ) [NeZero d] (t b : ℤ)
    (A : LocalAlgebra d (finiteChainRegion b N)) :
    quasiLocalTranslation d t (quasiLocalObservable d (finiteChainRegion b N) A) =
      quasiLocalObservable d (finiteChainRegion (b + t) N)
        ((intervalCoordinates d (b + t) N).symm (intervalCoordinates d b N A)) := by
  change quasiLocalTranslation d t (algebraicToQuasiLocal d
    (localObservable d (finiteChainRegion b N) A)) = _
  rw [quasiLocalTranslation_algebraicToQuasiLocal,
    algebraicLocalTranslation_intervalCoordinates]
  rfl


/-- Transporting a finite inclusion to shifted consecutive coordinates
is exactly inclusion of the translated observable.
Source context: arXiv:1703.09188, Appendix lines 2292--2306. -/
theorem intervalCoordinates_localInclusion_localTranslation {d : ℕ} [NeZero d]
    (N : ℕ) (t b : ℤ) {Λ : Finset ℤ} (hΛ : Λ ⊆ finiteChainRegion b N)
    (A : LocalAlgebra d Λ) :
    (intervalCoordinates d (b + t) N).symm
      (intervalCoordinates d b N (localInclusion hΛ A)) =
      localInclusion ((translateRegion_mono t hΛ).trans
        (translateRegion_finiteChainRegion b t N).le) (localTranslation d t Λ A) := by
  apply localObservable_injective d (finiteChainRegion (b + t) N)
  rw [localObservable_localInclusion]
  have h := algebraicLocalTranslation_intervalCoordinates d N t b (localInclusion hΛ A)
  rw [localObservable_localInclusion, algebraicLocalTranslation_localObservable] at h
  exact h.symm

end SpinChain
