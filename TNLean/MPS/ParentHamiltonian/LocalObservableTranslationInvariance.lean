/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableQuasiLocalState
import TNLean.QCA.QuasiLocalTranslation

/-!
# Translation invariance of the quasi-local MPS state

Lattice translation preserves increasing interval coordinates. The local
expectations of a trace-preserving tensor at an invariant virtual matrix
therefore agree on translated finite regions. Their continuous extension
is translation invariant on the completed quasi-local algebra.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.1)--(3.2b), translation-invariant GVBS expectations.
No purity assertion is made.
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

private theorem finiteChainConfigEquiv_translation_restrict (d : ℕ) (a b : ℤ) (N : ℕ)
    (σ : Fin N → Fin d) :
    (Config.translation d b (finiteChainRegion a N)).symm
      (Config.restrict (translateRegion_finiteChainRegion a b N).le
        (finiteChainConfigEquiv d N (a + b) σ)) = finiteChainConfigEquiv d N a σ := by
  funext x
  change σ _ = σ _
  congr 1
  apply Fin.ext
  change (((Finset.equivMap (Equiv.addRight b).toEmbedding (finiteChainRegion a N)) x : ℤ)
    - (a + b)).toNat = (x.1 - a).toNat
  rw [siteTranslation_apply_val]
  congr 1
  omega

/-- Translation leaves the numbered matrix coordinates of an interval
observable unchanged. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), translation invariance of local expectations. -/
theorem intervalCoordinates_localTranslation (d : ℕ) (a b : ℤ) (N : ℕ)
    (X : LocalAlgebra d (finiteChainRegion a N)) :
    intervalCoordinates d (a + b) N
      (localInclusion (translateRegion_finiteChainRegion a b N).le
        (localTranslation d b (finiteChainRegion a N) X)) = intervalCoordinates d a N X := by
  ext σ τ
  rw [intervalCoordinates_apply, localInclusion_apply, localTranslation_apply,
    finiteChainConfigEquiv_translation_restrict, finiteChainConfigEquiv_translation_restrict,
    intervalCoordinates_apply]
  have hcomp :
      (Config.splitEquiv (translateRegion_finiteChainRegion a b N).le
        (finiteChainConfigEquiv d N (a + b) σ)).2 =
      (Config.splitEquiv (translateRegion_finiteChainRegion a b N).le
        (finiteChainConfigEquiv d N (a + b) τ)).2 := by
    funext x
    have hx := Finset.mem_sdiff.mp x.2
    exact False.elim (hx.2 (by simpa only [translateRegion_finiteChainRegion] using hx.1))
  simp only [hcomp, ite_true, mul_one]

private theorem exists_subset_finiteChainRegion (Λ : Finset ℤ) :
    ∃ (a : ℤ) (N : ℕ), Λ ⊆ finiteChainRegion a N := by
  obtain ⟨u, hu⟩ := Finset.exists_le Λ
  obtain ⟨a, ha⟩ := Finset.exists_ge Λ
  refine ⟨a, (u + 1 - a).toNat, ?_⟩
  intro x hx
  have hxupper := hu x hx
  have hxlower := ha x hx
  simp only [finiteChainRegion, Finset.mem_Ico]
  omega

end SpinChain

open scoped Matrix BigOperators ComplexOrder
open SpinChain

namespace MPSTensor

variable {d D : ℕ}

/-- Local MPS expectations are invariant under translation of arbitrary
finite regions. Source: Nachtergaele, arXiv:cond-mat/9410110,
Section 3, equations (3.1)--(3.2b), translation-invariant local expectations. -/
theorem localObservableExpectation_localTranslation (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hfix : Kraus.transferMap A ρ = ρ) (b : ℤ) (Λ : Finset ℤ)
    (X : LocalAlgebra d Λ) :
    localObservableExpectation A ρ (translateRegion b Λ) (localTranslation d b Λ X) =
      localObservableExpectation A ρ Λ X := by
  obtain ⟨a, N, hΛ⟩ := exists_subset_finiteChainRegion Λ
  have htranslated := (translateRegion_mono b hΛ).trans
    (translateRegion_finiteChainRegion a b N).le
  have hcoords := intervalCoordinates_localTranslation d a b N (localInclusion hΛ X)
  rw [localTranslation_localInclusion] at hcoords
  simp only [← StarAlgHom.comp_apply, localInclusion_trans] at hcoords
  rw [localObservableExpectation_eq_of_subset_interval A ρ hTP hfix
    (a + b) N htranslated, localObservableExpectation_eq_of_subset_interval A ρ hTP hfix
      a N hΛ, hcoords]

/-- The completed quasi-local MPS expectation is translation invariant.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.1)--(3.2b), the translation-invariant GVBS state. -/
theorem quasiLocalExpectation_quasiLocalTranslation [NeZero d] (A : MPSTensor d D)
    (hTP : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap A ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (b : ℤ) (X : QuasiLocalAlgebra d) :
    quasiLocalExpectation A hTP hρ hfix htr (quasiLocalTranslation d b X) =
      quasiLocalExpectation A hTP hρ hfix htr X := by
  refine UniformSpace.Completion.induction_on X ?_ ?_
  · apply isClosed_eq
      ((quasiLocalExpectation A hTP hρ hfix htr).continuous.comp ?_)
      (quasiLocalExpectation A hTP hρ hfix htr).continuous
    change Continuous (UniformSpace.Completion.map (algebraicLocalTranslation d b))
    exact UniformSpace.Completion.continuous_map
  · intro Y
    induction Y using DirectLimit.induction with
    | _ Λ Y =>
      change quasiLocalExpectation A hTP hρ hfix htr
        (quasiLocalTranslation d b (quasiLocalObservable d Λ Y)) =
        quasiLocalExpectation A hTP hρ hfix htr (quasiLocalObservable d Λ Y)
      rw [quasiLocalTranslation_quasiLocalObservable,
        quasiLocalExpectation_quasiLocalObservable, quasiLocalExpectation_quasiLocalObservable]
      exact localObservableExpectation_localTranslation A ρ hTP hfix b Λ Y

end MPSTensor
