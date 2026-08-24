/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.BipartiteLocalAlgebra
import TNLean.QCA.FinitePropagation
import TNLean.QCA.TranslationCovariance

/-!
# Finite-region restrictions of finite-propagation automorphisms

If a quasi-local star-automorphism \(\omega\) propagates within a finite neighborhood
\(\mathcal N\), the inclusion
\[
  \omega(\mathcal A_\Lambda)\subseteq\mathcal A_{\Lambda+\mathcal N}
\]
determines a unique injective star-algebra homomorphism
\[
  \omega_{\Lambda,\mathcal N}\colon
  \mathcal A_\Lambda\longrightarrow\mathcal A_{\Lambda+\mathcal N}.
\]
These finite-region restrictions commute with enlargement of the source region. For a
translation-covariant automorphism, their canonical quasi-local images also commute with every
lattice translation. Their ranges provide the finite-dimensional star-subalgebras to which the
bipartite coordinates of `TNLean.QCA.BipartiteLocalAlgebra` may subsequently be applied.

No support algebra, matrix-factor theorem, adjacent-block generation theorem, or generalized
Margolus unitary is constructed here.

## Main definitions

* `SpinChain.PropagatesWithin.localRestriction` — the finite-region restriction of the
  automorphism.
* `SpinChain.PropagatesWithin.localRestrictionRange` — its range as a finite-dimensional
  star-subalgebra.
* `SpinChain.PropagatesWithin.bipartiteLocalRestrictionRange` — that range in fixed left/right
  matrix coordinates when the target is a disjoint union.

## Main results

* `SpinChain.PropagatesWithin.quasiLocalObservable_localRestriction` — the defining quasi-local
  equality.
* `SpinChain.PropagatesWithin.localRestriction_injective` — injectivity.
* `SpinChain.PropagatesWithin.localRestriction_localInclusion` — compatibility under enlargement.
* `SpinChain.PropagatesWithin.localRestriction_translation` — translation naturality in the
  canonical quasi-local algebra.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2298.
* Schumacher--Werner, quant-ph/0405174, Definition 1 and Lemma `lem:localrule`.
-/

namespace SpinChain

namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
  {𝓝 : Finset ℤ}

/-- The finite-region restriction of an automorphism with propagation neighborhood
\(\mathcal N\).

It is the unique map \(\omega_{\Lambda,\mathcal N}\) satisfying
\[
  \iota_{\Lambda+\mathcal N}(\omega_{\Lambda,\mathcal N}(A))
    =\omega(\iota_\Lambda(A)).
\]
The construction restricts the codomain of the quasi-local action to the range of the target
finite-region embedding, then uses the injectivity of that embedding. It therefore makes no
elementwise choice of local representatives.

Source context: arXiv:1703.09188, Appendix, line 2298; Schumacher--Werner,
quant-ph/0405174, Definition 1, lines 309--318. This finite-region map is the canonical map
determined by the cited locality inclusion, not a separately stated definition in either source. -/
noncomputable def localRestriction (hω : PropagatesWithin ω 𝓝) (Λ : Finset ℤ) :
    LocalAlgebra d Λ →⋆ₐ[ℂ] LocalAlgebra d (regionSumset Λ 𝓝) := by
  let j := quasiLocalObservable d (regionSumset Λ 𝓝)
  let f : LocalAlgebra d Λ →⋆ₐ[ℂ] QuasiLocalAlgebra d :=
    ω.toStarAlgHom.comp (quasiLocalObservable d Λ)
  let fRange : LocalAlgebra d Λ →⋆ₐ[ℂ] j.range :=
    f.codRestrict j.range fun A ↦ by
      exact (propagatesWithin_iff_range_subset.mp hω Λ) ⟨A, rfl⟩
  exact (StarAlgEquiv.ofInjective j
    (quasiLocalObservable_injective d (regionSumset Λ 𝓝))).symm.toStarAlgHom.comp fRange

/-- The defining equality for the finite-region restriction after the canonical quasi-local
embeddings.

Source context: arXiv:1703.09188, Appendix, line 2298. The displayed equality is the
finite-dimensional form of the cited inclusion, rather than a separately stated source lemma. -/
theorem quasiLocalObservable_localRestriction (hω : PropagatesWithin ω 𝓝)
    (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    quasiLocalObservable d (regionSumset Λ 𝓝) (hω.localRestriction Λ A) =
      ω (quasiLocalObservable d Λ A) := by
  let j := quasiLocalObservable d (regionSumset Λ 𝓝)
  let f : LocalAlgebra d Λ →⋆ₐ[ℂ] QuasiLocalAlgebra d :=
    ω.toStarAlgHom.comp (quasiLocalObservable d Λ)
  have hfA : f A ∈ j.range :=
    (propagatesWithin_iff_range_subset.mp hω Λ) ⟨A, rfl⟩
  let y : j.range := ⟨f A, hfA⟩
  let e := StarAlgEquiv.ofInjective j
    (quasiLocalObservable_injective d (regionSumset Λ 𝓝))
  change j (e.symm y) = f A
  exact congrArg Subtype.val (e.apply_symm_apply y)

/-- Every finite-region restriction of a star-automorphism is injective.

Source context: arXiv:1703.09188, Appendix, line 2298 assumes that the global action is an
automorphism; its injectivity gives the assertion here. Schumacher--Werner, quant-ph/0405174,
Definition 1, lines 309--318 supplies the corresponding finite local-rule setting. -/
theorem localRestriction_injective (hω : PropagatesWithin ω 𝓝) (Λ : Finset ℤ) :
    Function.Injective (hω.localRestriction Λ) := by
  intro A B hAB
  apply quasiLocalObservable_injective d Λ
  apply ω.injective
  change ω (quasiLocalObservable d Λ A) = ω (quasiLocalObservable d Λ B)
  rw [← hω.quasiLocalObservable_localRestriction Λ A,
    ← hω.quasiLocalObservable_localRestriction Λ B, hAB]

/-- Finite-region restrictions commute with canonical inclusions under enlargement of the source
region.

This is the coherent local-rule property underlying Schumacher--Werner, quant-ph/0405174,
Lemma `lem:localrule`, lines 331--365; the finite-region enlargement equality is not displayed
separately there. -/
theorem localRestriction_localInclusion (hω : PropagatesWithin ω 𝓝)
    {Λ Γ : Finset ℤ} (hΛΓ : Λ ⊆ Γ) (A : LocalAlgebra d Λ) :
    hω.localRestriction Γ (localInclusion hΛΓ A) =
      localInclusion (regionSumset_mono_left 𝓝 hΛΓ) (hω.localRestriction Λ A) := by
  apply quasiLocalObservable_injective d (regionSumset Γ 𝓝)
  rw [hω.quasiLocalObservable_localRestriction,
    quasiLocalObservable_localInclusion,
    quasiLocalObservable_localInclusion,
    hω.quasiLocalObservable_localRestriction]

/-- The range of a finite-region restriction as a star-subalgebra of
\(\mathcal A_{\Lambda+\mathcal N}\).

This is the local image to be written in bipartite coordinates before forming the GNVW support
algebras. No support algebra is formed here.

Source context: arXiv:1703.09188, Appendix, line 2298; GNVW, arXiv:0910.3675v2,
equation `RR2x`, lines 1249--1266. This finite-dimensional local image is determined by the cited
locality inclusion; it is not a separately stated source definition. -/
noncomputable def localRestrictionRange (hω : PropagatesWithin ω 𝓝) (Λ : Finset ℤ) :
    StarSubalgebra ℂ (LocalAlgebra d (regionSumset Λ 𝓝)) :=
  (hω.localRestriction Λ).range

/-- The source local algebra is star-algebra equivalent to the range of its finite-region
restriction.

This records that the local image in
\(\mathcal A_{\Lambda+\mathcal N}\) is an isomorphic copy of
\(\mathcal A_\Lambda\). It is a finite-dimensional consequence of the locality inclusion in
arXiv:1703.09188, Appendix, line 2298, rather than a separately stated theorem there. -/
noncomputable def localRestrictionRangeEquiv (hω : PropagatesWithin ω 𝓝)
    (Λ : Finset ℤ) :
    LocalAlgebra d Λ ≃⋆ₐ[ℂ] hω.localRestrictionRange Λ :=
  StarAlgEquiv.ofInjective (hω.localRestriction Λ) (hω.localRestriction_injective Λ)

/-- The finite local image written in fixed left/right matrix coordinates whenever its target
region is presented as a disjoint union.

The left matrix index is `Config d Γ` and the right matrix index is `Config d Δ`. The result is
therefore a star-subalgebra of the bipartite matrix algebra on which
`Matrix.leftSupportAlgebra` and `Matrix.rightSupportAlgebra` are defined; neither support algebra
is formed here.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266; the finite local image
comes from arXiv:1703.09188, Appendix, line 2298. -/
noncomputable def bipartiteLocalRestrictionRange (hω : PropagatesWithin ω 𝓝)
    (Λ Γ Δ : Finset ℤ) (hΓΔ : Disjoint Γ Δ)
    (htarget : regionSumset Λ 𝓝 = Γ ∪ Δ) :
    StarSubalgebra ℂ
      (Matrix (Config d Γ × Config d Δ) (Config d Γ × Config d Δ) ℂ) :=
  StarSubalgebra.bipartiteReindex hΓΔ (htarget ▸ hω.localRestrictionRange Λ)

/-- Translation covariance makes the finite-region restrictions natural under lattice
translations, expressed after the canonical embeddings of their propositionally equal target
regions.

For \(a\in\mathbb Z\), the two target regions are equal by
\((\Lambda+a)+\mathcal N=(\Lambda+\mathcal N)+a\). The displayed equality avoids choosing a
transport between the corresponding matrix index types.

Source context: arXiv:1703.09188, Appendix, line 2298; Schumacher--Werner,
quant-ph/0405174, Lemma `lem:localrule`, lines 331--365. This finite-region formula is not stated
separately in either source. -/
theorem localRestriction_translation (hω : PropagatesWithin ω 𝓝)
    (hcov : TranslationCovariant ω) (a : ℤ) (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    quasiLocalObservable d (regionSumset (translateRegion a Λ) 𝓝)
        (hω.localRestriction (translateRegion a Λ) (localTranslation d a Λ A)) =
      quasiLocalObservable d (translateRegion a (regionSumset Λ 𝓝))
        (localTranslation d a (regionSumset Λ 𝓝) (hω.localRestriction Λ A)) := by
  rw [hω.quasiLocalObservable_localRestriction]
  rw [← quasiLocalTranslation_quasiLocalObservable,
    ← quasiLocalTranslation_quasiLocalObservable,
    hω.quasiLocalObservable_localRestriction]
  exact (translationCovariant_iff ω).mp hcov a (quasiLocalObservable d Λ A)

end PropagatesWithin

end SpinChain
