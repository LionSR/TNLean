/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.QuasiLocalCommutant
import TNLean.QCA.TranslationCovariance

/-!
# Inverse propagation of quasi-local automorphisms

Finite forward propagation of a quasi-local star-automorphism implies finite forward propagation
of its inverse. At the neighborhood level, a bound by \(\mathcal N\) for the automorphism gives a
bound by the reflected neighborhood \(-\mathcal N\) for its inverse.

The QCA definitions in both cited sources are forward-only. Schumacher--Werner derive inverse
locality through Lemma 5, Theorem 6, and Corollary 7. Here the proof instead uses the exact
characterization of finite support by commutation with all observables outside the region.

## Main results

* `SpinChain.disjoint_regionSumset_of_disjoint_regionSumset_neg` — reflected-neighborhood region
  arithmetic.
* `SpinChain.PropagatesWithin.symm` — a forward propagation bound gives the reflected bound for
  the inverse.
* `SpinChain.HasFinitePropagation.symm` — finite propagation is preserved by inversion.
* `SpinChain.TranslationCovariant.symm` — translation covariance is preserved by inversion.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, line 2298.
* Schumacher--Werner, quant-ph/0405174, Lemma 5, Theorem 6, and Corollary 7.
-/

open scoped Pointwise

namespace SpinChain

/-- If \(\Gamma\) is disjoint from \(\Lambda+(-\mathcal N)\), then
\(\Gamma+\mathcal N\) is disjoint from \(\Lambda\).

This is elementary finite-region arithmetic underlying the reflected inverse-propagation bound. -/
lemma disjoint_regionSumset_of_disjoint_regionSumset_neg
    {Γ Λ 𝓝 : Finset ℤ} (h : Disjoint Γ (regionSumset Λ (-𝓝))) :
    Disjoint (regionSumset Γ 𝓝) Λ := by
  rw [Finset.disjoint_left] at h ⊢
  intro z hz hzΛ
  obtain ⟨g, hg, n, hn, hgn⟩ := (mem_regionSumset z Γ 𝓝).mp hz
  apply h hg
  rw [mem_regionSumset]
  refine ⟨z, hzΛ, -n, ?_, ?_⟩
  · exact Finset.neg_mem_neg hn
  · omega

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d} {𝓝 : Finset ℤ}

namespace PropagatesWithin

/-- If an automorphism propagates within \(\mathcal N\), then its inverse propagates within the
reflected neighborhood \(-\mathcal N\).

The source definitions are forward-only. Schumacher--Werner derive inverse locality from their
Lemma 5, Theorem 6, and Corollary 7. This proof uses the exact outside-commutant characterization
of finite support. -/
theorem symm (hω : PropagatesWithin ω 𝓝) : PropagatesWithin ω.symm (-𝓝) := by
  intro Λ x hx
  rw [quasiLocalSupportedIn_iff_commute_disjoint]
  intro Γ hΓ y hy
  have hωy := hω Γ y hy
  have hregions := disjoint_regionSumset_of_disjoint_regionSumset_neg hΓ
  have hcomm : Commute x (ω y) :=
    (quasiLocalSupportedIn_iff_commute_disjoint x Λ).mp hx
      (regionSumset Γ 𝓝) hregions (ω y) hωy
  simpa only [StarAlgEquiv.symm_apply_apply] using hcomm.map ω.symm

end PropagatesWithin

namespace HasFinitePropagation

/-- Finite forward propagation is preserved by inversion.

This is derived from the forward-only locality condition. Source route: Schumacher--Werner,
Lemma 5, Theorem 6, and Corollary 7. -/
theorem symm (hω : HasFinitePropagation ω) : HasFinitePropagation ω.symm := by
  obtain ⟨𝓝, h𝓝⟩ := hω
  exact ⟨-𝓝, h𝓝.symm⟩

end HasFinitePropagation

namespace TranslationCovariant

/-- The inverse of a translation-covariant automorphism is translation covariant.

Source context: arXiv:1703.09188, Appendix, line 2298. -/
theorem symm (hω : TranslationCovariant ω) : TranslationCovariant ω.symm := by
  intro a
  rw [← StarAlgEquiv.aut_inv]
  exact (hω a).inv_left

end TranslationCovariant

end SpinChain
