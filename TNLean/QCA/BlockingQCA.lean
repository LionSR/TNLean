/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.BlockingTranslation
import TNLean.QCA.IsQCA

/-!
# Transporting quantum cellular automata through site blocking

Conjugating an original-chain automorphism by the quasi-local site-blocking equivalence produces
an automorphism of the blocked chain.  A finite original propagation neighborhood induces the
carry-aware blocked neighborhood from `BlockingTranslation`, while blocked unit translation
corresponds exactly to original translation by one block length.

Only the forward implications needed for blocking a QCA are asserted here.  In particular,
commutation with original translation by `L` need not imply covariance under original unit
translation.

## Main definitions

* `SpinChain.blockedAutomorphism` — the conjugate `B⁻¹ ω B` on the blocked chain.

## Main results

* `SpinChain.PropagatesWithin.blocked` — carry-aware transport of a propagation neighborhood.
* `SpinChain.HasFinitePropagation.blocked` — finite forward propagation survives blocking.
* `SpinChain.translationCovariant_blockedAutomorphism_iff` — blocked translation covariance is
  exactly commutation with original translation by `L`.
* `SpinChain.TranslationCovariant.blocked` — original translation covariance survives blocking.
* `SpinChain.IsQCA.blocked` — a QCA remains a QCA after site blocking.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, line 2308.
-/

namespace SpinChain

/-- Conjugate an original-chain star-automorphism by the quasi-local blocking equivalence.

If `B` denotes `quasiLocalBlocking d L`, then this is the blocked-chain automorphism
`B⁻¹ ω B`.

Source: arXiv:1703.09188, Appendix, line 2308. -/
noncomputable def blockedAutomorphism (d L : ℕ) [NeZero d] [NeZero L]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) :
    QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) ≃⋆ₐ[ℂ]
      QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) :=
  ((quasiLocalBlocking d L).trans ω).trans (quasiLocalBlocking d L).symm

/-- Evaluation of the blocked automorphism displays the conjugation orientation explicitly. -/
@[simp]
lemma blockedAutomorphism_apply (d L : ℕ) [NeZero d] [NeZero L]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d)
    (A : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L)) :
    blockedAutomorphism d L ω A =
      (quasiLocalBlocking d L).symm (ω (quasiLocalBlocking d L A)) :=
  rfl

/-- Blocking commutes with taking the inverse automorphism. -/
@[simp]
lemma blockedAutomorphism_symm (d L : ℕ) [NeZero d] [NeZero L]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) :
    (blockedAutomorphism d L ω).symm = blockedAutomorphism d L ω.symm := by
  ext A
  rw [StarAlgEquiv.symm_apply_eq]
  simp only [blockedAutomorphism_apply, StarAlgEquiv.apply_symm_apply,
    StarAlgEquiv.symm_apply_apply]

namespace PropagatesWithin

/-- A propagation neighborhood transports through site blocking to its exact carry-aware blocked
neighborhood.

Source context: arXiv:1703.09188, Appendix, line 2308. -/
lemma blocked {d L : ℕ} [NeZero d] [NeZero L]
    {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d} {𝓝 : Finset ℤ}
    (hω : PropagatesWithin ω 𝓝) :
    PropagatesWithin (blockedAutomorphism d L ω) (blockedNeighborhood L 𝓝) := by
  intro Λ A hA
  have hblocked := quasiLocalBlocking_supportedIn d L hA
  have himage := hω (expandedRegion L Λ) (quasiLocalBlocking d L A) hblocked
  have hreverse := quasiLocalBlocking_symm_supportedIn d L himage
  rw [blockHull_regionSumset_expandedRegion] at hreverse
  simpa only [blockedAutomorphism_apply] using hreverse

end PropagatesWithin

namespace HasFinitePropagation

/-- Finite forward propagation is preserved by site blocking. -/
lemma blocked {d L : ℕ} [NeZero d] [NeZero L]
    {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
    (hω : HasFinitePropagation ω) : HasFinitePropagation (blockedAutomorphism d L ω) := by
  obtain ⟨𝓝, h𝓝⟩ := hω
  exact ⟨blockedNeighborhood L 𝓝, h𝓝.blocked⟩

end HasFinitePropagation

/-- Translation covariance of the blocked automorphism is equivalent to commutation of the
original automorphism with translation by one whole block.

This does not characterize covariance under original unit translation when `L ≠ 1`.
Source context: arXiv:1703.09188, Appendix, line 2308. -/
theorem translationCovariant_blockedAutomorphism_iff
    (d L : ℕ) [NeZero d] [NeZero L]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) :
    TranslationCovariant (blockedAutomorphism d L ω) ↔
      Commute ω (quasiLocalTranslation d (L : ℤ)) := by
  rw [translationCovariant_iff_commute_one]
  constructor
  · intro h
    change ω * quasiLocalTranslation d (L : ℤ) = quasiLocalTranslation d (L : ℤ) * ω
    ext A
    let X := (quasiLocalBlocking d L).symm A
    have hX := DFunLike.congr_fun h.eq X
    have hBX := congrArg (quasiLocalBlocking d L) hX
    simpa only [StarAlgEquiv.mul_apply, blockedAutomorphism_apply, X,
      StarAlgEquiv.apply_symm_apply, StarAlgEquiv.symm_apply_apply,
      quasiLocalBlocking_translation, one_mul] using hBX
  · intro h
    change blockedAutomorphism d L ω * quasiLocalTranslation _ 1 =
      quasiLocalTranslation _ 1 * blockedAutomorphism d L ω
    ext A
    change blockedAutomorphism d L ω (quasiLocalTranslation _ 1 A) =
      quasiLocalTranslation _ 1 (blockedAutomorphism d L ω A)
    have hA : ω (quasiLocalTranslation d (L : ℤ) (quasiLocalBlocking d L A)) =
        quasiLocalTranslation d (L : ℤ) (ω (quasiLocalBlocking d L A)) := by
      simpa only [StarAlgEquiv.mul_apply] using
        DFunLike.congr_fun h.eq (quasiLocalBlocking d L A)
    rw [blockedAutomorphism_apply, quasiLocalBlocking_translation, one_mul, hA,
      blockedAutomorphism_apply]
    rw [StarAlgEquiv.symm_apply_eq, quasiLocalBlocking_translation, one_mul,
      StarAlgEquiv.apply_symm_apply]

namespace TranslationCovariant

/-- Translation covariance is preserved by site blocking.

Only this forward implication is valid in general: blocked unit covariance records commutation of
the original automorphism with translation by `L`, not necessarily by one site.
Source context: arXiv:1703.09188, Appendix, line 2308. -/
lemma blocked {d L : ℕ} [NeZero d] [NeZero L]
    {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
    (hω : TranslationCovariant ω) : TranslationCovariant (blockedAutomorphism d L ω) :=
  (translationCovariant_blockedAutomorphism_iff d L ω).2 (hω (L : ℤ))

end TranslationCovariant

namespace IsQCA

/-- A one-dimensional QCA remains a QCA after grouping `L` consecutive sites into one blocked
site.

Source: arXiv:1703.09188, Appendix, line 2308. -/
lemma blocked {d L : ℕ} [NeZero d] [NeZero L]
    {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
    (hω : IsQCA ω) : IsQCA (blockedAutomorphism d L ω) :=
  ⟨hω.translationCovariant.blocked, hω.hasFinitePropagation.blocked⟩

end IsQCA

end SpinChain
