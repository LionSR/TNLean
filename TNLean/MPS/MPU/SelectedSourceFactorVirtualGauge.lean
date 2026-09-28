/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.NormalizedSourceDecompositionUniqueness
import TNLean.MPS.MPU.SimpleTensorEquivalence
import TNLean.MPS.MPU.VirtualSourceFactorTransport

/-!
# Selected source factors under a virtual unitary gauge

The selected source factorizations of two simple canonical-form-II tensors
are compared after one tensor is conjugated on its virtual leg. The two
recorded fixed points remain independent.

## References

* CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624–648).
* FBC25, arXiv:2502.20257, Lemma `lem:deco` (lines 1052–1066).
-/

open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

private theorem selected_source_u_unitary_of_simple
    {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSimple : IsMPUSimple U) :
    (SourceFactors.sourceU U (sourceFactors U hU.ρ hU.ρ_posDef)).IsUnitaryBetween := by
  change (sourceU U hU.ρ hU.ρ_posDef).IsUnitaryBetween
  exact (hU.isMPUSimple_tfae.out 1 3).mp hSimple

end MPOTensor

namespace MPOTensor

/-- The source factors selected for a unitary virtual conjugate differ from
the transported source factors by unitary changes of the two source-rank
coordinates. There is no positive rescaling because both second-cut left
factors are isometries.

This is the forward source-factor comparison associated with CPSV17,
arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624–648), using the
raw cut transport of Proposition IV.5 (lines 786–812) and the normalized form
of FBC25, arXiv:2502.20257, Lemma `lem:deco` (lines 1052–1066). The recorded weights
of the two tensors remain independent. In the source diagrams
`II_RelationStandard1.png` and `II_RelationStandard2.png`, the gauges are
oriented as $x=W_2^\dagger$ and $y=W_1^\dagger$. This orientation is a
consequence of the factor identities above, obtained by substituting them into
the source-gate contraction and using $z^\dagger z=I_D$; it is not asserted by
this theorem. -/
theorem IsMPUCanonicalFormII.exists_selected_source_factor_unitary_gauges
    {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hSimpleU : IsMPUSimple U)
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (hV : IsMPUCanonicalFormII
      (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ))))
    (hSimpleV : IsMPUSimple
      (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
        (star (z : Matrix (Fin D) (Fin D) ℂ)))) :
    let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))
    let er : Fin r[U] ≃ Fin r[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
    let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
    let S := sourceFactors U hU.ρ hU.ρ_posDef
    let T := sourceFactors V hV.ρ hV.ρ_posDef
    let X₁ := Matrix.reindex (Equiv.refl _) er
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁)
    let Y₁ := Matrix.reindex er (Equiv.refl _)
      (S.Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)))
    let X₂ := Matrix.reindex (Equiv.refl _) el
      (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂)
    let Y₂ := Matrix.reindex el (Equiv.refl _)
      (S.Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        star (z : Matrix (Fin D) (Fin D) ℂ)))
    ∃ (W₁ : Matrix.unitaryGroup (Fin r[V]) ℂ)
      (W₂ : Matrix.unitaryGroup (Fin ℓ[V]) ℂ),
      T.X₁ = X₁ * (W₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ) ∧
      T.Y₁ = star (W₁ : Matrix (Fin r[V]) (Fin r[V]) ℂ) * Y₁ ∧
      T.X₂ = X₂ * (W₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ∧
      T.Y₂ = star (W₂ : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) * Y₂ := by
  let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))
  let er : Fin r[U] ≃ Fin r[V] :=
    (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
  let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
    (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  let T := sourceFactors V hV.ρ hV.ρ_posDef
  let R₁ := ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℂ))
  let R₂ := ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      star (z : Matrix (Fin D) (Fin D) ℂ))
  let X₁ := Matrix.reindex (Equiv.refl _) er
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁)
  let Y₁ := Matrix.reindex er (Equiv.refl _) (S.Y₁ * R₁)
  let Z₁ := Matrix.reindex (Equiv.refl _) er (R₁ᴴ * S.Z₁)
  let X₂ := Matrix.reindex (Equiv.refl _) el
      (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂)
  let Y₂ := Matrix.reindex el (Equiv.refl _) (S.Y₂ * R₂)
  let Z₂ := Matrix.reindex (Equiv.refl _) el (R₂ᴴ * S.Z₂)
  have huU := selected_source_u_unitary_of_simple hU hSimpleU
  have huV := selected_source_u_unitary_of_simple hV hSimpleV
  have hp := transported_source_factor_premises_at_selected_ranks U z S huU
  have hleft₁ : (T.X₁ᴴ * sourceWeight (d := d) hV.ρ) * T.X₁ = 1 :=
    T.X₁_weighted_isometry
  have hleft₂ : T.X₂ᴴ * T.X₂ = 1 := T.X₂_isometry
  have hresult := exists_unitary_source_gauges_of_isometric_second_factors
    (U := V) (X₁ := X₁) (Xt₁ := T.X₁) (Y₁ := Y₁) (Yt₁ := T.Y₁)
    (X₂ := X₂) (Xt₂ := T.X₂) (Y₂ := Y₂) (Yt₂ := T.Y₂)
    (Lt₁ := T.X₁ᴴ * sourceWeight (d := d) hV.ρ) (R₁ := Z₁)
    (Lt₂ := T.X₂ᴴ) (R₂ := Z₂)
    hp.1.symm T.sourceCutM₁_eq.symm hp.2.1.symm T.sourceCutM₂_eq.symm
    hleft₁ hp.2.2.1 hleft₂ hp.2.2.2.1 hp.2.2.2.2.2 huV
    hp.2.2.2.2.1 T.X₂_isometry
  exact hresult

end MPOTensor
