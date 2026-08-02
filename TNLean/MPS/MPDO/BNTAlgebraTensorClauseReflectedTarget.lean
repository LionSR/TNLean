/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseConditionalRFP
import TNLean.MPS.MPDO.TwoSitePrefixReflectedMarkedChain

/-!
# The positive-tail reflected target of the two-site algebra tensor

This file completes the one-site/two-site marked comparison in Appendix C.4
of arXiv:1606.00608.  A one-site raw sector corner and a two-site
gauge-dressed corner are reflected while retaining the same unblocked tail.
The resulting common target identifies the two Gram dressings by the literal
CPSV form of Lemma L.

## Main results

* `TwoSiteExactSectorGauge.gramDressing_gauge_eq_one`
* `TwoSiteExactSectorGauge.has_identity_positive_tail_reflected_target`
* `BNTAlgebraTensorClause.isRFPViaTS`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13 and Appendix C.4, lines 2048--2085
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteExactSectorGauge

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- The exact two-site gauge and the identity gauge give the same Gram
dressing of every algebra-side sector.

The proof reflects the one-site raw corner and the two-site gauge-dressed
corner against a common unblocked tail.  Both resulting marked tensors lie in
the physical-letter span of the one-site tensor, so literal CPSV Lemma L
identifies them.

**Local fix (mixed one-site/two-site prefix):** Appendix C.4 invokes
Proposition 4.13 after independently choosing the one-site and two-site
vertical forms.  The formal proof compares their marked chains by compressing
one physical site in the first form and two physical sites in the second,
while retaining the same unblocked tail.  This fills the omitted common-space
comparison recorded in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and lines
1898--1921, and Appendix C.4, lines 2048--2057. -/
theorem gramDressing_gauge_eq_one
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount) :
    gramDressing (S.gauge γ)
        (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ)) =
      gramDressing
        (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
        (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
          (H.tensor γ)) := by
  classical
  let A : MPSTensor (D * D)
      (S.decomposition.bondDim (S.relabel γ)) :=
    cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ)) (H.tensor γ)
  obtain ⟨W, c, _hW, hc, hCornerOne⟩ :=
    S.exists_oneSite_raw_sector_corner γ
  obtain ⟨V, k, _hV, hk, hCornerTwo⟩ :=
    S.exists_blockTwo_gauge_sector_corner γ
  let G : Matrix
      (Fin (S.decomposition.bondDim (S.relabel γ)))
      (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ :=
    (S.gauge γ : Matrix
      (Fin (S.decomposition.bondDim (S.relabel γ)))
      (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ *
      (S.gauge γ : Matrix
        (Fin (S.decomposition.bondDim (S.relabel γ)))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)
  let fGauge := twoSidedCompressionCoefficients
    (W * Gᴴ) (W * G⁻¹) c
  let fOne := twoSidedCompressionCoefficients W W c
  have hGaugeCompression : ∀ v : Fin (D * D),
      (W * Gᴴ)ᴴ * verticalTensor M v * (W * G⁻¹) =
        c • gramDressing (S.gauge γ) A v := by
    intro v
    calc
      (W * Gᴴ)ᴴ * verticalTensor M v * (W * G⁻¹) =
          G * (Wᴴ * verticalTensor M v * W) * G⁻¹ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
      _ = G * (c • A v) * G⁻¹ := by rw [hCornerOne v]
      _ = c • gramDressing (S.gauge γ) A v := by
        simp only [G, gramDressing, Matrix.mul_smul, Matrix.smul_mul]
  have hPhysicalGauge : ∀ u,
      MPSTensor.linearMarkedTensor fGauge M.toMPSTensor u =
        horizontalSlice (gramDressing (S.gauge γ) A) u.divNat u.modNat := by
    intro u
    exact linearMarkedTensor_twoSidedCompressionCoefficients
      (gramDressing (S.gauge γ) A) (W * Gᴴ) (W * G⁻¹) c
      (ne_of_gt hc) hGaugeCompression u
  have hPhysicalOne : ∀ u,
      MPSTensor.linearMarkedTensor fOne M.toMPSTensor u =
        horizontalSlice A u.divNat u.modNat := by
    intro u
    exact linearMarkedTensor_twoSidedCompressionCoefficients
      A W W c (ne_of_gt hc) hCornerOne u
  have hMarked : ∀ (N : ℕ)
      (r s : Fin (S.decomposition.bondDim (S.relabel γ)))
      (σ τ : Fin N → Fin d),
      markedChainCoefficient (gramDressing (S.gauge γ) A) M r s
          (List.ofFn σ) (List.ofFn τ) =
        markedChainCoefficient A M r s (List.ofFn σ) (List.ofFn τ) := by
    intro N r s σ τ
    exact
      (hM.markedChainCoefficient_blockTwoPrefix_gramDressing_eq_reflectedAdjoint
        A V (S.gauge γ) k hk hCornerTwo N r s σ τ).trans
      (hM.markedChainCoefficient_eq_reflectedAdjoint
        A W c hc hCornerOne N r s σ τ).symm
  have hTrace : ∀ (L : ℕ), 0 < L → ∀
      (u : Fin (S.decomposition.bondDim (S.relabel γ) *
        S.decomposition.bondDim (S.relabel γ)))
      (w : Fin L → Fin (d * d)),
      Matrix.trace
          (MPSTensor.linearMarkedTensor fGauge M.toMPSTensor u *
            MPSTensor.evalWord M.toMPSTensor (List.ofFn w)) =
        Matrix.trace
          (MPSTensor.linearMarkedTensor fOne M.toMPSTensor u *
            MPSTensor.evalWord M.toMPSTensor (List.ofFn w)) := by
    intro L _hL u w
    rw [hPhysicalGauge u, hPhysicalOne u,
      evalWord_toMPSTensor_ofFn]
    exact hMarked L u.divNat u.modNat
      (fun t ↦ (w t).divNat) (fun t ↦ (w t).modNat)
  have hMarks :
      MPSTensor.linearMarkedTensor fGauge M.toMPSTensor =
        MPSTensor.linearMarkedTensor fOne M.toMPSTensor :=
    hCanonical.linearMarkedTensor_eq_of_trace_agree
      M.toMPSTensor fGauge fOne hTrace
  have hRaw : gramDressing (S.gauge γ) A = A := by
    funext v
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective v
    ext r s
    have hSlice := congrFun hMarks (finProdFinEquiv (r, s))
    rw [hPhysicalGauge, hPhysicalOne] at hSlice
    simpa only [horizontalSlice, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat] using
        congrFun (congrFun hSlice a) b
  have hOne : gramDressing
      (1 : GL (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) A = A := by
    funext v
    simp only [gramDressing, Units.val_one, Matrix.conjTranspose_one,
      Matrix.one_mul, inv_one, Matrix.mul_one]
  simpa only [A] using hRaw.trans hOne.symm

/-- The positive-tail reflected target follows from the tensor-attached
algebra clause, literal CPSV canonical form, and MPDO positivity.

**Local fix (mixed one-site/two-site prefix):** The common target is obtained
from the mixed-prefix comparison used in `gramDressing_gauge_eq_one`, as
documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and lines
1898--1921, and Appendix C.4, lines 2048--2057. -/
theorem has_identity_positive_tail_reflected_target
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount) :
    HasIdentityPositiveTailReflectedTarget S γ := by
  have hGram := S.gramDressing_gauge_eq_one hCanonical hM γ
  intro N _hN r s σ τ
  rw [← hGram]
  exact S.markedChainCoefficient_gauge_eq_reflectedAdjoint
    hM γ N r s σ τ

/-- The Gram matrix of every exact two-site sector gauge is a positive real
multiple of the identity.

**Local fix (mixed one-site/two-site prefix):** The marked comparison needed
for the Gram conclusion is supplied as documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1898--1921, and
Appendix C.4, lines 2048--2057. -/
theorem gauge_gram_eq_pos_smul_one
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount) :
    ∃ ω : ℝ, 0 < ω ∧
      (S.gauge γ : Matrix
        (Fin (S.decomposition.bondDim (S.relabel γ)))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ *
          (S.gauge γ : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) =
        (ω : ℂ) • 1 :=
  S.gauge_gram_eq_pos_smul_one_of_positive_tail_reflected_target
    hCanonical hM γ
      (S.has_identity_positive_tail_reflected_target hCanonical hM γ)

/-- Every exact two-site sector gauge can be normalized to a unitary with the
same conjugation action.

**Local fix (mixed one-site/two-site prefix):** The positive Gram scalar used
in the normalization is obtained by the marked comparison documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1903--1908, applied at
Appendix C.4, lines 2048--2057. -/
theorem exists_unitary_sector_conjugacy
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (γ : Fin H.labelCount) :
    ∃ U : Matrix.unitaryGroup
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ,
      ∀ i : Fin (D * D),
        S.decomposition.tensor (S.relabel γ) i =
          (U : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
          (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
            (H.tensor γ)) i *
          (U : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ :=
  S.exists_unitary_sector_conjugacy_of_positive_tail_reflected_target
    hCanonical hM γ
      (S.has_identity_positive_tail_reflected_target hCanonical hM γ)

/-- The exact sector gauges determine simultaneous unitary conjugacies between
the paired one-site and two-site BNT tensors.

**Local fix (mixed one-site/two-site prefix):** The pointwise unitary
normalizations use the marked comparison documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1903--1908, and
Appendix C.4, lines 2048--2057. -/
noncomputable def UnitarySectorConjugacy.ofAlgebraTensorClause
    (S : TwoSiteExactSectorGauge H)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) : UnitarySectorConjugacy S :=
  UnitarySectorConjugacy.ofPositiveTailReflectedTarget
    S hCanonical hM fun γ ↦
      S.has_identity_positive_tail_reflected_target hCanonical hM γ

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

namespace BNTAlgebraTensorClause

/-- **Theorem 4.14(ii) implies (i).** A tensor-attached BNT algebra clause for
an MPDO in literal CPSV canonical form yields the renormalization fixed-point
condition of Definition 4.1.

**Local fix (mixed one-site/two-site prefix):** The omitted marked comparison
in Appendix C.4, lines 2048--2057, including its invocation at line 2057, is
supplied by the mixed-prefix argument documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

**Local fix (zero-sector complement):** The physical maps are completed on
the discarded complements as documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Theorem 4.14(ii)--(i), lines 972--993, and
Appendix C.4, lines 2046--2085. -/
theorem isRFPViaTS (H : BNTAlgebraTensorClause M)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) : IsRFPViaTS M := by
  let S := H.toTwoSiteExactSectorGauge hCanonical hM
  exact (TwoSiteExactSectorGauge.UnitarySectorConjugacy.ofAlgebraTensorClause
    S hCanonical hM).isRFPViaTS

end BNTAlgebraTensorClause

namespace HasBNTAlgebraTensorClause

/-- The existential tensor-attached BNT algebra condition implies the
renormalization fixed-point condition for an MPDO in literal CPSV canonical
form.

**Local fix (mixed one-site/two-site prefix):** The omitted marked comparison
is supplied as documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

**Local fix (zero-sector complement):** The physical maps are completed on
the discarded complements as documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Theorem 4.14(ii)--(i), lines 972--993, and
Appendix C.4, lines 2046--2085. -/
theorem isRFPViaTS (h : HasBNTAlgebraTensorClause M)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) : IsRFPViaTS M := by
  obtain ⟨H⟩ := h
  exact H.isRFPViaTS hCanonical hM

end HasBNTAlgebraTensorClause

end MPOTensor
