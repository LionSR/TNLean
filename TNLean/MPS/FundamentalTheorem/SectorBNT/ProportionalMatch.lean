/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.ProportionalMatch.Core
import TNLean.MPS.FundamentalTheorem.SectorBNT.CoeffIdentity

/-!
# Proportional sector matching for two BNT canonical forms

The analytic single-sector matcher yields full-basis and bijective matching
consequences, culminating in the proportional sector-matching theorem.

The main theorem `MPSTensor.ft_sector_bnt_proportional_sector_match_witnesses`
delivers the basis-count identity $g_P = g_Q$, a basis bijection
$\beta : \{1,\dots,g_Q\} \to \{1,\dots,g_P\}$, per-block bond-dimension
equality $D_P^{(\beta k)} = D_Q^{(k)}$, and per-block gauge-phase equivalence
$B_k = \zeta_k X_k A_{\beta k} X_k^{-1}$.

## References

* CPSV16: arXiv:1606.00608, lines 349–352 (theorem `thm1`), 1167–1170
  (restatement), and Appendix MPV proof, line 1182 (matching proof).
* CPSV21: arXiv:2011.12127, lines 1891–1894 (proportional target).
-/

open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Bijective matching from per-block existentials in both directions

The forward and backward existential matches (now in `ProportionalMatch/Core.lean`
as `forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional`) are fed
into the shared bijection construction `bijection_from_matches` (in
`MatchAux.lean`).  The cast-aware symmetry and transitivity lemmas
(`gaugePhaseEquiv_symm_same_dim`, `gaugePhaseEquiv_swap_cast`,
`gaugePhaseEquiv_trans_same_dim`, `gaugePhaseEquiv_cast_compose_via_centre`)
are shared with the equal-MPV variant in `SectorBNT/StrongMatch.lean`. -/

/-- **Bijective proportional matching.**

Applying the per-block matching in both the $Q \to P$ and $P \to Q$
directions gives two injective maps; finite cardinality comparison turns
the forward one into an equivalence $\beta : \{1,\dots,g_Q\} \to
\{1,\dots,g_P\}$, carrying the matched bond-dimension equality,
gauge-phase equivalence, and non-decaying overlap for every sector of $Q$.

Paper anchor: CPSV16 Appendix MPV proof, line 1182, the symmetry step
"$g_A \ge g_B$ and $g_B \ge g_A$". -/
theorem bijective_match_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ β : Fin Q.basisCount ≃ Fin P.basisCount,
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (β k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (β k)) (Q.basis k) N)
          atTop (𝓝 0) := by
  have hProp_symm : EventuallyNonzeroProportionalMPV₂ Q.toTensor P.toTensor :=
    hProp.symm
  have hFwd := forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional hP hQ hProp
  have hBwd := forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional hQ hP hProp_symm
  exact bijection_from_matches hP hQ hFwd hBwd

/-! ### Final theorem: proportional sector matching with basis-count equality -/

/-- **Proportional sector matching with explicit unit phases and block gauges.**

The proportional BNT matching of CPSV16 Appendix MPV proof, line 1182 gives a
bijection between the sectors.  For each matched pair, the gauge-phase
equivalence provides an invertible matrix `Xblock k` and a scalar `ζ k`; the BNT
self-overlap normalization forces `‖ζ k‖ = 1`, so these scalars are the unit
phases in the proportional theorem.

The statement records the sector-level conclusion: basis-count equality,
matched bond dimensions, block gauges, unit phases, and the corresponding
length-`N` MPV phase identity for each normal block.  It requires no
per-sector unit-modulus copy-weight hypothesis.  The copy-weight comparison and
coefficient identities form a separate later statement, not a restriction on
this matching theorem. -/
theorem ft_sector_bnt_proportional_sector_match_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (ζ : Fin Q.basisCount → ℂ)
      (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
              Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))) ∧
      (∀ (k : Fin Q.basisCount) (N : ℕ) (σ : Fin N → Fin d),
        mpv (Q.basis k) σ = (ζ k) ^ N * mpv (P.basis (β k)) σ) := by
  classical
  obtain ⟨β, hβ⟩ :=
    bijective_match_of_eventuallyProportional hP hQ hProp
  let hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k :=
    fun k => (hβ k).choose
  let hGPE : ∀ k : Fin Q.basisCount,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) (Q.basis k) :=
    fun k => (hβ k).choose_spec.1
  let Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ :=
    fun k => (hGPE k).choose
  let ζ : Fin Q.basisCount → ℂ := fun k => (hGPE k).choose_spec.choose
  have hConj : ∀ (k : Fin Q.basisCount) (i : Fin d),
      Q.basis k i =
        ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
          (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
          (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
            Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)) := by
    intro k i
    exact (hGPE k).choose_spec.choose_spec.2 i
  have hMpv : ∀ (k : Fin Q.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis k) σ = (ζ k) ^ N * mpv (P.basis (β k)) σ := by
    intro k N σ
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k)))
      (B := Q.basis k) (Xblock k) (ζ k) (hConj k) N σ,
      mpv_cast_dim (hDim k) (P.basis (β k)) N σ]
  have hζ_norm : ∀ k : Fin Q.basisCount, ‖ζ k‖ = 1 := by
    intro k
    exact hP.norm_phase_of_matched_mpv hQ (fun N _hN σ => hMpv k N σ)
  exact ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, hMpv⟩

end MPSTensor
