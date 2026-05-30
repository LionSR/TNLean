/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.ProportionalMatch.Core
import TNLean.MPS.FundamentalTheorem.SectorBNT.CoeffIdentity

/-!
# Proportional sector matching for two BNT canonical forms

This file assembles the full-basis and bijective matching consequences from the
analytic core into the final proportional sector-matching theorem.

The main theorem `MPSTensor.ft_sector_bnt_proportional_sector_match` delivers
the basis-count identity $g_P = g_Q$, a basis bijection
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

/-! ### Full-basis proportional matching (Q → P direction)

For every sector `k` of `Q`, there exists a sector `j` of `P` of equal
bond dimension, gauge-phase equivalent in the cast-compatible shape, and
with non-decaying cross-overlap.  This is the proportional analogue of
`StrongMatch.forall_k_exists_j_nondecaying_overlap_of_sameMPV`.

Paper anchor: CPSV16 §II.C lines 349–352 (theorem `thm1`);
Appendix MPV theorem statement lines 1167–1170 and Appendix MPV proof
line 1182 (matching). -/
theorem forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∀ k : Fin Q.basisCount,
      ∃ (j : Fin P.basisCount) (h : P.basisDim j = Q.basisDim k),
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis j))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
          atTop (𝓝 0) := by
  classical
  intro k
  obtain ⟨j_w, q_w, hq_w⟩ := hP.weight_unit_exists
  obtain ⟨j₁, hDim, hGE, hNonDecay⟩ :=
    exists_block_match_at_Q_of_eventuallyProportional
      hP hQ k (hUnitQ k) j_w ⟨q_w, hq_w⟩ hProp
  exact ⟨j₁, hDim, hGE, hNonDecay⟩

/-! ### Bijective matching from per-block existentials in both directions

The bijection construction composes two gauge-phase equivalences through a
common centre.  The cast-aware symmetry and transitivity lemmas
(`gaugePhaseEquiv_symm_same_dim`, `gaugePhaseEquiv_swap_cast`,
`gaugePhaseEquiv_trans_same_dim`, `gaugePhaseEquiv_cast_compose_via_centre`)
are shared with the equal-MPV variant in
`SectorBNT/StrongMatch.lean`. -/

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
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ β : Fin Q.basisCount ≃ Fin P.basisCount,
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (β k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (β k)) (Q.basis k) N)
          atTop (𝓝 0) := by
  classical
  have hFwd :=
    forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional
      hP hQ hUnitQ hProp
  have hProp_symm : EventuallyNonzeroProportionalMPV₂ Q.toTensor P.toTensor :=
    hProp.symm
  have hBwd :=
    forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional
      hQ hP hUnitP hProp_symm
  let φ₀ : Fin Q.basisCount → Fin P.basisCount := fun k => (hFwd k).choose
  have φ₀_spec : ∀ k : Fin Q.basisCount,
      ∃ h : P.basisDim (φ₀ k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (φ₀ k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (φ₀ k)) (Q.basis k) N)
          atTop (𝓝 0) := fun k => (hFwd k).choose_spec
  have rebase_centre_P :
      ∀ (j j' : Fin P.basisCount) (_hj : j = j')
        {kv : Fin Q.basisCount}
        (h_t : P.basisDim j' = Q.basisDim kv)
        (_GE : GaugePhaseEquiv
                  (cast (congr_arg (MPSTensor d) h_t) (P.basis j'))
                  (Q.basis kv)),
        ∃ h_t' : P.basisDim j = Q.basisDim kv,
          GaugePhaseEquiv
              (cast (congr_arg (MPSTensor d) h_t') (P.basis j))
              (Q.basis kv) := by
    rintro _ _ rfl _ h_t GE
    exact ⟨h_t, GE⟩
  have hφ₀_inj : Function.Injective φ₀ := by
    intro k₁ k₂ hjEq
    obtain ⟨h₁, GE₁, _⟩ := φ₀_spec k₁
    obtain ⟨h₂, GE₂, _⟩ := φ₀_spec k₂
    by_contra hne
    obtain ⟨h₂', GE₂'⟩ :=
      rebase_centre_P (φ₀ k₁) (φ₀ k₂) hjEq h₂ GE₂
    have hQdim : Q.basisDim k₁ = Q.basisDim k₂ := h₁.symm.trans h₂'
    have hQGE :
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hQdim) (Q.basis k₁))
            (Q.basis k₂) :=
      gaugePhaseEquiv_cast_compose_via_centre
        (A := P.basis (φ₀ k₁))
        (B := Q.basis k₁) (C := Q.basis k₂) h₁ h₂' GE₁ GE₂'
    exact hQ.basis_distinct k₁ k₂ hne hQdim hQGE
  let ψ₀ : Fin P.basisCount → Fin Q.basisCount := fun j => (hBwd j).choose
  have ψ₀_spec : ∀ j : Fin P.basisCount,
      ∃ h : Q.basisDim (ψ₀ j) = P.basisDim j,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (Q.basis (ψ₀ j)))
            (P.basis j) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (Q.basis (ψ₀ j)) (P.basis j) N)
          atTop (𝓝 0) := fun j => (hBwd j).choose_spec
  have rebase_centre_Q :
      ∀ (k k' : Fin Q.basisCount) (_hk : k = k')
        {jv : Fin P.basisCount}
        (h_t : Q.basisDim k' = P.basisDim jv)
        (_GE : GaugePhaseEquiv
                  (cast (congr_arg (MPSTensor d) h_t) (Q.basis k'))
                  (P.basis jv)),
        ∃ h_t' : Q.basisDim k = P.basisDim jv,
          GaugePhaseEquiv
              (cast (congr_arg (MPSTensor d) h_t') (Q.basis k))
              (P.basis jv) := by
    rintro _ _ rfl _ h_t GE
    exact ⟨h_t, GE⟩
  have hψ₀_inj : Function.Injective ψ₀ := by
    intro j₁ j₂ hkEq
    obtain ⟨h₁, GE₁, _⟩ := ψ₀_spec j₁
    obtain ⟨h₂, GE₂, _⟩ := ψ₀_spec j₂
    by_contra hne
    obtain ⟨h₂', GE₂'⟩ :=
      rebase_centre_Q (ψ₀ j₁) (ψ₀ j₂) hkEq h₂ GE₂
    have hPdim : P.basisDim j₁ = P.basisDim j₂ := h₁.symm.trans h₂'
    have hPGE :
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hPdim) (P.basis j₁))
            (P.basis j₂) :=
      gaugePhaseEquiv_cast_compose_via_centre
        (A := Q.basis (ψ₀ j₁))
        (B := P.basis j₁) (C := P.basis j₂) h₁ h₂' GE₁ GE₂'
    exact hP.basis_distinct j₁ j₂ hne hPdim hPGE
  have hCardQP :
      Fintype.card (Fin Q.basisCount) ≤ Fintype.card (Fin P.basisCount) :=
    Fintype.card_le_of_injective φ₀ hφ₀_inj
  have hCardPQ :
      Fintype.card (Fin P.basisCount) ≤ Fintype.card (Fin Q.basisCount) :=
    Fintype.card_le_of_injective ψ₀ hψ₀_inj
  have hCard :
      Fintype.card (Fin Q.basisCount) = Fintype.card (Fin P.basisCount) :=
    le_antisymm hCardQP hCardPQ
  have hφ₀_bij : Function.Bijective φ₀ :=
    (Fintype.bijective_iff_injective_and_card φ₀).2 ⟨hφ₀_inj, hCard⟩
  let β : Fin Q.basisCount ≃ Fin P.basisCount := Equiv.ofBijective φ₀ hφ₀_bij
  refine ⟨β, ?_⟩
  intro k
  simpa [β] using φ₀_spec k

/-! ### Final theorem: proportional sector matching with basis-count equality -/

/-- **Proportional sector matching for two BNT canonical forms.**

If two BNT canonical sector decompositions have eventually proportional
assembled tensors with nonzero per-$N$ scalar, and each basis sector on both
sides carries a unit-modulus copy weight, then the basis counts agree and
there is a basis bijection carrying matched bond-dimension equality and
per-block gauge-phase equivalence.

Paper anchor: CPSV16 §II.C lines 349–352 (theorem `thm1`), Appendix MPV
theorem statement lines 1167–1170, and Appendix MPV proof line 1182 (matching
proof); CPSV21 lines 1891–1894 (proportional-MPV theorem-level target).
This is the proportional analogue
of `ft_sector_bnt_equal_mps_gaugeEquiv_witnesses` (`SectorBNT/FundamentalCoord.lean`)
in the matching layer. The source proportional theorem stops at sector
matching; the weight comparison and global gauge in CPSV16 Appendix MPV proof,
lines 1187–1192, belong to the equal-MPV corollary unless an additional
proportional coefficient theorem controls the length-dependent scalar. -/
theorem ft_sector_bnt_proportional_sector_match
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    P.basisCount = Q.basisCount ∧
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount),
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k) := by
  classical
  obtain ⟨β, hβ⟩ :=
    bijective_match_of_eventuallyProportional hP hQ hUnitP hUnitQ hProp
  refine ⟨?_, β, ?_⟩
  · have hCard := Fintype.card_congr β
    simpa using hCard.symm
  · intro k
    obtain ⟨h, hGE, _⟩ := hβ k
    exact ⟨h, hGE⟩

/-- **Proportional sector matching with explicit unit phases and block gauges.**

This is the witness form of `ft_sector_bnt_proportional_sector_match`: after
the proportional BNT block matching of CPSV16 Appendix MPV proof, line 1182, the
matched gauge-phase equivalences provide actual matrices `Xblock k` and
scalars `ζ k`.  The BNT self-overlap normalization forces `‖ζ k‖ = 1`, so
these are the unit phases appearing in the source proportional theorem.

The theorem intentionally stops before the raw coefficient identity.  Under
`EventuallyNonzeroProportionalMPV₂`, that step still has to control the
length-dependent proportionality scalar; it is not the equal-MPV coefficient
identity proved by `coeff_identity_via_matched_mpv_phase`, and it is not
contained in CPSV16 Appendix MPV proof, lines 1187–1192, without the equal-MPV
specialization.

**Scope restriction (per-sector unit weights):** This theorem assumes a
unit-modulus copy in every sector on both sides. CPSV16 Section II.C, line 246
gives only one global unit-weight witness. See
`docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex`. -/
theorem ft_sector_bnt_proportional_sector_match_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hUnitP : ∀ j : Fin P.basisCount, ∃ q : Fin (P.copies j), ‖P.weight j q‖ = 1)
    (hUnitQ : ∀ k : Fin Q.basisCount, ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
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
    bijective_match_of_eventuallyProportional hP hQ hUnitP hUnitQ hProp
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
    exact hP.norm_phase_of_matched_mpv hQ (hMpv k)
  exact ⟨β, hDim, ζ, Xblock, hζ_norm, hConj, hMpv⟩

end MPSTensor
