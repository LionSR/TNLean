/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.StrongMatch

/-!
# Analytic core for proportional sector matching

Two BNT canonical decompositions with eventually nonzero proportional MPV states
have matching sectors.  More precisely, if
$V^{(N)}(P) = c_N V^{(N)}(Q)$ eventually with $c_N \ne 0$, then every sector of
one decomposition has a sector of the other with non-decaying overlap, equal bond
dimension, and gauge-phase equivalence.

The argument is the proportional analogue of the exact equal-MPV matcher:
partition the `P`-sectors by whether all overlaps against `Q` decay, rewrite the
complementary sectors as exact scalar multiples of `Q`-sector states, and apply
fixed-length linear independence to the resulting relation.  The proportionality
scalar $c_N$ only changes the aggregated `Q`-coefficients; the chosen
`P`-coefficient is still isolated exactly and contradicts
`IsBNTCanonicalForm.coeff_not_eventually_zero`.

## References

* CPSV16: arXiv:1606.00608, lines 349–352 (theorem `thm1`), 1167–1170
  (restatement), and Appendix MPV proof, line 1182 (matching proof).
* CPSV21: arXiv:2011.12127, lines 1891–1894 (proportional target).
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- Convert a fixed-length pointwise MPV proportionality into equality of
`mpvState` vectors. -/
lemma mpvState_eq_smul_of_mpv_eq_mul
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {N : ℕ} {c : ℂ}
    (h : ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ) :
    mpvState A N = c • mpvState B N := by
  apply PiLp.ext
  intro σ
  simpa [mpvState_apply] using h σ

/-- Exact non-decaying-overlap extraction at a fixed `P`-sector from eventual
nonzero proportionality.  The proof is by fixed-length linear-independence
coefficient comparison: the proportionality scalar only scales the aggregated
`Q`-coefficients, while the selected `P`-coefficient remains exact.

This formalizes the CPSV16 matching step: arXiv:1606.00608 (`Cirac2016MPDO_arXiv`),
§II.C lines 349–352, Appendix MPV statement lines 1167–1170, and Appendix MPV
proof line 1182. -/
lemma exists_nondecaying_overlap_exact_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount,
      ¬ Tendsto (fun N : ℕ =>
        mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N) atTop (𝓝 0) := by
  classical
  by_contra hNo
  push Not at hNo
  let T : Finset (Fin P.basisCount) :=
    Finset.univ.filter fun j : Fin P.basisCount =>
      ∀ k : Fin Q.basisCount,
        Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0)
  have hj₀T : j₀ ∈ T := by
    simp [T, hNo]
  have hTQ : ∀ (j : Fin P.basisCount), j ∈ T → ∀ k : Fin Q.basisCount,
      Tendsto (fun N : ℕ =>
        mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0) := by
    intro j hj k
    simpa [T] using (Finset.mem_filter.mp hj).2 k
  have hNotT_nondecay : ∀ j : Fin P.basisCount, j ∉ T →
      ∃ k : Fin Q.basisCount,
        ¬ Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0) := by
    intro j hjT
    have hnot : ¬ (∀ k : Fin Q.basisCount,
        Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0)) := by
      intro hall
      exact hjT (by simp [T, hall])
    push Not at hnot
    exact hnot
  have hScalar : ∀ c : {j : Fin P.basisCount // j ∉ T},
      ∃ k : Fin Q.basisCount, ∃ α : ℕ → ℂ, ∀ N : ℕ,
        mpvState (d := d) (P.basis c.1) N =
          α N • mpvState (d := d) (Q.basis k) N := by
    intro c
    obtain ⟨k, hk⟩ := hNotT_nondecay c.1 c.2
    obtain ⟨α, hα⟩ := exists_state_scalar_of_nondecaying_overlap hP hQ hk
    exact ⟨k, α, hα⟩
  choose kOf αOf hStateOf using hScalar
  letI : Fintype {j : Fin P.basisCount // j ∈ T} := Subtype.fintype (fun j => j ∈ T)
  letI : Fintype {j : Fin P.basisCount // j ∉ T} := Subtype.fintype (fun j => j ∉ T)
  have hLI : ∀ᶠ N in atTop,
      LinearIndependent ℂ
        (Sum.elim
          (fun j : {j : Fin P.basisCount // j ∈ T} =>
            mpvState (d := d) (P.basis j.1) N)
          (fun k : Fin Q.basisCount =>
            mpvState (d := d) (Q.basis k) N)) :=
    restricted_combined_family_eventually_li hP hQ T hTQ
  have hCoeff_eventually_zero :
      ∀ᶠ N : ℕ in atTop, P.coeff N j₀ = 0 := by
    refine (hLI.and hProp).mono ?_
    intro N hN
    rcases hN with ⟨hLIN, hPropN⟩
    rcases hPropN with ⟨c, _hc_ne, hEq⟩
    have hPstate :
        mpvState (d := d) P.toTensor N =
          ∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N := by
      refine mpvState_eq_sum_of_decomp (d := d) P.toTensor P.basis
        (N := N) (fun j => P.coeff N j) ?_
      intro σ
      simpa [smul_eq_mul] using P.mpv_toTensor_eq_sum_coeff (N := N) σ
    have hQstate :
        mpvState (d := d) Q.toTensor N =
          ∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N := by
      refine mpvState_eq_sum_of_decomp (d := d) Q.toTensor Q.basis
        (N := N) (fun k => Q.coeff N k) ?_
      intro σ
      simpa [smul_eq_mul] using Q.mpv_toTensor_eq_sum_coeff (N := N) σ
    have hStateEq :
        mpvState (d := d) P.toTensor N =
          c • mpvState (d := d) Q.toTensor N :=
      mpvState_eq_smul_of_mpv_eq_mul (d := d) P.toTensor Q.toTensor hEq
    have hPQsum :
        (∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N) =
          ∑ k : Fin Q.basisCount, (c * Q.coeff N k) •
            mpvState (d := d) (Q.basis k) N := by
      calc
        (∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N)
            = mpvState (d := d) P.toTensor N := hPstate.symm
        _ = c • mpvState (d := d) Q.toTensor N := hStateEq
        _ = c • (∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N) := by rw [hQstate]
        _ = ∑ k : Fin Q.basisCount, (c * Q.coeff N k) •
            mpvState (d := d) (Q.basis k) N := by
              simp [Finset.smul_sum, smul_smul]
    let sumT : MPVSpace d N :=
      ∑ t : {j : Fin P.basisCount // j ∈ T}, P.coeff N t.1 •
        mpvState (d := d) (P.basis t.1) N
    let sumC : MPVSpace d N :=
      ∑ c' : {j : Fin P.basisCount // j ∉ T}, P.coeff N c'.1 •
        mpvState (d := d) (P.basis c'.1) N
    let sumQ : MPVSpace d N :=
      ∑ k : Fin Q.basisCount, (c * Q.coeff N k) •
        mpvState (d := d) (Q.basis k) N
    let agg : Fin Q.basisCount → ℂ := fun k =>
      ∑ c' : {j : Fin P.basisCount // j ∉ T},
        if kOf c' = k then P.coeff N c'.1 * αOf c' N else 0
    let sumAgg : MPVSpace d N :=
      ∑ k : Fin Q.basisCount, agg k • mpvState (d := d) (Q.basis k) N
    have hSplitP : sumT + sumC = sumQ := by
      have hsplit :=
        Fintype.sum_subtype_add_sum_subtype
          (p := fun j : Fin P.basisCount => j ∈ T)
          (f := fun j : Fin P.basisCount =>
            P.coeff N j • mpvState (d := d) (P.basis j) N)
      change
        (∑ t : {j : Fin P.basisCount // j ∈ T}, P.coeff N t.1 •
            mpvState (d := d) (P.basis t.1) N) +
          (∑ c' : {j : Fin P.basisCount // j ∉ T}, P.coeff N c'.1 •
            mpvState (d := d) (P.basis c'.1) N) =
        ∑ k : Fin Q.basisCount, (c * Q.coeff N k) •
          mpvState (d := d) (Q.basis k) N
      exact hsplit.trans hPQsum
    have hC_subst :
        sumC = ∑ c' : {j : Fin P.basisCount // j ∉ T},
          (P.coeff N c'.1 * αOf c' N) •
            mpvState (d := d) (Q.basis (kOf c')) N := by
      refine Finset.sum_congr rfl ?_
      intro c' _
      calc
        P.coeff N c'.1 • mpvState (d := d) (P.basis c'.1) N
            = P.coeff N c'.1 •
                (αOf c' N • mpvState (d := d) (Q.basis (kOf c')) N) := by
              rw [hStateOf c' N]
        _ = (P.coeff N c'.1 * αOf c' N) •
                mpvState (d := d) (Q.basis (kOf c')) N := by
              rw [smul_smul]
    have hC_group :
        (∑ c' : {j : Fin P.basisCount // j ∉ T},
          (P.coeff N c'.1 * αOf c' N) •
            mpvState (d := d) (Q.basis (kOf c')) N) = sumAgg := by
      simpa [sumAgg, agg] using
        (sum_fiber_smul (φ := kOf)
          (a := fun c' : {j : Fin P.basisCount // j ∉ T} =>
            P.coeff N c'.1 * αOf c' N)
          (v := fun k : Fin Q.basisCount => mpvState (d := d) (Q.basis k) N))
    have hMain : sumT + sumAgg = sumQ := by
      calc
        sumT + sumAgg = sumT + sumC := by
          rw [← hC_group, ← hC_subst]
        _ = sumQ := hSplitP
    let coeff : Sum {j : Fin P.basisCount // j ∈ T} (Fin Q.basisCount) → ℂ :=
      Sum.elim (fun t => P.coeff N t.1) (fun k => agg k - c * Q.coeff N k)
    have hZeroCombined :
        ∑ x : Sum {j : Fin P.basisCount // j ∈ T} (Fin Q.basisCount),
          coeff x •
            Sum.elim
              (fun t : {j : Fin P.basisCount // j ∈ T} =>
                mpvState (d := d) (P.basis t.1) N)
              (fun k : Fin Q.basisCount =>
                mpvState (d := d) (Q.basis k) N) x = 0 := by
      have hQsub :
          (∑ k : Fin Q.basisCount, (agg k - c * Q.coeff N k) •
              mpvState (d := d) (Q.basis k) N)
            = sumAgg - sumQ := by
        simp [sumAgg, sumQ, sub_smul, Finset.sum_sub_distrib]
      have hZero : sumT +
          (∑ k : Fin Q.basisCount, (agg k - c * Q.coeff N k) •
              mpvState (d := d) (Q.basis k) N) = 0 := by
        calc
          sumT +
              (∑ k : Fin Q.basisCount, (agg k - c * Q.coeff N k) •
                mpvState (d := d) (Q.basis k) N)
              = sumT + (sumAgg - sumQ) := by rw [hQsub]
          _ = (sumT + sumAgg) - sumQ := by abel
          _ = 0 := sub_eq_zero.mpr hMain
      simpa [coeff, sumT] using hZero
    have hcoeff :=
      Fintype.linearIndependent_iff.mp hLIN coeff hZeroCombined
        (Sum.inl ⟨j₀, hj₀T⟩)
    simpa [coeff] using hcoeff
  exact (hP.coeff_not_eventually_zero j₀) hCoeff_eventually_zero

/-- Exact proportional single-block matching without any per-sector unit-modulus
copy-weight hypothesis.  A non-decaying overlap is extracted by fixed-length
linear independence, and the usual irreducible-TP overlap dichotomies recover
dimension equality and gauge-phase equivalence.

This formalizes the CPSV16 matching step: arXiv:1606.00608 (`Cirac2016MPDO_arXiv`),
§II.C lines 349–352, Appendix MPV statement lines 1167–1170, and Appendix MPV
proof line 1182. -/
theorem exists_block_match_exact_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount, ∃ h : P.basisDim j₀ = Q.basisDim k₀,
      GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis j₀)) (Q.basis k₀) ∧
      ¬ Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N)
        atTop (𝓝 0) := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_nondecaying_overlap_exact_of_eventuallyProportional
    (P := P) (Q := Q) hP hQ j₀ hProp
  haveI hj₀dim : NeZero (P.basisDim j₀) := ⟨(hP.basis_dim_pos j₀).ne'⟩
  haveI hk₀dim : NeZero (Q.basisDim k₀) := ⟨(hQ.basis_dim_pos k₀).ne'⟩
  have hDim : P.basisDim j₀ = Q.basisDim k₀ := by
    by_contra hne
    exact hk₀ <|
      mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
        (P.basis j₀) (Q.basis k₀)
        (hP.basis_irreducible j₀) (hQ.basis_irreducible k₀)
        (hP.basis_left_canonical j₀) (hQ.basis_left_canonical k₀)
        hne
  have hGPE :
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀)) (Q.basis k₀) := by
    by_contra hNot
    exact hk₀ <|
      mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
        (hdim := hDim) (A := P.basis j₀) (B := Q.basis k₀)
        (hA_irr := hP.basis_irreducible j₀)
        (hB_irr := hQ.basis_irreducible k₀)
        (hA_norm := hP.basis_left_canonical j₀)
        (hB_norm := hQ.basis_left_canonical k₀)
        (hNot := hNot)
  exact ⟨k₀, hDim, hGPE, hk₀⟩

end MPSTensor
