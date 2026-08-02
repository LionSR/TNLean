/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.FundamentalTheorem.SectorBNT.MatchAux

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
    exact coefficient_eq_zero_of_sum_eq_of_complement_smul
      (T := T) (a := fun j => P.coeff N j)
      (u := fun j => mpvState (d := d) (P.basis j) N)
      (b := fun k => c * Q.coeff N k)
      (v := fun k => mpvState (d := d) (Q.basis k) N)
      (kOf := kOf) (α := fun c' => αOf c' N)
      (hComplement := fun c' => hStateOf c' N)
      (hSum := hPQsum) (hLI := hLIN) (i₀ := j₀) hj₀T
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
  obtain ⟨hDim, hGPE⟩ := dim_and_gaugePhase_of_nondecaying_overlap hP hQ hk₀
  exact ⟨k₀, hDim, hGPE, hk₀⟩

/-! ### Full-basis proportional matching (Q → P direction)

For every sector `k` of `Q`, there exists a sector `j` of `P` of equal
bond dimension, gauge-phase equivalent in the cast-compatible shape, and
with non-decaying cross-overlap.  This is the proportional analogue of
the strong existential matching theorem (equal-MPV case).

Paper anchor: CPSV16 §II.C lines 349–352 (theorem `thm1`);
Appendix MPV theorem statement lines 1167–1170 and Appendix MPV proof
line 1182 (matching). -/
theorem forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
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
  have hProp_symm : EventuallyNonzeroProportionalMPV₂ Q.toTensor P.toTensor :=
    hProp.symm
  obtain ⟨j, hsymDim, hGE_swapped, hNonDecay_swapped⟩ :=
    exists_block_match_exact_of_eventuallyProportional
      (P := Q) (Q := P) hQ hP k hProp_symm
  refine ⟨j, hsymDim.symm, ?_, ?_⟩
  · exact gaugePhaseEquiv_swap_cast hsymDim.symm
      (by simpa using hGE_swapped)
  · intro hTend
    apply hNonDecay_swapped
    exact tendsto_mpvOverlap_zero_swap (P.basis j) (Q.basis k) hTend

end MPSTensor
