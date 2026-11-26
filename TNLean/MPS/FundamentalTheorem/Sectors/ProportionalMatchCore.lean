/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Combinatorics.FinSum
import TNLean.MPS.FundamentalTheorem.Sectors.MatchAux
import TNLean.MPS.Tensor.DirectSum.SectorDecomposition
import TNLean.MPS.FundamentalTheorem.Sectors.CoeffIdentity

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
`SectorDecomposition.coeff_not_eventually_zero`.

It also contains the following results.

* `MPSTensor.bijective_match_of_eventuallyProportional`,
  `MPSTensor.ft_sector_bnt_proportional_sector_match_witnesses`: proportional sector matching for
  two BNT canonical forms.
* `MPSTensor.forall_k_exists_j_nondecaying_overlap_of_sameMPV`,
  `MPSTensor.bijective_match_of_sameMPV`: strong existential and bijective sector matching.

## References

* CPSV16: arXiv:1606.00608, lines 349–352 (theorem `thm1`), 1167–1170
  (restatement), and Appendix MPV proof, line 1182 (matching proof).
* CPSV21: arXiv:2011.12127, lines 1891–1894 (proportional target).

## Exact block matching for BNT canonical forms

Two BNT canonical forms with the same positive-length MPV family have exact
single-sector matches: for each sector of one decomposition, some sector of the
other has the same bond dimension, is gauge-phase equivalent after the dimension
cast, and has non-decaying overlap. This is the equal-MPV specialization of the
proportional sector matcher.
-/

open MPTensor

section ProportionalMatchCore

section

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
  let : Fintype {j : Fin P.basisCount // j ∈ T} := Subtype.fintype (fun j => j ∈ T)
  let : Fintype {j : Fin P.basisCount // j ∉ T} := Subtype.fintype (fun j => j ∉ T)
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
    have hPstate := P.mpvState_toTensor_eq_sum_coeff N
    have hQstate := Q.mpvState_toTensor_eq_sum_coeff N
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
    exact LinearIndependent.coefficient_eq_zero_of_sum_eq_of_complement_smul
      (T := T) (a := fun j => P.coeff N j)
      (u := fun j => mpvState (d := d) (P.basis j) N)
      (b := fun k => c * Q.coeff N k)
      (v := fun k => mpvState (d := d) (Q.basis k) N)
      (kOf := kOf) (α := fun c' => αOf c' N)
      (hComplement := fun c' => hStateOf c' N)
      (hSum := hPQsum) (hLI := hLIN) (i₀ := j₀) hj₀T
  exact (P.coeff_not_eventually_zero j₀) hCoeff_eventually_zero

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

end

section

open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- Exact single-block matching without a per-sector unit-modulus hypothesis.

Equality at every positive length gives eventual nonzero proportionality with
scalar one, so this follows from the proportional single-block matcher. -/
theorem exists_block_match_exact
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount,
      ∃ h : P.basisDim j₀ = Q.basisDim k₀,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis j₀)) (Q.basis k₀) ∧
        ¬ Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N)
          atTop (𝓝 0) := by
  exact exists_block_match_exact_of_eventuallyProportional hP hQ j₀
    hEqual.toNonzeroProportionalMPV₂.eventually

end MPSTensor

end

end ProportionalMatchCore

section ProportionalMatch

/-!
## Proportional sector matching for two BNT canonical forms

The analytic single-sector matcher yields full-basis and bijective matching
consequences, culminating in the proportional sector-matching theorem.

The main theorem `MPSTensor.ft_sector_bnt_proportional_sector_match_witnesses`
delivers the basis-count identity $g_P = g_Q$, a basis bijection
$\beta : \{1,\dots,g_Q\} \to \{1,\dots,g_P\}$, per-block bond-dimension
equality $D_P^{(\beta k)} = D_Q^{(k)}$, and per-block gauge-phase equivalence
$B_k = \zeta_k X_k A_{\beta k} X_k^{-1}$.

### References

* CPSV16: arXiv:1606.00608, lines 349–352 (theorem `thm1`), 1167–1170
  (restatement), and Appendix MPV proof, line 1182 (matching proof).
* CPSV21: arXiv:2011.12127, lines 1891–1894 (proportional target).
-/

open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Bijective matching from per-block existentials in both directions

The forward and backward existential matches
`forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional` provide the
input to the shared bijection construction `bijection_from_matches`.  The
cast-aware symmetry and transitivity lemmas
(`gaugePhaseEquiv_symm_same_dim`, `gaugePhaseEquiv_swap_cast`,
`gaugePhaseEquiv_trans_same_dim`, `gaugePhaseEquiv_cast_compose_via_centre`)
are shared with the equal-MPV bijection theorem. -/

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

end ProportionalMatch

section StrongMatch

/-!
## Strong existential and bijective sector matching

The strong existential matching theorem states the CPSV16 Appendix MPV proof,
line 1182, matching conclusion directly on the original pair `(P, Q)` of BNT
canonical forms.  In the equal-MPV case the existential theorem reduces to
its proportional-sector counterpart via the
`SameMPV₂Pos → EventuallyNonzeroProportionalMPV₂` conversion, and the
bijection theorem applies that reduction in both directions through the
shared construction `bijection_from_matches`.

The coefficient identity of CPSV16 Appendix MPV proof, lines 1187–1188
(Corollary substitution) lives in the companion module
`SectorBNT/CoeffIdentity.lean`.

### Paper anchor

CPSV16 (arXiv:1606.00608) Appendix MPV proof, line 1182, gives the matching
step of the proportional theorem proof.  The equal-vector corollary gives an
index $j_k$ with $|V^{(N)}(B_k)\rangle = |V^{(N)}(A_{j_k})\rangle$, and the
single-block fundamental theorem gives $B_k = X_k A_{j_k} X_k^{-1}$.
-/

open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Strong existential matching: CPSV16 Appendix MPV proof, line 1182 -/

/-- **CPSV16 Appendix MPV proof, line 1182, Step 1 (full-basis form).**

Suppose that the total tensors of `P` and `Q` generate the same MPV family at
every positive length.  For every sector `k` of `Q`, there exists a sector `j`
of `P` of equal bond dimension, gauge-phase equivalent to `Q.basis k` after the
dimension cast, and with non-decaying cross-overlap.

This is derived from the proportional sector-matching lemma
`forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional` using the
conversion `SameMPV₂Pos.toNonzeroProportionalMPV₂.eventually`.

Paper anchor: CPSV16 Appendix MPV proof, line 1182 (arXiv:1606.00608), CPSV21
Definition 4.2 lines 1846–1850, and the two-layer display at lines 1864–1884. -/
theorem forall_k_exists_j_nondecaying_overlap_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∀ k : Fin Q.basisCount, ∃ (j : Fin P.basisCount) (h : P.basisDim j = Q.basisDim k),
      GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis j))
          (Q.basis k) ∧
      ¬ Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
        atTop (𝓝 0) :=
  forall_k_exists_j_nondecaying_overlap_of_eventuallyProportional hP hQ
    (hEqual.toNonzeroProportionalMPV₂.eventually)

/-! ### Bijective sector matching by symmetry -/

/-- **CPSV16 Appendix MPV proof, line 1182, full-basis bijection.**

Applying `forall_k_exists_j_nondecaying_overlap_of_sameMPV` in both
directions gives injective maps `Fin Q.basisCount → Fin P.basisCount` and
`Fin P.basisCount → Fin Q.basisCount`.  Finite cardinal comparison turns
the forward injection into an equivalence `β : Fin Q.basisCount ≃
Fin P.basisCount`, carrying the matched bond-dimension equality,
gauge-phase equivalence, and non-decaying overlap for every sector of `Q`.

The bijection step is the shared construction `bijection_from_matches`,
applied to both directions of
`forall_k_exists_j_nondecaying_overlap_of_sameMPV`. -/
theorem bijective_match_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ β : Fin Q.basisCount ≃ Fin P.basisCount,
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (β k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (β k)) (Q.basis k) N)
          atTop (𝓝 0) := by
  exact bijection_from_matches hP hQ
    (forall_k_exists_j_nondecaying_overlap_of_sameMPV hP hQ hEqual)
    (forall_k_exists_j_nondecaying_overlap_of_sameMPV hQ hP hEqual.symm)

end MPSTensor

end StrongMatch
