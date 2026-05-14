/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.Api
import TNLean.MPS.FundamentalTheorem.PaperBNT.DropSector
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase

/-!
# Cross-overlap decay against a dropped BNT sector

This module supplies the cross-overlap decay input needed by the
strong-induction step of CPSV16 §II `II_cor2` (lines 1172–1192).  Given
a matched basis-sector pair `(j₀, k₀)` between two paper-faithful BNT
canonical forms, with cast-compatible gauge-phase equivalence between
`P.basis j₀` and `Q.basis k₀`, the **matched** P-block has decaying
cross-overlap with every surviving Q-basis block of `Q.dropSector …`.

This is the lemma that, once combined with the per-family cross-overlap
decay of `Api.lean` (`cross_overlap_basis_tendsto_zero`) and the matched
P-block decay supplied here, feeds the cross-family hypothesis of
`combined_family_eventually_li` for the **reduced** pair
`(P, Q.dropSector hcardQ k₀)`.

## Scope

The lemma proved here covers the **matched** P-side index `j₀`.  For an
unmatched P-side index `j ≠ j₀`, cross-overlap decay against the dropped
Q-basis is **not** a consequence of the matched-pair gauge-phase data
alone: the matched-pair witness relates `P.basis j₀` to `Q.basis k₀`,
not to any other `Q.basis k₀.succAbove l`, and `IsBNTCanonicalForm.basis_distinct`
on the `P` side relates `P.basis j` to `P.basis j₀`, not to a `Q`-side
basis block.  The unmatched-index case enters the
CPSV16 §II `II_cor2` argument through the **outer** induction on
`P.basisCount + Q.basisCount`, where the surviving `(P, Q.dropSector …)`
pair is paired with a fresh matched-pair extraction by
`DominantMatch.lean` before the next subtraction step.

A separate **dimension-mismatch** helper
`cross_overlap_basis_dropSector_tendsto_zero_of_dim_ne` is also provided:
for any P-side index `j` and any dropped Q-basis index `l`, if the bond
dimensions disagree, decay follows directly from the irreducible/TP-decay
lemma of `Spectral/SpectralGapNT.lean` (CPSV16 line 1080 unequal-dimension
case).

The two lemmas together cover **all dimension-mismatched** cross-pairs
and the **matched P-block** at the equal-dimension level.  The residual
case (`j ≠ j₀`, dimensions match, gauge-distinct on the cast surface) is
deferred to the outer induction assembly: see the docstring of
`cross_overlap_basis_matched_dropSector_tendsto_zero` below for the full
accounting.

## Main results

* `MPSTensor.cross_overlap_basis_dropSector_tendsto_zero_of_dim_ne` —
  dimension-mismatch decay for any P-side index against a dropped
  Q-basis index (CPSV16 line 1080 unequal-dimension case).
* `MPSTensor.cross_overlap_basis_matched_dropSector_tendsto_zero` —
  matched P-block cross-overlap decays against every surviving Q-basis
  block of `Q.dropSector hcardQ k₀` (CPSV16 lines 264–279
  gauge-phase grouping rule transported through the matched-pair
  gauge-phase equivalence; CPSV16 lines 1180–1188 matched-pair data).

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.  Source-line tags:
  264–279 (gauge-phase sector grouping rule), 1080–1091 (normal-tensor
  overlap dichotomy), 1148–1167 (dimension uniqueness from non-decaying
  cross-overlap), 1172–1192 (`II_cor2` strong-induction step),
  1180–1188 (matched-pair data: gauge-phase equivalence on basis MPVs
  and multiplicity recovery on the weight multiset).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete, *Matrix product states
  and projected entangled pair states*, Rev. Mod. Phys. **93**, 045003
  (2021); arXiv:2011.12127.  Lines 1846–1884 (BNT and two-layer BNT
  decomposition with raw `μ_{j,q}`), 1891–1900 (Theorem 4.5 — equal-MPV
  uniqueness on the BNT surface).

## Tags

matrix product states, fundamental theorem, BNT, paper-faithful BNT
canonical form, cross-overlap decay, dropped sector, gauge-phase
equivalence.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Dimension-mismatch decay against a dropped Q-basis block

The dimension-mismatch case of the CPSV16 line 1080 overlap dichotomy
extends componentwise to the dropped Q-basis: when the P-side block
`P.basis j` and the surviving Q-side block
`(Q.dropSector hcardQ k₀).basis l` have unequal bond dimensions, the
cross-overlap decays without any reference to the matched-pair gauge
data.  This case carries no `j = j₀` restriction. -/

/-- **Cross-overlap decay against a dropped Q-basis block from dimension
mismatch** (CPSV16 line 1080 unequal-dimension case).

For any P-side index `j` and any dropped Q-basis index `l`, if
`P.basisDim j ≠ Q.basisDim (Fin.cast hcardQ.symm (k₀.succAbove l))` then
the cross-overlap
`mpvOverlap (P.basis j) ((Q.dropSector hcardQ k₀).basis l)` decays to
`0`.  Dispatch goes through
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`. -/
lemma cross_overlap_basis_dropSector_tendsto_zero_of_dim_ne
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    {nQ : ℕ} (hcardQ : Q.basisCount = nQ + 1) (k₀ : Fin (nQ + 1))
    (j : Fin P.basisCount) (l : Fin nQ)
    (hDim :
      P.basisDim j ≠
        Q.basisDim (Fin.cast hcardQ.symm (k₀.succAbove l))) :
    Tendsto
      (fun N : ℕ =>
        mpvOverlap (d := d) (P.basis j)
          ((Q.dropSector hcardQ k₀).basis l) N)
      atTop (𝓝 0) := by
  haveI hjpos : NeZero (P.basisDim j) := ⟨(hP.basis_dim_pos j).ne'⟩
  haveI hkpos :
      NeZero (Q.basisDim (Fin.cast hcardQ.symm (k₀.succAbove l))) :=
    ⟨(hQ.basis_dim_pos _).ne'⟩
  -- The dropped Q-basis at index `l` is `Q.basis (Fin.cast … (k₀.succAbove l))`
  -- by the `dropSector_basis` unfolding lemma.
  simp only [SectorDecomposition.dropSector_basis]
  exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
    (P.basis j)
    (Q.basis (Fin.cast hcardQ.symm (k₀.succAbove l)))
    (hP.basis_irreducible j)
    (hQ.basis_irreducible _)
    (hP.basis_left_canonical j)
    (hQ.basis_left_canonical _)
    hDim

/-! ### Norm-one gauge phase from matched-pair self-overlap scaling

Internal helper.  When the matched-pair gauge-phase witness on the cast
basis tensors is in hand, the gauge phase `ζ` has unit norm.  This
specialises `norm_eq_one_of_selfOverlap_scale`
(`SharedInfra/GaugePhase.lean`) to the paper-faithful canonical-form
self-overlap data carried by `IsBNTCanonicalForm`
(`basis_normalized_self_overlap` field, CPSV21 line 1818). -/

private lemma _root_.MPSTensor.IsBNTCanonicalForm.norm_gaugePhase_eq_one_of_basis
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    {j₀ : Fin P.basisCount} {k₀ : Fin Q.basisCount}
    (hDim : P.basisDim j₀ = Q.basisDim k₀)
    {X : GL (Fin (Q.basisDim k₀)) ℂ} {ζ : ℂ}
    (hX : ∀ i : Fin d,
      Q.basis k₀ i =
        ζ • ((X : Matrix _ _ ℂ) *
          (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀)) i *
          ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ))) :
    ‖ζ‖ = 1 := by
  -- Basis-MPV power identity from the gauge-phase witness.
  have hmpv :
      ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (Q.basis k₀) σ =
          ζ ^ N * mpv (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀)) σ :=
    mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) hDim) (P.basis j₀))
      (B := Q.basis k₀) X ζ hX
  -- Self-overlap scaling identity.
  have hScale :
      ∀ N : ℕ,
        mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N =
          (ζ * starRingEnd ℂ ζ) ^ N *
            mpvOverlap (d := d)
              (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀))
              (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀)) N :=
    mpvOverlap_self_scale_of_mpv_eq_pow_mul
      (A := cast (congr_arg (MPSTensor d) hDim) (P.basis j₀))
      (B := Q.basis k₀) (ζ := ζ) hmpv
  -- Self-overlap of the cast basis tensor agrees with that of the uncast one.
  have hScale' :
      ∀ N : ℕ,
        mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N =
          (ζ * starRingEnd ℂ ζ) ^ N *
            mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N := by
    intro N
    have := hScale N
    rw [mpvOverlap_cast_dim_left hDim (P.basis j₀)
        (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀)) N] at this
    -- Now the right-hand mpvOverlap still has a cast on the right argument.
    -- Eliminate it via `mpv_cast_dim` componentwise.
    have hCast :
        mpvOverlap (d := d) (P.basis j₀)
            (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀)) N =
          mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N := by
      classical
      simp only [mpvOverlap]
      refine Finset.sum_congr rfl ?_
      intro σ _
      rw [mpv_cast_dim hDim (P.basis j₀) N σ]
    rw [hCast] at this
    exact this
  -- Self-overlap norms tend to 1 on both sides via `basis_normalized_self_overlap`.
  have hPP :
      Tendsto (fun N => ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N‖)
        atTop (𝓝 1) := by
    have h := (hP.basis_normalized_self_overlap j₀).norm
    simpa using h
  have hQQ :
      Tendsto (fun N => ‖mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N‖)
        atTop (𝓝 1) := by
    have h := (hQ.basis_normalized_self_overlap k₀).norm
    simpa using h
  exact norm_eq_one_of_selfOverlap_scale (A := P.basis j₀) (B := Q.basis k₀)
    (ζ := ζ) hPP hQQ hScale'

/-! ### Matched P-block cross-overlap decays against the dropped Q-basis

The CPSV16 §II `II_cor2` strong induction needs the cross-overlaps
`mpvOverlap (P.basis j) ((Q.dropSector …).basis l)` to all decay so that
`combined_family_eventually_li` (`Api.lean`) on the reduced pair
`(P, Q.dropSector hcardQ k₀)` produces the eventual linear independence
input.  For the **matched** P-index `j₀`, the matched-pair gauge-phase
equivalence transports the cross-overlap into a same-family Q-overlap
between `Q.basis k₀` and `Q.basis (k₀.succAbove l)`, which decays by
`IsBNTCanonicalForm.cross_overlap_basis_tendsto_zero` (since the two
Q-indices differ).  The transported scalar factor `ζ^{-N}` is bounded:
`‖ζ‖ = 1` by the matched-pair self-overlap scaling specialisation. -/

/-- **Matched P-block cross-overlap decays against the dropped Q-basis.**

Given paper-faithful BNT canonical forms `hP`, `hQ` on `P`, `Q`, a
matched basis-sector pair `(j₀, k₀)` with bond-dimension equality
`hDim` and matched-pair gauge-phase equivalence
`hGPE : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀))
                        (Q.basis (Fin.cast hcardQ.symm k₀))`
of CPSV16 line 1180, the matched P-block `P.basis j₀` has decaying
cross-overlap with every surviving Q-basis block
`(Q.dropSector hcardQ k₀).basis l`.

Proof sketch:

* Unfold `(Q.dropSector hcardQ k₀).basis l =
    Q.basis (Fin.cast hcardQ.symm (k₀.succAbove l))` via the
  `dropSector_basis` unfolding lemma.
* The matched-pair gauge-phase witness `hGPE` gives
  `mpv (Q.basis k₀') σ = ζ^N * mpv (P.basis j₀) σ` with `ζ ≠ 0` and
  `‖ζ‖ = 1`, by composing `mpv_eq_pow_mul_of_gaugePhase` with
  `mpv_cast_dim` to absorb the bond-dimension cast.
* The cross-overlap factors as
  `mpvOverlap (P.basis j₀) (Q.basis (succAbove l)) N
     = ζ^{-N} * mpvOverlap (Q.basis k₀') (Q.basis (succAbove l)) N`.
* The Q-side same-family overlap decays by
  `IsBNTCanonicalForm.cross_overlap_basis_tendsto_zero hQ` at the two
  distinct indices `k₀'` and `Fin.cast hcardQ.symm (k₀.succAbove l)`
  (distinct because `k₀.succAbove l ≠ k₀` by `Fin.succAbove_ne`).
* Since `‖ζ‖ = 1`, the prefactor `ζ^{-N}` has unit modulus and the
  product decays via a norm bound and `squeeze_zero_norm`.

The CPSV16 §II `II_cor2` strong induction (lines 1172–1192) consumes
this matched-block decay together with the dimension-mismatch helper
(`cross_overlap_basis_dropSector_tendsto_zero_of_dim_ne`) to assemble
the cross-family decay input of
`IsBNTCanonicalForm.combined_family_eventually_li` on the reduced pair
`(P, Q.dropSector hcardQ k₀)`.  The unmatched-P-index residual
(`j ≠ j₀`, dimensions match, gauge-distinct on the cast surface) does
**not** follow from the matched-pair data alone — it is supplied by the
outer induction on `P.basisCount + Q.basisCount`, where the surviving
`(P, Q.dropSector …)` pair is paired with a fresh matched-pair
extraction by `DominantMatch.lean` before the next subtraction.

Paper anchors: CPSV16 lines 264–279 (gauge-phase grouping rule),
1148–1167 (dimension uniqueness from non-decaying cross-overlap),
1180–1188 (matched-pair gauge-phase equivalence and multiplicity
recovery), 1172–1192 (`II_cor2` strong-induction step). -/
theorem cross_overlap_basis_matched_dropSector_tendsto_zero
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    {nQ : ℕ} (hcardQ : Q.basisCount = nQ + 1)
    (j₀ : Fin P.basisCount) (k₀ : Fin (nQ + 1))
    (hDim : P.basisDim j₀ =
      Q.basisDim (Fin.cast hcardQ.symm k₀))
    (hGPE :
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀))
        (Q.basis (Fin.cast hcardQ.symm k₀))) :
    ∀ l : Fin nQ,
      Tendsto
        (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j₀)
            ((Q.dropSector hcardQ k₀).basis l) N)
        atTop (𝓝 0) := by
  classical
  -- Destructure the matched-pair gauge-phase witness.
  obtain ⟨X, ζ, hζ_ne, hX⟩ := hGPE
  -- Cast-lifted matched Q-index (plain `let` so the existing `hX` retains its
  -- unfolded form `Q.basis (Fin.cast hcardQ.symm k₀)`).
  let k₀' : Fin Q.basisCount := Fin.cast hcardQ.symm k₀
  have hk₀'_def : k₀' = Fin.cast hcardQ.symm k₀ := rfl
  -- Norm-one gauge phase from self-overlap scaling.
  have hζ_norm : ‖ζ‖ = 1 :=
    IsBNTCanonicalForm.norm_gaugePhase_eq_one_of_basis (hP := hP) (hQ := hQ)
      (j₀ := j₀) (k₀ := Fin.cast hcardQ.symm k₀)
      (hDim := hDim) (X := X) (ζ := ζ) hX
  -- Basis-MPV power identity from the gauge-phase witness, with the
  -- cast on the P-side absorbed by `mpv_cast_dim`.
  have hMpv :
      ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (Q.basis k₀') σ = ζ ^ N * mpv (P.basis j₀) σ := by
    intro N σ
    have h₁ :=
      mpv_eq_pow_mul_of_gaugePhase
        (A := cast (congr_arg (MPSTensor d) hDim) (P.basis j₀))
        (B := Q.basis (Fin.cast hcardQ.symm k₀)) X ζ hX N σ
    change mpv (Q.basis (Fin.cast hcardQ.symm k₀)) σ = ζ ^ N * mpv (P.basis j₀) σ
    rw [h₁, mpv_cast_dim hDim (P.basis j₀) N σ]
  intro l
  -- Reindexed Q-basis at the dropped position `l`.
  let k : Fin Q.basisCount := Fin.cast hcardQ.symm (k₀.succAbove l)
  have hk_def : k = Fin.cast hcardQ.symm (k₀.succAbove l) := rfl
  -- `k ≠ k₀'` because `k₀.succAbove l ≠ k₀`.
  have hkk₀' : k ≠ k₀' := by
    intro hkk
    have : k₀.succAbove l = k₀ := by
      have := congrArg (fun (m : Fin Q.basisCount) => (m.val : ℕ)) hkk
      -- Both sides have the same `.val`; reconstruct the `Fin` equality.
      exact Fin.ext this
    exact Fin.succAbove_ne k₀ l this
  -- Unfold the dropped Q-basis at `l`.
  have hUnfold :
      ∀ N : ℕ,
        mpvOverlap (d := d) (P.basis j₀)
            ((Q.dropSector hcardQ k₀).basis l) N =
          mpvOverlap (d := d) (P.basis j₀) (Q.basis k) N := by
    intro N
    rfl
  -- Pointwise factorisation: the matched-pair `hMpv` transports the
  -- cross-overlap into a same-family Q-overlap scaled by `ζ⁻^N`.
  have hFactor :
      ∀ N : ℕ,
        mpvOverlap (d := d) (P.basis j₀) (Q.basis k) N =
          (ζ⁻¹) ^ N *
            mpvOverlap (d := d) (Q.basis k₀') (Q.basis k) N := by
    intro N
    classical
    simp only [mpvOverlap]
    -- For each `σ`, `mpv (P.basis j₀) σ = ζ⁻^N * mpv (Q.basis k₀') σ`.
    have hInv :
        ∀ σ : Cfg d N, mpv (P.basis j₀) σ = ζ⁻¹ ^ N * mpv (Q.basis k₀') σ := by
      intro σ
      have hPow : ζ⁻¹ ^ N * ζ ^ N = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hζ_ne, one_pow]
      have hMul := hMpv N σ
      -- Multiply `hMul` by `ζ⁻^N` on the left and cancel.
      calc mpv (P.basis j₀) σ
          = 1 * mpv (P.basis j₀) σ := (one_mul _).symm
        _ = (ζ⁻¹ ^ N * ζ ^ N) * mpv (P.basis j₀) σ := by rw [hPow]
        _ = ζ⁻¹ ^ N * (ζ ^ N * mpv (P.basis j₀) σ) := by ring
        _ = ζ⁻¹ ^ N * mpv (Q.basis k₀') σ := by rw [← hMul]
    -- Distribute and pull out the constant.
    calc
      (∑ σ : Cfg d N, mpv (P.basis j₀) σ * star (mpv (Q.basis k) σ))
          = ∑ σ : Cfg d N,
              (ζ⁻¹ ^ N * mpv (Q.basis k₀') σ) * star (mpv (Q.basis k) σ) := by
              refine Finset.sum_congr rfl ?_
              intro σ _; rw [hInv σ]
      _ = ζ⁻¹ ^ N *
            ∑ σ : Cfg d N, mpv (Q.basis k₀') σ * star (mpv (Q.basis k) σ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro σ _; ring
  -- Q-side same-family decay between `k₀'` and `k`.
  have hQDecay :
      Tendsto
        (fun N : ℕ => mpvOverlap (d := d) (Q.basis k₀') (Q.basis k) N)
        atTop (𝓝 0) :=
    hQ.cross_overlap_basis_tendsto_zero (hkk₀'.symm)
  -- Norm bound: `‖ζ⁻^N‖ = 1`.
  have hζ_inv_norm : ‖ζ⁻¹‖ = 1 := by
    rw [norm_inv, hζ_norm, inv_one]
  -- Squeeze: `‖cross‖ ≤ ‖mpvOverlap(k₀', k)‖`.
  refine squeeze_zero_norm (a := fun N =>
    ‖mpvOverlap (d := d) (Q.basis k₀') (Q.basis k) N‖)
    (fun N => ?_) ?_
  · rw [hUnfold N, hFactor N]
    rw [norm_mul, norm_pow, hζ_inv_norm, one_pow, one_mul]
  · simpa using hQDecay.norm

end MPSTensor
