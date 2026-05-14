/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.DominantMatch
import TNLean.MPS.FundamentalTheorem.PaperBNT.DropMatchedSector
import TNLean.MPS.FundamentalTheorem.PaperBNT.NewtonGirard
import TNLean.MPS.FundamentalTheorem.SectorWeightComparison

/-!
# Matched-sector coefficient identity and weight permutation extraction

This module is **Phase 4c** of the CPSV16/CPSV21 fundamental-theorem
clean-slate plan (issue #1688).  Its task is to land the **matched-sector
coefficient identity** that closes the gap between the
dominant-pair-matching surface
(`PaperBNT/DominantMatch.lean`) and the matched-sector subtraction
(`PaperBNT/DropMatchedSector.lean`), and then to use Newton–Girard
(`PaperBNT/NewtonGirard.lean`) to extract the matched per-copy weight
multiset equality.

## Contributions of this module

* `matched_sector_coeff_identity_eventually` — given `SameMPV₂`, a matched
  gauge-phase pair `(j₀, k₀)` with phase `ζ`, and a combined-family
  eventual linear independence input on
  `P.basis ⊔ (Q.dropSector k₀).basis`, derive
  `∃ N₀ : ℕ, ∀ N > N₀, P.coeff N j₀ = ζ^N · Q.coeff N k₀'`.

* `matched_sector_weight_multiset_eq` — from the eventual coefficient
  identity above (after extension to all positive exponents) and
  `Multiset.eq_of_power_sum_eq`, conclude that the per-copy weight
  multisets coincide:
  `Multiset.map (Q.weight k₀') Finset.univ.val
     = Multiset.map (fun q => ζ⁻¹ · P.weight j₀ q) Finset.univ.val'`
  with `Finset.univ.val'` the cast-reindexed universe.  The matched
  per-copy multiplicities `Q.copies k₀' = P.copies j₀` then follow.

These are the precise inputs consumed by
`MPSTensor.sameMPV_dropSector_dropSector_of_gaugePhaseEquiv`
(`PaperBNT/DropMatchedSector.lean`).

## Scope and deferred content

The full per-direction non-decaying overlap conjunction
(the strong-induction theorem `forall_exists_nondecaying_overlap_of_sameMPV`
named in the issue description) is **not** assembled in this module:
lifting the matched coefficient identity through the induction requires
either propagating a substantial bundle of carried-through hypotheses
(per-sector dominant-coefficient non-decay and per-step combined-family
LI), or first proving the cross-overlap decay between `P` and
`Q.dropSector k₀` from the matched-pair gauge-phase data alone.  Both are
paper-faithful but substantial side projects; they are tracked in the
follow-up issue noted in the PR description for this module.

## Proof outline

The matched-sector coefficient identity follows the **Step 1** linear-
independence projection of the CPSV16 `II_cor2` proof (lines 1170–1192):

1. Express `SameMPV₂` as a vector identity in the combined `mpvState`
   family `P.basis ⊔ (Q.dropSector k₀).basis`, using the gauge-phase
   relation `mpv (Q.basis k₀') σ = ζ^N · mpv (P.basis j₀) σ` to substitute
   the matched basis MPV on the `Q`-side and the standard
   `Fin.sum_univ_succAbove` succAbove-splitting on the `Q`-sum to redirect
   the non-matched terms onto the dropped subfamily basis.
2. Read the difference of the two `mpv X.toTensor σ` expansions as the
   vanishing of a single linear combination of the combined-family
   `mpvState`s.
3. Apply the combined-family eventual linear independence
   (`IsBNTCanonicalForm.combined_family_eventually_li` is the natural
   producer, but the lemma here consumes the LI input directly to
   maximise reusability) and `Fintype.linearIndependent_iff` to extract
   the coefficient at `inl j₀`, which is exactly
   `P.coeff N j₀ - ζ^N · Q.coeff N k₀'`.

The weight multiset equality then chains:

* `power_sums_eq_of_eventually_eq_hetero`
  (`PaperBNT/.../SectorWeightComparison.lean`) — extend the eventual
  coefficient identity to **all** positive exponents;
* `Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card`
  forces matching cardinalities and weight multisets.

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and
  Boundary Theories*, Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.
  Source-line tags used below: 1121–1132 (Lem1, combined-family eventual
  linear independence — the input consumed by the matched coefficient
  identity), 1140–1230 (`II_cor2` strong-induction structure),
  1170–1192 (matched-block subtraction step), 1184–1188 (raw power-sum
  comparison, multiplicity recovery `r_{a,j} = r_{b,j}` and
  `μ_{j,q} = ν_{j,q} · e^{i\phi_j}`).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix product states and projected entangled pair states*,
  Rev. Mod. Phys. **93**, 045003 (2021); arXiv:2011.12127.  Lines
  1846–1884 (BNT and two-layer BNT decomposition with raw `μ_{j,q}`).

## Tags

matrix product states, fundamental theorem, BNT, paper-faithful BNT
canonical form, matched-sector coefficient identity, Newton–Girard,
weight multiset, gauge-phase equivalence.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Matched-sector coefficient identity (eventual form)

This is the **Step 1 of `II_cor2`** projection: under the matched basis-MPV
relation `mpv (Q.basis k₀') σ = ζ^N · mpv (P.basis j₀) σ`, the `SameMPV₂`
identity becomes a linear relation among the combined family
`P.basis ⊔ (Q.dropSector k₀).basis`, and the combined-family eventual
linear independence (CPSV16 lines 1121–1132) extracts the matched
coefficient identity `P.coeff N j₀ = ζ^N · Q.coeff N k₀'` eventually
in `N`.
-/

/-- **Matched-sector coefficient identity (eventual).**

Given:

* `hEqual : SameMPV₂ P.toTensor Q.toTensor` (CPSV16 `II_cor2` hypothesis);
* a matched `Q`-sector `k₀' = Fin.cast hcardQ.symm k₀` and a `P`-side
  index `j₀ : Fin P.basisCount` together with the gauge-phase relation
  `mpv (Q.basis k₀') σ = ζ^N · mpv (P.basis j₀) σ` for every system size
  and configuration (this is the output of
  `MPSTensor.mpv_eq_pow_mul_of_gaugePhase` applied to the
  `GaugePhaseEquiv` witness from `exists_dominant_match_of_sameMPV`,
  CPSV16 line 1187);
* `hCombLI` — combined-family eventual linear independence of
  `P.basis ⊔ (Q.dropSector k₀).basis` (the paper-faithful Lem1 input,
  CPSV16 lines 1121–1132);

the matched-sector coefficient identity holds eventually:
`∃ N₀ : ℕ, ∀ N > N₀, P.coeff N j₀ = ζ^N · Q.coeff N k₀'`.

The proof is the linear-independence projection of CPSV16 `II_cor2`
Step 1 (lines 1170–1192): substituting `hMpv` rewrites the `Q`-side
expansion as a sum on the combined family, after which the difference
of the two expansions is a single combined-family linear relation whose
coefficient at `inl j₀` is exactly `P.coeff N j₀ - ζ^N · Q.coeff N k₀'`. -/
theorem matched_sector_coeff_identity_eventually
    {P Q : SectorDecomposition d}
    (hEqual : SameMPV₂ P.toTensor Q.toTensor)
    {nQ : ℕ}
    (hcardQ : Q.basisCount = nQ + 1)
    (j₀ : Fin P.basisCount) (k₀ : Fin (nQ + 1))
    (ζ : ℂ)
    (hMpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (Q.basis (Fin.cast hcardQ.symm k₀)) σ =
          ζ ^ N * mpv (P.basis j₀) σ)
    (hCombLI : ∃ N₀ : ℕ, ∀ N > N₀,
        LinearIndependent ℂ
          (Sum.elim
            (fun j : Fin P.basisCount => mpvState (d := d) (P.basis j) N)
            (fun l : Fin nQ =>
              mpvState (d := d) ((Q.dropSector hcardQ k₀).basis l) N))) :
    ∃ N₀ : ℕ, ∀ N > N₀,
      P.coeff N j₀ = ζ ^ N * Q.coeff N (Fin.cast hcardQ.symm k₀) := by
  classical
  obtain ⟨N₀, hLI⟩ := hCombLI
  refine ⟨N₀, fun N hN => ?_⟩
  -- Abbreviate the lifted matched-`Q`-index.
  set k₀' : Fin Q.basisCount := Fin.cast hcardQ.symm k₀ with hk₀'_def
  -- LHS coefficient: the `P`-side coefficient function on the combined family.
  -- Pads the combined family with `0` on the dropped-`Q` half.
  let cS : Sum (Fin P.basisCount) (Fin nQ) → ℂ :=
    Sum.elim (fun j : Fin P.basisCount => P.coeff N j) (fun _ : Fin nQ => 0)
  -- RHS coefficient: the `Q`-side coefficient function, transformed by `hMpv`
  -- onto the combined family.  `Q.coeff N k₀'` is moved to the matched
  -- `P`-side basis (with the gauge-phase factor `ζ^N`); the other `Q`
  -- coefficients are redistributed onto the dropped subfamily.
  let cT : Sum (Fin P.basisCount) (Fin nQ) → ℂ :=
    Sum.elim
      (fun j : Fin P.basisCount =>
        if j = j₀ then ζ ^ N * Q.coeff N k₀' else 0)
      (fun l : Fin nQ =>
        Q.coeff N (Fin.cast hcardQ.symm (k₀.succAbove l)))
  -- Combined `mpvState` family.
  let v : Sum (Fin P.basisCount) (Fin nQ) →
      EuclideanSpace ℂ (Fin N → Fin d) :=
    Sum.elim
      (fun j : Fin P.basisCount => mpvState (d := d) (P.basis j) N)
      (fun l : Fin nQ => mpvState (d := d) ((Q.dropSector hcardQ k₀).basis l) N)
  -- Sum identity: ∑ x, cS x • v x = ∑ x, cT x • v x.
  -- This follows from the two MPV expansions, the `Fin.sum_univ_succAbove`
  -- decomposition of the `Q`-sum, and the gauge-phase relation `hMpv`.
  have hSums :
      ∑ x : Sum (Fin P.basisCount) (Fin nQ), cS x • v x
        = ∑ x : Sum (Fin P.basisCount) (Fin nQ), cT x • v x := by
    -- Reduce vector equality to pointwise equality.
    ext σ
    -- Project the `mpvState` smul-sum to the `mpv` value at `σ`.
    have hLHS_pt :
        (∑ x : Sum (Fin P.basisCount) (Fin nQ), cS x • v x) σ
          = ∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ := by
      simp only [Fintype.sum_sum_type, WithLp.ofLp_add, WithLp.ofLp_sum,
        WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
        smul_eq_mul, cS, v, Sum.elim_inl, Sum.elim_inr,
        mpvState_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have hRHS_pt :
        (∑ x : Sum (Fin P.basisCount) (Fin nQ), cT x • v x) σ
          = (ζ ^ N * Q.coeff N k₀') * mpv (P.basis j₀) σ
            + ∑ l : Fin nQ,
                Q.coeff N (Fin.cast hcardQ.symm (k₀.succAbove l)) *
                  mpv (Q.basis (Fin.cast hcardQ.symm (k₀.succAbove l))) σ := by
      have hSum_ite :
          (∑ j : Fin P.basisCount,
              (if j = j₀ then ζ ^ N * Q.coeff N k₀' else (0 : ℂ)) *
                mpv (P.basis j) σ)
            = (ζ ^ N * Q.coeff N k₀') * mpv (P.basis j₀) σ := by
        have hRewrite :
            (∑ j : Fin P.basisCount,
                (if j = j₀ then ζ ^ N * Q.coeff N k₀' else (0 : ℂ)) *
                  mpv (P.basis j) σ)
              = ∑ j : Fin P.basisCount,
                  (if j = j₀ then
                    (ζ ^ N * Q.coeff N k₀') * mpv (P.basis j) σ else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          by_cases hj : j = j₀
          · simp [hj]
          · simp [hj]
        rw [hRewrite, Finset.sum_ite_eq' Finset.univ j₀
              (fun j => (ζ ^ N * Q.coeff N k₀') * mpv (P.basis j) σ)]
        simp
      simp only [Fintype.sum_sum_type, WithLp.ofLp_add, WithLp.ofLp_sum,
        WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
        smul_eq_mul, cT, v, Sum.elim_inl, Sum.elim_inr,
        mpvState_apply, SectorDecomposition.dropSector_basis]
      rw [hSum_ite]
      rfl
    -- Pointwise goal: LHS_pt = RHS_pt.  Use SameMPV₂ and reindex the
    -- `Q`-sum to splice in the matched sector.
    rw [hLHS_pt, hRHS_pt]
    have hP_expand : mpv P.toTensor σ
        = ∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ :=
      P.mpv_toTensor_eq_sum_coeff σ
    have hQ_expand : mpv Q.toTensor σ
        = ∑ k : Fin Q.basisCount, Q.coeff N k * mpv (Q.basis k) σ :=
      Q.mpv_toTensor_eq_sum_coeff σ
    have hQ_reindex :
        ∑ k : Fin Q.basisCount, Q.coeff N k * mpv (Q.basis k) σ
          = ∑ k : Fin (nQ + 1),
              Q.coeff N (Fin.cast hcardQ.symm k) *
                mpv (Q.basis (Fin.cast hcardQ.symm k)) σ := by
      refine Fintype.sum_equiv (Fin.castOrderIso hcardQ).toEquiv _ _ ?_
      intro k; rfl
    have hQ_split :
        ∑ k : Fin (nQ + 1),
            Q.coeff N (Fin.cast hcardQ.symm k) *
              mpv (Q.basis (Fin.cast hcardQ.symm k)) σ
          = Q.coeff N k₀' * mpv (Q.basis k₀') σ
            + ∑ l : Fin nQ,
                Q.coeff N (Fin.cast hcardQ.symm (k₀.succAbove l)) *
                  mpv (Q.basis (Fin.cast hcardQ.symm (k₀.succAbove l))) σ := by
      simpa [hk₀'_def] using
        Fin.sum_univ_succAbove
          (fun k : Fin (nQ + 1) =>
            Q.coeff N (Fin.cast hcardQ.symm k) *
              mpv (Q.basis (Fin.cast hcardQ.symm k)) σ) k₀
    -- `mpv (Q.basis k₀') σ = ζ^N · mpv (P.basis j₀) σ`.
    have hMpv_N := hMpv N σ
    -- Combine: SameMPV₂ + reindex + split + hMpv.
    have hSame : mpv P.toTensor σ = mpv Q.toTensor σ := hEqual N σ
    calc
      (∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ)
          = mpv P.toTensor σ := hP_expand.symm
      _ = mpv Q.toTensor σ := hSame
      _ = ∑ k : Fin Q.basisCount, Q.coeff N k * mpv (Q.basis k) σ := hQ_expand
      _ = ∑ k : Fin (nQ + 1),
            Q.coeff N (Fin.cast hcardQ.symm k) *
              mpv (Q.basis (Fin.cast hcardQ.symm k)) σ := hQ_reindex
      _ = Q.coeff N k₀' * mpv (Q.basis k₀') σ
            + ∑ l : Fin nQ,
                Q.coeff N (Fin.cast hcardQ.symm (k₀.succAbove l)) *
                  mpv (Q.basis (Fin.cast hcardQ.symm (k₀.succAbove l))) σ :=
        hQ_split
      _ = (ζ ^ N * Q.coeff N k₀') * mpv (P.basis j₀) σ
            + ∑ l : Fin nQ,
                Q.coeff N (Fin.cast hcardQ.symm (k₀.succAbove l)) *
                  mpv (Q.basis (Fin.cast hcardQ.symm (k₀.succAbove l))) σ := by
        rw [hMpv_N]; ring
  -- Difference relation: ∑ x, (cS x - cT x) • v x = 0.
  have hDiff :
      ∑ x : Sum (Fin P.basisCount) (Fin nQ), (cS x - cT x) • v x = 0 := by
    have := sub_eq_zero.mpr hSums
    simpa [Finset.sum_sub_distrib, sub_smul] using this
  -- Apply combined-family LI to conclude cS x - cT x = 0 for every x.
  have hLI_N := hLI N hN
  have hCoeffZero :
      ∀ x : Sum (Fin P.basisCount) (Fin nQ), cS x - cT x = 0 :=
    Fintype.linearIndependent_iff.mp hLI_N (fun x => cS x - cT x) hDiff
  -- Specialise at `inl j₀`.
  have hAt : cS (Sum.inl j₀) - cT (Sum.inl j₀) = 0 := hCoeffZero (Sum.inl j₀)
  -- Unfold `cS` and `cT` at `inl j₀`.
  have hUnfold : cS (Sum.inl j₀) - cT (Sum.inl j₀)
      = P.coeff N j₀ - ζ ^ N * Q.coeff N k₀' := by
    simp [cS, cT]
  have hEq : P.coeff N j₀ - ζ ^ N * Q.coeff N k₀' = 0 := hUnfold ▸ hAt
  exact sub_eq_zero.mp hEq

/-! ### Matched-sector weight multiset equality

Once the eventual coefficient identity
`P.coeff N j₀ = ζ^N · Q.coeff N k₀'` holds, the equivalent eventual
power-sum identity `∑_q (P.weight j₀ q)^N = ∑_q (ζ · Q.weight k₀' q)^N`
combined with the unequal-cardinality power-sum recovery
(`Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card`)
forces equality of the underlying weight multisets.  This is the
algebraic crux of CPSV16 line 1188 (`μ_{j,q} = ν_{j,q} · e^{i\phi_j}`
and matching per-sector multiplicities `r_{a,j} = r_{b,j}`).
-/

/-- **Matched-sector weight multiset equality and per-copy multiplicity match.**

If `P.coeff N j₀ = ζ^N · Q.coeff N k₀'` for every `N` past some threshold
`N₀`, with `ζ ≠ 0`, then `P.copies j₀ = Q.copies k₀'` and the two
per-copy weight multisets agree:
`Multiset.map (P.weight j₀) Finset.univ.val
   = Multiset.map (fun q => ζ * Q.weight k₀' q) Finset.univ.val`.

This is CPSV16 line 1188 read on a single matched sector: equal power
sums (eventually in `N`) and nonzero entries imply equal multisets, hence
equal cardinalities.

The proof composes `power_sums_eq_of_eventually_eq_hetero` (extension
from eventual to all positive exponents) with
`Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card`
(unequal-cardinality power-sum recovery). -/
theorem matched_sector_weight_multiset_eq
    {P Q : SectorDecomposition d}
    (j₀ : Fin P.basisCount) (k₀' : Fin Q.basisCount)
    (ζ : ℂ) (hζ : ζ ≠ 0)
    {N₀ : ℕ}
    (hCoeff : ∀ N > N₀, P.coeff N j₀ = ζ ^ N * Q.coeff N k₀') :
    ∃ hCopies : P.copies j₀ = Q.copies k₀',
      Multiset.map (P.weight j₀) (Finset.univ : Finset (Fin (P.copies j₀))).val
        = Multiset.map
            (fun q : Fin (P.copies j₀) =>
              ζ * Q.weight k₀' (Fin.cast hCopies q))
            (Finset.univ : Finset (Fin (P.copies j₀))).val := by
  classical
  -- Define the rescaled `Q`-side weight family `w'(q) := ζ · Q.weight k₀' q`.
  -- Its power sums match the `P`-side weight `P.weight j₀` power sums
  -- eventually.
  let wQ : Fin (Q.copies k₀') → ℂ := fun q => ζ * Q.weight k₀' q
  have hwQ_ne : ∀ q : Fin (Q.copies k₀'), wQ q ≠ 0 := by
    intro q
    exact mul_ne_zero hζ (Q.weight_ne_zero k₀' q)
  have hwP_ne : ∀ q : Fin (P.copies j₀), P.weight j₀ q ≠ 0 :=
    fun q => P.weight_ne_zero j₀ q
  -- Eventual equality of `∑ (P.weight j₀ q)^N` and `∑ (ζ · Q.weight k₀' q)^N`.
  have hPow : ∀ N, N₀ + 1 ≤ N →
      (∑ q : Fin (P.copies j₀), (P.weight j₀ q) ^ N)
        = ∑ q : Fin (Q.copies k₀'), wQ q ^ N := by
    intro N hN
    have hN' : N > N₀ := by omega
    have hCN := hCoeff N hN'
    -- Unfold `coeff` on both sides and distribute `ζ^N` through the `Q` sum.
    have hPdef : P.coeff N j₀
        = ∑ q : Fin (P.copies j₀), (P.weight j₀ q) ^ N :=
      P.coeff_eq_sum_weight_pow N j₀
    have hQdef : Q.coeff N k₀'
        = ∑ q : Fin (Q.copies k₀'), (Q.weight k₀' q) ^ N :=
      Q.coeff_eq_sum_weight_pow N k₀'
    have hRHS_distrib :
        ζ ^ N * (∑ q : Fin (Q.copies k₀'), (Q.weight k₀' q) ^ N)
          = ∑ q : Fin (Q.copies k₀'), wQ q ^ N := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro q _
      change ζ ^ N * (Q.weight k₀' q) ^ N = (ζ * Q.weight k₀' q) ^ N
      rw [mul_pow]
    calc
      ∑ q : Fin (P.copies j₀), (P.weight j₀ q) ^ N
          = P.coeff N j₀ := hPdef.symm
      _ = ζ ^ N * Q.coeff N k₀' := hCN
      _ = ζ ^ N * (∑ q : Fin (Q.copies k₀'), (Q.weight k₀' q) ^ N) := by
            rw [hQdef]
      _ = ∑ q : Fin (Q.copies k₀'), wQ q ^ N := hRHS_distrib
  -- Extend to all positive exponents via
  -- `power_sums_eq_of_eventually_eq_hetero`.
  have hAll :=
    SectorWeightData.power_sums_eq_of_eventually_eq_hetero
      (P.weight j₀) wQ hwP_ne hwQ_ne (M := N₀ + 1) hPow
  -- Apply the unequal-cardinality multiset-recovery lemma.
  obtain ⟨hCopies, hMultiset⟩ :=
    Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card
      (P.copies j₀) (Q.copies k₀') (P.weight j₀) wQ hwP_ne hwQ_ne
      (fun k _hk _hkMax => hAll k)
  refine ⟨hCopies, ?_⟩
  -- The recovery lemma yields
  --   `Multiset.map (P.weight j₀) univ = Multiset.map wQ univ`,
  -- and `wQ q = ζ · Q.weight k₀' q`.  Reindex via `Fin.cast hCopies`.
  have hReindex :
      (Finset.univ : Finset (Fin (Q.copies k₀'))).val.map wQ
        = (Finset.univ : Finset (Fin (P.copies j₀))).val.map
            (fun q : Fin (P.copies j₀) =>
              ζ * Q.weight k₀' (Fin.cast hCopies q)) := by
    let e : Fin (P.copies j₀) ≃ Fin (Q.copies k₀') :=
      (Fin.castOrderIso hCopies).toEquiv
    have hMap : Multiset.map e
        (Finset.univ : Finset (Fin (P.copies j₀))).val
          = (Finset.univ : Finset (Fin (Q.copies k₀'))).val :=
      Multiset.map_univ_val_equiv e
    calc
      (Finset.univ : Finset (Fin (Q.copies k₀'))).val.map wQ
          = (Multiset.map e
                (Finset.univ : Finset (Fin (P.copies j₀))).val).map wQ := by
            rw [hMap]
      _ = (Finset.univ : Finset (Fin (P.copies j₀))).val.map (wQ ∘ e) := by
            rw [Multiset.map_map]
      _ = (Finset.univ : Finset (Fin (P.copies j₀))).val.map
            (fun q : Fin (P.copies j₀) =>
              ζ * Q.weight k₀' (Fin.cast hCopies q)) := by
            refine Multiset.map_congr rfl ?_
            intro q _; rfl
  exact hMultiset.trans hReindex

/-! ### Matched-sector weight-permutation extractor

The multiset equality above is upgraded to an *explicit* permutation
`τ : Fin (P.copies j₀) ≃ Fin (Q.copies k₀')` matching individual per-copy
weights up to the gauge-phase factor `ζ`.  This is the per-copy form of
CPSV16 line 1188 (`μ_{j,q} = ν_{j,q} · e^{i\phi_j}` for an indexing of
the `Q`-copies determined by a matching).

The proof reduces to a generic helper extracting an `Equiv.Perm` from a
multiset-map equality on `Fin`, then composes with the cardinality cast
and clears the `ζ` factor with `mul_inv_cancel₀ hζ`.
-/

/-- **Auxiliary: extract `Equiv.Perm (Fin n)` from a multiset map equality.**

Given `f, g : Fin n → α` whose `Multiset.map`s over `Finset.univ.val`
coincide, there exists a permutation `σ` of `Fin n` with
`f q = g (σ q)` for every `q`.

Proof by induction on `n`: at the successor step, locate an index `j`
in the codomain of `g` matching `f 0`, decompose both multisets via
`Fin.univ_succAbove`, apply the inductive hypothesis to the restricted
functions on `Fin n`, and reassemble via `finSuccEquiv'` and
`Equiv.optionCongr`. -/
private lemma exists_perm_of_multiset_map_univ_eq {α : Type*} :
    ∀ {n : ℕ} (f g : Fin n → α),
      Multiset.map f (Finset.univ : Finset (Fin n)).val =
        Multiset.map g (Finset.univ : Finset (Fin n)).val →
      ∃ σ : Equiv.Perm (Fin n), ∀ q, f q = g (σ q) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _
    exact ⟨Equiv.refl _, fun q => q.elim0⟩
  | succ n ih =>
    intro f g hMap
    classical
    -- Locate `j : Fin (n+1)` with `g j = f 0`.
    have hMem : f 0 ∈ Multiset.map g (Finset.univ : Finset (Fin (n+1))).val := by
      rw [← hMap]
      exact Multiset.mem_map_of_mem f (Finset.mem_univ_val 0)
    obtain ⟨j, _hjMem, hj⟩ := Multiset.mem_map.mp hMem
    -- `Multiset.map h univ = h p ::ₘ Multiset.map (h ∘ p.succAbove) univ`.
    have decomp : ∀ (h : Fin (n+1) → α) (p : Fin (n+1)),
        Multiset.map h (Finset.univ : Finset (Fin (n+1))).val =
          h p ::ₘ Multiset.map (h ∘ p.succAbove)
            (Finset.univ : Finset (Fin n)).val := by
      intro h p
      have hUniv : (Finset.univ : Finset (Fin (n+1))).val =
          p ::ₘ ((Finset.univ : Finset (Fin n)).val.map p.succAboveEmb) := by
        rw [Fin.univ_succAbove n p, Finset.cons_val, Finset.map_val]
      rw [hUniv, Multiset.map_cons, Multiset.map_map]
      rfl
    -- Reduce to a multiset-map equality on `Fin n`.
    have hRestricted :
        Multiset.map (f ∘ (0 : Fin (n+1)).succAbove)
            (Finset.univ : Finset (Fin n)).val =
          Multiset.map (g ∘ j.succAbove)
            (Finset.univ : Finset (Fin n)).val := by
      have hEqCons :
          f 0 ::ₘ Multiset.map (f ∘ (0 : Fin (n+1)).succAbove)
              (Finset.univ : Finset (Fin n)).val =
            g j ::ₘ Multiset.map (g ∘ j.succAbove)
              (Finset.univ : Finset (Fin n)).val := by
        rw [← decomp f 0, ← decomp g j]
        exact hMap
      rw [hj] at hEqCons
      exact (Multiset.cons_inj_right (f 0)).mp hEqCons
    -- Apply the inductive hypothesis.
    obtain ⟨σ', hσ'⟩ := ih _ _ hRestricted
    -- Assemble `σ : Fin (n+1) ≃ Fin (n+1)` via `finSuccEquiv'`.
    refine ⟨((finSuccEquiv' (0 : Fin (n+1))).trans σ'.optionCongr).trans
              (finSuccEquiv' j).symm, ?_⟩
    intro q
    refine q.cases ?_ ?_
    · -- Case `q = 0`: `σ 0 = j`, and `g j = f 0` by `hj`.
      simp only [Equiv.trans_apply, finSuccEquiv'_at,
        Equiv.optionCongr_apply, Option.map_none, finSuccEquiv'_symm_none]
      exact hj.symm
    · -- Case `q = i.succ`: `σ i.succ = j.succAbove (σ' i)`.
      intro i
      have hRec := hσ' i
      simp only [Function.comp_apply, Fin.zero_succAbove] at hRec
      simp only [Equiv.trans_apply, ← Fin.zero_succAbove,
        finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
        Option.map_some, finSuccEquiv'_symm_some]
      exact hRec

set_option linter.unusedVariables false in
/-- **Matched-sector weight-permutation extractor.**

Refines `matched_sector_weight_multiset_eq` into an explicit permutation
`τ` realising CPSV16 line 1188's per-copy identification.

Paper anchor: CPSV16 §II.C lines 1158-1167, 1184, 1188 (arXiv:1606.00608). -/
theorem matched_sector_weight_equiv
    {P Q : SectorDecomposition d}
    (j₀ : Fin P.basisCount) (k₀' : Fin Q.basisCount)
    (ζ : ℂ) (hζ : ζ ≠ 0)
    {N₀ : ℕ}
    (hCoeff : ∀ N > N₀, P.coeff N j₀ = ζ ^ N * Q.coeff N k₀') :
    ∃ (hCopies : P.copies j₀ = Q.copies k₀')
      (τ : Fin (P.copies j₀) ≃ Fin (Q.copies k₀')),
      ∀ q : Fin (P.copies j₀),
        Q.weight k₀' (τ q) = ζ⁻¹ * P.weight j₀ q := by
  classical
  obtain ⟨hCopies, hMultiset⟩ :=
    matched_sector_weight_multiset_eq j₀ k₀' ζ hζ hCoeff
  -- Extract `σ : Fin (P.copies j₀) ≃ Fin (P.copies j₀)` matching the
  -- per-copy weights up to the gauge-phase factor `ζ`.
  obtain ⟨σ, hσ⟩ :=
    exists_perm_of_multiset_map_univ_eq
      (P.weight j₀)
      (fun q : Fin (P.copies j₀) => ζ * Q.weight k₀' (Fin.cast hCopies q))
      hMultiset
  -- Compose with the cardinality cast `Fin (P.copies j₀) ≃ Fin (Q.copies k₀')`.
  let castEquiv : Fin (P.copies j₀) ≃ Fin (Q.copies k₀') :=
    (Fin.castOrderIso hCopies).toEquiv
  refine ⟨hCopies, σ.trans castEquiv, ?_⟩
  intro q
  have hPoint : P.weight j₀ q = ζ * Q.weight k₀' (Fin.cast hCopies (σ q)) :=
    hσ q
  have hQ : Q.weight k₀' ((σ.trans castEquiv) q)
      = Q.weight k₀' (Fin.cast hCopies (σ q)) := by
    simp [castEquiv]
  rw [hQ, hPoint, ← mul_assoc, inv_mul_cancel₀ hζ, one_mul]

end MPSTensor
