/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.DropSector
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase

/-!
# Matched-sector subtraction on the paper-faithful BNT canonical-form surface

This module is **Phase 4b-iii** of the CPSV16/CPSV21 fundamental-theorem
clean-slate plan (issue #1688).  It is the algebraic cancellation step that
drives the strong-induction route to the full equal-MPV non-decaying-overlap
statement (CPSV16 §II `II_cor2`, lines 1172–1192).

The result is:

> If `P` and `Q` are two `SectorDecomposition`s with `SameMPV₂`, and a single
> basis-sector pair `(i₀, k₀)` is **matched** — meaning their basis MPVs are
> related by a global gauge phase `ζ` and their per-copy weight multisets are
> related by a permutation `τ` with the inverse phase `ζ⁻¹` — then dropping
> that sector from each side preserves `SameMPV₂`.

The matched-pair hypotheses (`hMpv` for the gauge-phase relation on basis
MPVs, and `τ`/`hWeight` for the weight permutation) are exactly the data
extracted, in the CPSV16 §II `II_cor2` proof outline, from:

* `exists_dominant_match_of_sameMPV` (`PaperBNT/DominantMatch.lean`),
  Phase 4b-ii, supplying `(k₀, h_dim, GaugePhaseEquiv)`;
* `Multiset.eq_of_power_sum_eq` (`PaperBNT/NewtonGirard.lean`), Phase 4b-i,
  supplying the matched weight permutation via multiplicity recovery.

Phase 4c will compose those two with the present cancellation lemma to drive
the strong induction on `P.basisCount + Q.basisCount`.

## Conventions

The single gauge phase `ζ` couples both the basis MPVs and the weight
multisets, consistent with the CPSV16 lines 1184–1188 display
`μ_{j,q} = ν_{j,q} · e^{i φ_j}`.  In our notation, with the matched indices
written as the (cast) `Fin P.basisCount`-shaped `i₀'` and
`Fin Q.basisCount`-shaped `k₀'`:

* `mpv (Q.basis k₀') σ = ζ^N · mpv (P.basis i₀') σ`
  (CPSV16 line 1187 multiplicity row, `V^{(N)}(B_k) = e^{i φ N} V^{(N)}(A_j)`);
* `Q.weight k₀' (τ q) = ζ⁻¹ · P.weight i₀' q`
  (CPSV16 line 1188 conclusion, `μ_{j,q} = ν_{j,q} · e^{i φ_j}`,
  inverted to express the `Q`-side weights in terms of the `P`-side).

The two relations share the **same** `ζ`; this coupling is what makes the
matched-sector subtraction cancel cleanly without producing a residual
`ζ^{2N}` factor.  See the proof body for the explicit cancellation
`ζ⁻^N · ζ^N = 1`.

## Main result

* `MPSTensor.sameMPV_dropSector_dropSector` — the matched-sector subtraction
  identity, stated above.

## Proof outline

For each `(N, σ)`:

1. Expand both `mpv (P.dropSector …).toTensor σ` and
   `mpv (Q.dropSector …).toTensor σ` via
   `mpv_toTensor_dropSector_eq_sub` (Phase 4a, `PaperBNT/DropSector.lean`),
   yielding
   `mpv P.toTensor σ - P.coeff N i₀' · mpv (P.basis i₀') σ`
   and the analogous expression on the `Q`-side.
2. Use `hEqual` to identify the two total MPVs.
3. Compute `Q.coeff N k₀' = ζ⁻^N · P.coeff N i₀'` by reindexing the
   per-copy sum along `τ`, substituting the weight relation, and factoring
   `(ζ⁻¹)^N` out of the sum.
4. Substitute the gauge-phase basis-MPV relation `hMpv` and the coefficient
   identity to reduce the goal to the algebraic identity
   `(ζ⁻^N · P.coeff) · (ζ^N · mpv) = P.coeff · mpv`, which `linear_combination`
   closes using `ζ⁻^N · ζ^N = 1`.

## Use in Phase 4c

Phase 4c (strong induction → full conjunction) will iterate:

* invoke `exists_dominant_match_of_sameMPV` to extract a matched index;
* invoke `Multiset.eq_of_power_sum_eq` (after coefficient extraction) to
  build the weight permutation `τ`;
* invoke the present `sameMPV_dropSector_dropSector` to drop both matched
  sectors;
* recurse on the smaller `(P.dropSector …, Q.dropSector …)` pair until
  `basisCount = 0` on one side.

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.  Source-line tags:
  287–301 (raw two-layer BNT display, `A = ⊕_j (∑_q μ_{j,q}^N) ⊗ A_j`),
  1172–1192 (`II_cor2` strong-induction step, matched-sector subtraction),
  1184–1188 (multiplicity recovery: `μ_{j,q} = ν_{j,q} · e^{i φ_j}` and
  identical per-sector multiplicities `r_{a,j} = r_{b,j}`).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete, *Matrix product states and
  projected entangled pair states*, Rev. Mod. Phys. **93**, 045003 (2021);
  arXiv:2011.12127.  Lines 1846–1884 (BNT, two-layer BNT with raw `μ_{j,q}`),
  1896–1900 (Theorem 4.5 — equal-MPV uniqueness on the BNT surface).

## Tags

matrix product states, fundamental theorem, BNT, paper-faithful BNT
canonical form, matched-sector subtraction, gauge-phase equivalence,
strong induction.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **Matched-sector subtraction preserves `SameMPV₂`.**

Given two `SectorDecomposition`s `P` and `Q` with `SameMPV₂ P.toTensor
Q.toTensor`, a basis-sector index pair `(i₀, k₀)` that is **matched** via
a single common phase `ζ ≠ 0`:

* (basis-MPV relation) `mpv (Q.basis k₀') σ = ζ^N · mpv (P.basis i₀') σ`
  for every system size `N` and configuration `σ` — the gauge-phase
  equivalence on basis MPVs at index pair `(i₀', k₀')`
  (CPSV16 line 1187 display, after `mpv_eq_pow_mul_of_gaugePhase` from
  `Defs.lean`);

* (weight relation) `Q.weight k₀' (τ q) = ζ⁻¹ · P.weight i₀' q` for every
  copy `q`, where `τ` is a bijection between the per-copy index sets —
  the multiplicity recovery `μ_{j,q} = ν_{j,q} · e^{i φ_j}`
  (CPSV16 line 1188; obtained from `Multiset.eq_of_power_sum_eq`
  applied to the coefficient comparison after the dominant-match step);

dropping the matched sector from each side preserves `SameMPV₂`.

The reduced family `(P.dropSector hcardP i₀, Q.dropSector hcardQ k₀)` is
exactly the input of the **next** inductive step in the CPSV16 §II
`II_cor2` strong induction (lines 1172–1192).

Throughout, `i₀'` and `k₀'` denote the `Fin.cast …` lifts of `i₀` and `k₀`
into `Fin P.basisCount` and `Fin Q.basisCount`, respectively, matching the
indexing convention adopted by `mpv_toTensor_dropSector_eq_sub`
(`PaperBNT/DropSector.lean`).

The `IsBNTCanonicalForm` hypotheses `hP` and `hQ` are recorded for
caller-symmetry with the downstream Phase 4c induction step, which will
have these in hand; the present algebraic identity itself does not
consume them. -/
theorem sameMPV_dropSector_dropSector
    {P Q : SectorDecomposition d}
    (_hP : IsBNTCanonicalForm P) (_hQ : IsBNTCanonicalForm Q)
    {nP nQ : ℕ}
    (hcardP : P.basisCount = nP + 1) (hcardQ : Q.basisCount = nQ + 1)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor)
    (i₀ : Fin (nP + 1)) (k₀ : Fin (nQ + 1))
    (ζ : ℂ) (hζ : ζ ≠ 0)
    (hMpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (Q.basis (Fin.cast hcardQ.symm k₀)) σ =
          ζ ^ N * mpv (P.basis (Fin.cast hcardP.symm i₀)) σ)
    (τ : Fin (P.copies (Fin.cast hcardP.symm i₀)) ≃
         Fin (Q.copies (Fin.cast hcardQ.symm k₀)))
    (hWeight : ∀ q : Fin (P.copies (Fin.cast hcardP.symm i₀)),
        Q.weight (Fin.cast hcardQ.symm k₀) (τ q) =
          ζ⁻¹ * P.weight (Fin.cast hcardP.symm i₀) q) :
    SameMPV₂ (P.dropSector hcardP i₀).toTensor
             (Q.dropSector hcardQ k₀).toTensor := by
  classical
  -- Convenience abbreviations for the cast-lifted indices.  We use plain
  -- `let`s (which only introduce a local definition and do NOT touch the
  -- already-introduced hypotheses) rather than `set` (which would force
  -- a syntactic substitution that mismatches the existing `hWeight`
  -- statement).
  let i₀' : Fin P.basisCount := Fin.cast hcardP.symm i₀
  let k₀' : Fin Q.basisCount := Fin.cast hcardQ.symm k₀
  -- Common cancellation identity: with `ζ ≠ 0`, the two phase powers cancel.
  -- This is the algebraic reason the matched-sector subtraction does not
  -- leave a residual `ζ^{2N}` factor (cf. the module docstring).
  have hCancel : ∀ N : ℕ, ζ⁻¹ ^ N * ζ ^ N = 1 := by
    intro N
    rw [← mul_pow, inv_mul_cancel₀ hζ, one_pow]
  intro N σ
  -- Step 1: subtraction display on each side
  --   (Phase 4a, CPSV16 lines 287–301 read on the dropped tensor).
  have hLHS :
      mpv (P.dropSector hcardP i₀).toTensor σ =
        mpv P.toTensor σ - P.coeff N i₀' * mpv (P.basis i₀') σ :=
    SectorDecomposition.mpv_toTensor_dropSector_eq_sub
      (P := P) hcardP i₀ (N := N) σ
  have hRHS :
      mpv (Q.dropSector hcardQ k₀).toTensor σ =
        mpv Q.toTensor σ - Q.coeff N k₀' * mpv (Q.basis k₀') σ :=
    SectorDecomposition.mpv_toTensor_dropSector_eq_sub
      (P := Q) hcardQ k₀ (N := N) σ
  -- Step 2: total MPV equality from `SameMPV₂`.
  have hSame : mpv P.toTensor σ = mpv Q.toTensor σ := hEqual N σ
  -- Step 3: matched coefficient identity
  --   `Q.coeff N k₀' = ζ⁻^N · P.coeff N i₀'`.
  -- Proof: reindex the per-copy sum by `τ`, substitute the weight relation,
  -- distribute the power, and factor `(ζ⁻¹)^N` out of the sum.
  -- This is the per-`(N,j)` reading of CPSV16 line 1188:
  --   `∑_q ν_{j,q}^N = e^{-i φ_j N} · ∑_q μ_{j,q}^N`.
  have hQ_coeff : Q.coeff N k₀' = ζ⁻¹ ^ N * P.coeff N i₀' := by
    -- Unfold both `coeff`s to explicit per-copy power sums.
    change (∑ q' : Fin (Q.copies k₀'), (Q.weight k₀' q') ^ N)
          = ζ⁻¹ ^ N * ∑ q : Fin (P.copies i₀'), (P.weight i₀' q) ^ N
    -- Reindex the `Q`-side sum along the matching permutation `τ`.
    have hReindex :
        (∑ q' : Fin (Q.copies k₀'), (Q.weight k₀' q') ^ N)
          = ∑ q : Fin (P.copies i₀'), (Q.weight k₀' (τ q)) ^ N :=
      (Equiv.sum_comp τ (fun q' => (Q.weight k₀' q') ^ N)).symm
    -- Per-term substitution of the matched-weight relation, distributing `(·)^N`.
    have hPerTerm :
        (∑ q : Fin (P.copies i₀'), (Q.weight k₀' (τ q)) ^ N)
          = ∑ q : Fin (P.copies i₀'), ζ⁻¹ ^ N * (P.weight i₀' q) ^ N := by
      refine Finset.sum_congr rfl ?_
      intro q _
      rw [hWeight q, mul_pow]
    rw [hReindex, hPerTerm, ← Finset.mul_sum]
  -- Step 4: rewrite and cancel.  The residual identity reduces to
  --   `P.coeff · mpv (P.basis i₀') σ = ζ⁻^N · ζ^N · P.coeff · mpv (P.basis i₀') σ`,
  -- which holds because `ζ⁻^N · ζ^N = 1` (`hCancel`).
  rw [hLHS, hRHS, hSame, hQ_coeff, hMpv N σ]
  -- Remaining goal:
  --   mpv Q.toTensor σ - P.coeff N i₀' · mpv (P.basis i₀') σ
  --     = mpv Q.toTensor σ
  --         - (ζ⁻¹^N · P.coeff N i₀') · (ζ^N · mpv (P.basis i₀') σ)
  -- Use `linear_combination` with the cancellation identity scaled by
  -- the common factor `P.coeff · mpv`.
  linear_combination
    (P.coeff N i₀' * mpv (P.basis i₀') σ) * hCancel N

/-! ### Equivalent formulation with explicit gauge phase and conjugation witness

This is an equivalent formulation of `sameMPV_dropSector_dropSector`
suited for Phase 4c, where the matched-pair gauge-phase equivalence is
supplied via explicit witnesses: a nonzero gauge phase `ζ`, a conjugating
matrix `X`, and a weight permutation `τ`.  The conjugation hypothesis
`hζ_of_hGPE` asserts the existence of `X` realising
`Q.basis k₀' i = ζ • (X * P.basis i₀' i * X⁻¹)`
(bond-dimension cast of `P.basis i₀'` accounted for by `h_dim`).
From `hζ_of_hGPE` the basis-MPV relation `hMpv` is derived via
`MPSTensor.mpv_eq_pow_mul_of_gaugePhase` (`SharedInfra/GaugePhase.lean`)
together with `MPSTensor.mpv_cast_dim` (`Overlap/CastLemmas.lean`), and
the result is then dispatched to `sameMPV_dropSector_dropSector`.

Paper anchor: CPSV16 lines 1172–1192 (`II_cor2`) joins the gauge-phase
equivalence `B_k = e^{i φ_k} X_k A_{j_k} X_k^{-1}` (line 1180) with the
multiplicity recovery `μ_{j,q} = ν_{j,q} · e^{i φ_j}` (line 1188); the
present reformulation feeds both into the cancellation. -/
theorem sameMPV_dropSector_dropSector_of_gaugePhaseEquiv
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    {nP nQ : ℕ}
    (hcardP : P.basisCount = nP + 1) (hcardQ : Q.basisCount = nQ + 1)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor)
    (i₀ : Fin (nP + 1)) (k₀ : Fin (nQ + 1))
    (h_dim : P.basisDim (Fin.cast hcardP.symm i₀)
             = Q.basisDim (Fin.cast hcardQ.symm k₀))
    (τ : Fin (P.copies (Fin.cast hcardP.symm i₀)) ≃
         Fin (Q.copies (Fin.cast hcardQ.symm k₀)))
    (ζ : ℂ)
    (hζ : ζ ≠ 0)
    (hζ_of_hGPE :
      ∃ X : GL (Fin (Q.basisDim (Fin.cast hcardQ.symm k₀))) ℂ,
        ∀ i : Fin d,
          Q.basis (Fin.cast hcardQ.symm k₀) i =
            ζ • ((X : Matrix _ _ ℂ) *
              (cast (congr_arg (MPSTensor d) h_dim)
                    (P.basis (Fin.cast hcardP.symm i₀))) i *
              ((X⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)))
    (hWeight : ∀ q : Fin (P.copies (Fin.cast hcardP.symm i₀)),
        Q.weight (Fin.cast hcardQ.symm k₀) (τ q) =
          ζ⁻¹ * P.weight (Fin.cast hcardP.symm i₀) q) :
    SameMPV₂ (P.dropSector hcardP i₀).toTensor
             (Q.dropSector hcardQ k₀).toTensor := by
  obtain ⟨X, hX⟩ := hζ_of_hGPE
  -- Derive the `hMpv` relation:
  --   `mpv (Q.basis k₀') σ = ζ^N · mpv (P.basis i₀') σ`.
  have hMpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis (Fin.cast hcardQ.symm k₀)) σ =
        ζ ^ N * mpv (P.basis (Fin.cast hcardP.symm i₀)) σ := by
    intro N σ
    have h₁ :=
      mpv_eq_pow_mul_of_gaugePhase
        (A := cast (congr_arg (MPSTensor d) h_dim)
              (P.basis (Fin.cast hcardP.symm i₀)))
        (B := Q.basis (Fin.cast hcardQ.symm k₀))
        X ζ hX N σ
    rw [h₁, mpv_cast_dim h_dim]
  exact sameMPV_dropSector_dropSector
    (P := P) (Q := Q) hP hQ hcardP hcardQ hEqual i₀ k₀ ζ hζ hMpv τ hWeight

end MPSTensor
