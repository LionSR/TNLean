/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.FundamentalTheorem.SectorWeightComparison
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Overlap.Basic

/-!
# BNT canonical form on a `SectorDecomposition`

This module introduces the canonical-form predicate
`IsBNTCanonicalForm` over a `SectorDecomposition d`.

The structure is the minimal CPSV16/CPSV21 BNT canonical-form data on top of
a `SectorDecomposition`.  It records:

* **per-block normality** (injective, irreducible, left-canonical) and
  **self-overlap → 1** (non-periodic / after-blocking surface);
* **eventual linear independence** of basis MPV states (`HasBNTSectorData`);
* **block distinctness** in the cast-compatible gauge-phase shape, ruling out
  gauge-phase equivalence between distinct basis blocks of equal bond
  dimension;
* the CPSV16 §II.A line-246 **normalization convention** on the raw sector
  weights `μ_{j,q}`: `|μ_{j,q}| ≤ 1` and at least one of them equals one
  (lines 246 and 1244).

The per-block unit-modulus convention `∀ j, ∃ q, ‖μ_{j,q}‖ = 1` — implicit
in CPSV16 §II.C line 1182's projection step and not explicitly stated in
CPSV16 §II.A line 246 (which is global) nor in CPSV21 §III.2 lines 1846–1884
(which normalizes the spectral radius of the BNT *basis tensors*, not the
copy coefficients) — is **not** a structural field of `IsBNTCanonicalForm`.
The fundamental-theorem statements (`coeff_not_tendsto_zero_at_block`,
`exists_block_match_of_sameMPV`, `bijective_match_of_sameMPV`,
`ft_sector_bnt_equal_*`) take the per-block witness as an explicit
hypothesis at the theorem level, keeping the canonical-form predicate
minimal and the line-1182 implicit convention local to the theorems
that actually need it.

The structure does **not** impose an equal-modulus or strict-order
condition on the raw sector weights `P.weight j q`.  CPSV16
`eq:II_ABasicTensors` (line 286), CPSV21 Definition 4.2 (lines 1846–1850),
and the CPSV21 two-layer display (lines 1864–1884) use raw entries
`μ_{j,q}` and a coefficient `∑_q μ_{j,q}^N`; they do not require
`|μ_{j,q}|` to be constant in `q`, nor do they impose a strict order on the
moduli of distinct BNT basis elements.  The audit memo
`audits/2026-05-13_cpsv16_sector_bnt_phase_1_multiplicity_audit.md` collects
the counter-examples (`C ⊕ D`, `C ⊕ (1/2)C`, `C ⊕ (-C) ⊕ (1/2)C`) that
motivate keeping the equal-modulus layer out of the core predicate; all of
them are admitted by the line-246 normalization fields below (every weight
has modulus `≤ 1`, and at least one copy of one basis sector has unit
modulus).

An optional equal-modulus weight layer is provided separately as
`HasEqualModulusWeightLayer` in `SectorBNT/EqualModulus.lean`.  Some
downstream estimates may consume that layer; it is not part of the
core BNT predicate.

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.  Source-line tags used
  below: 217–246 (global modulus normalization), 264–279 (gauge-phase
  grouping rule), 271–301 (two-layer BNT display with raw `μ_{j,q}`),
  1121–1132 (combined-family LI input), 1181–1188 (multiplicity recovery
  via power-sum comparison).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete, *Matrix product states and
  projected entangled pair states: Concepts, symmetries, theorems*,
  Rev. Mod. Phys. **93**, 045003 (2021); arXiv:2011.12127.  Source-line tags
  used below: 1815–1837 (normal tensors primitive after blocking; canonical
  form `⊕_k μ_k A_k`), 1846–1884 (BNT and two-layer BNT decomposition with
  raw `μ_{j,q}` and per-block spectral-radius-one normalization),
  1905–1908 (unital gauge optional; non-periodic theorem separated from
  periodic generalization).
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/--
**BNT canonical form (core predicate `IsBNTCanonicalForm`).**

Given `P : SectorDecomposition d`, this captures the minimal CPSV16/CPSV21
BNT canonical-form data without any equal-modulus or strict-ordering
assumption on the raw sector weights.  The MPV expansion that flows from
this predicate is

```
mpv P.toTensor σ
  = ∑_j (∑_q (P.weight j q)^N) · mpv (P.basis j) σ,
```

i.e. CPSV16 §II's two-layer BNT display (lines 271–301) and CPSV21
Definition 4.2 (lines 1846–1850) together with the two-layer display
(lines 1864–1884) with **raw** `μ_{j,q}` entries and
coefficient `∑_q μ_{j,q}^N`.

The audit `audits/2026-05-13_cpsv16_sector_bnt_phase_1_multiplicity_audit.md`
records the counter-examples that motivate keeping equal-modulus/spectral
data out of this core predicate.
-/
structure IsBNTCanonicalForm (P : SectorDecomposition d) where
  /-- Every basis bond dimension is positive (needed for `NeZero` typeclass
  inference on `Fin (P.basisDim j)`; cf. CPSV21 lines 1815–1830 where the
  primitive transfer map lives on a positive-dimension block). -/
  basis_dim_pos : ∀ j : Fin P.basisCount, 0 < P.basisDim j
  /-- **Per-block injectivity.**  Each basis block `P.basis j` is an
  injective MPS tensor (CPSV21 lines 1815–1830). -/
  basis_injective : ∀ j : Fin P.basisCount, IsInjective (P.basis j)
  /-- **Per-block irreducibility.**  Each basis block has irreducible
  transfer map after blocking (CPSV16 lines 233–234; CPSV21 lines
  1815–1830). -/
  basis_irreducible : ∀ j : Fin P.basisCount, IsIrreducibleTensor (P.basis j)
  /-- **Per-block left-canonical form** (CPSV21 lines 1815–1837). -/
  basis_left_canonical : ∀ j : Fin P.basisCount, IsLeftCanonical (P.basis j)
  /-- **Per-block normalized self-overlap.**  Each basis block has
  `mpvOverlap (P.basis j) (P.basis j) N → 1` as `N → ∞`.  This selects the
  non-periodic / after-blocking BNT surface (CPSV21 line 1818; the periodic
  generalization at CPSV21 lines 1905–1908 is deliberately not included
  here). -/
  basis_normalized_self_overlap : ∀ j : Fin P.basisCount,
    Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
      atTop (𝓝 1)
  /-- **BNT eventual linear independence** of the basis MPV states
  (CPSV21 Definition 4.2, lines 1846–1850; combined-family LI input at
  CPSV16 lines 1121–1132). -/
  bnt_data : HasBNTSectorData P
  /-- **Block distinctness.**  No gauge-phase equivalence between distinct
  basis blocks of equal bond dimension; this is the cast-compatible shape
  used by `BlocksNotGaugePhaseEquiv` in
  `TNLean/MPS/BNT/Construction.lean`, matching the CPSV16 lines 264–279
  grouping rule. -/
  basis_distinct : ∀ j k : Fin P.basisCount, j ≠ k →
    ∀ h : P.basisDim j = P.basisDim k,
      ¬ GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis j)) (P.basis k)
  /-- **CPSV16 line-246 normalization, modulus bound.**  Every raw sector
  weight has modulus at most one.  CPSV16 §II.A line 246: "we can always
  choose `|μ_k| ≤ 1`"; reinvoked in the body of the FT proof at line 1244
  ("the assumed normalization `|μ_{jq}| ≤ 1` … implies that `𝔼^N` converges").
  This convention admits all counter-examples of the prior audit
  (`audits/2026-05-13_cpsv16_sector_bnt_phase_1_multiplicity_audit.md`):
  `C ⊕ D` (weights `(1, 1)`), `C ⊕ (-C)` (weights `(1, -1)`),
  `C ⊕ (1/2)C` (weights `(1, 1/2)`), and `C ⊕ (-C) ⊕ (1/2)C`. -/
  weight_norm_le_one : ∀ (j : Fin P.basisCount) (q : Fin (P.copies j)),
    ‖P.weight j q‖ ≤ 1
  /-- **CPSV16 line-246 global unit witness.**  At least one copy of one
  basis sector has unit-modulus weight.  CPSV16 §II.A line 246: "we can
  always choose `|μ_k| ≤ 1` and at least one of them equals one."  This
  is the global (not per-block) normalization condition; the per-block
  refinement `∀ j, ∃ q, ‖μ_{j,q}‖ = 1` is paper-implicit in CPSV16 §II.C
  line 1182's projection argument and is therefore taken as an explicit
  per-theorem hypothesis on the fundamental-theorem theorems, rather
  than baked into this structural predicate. -/
  weight_unit_exists : ∃ (j : Fin P.basisCount) (q : Fin (P.copies j)),
    ‖P.weight j q‖ = 1

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- **Sector coefficient is not eventually zero.**

For any sector `j`, the power-sum coefficient
`P.coeff N j = ∑_q (P.weight j q)^N` is not eventually zero in `N`.  This
rules out the pathological cancellation that would obstruct the CPSV16 §II
Step 1 coefficient-comparison argument: once combined-family LI isolates
the `j`-th sector coefficient (CPSV16 lines 1121–1132), the surviving
relation cannot be `0 = 0` for large `N`, so the multiplicity-recovery
argument of CPSV16 lines 1181–1188 has a nonvanishing left-hand side to
compare against.

The proof feeds nonzero weights `P.weight j q ≠ 0` (from
`P.weight_ne_zero`) into `geom_sum_eventually_zero`
(`TNLean/MPS/FundamentalTheorem/SectorWeightComparison.lean`): if the
power-sum were eventually zero, the geometric-extrapolation lemma would
force it to vanish at every exponent including `0`, contradicting the
positivity of `P.copies j` (i.e. `∑_q 1 = P.copies j ≠ 0`).
-/
lemma coeff_not_eventually_zero
    (_h : IsBNTCanonicalForm P) (j : Fin P.basisCount) :
    ¬ (∀ᶠ N in Filter.atTop, P.coeff N j = 0) := by
  classical
  intro hEv
  -- Extract an explicit threshold `M` past which the power sum vanishes.
  rw [Filter.eventually_atTop] at hEv
  obtain ⟨M, hM⟩ := hEv
  -- Apply `geom_sum_eventually_zero` with weights `P.weight j` (all nonzero)
  -- and constants `c q = 1`, to conclude vanishing at every exponent.
  have hwne : ∀ q : Fin (P.copies j), P.weight j q ≠ 0 :=
    fun q => P.weight_ne_zero j q
  have hAll : ∀ k, ∑ q : Fin (P.copies j), (1 : ℂ) * (P.weight j q) ^ k = 0 := by
    refine SectorWeightData.geom_sum_eventually_zero
      (w := P.weight j) (c := fun _ => 1) hwne (M := M) ?_
    intro N hN
    have hzero : P.coeff N j = 0 := hM N hN
    -- `∑ q, 1 * w^N = ∑ q, w^N = coeff`.
    simpa [SectorDecomposition.coeff, SectorWeightData.coeff, one_mul] using hzero
  -- Specialize at `k = 0` to get `(P.copies j : ℂ) = 0`, contradicting positivity.
  have h0 := hAll 0
  -- `∑ q, 1 * w^0 = ∑ q, 1 = P.copies j`.
  have hcard : (∑ _q : Fin (P.copies j), (1 : ℂ) * (P.weight j _q) ^ 0)
      = (P.copies j : ℂ) := by
    simp
  rw [hcard] at h0
  -- But `0 < P.copies j` rules out `(P.copies j : ℂ) = 0`.
  have hpos : 0 < P.copies j := P.copies_pos j
  exact (Nat.cast_ne_zero.mpr hpos.ne') h0

end IsBNTCanonicalForm

end MPSTensor
