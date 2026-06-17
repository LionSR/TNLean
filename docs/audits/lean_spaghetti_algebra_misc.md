# Lean 4 Code Quality Audit: `lean_spaghetti_4`

Date: 2026-04-08

Scope audited:

- `TNLean/PiAlgebra/`
- `TNLean/Algebra/`
- `TNLean/Analysis/`
- `TNLean/MPS/MPDO/`
- `TNLean/MPS/Defs.lean`
- `TNLean/MPS/Overlap/`
- `TNLean/MPS/Periodic/`
- `TNLean/MPS/Chain/`
- `TNLean/PEPS/`

Method:

- Ran the three requested global shell commands.
- Scanned each target file for line count, real `sorry` tokens, `axiom` declarations, TODO/FIXME/XXX markers, Lean 3 syntax markers (`begin ... end`, `by { ... }`), and broad `simp` calls.
- Heuristically flagged theorem/lemma/instance bodies longer than 50 lines.
- Read all files with actual placeholders plus the main long-proof hotspots.

Notes:

- `simp` without `only` is reported because you requested it; this is not automatically a defect.
- Dead-code and copy-paste findings are conservative. I did not run semantic unused-declaration analysis.

## Executive Summary

Highest-signal findings:

1. `TNLean/PEPS/FundamentalTheorem.lean` is the only audited file with real `sorry`s. It is explicitly a scaffold file, imported at the project root, and contains 6 placeholder theorem bodies plus 8 TODO markers. Two sorrys look like plausible near-term proof tasks; four are blocked by missing PEPS infrastructure already documented in comments.
2. No audited file declares an `axiom`. Repo-wide, the only actual `axiom` declaration is `TNLean/Axioms/Entropy.lean:55`.
3. No Lean 3 style syntax (`begin ... end`, `by { ... }`) was found in the audited scope.
4. The main maintainability risk outside PEPS is proof size. The worst long-proof clusters are in:
   - `TNLean/MPS/Overlap/PeripheralToSpectralGap.lean`
   - `TNLean/Algebra/ProjectionTriangularTrace.lean`
   - `TNLean/Algebra/BurnsideTheorem.lean`
   - `TNLean/Algebra/IrreducibleTensorAction.lean`
   - `TNLean/MPS/Chain/TensorEquality.lean`
   - `TNLean/PiAlgebra/CanonicalFormSepAux.lean`
5. Copy-paste risk is low overall. The only clear duplication I saw is relation-law boilerplate duplicated between `TNLean/MPS/Chain/Defs.lean` and `TNLean/MPS/Periodic/Defs.lean`, plus repeated TODO+`sorry` scaffolding in `TNLean/PEPS/FundamentalTheorem.lean`.

## Global Checks

Requested command:

```bash
find TNLean -name "*.lean" | xargs wc -l | sort -n | tail -20
```

Output:

```text
     757 TNLean/PiAlgebra/CanonicalFormSep.lean
     774 TNLean/MPS/FundamentalTheorem/PeriodicOverlap.lean
     829 TNLean/MPS/Symmetry/StringOrderAux.lean
     838 TNLean/Wielandt/RectangularSpan/Universality.lean
     860 TNLean/PiAlgebra/CanonicalFormSepAux.lean
     865 TNLean/MPS/Structure/InvariantSubspaceDecomp.lean
     901 TNLean/Channel/Semigroup/RelaxationConditions.lean
     922 TNLean/Archive/BlockingPeriodicityCFII2.lean
     939 TNLean/MPS/BNT/PermutationRigidity.lean
     972 TNLean/Channel/Irreducible/Growth.lean
    1035 TNLean/Wielandt/Primitivity/StronglyIrreducibleToFullRank.lean
    1039 TNLean/Channel/Schwarz/PositiveOnAbelian.lean
    1097 TNLean/Wielandt/RectangularSpan/UniversalityAux.lean
    1113 TNLean/Spectral/SpectralGap.lean
    1121 TNLean/MPS/CanonicalForm/Assembly.lean
    1202 TNLean/Channel/Determinant.lean
    1275 TNLean/Spectral/SpectralGapNT.lean
    1344 TNLean/MPS/FundamentalTheorem/Full.lean
    1426 TNLean/Channel/Peripheral/CyclicDecomposition.lean
   77961 total
```

Requested command:

```bash
grep -rn "axiom " TNLean/ --include="*.lean"
```

Raw output:

```text
TNLean/Axioms/Entropy.lean:10:This module isolates the axiom for **strong subadditivity** (Lieb–Ruskai 1973)
TNLean/Axioms/Entropy.lean:11:so that the axiom is clearly separated from the proved results.
TNLean/Axioms/Entropy.lean:55:axiom strong_subadditivity
TNLean/MPS/BNT/Construction.lean:125:`IsCanonicalFormBNT`, since the separation axiom is vacuous. -/
TNLean/MPS/BNT/Construction.lean:238:Only injectivity, left-canonical normalization, and the BNT non-equivalence axiom are used. -/
TNLean/MPS/BNT/Construction.lean:331:Only irreducibility, left-canonical normalization, and the BNT non-equivalence axiom are used. -/
```

Interpretation:

- The raw `grep` hits in `TNLean/MPS/BNT/Construction.lean` are prose only.
- The only actual `axiom` declaration in the whole repo is:

```text
TNLean/Axioms/Entropy.lean:55:axiom strong_subadditivity
```

Requested command:

```bash
grep -rn "sorry" TNLean/ --include="*.lean" | grep -v "^.*:.*--" | wc -l
```

Output:

```text
54
```

Interpretation:

- Repo-wide real `sorry` count from the requested command: 54.
- Audited-scope real `sorry` count: 6, all in `TNLean/PEPS/FundamentalTheorem.lean`.

## File-By-File Audit

## PiAlgebra

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/PiAlgebra/BlockSeparation.lean` | 187 | 0 | `theorem sameMPV₂_repeated_word` (104-187, 84 lines) | None obvious. | None obvious. | 2 hit(s) at [81, 88] | No sorrys. | No. | None | None |
| `TNLean/PiAlgebra/CanonicalFormSep.lean` | 757 | 0 | `theorem block_separation_all_words_of_irreducible_TP` (539-610, 72 lines) | None obvious. | None obvious. | 5 hit(s) at [128, 134, 154, 201, 318] | No sorrys. | No. | None | None |
| `TNLean/PiAlgebra/CanonicalFormSepAux.lean` | 860 | 0 | `theorem toIsNormalCanonicalForm` (377-451, 75 lines); `lemma leftCanonical_mpvOverlap_self_bound` (452-513, 62 lines); `lemma leftCanonical_mpvOverlap_bound` (539-630, 92 lines); `theorem peeling_exponential_bound` (675-754, 80 lines) | None obvious. | None obvious. | 17 hit(s); first hits [444, 448, 479, 500, 506, 508] | No sorrys. | No. | None | None |
| `TNLean/PiAlgebra/Construction.lean` | 290 | 0 | None | None obvious. | None obvious. | 9 hit(s); first hits [152, 165, 175, 177, 178, 181] | No sorrys. | No. | None | None |
| `TNLean/PiAlgebra/FundamentalTheoremComplete.lean` | 222 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/PiAlgebra/GlobalSymmetry.lean` | 187 | 0 | `theorem gaugeMatrix_projective_mul` (109-187, 79 lines) | None obvious. | None obvious. | 9 hit(s); first hits [62, 64, 69, 73, 77, 81] | No sorrys. | No. | None | None |
| `TNLean/PiAlgebra/TIReduction.lean` | 82 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |

PiAlgebra remarks:

- Main issue is concentration of very long proofs in `CanonicalFormSepAux.lean` and a smaller cluster in `CanonicalFormSep.lean`.
- No placeholders, TODOs, axioms, or Lean 3 syntax in this subtree.

## Algebra

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/Algebra/BlockPermutation.lean` | 172 | 0 | None | None obvious. | None obvious. | 4 hit(s) at [95, 156, 161, 165] | No sorrys. | No. | None | None |
| `TNLean/Algebra/BlockTriangularTrace.lean` | 195 | 0 | `lemma mpv_upperFin_eq_mpv_diagFin` (129-182, 54 lines) | None obvious. | None obvious. | 8 hit(s); first hits [67, 86, 91, 105, 107, 124] | No sorrys. | No. | None | None |
| `TNLean/Algebra/BurnsideMatrix.lean` | 269 | 0 | None | None obvious. | None obvious. | 2 hit(s) at [127, 129] | No sorrys. | No. | None | None |
| `TNLean/Algebra/BurnsideTheorem.lean` | 197 | 0 | `theorem burnside_matrix [NeZero D]` (76-197, 122 lines) | None obvious. | None obvious. | 5 hit(s) at [107, 148, 159, 176, 194] | No sorrys. | No. | None | None |
| `TNLean/Algebra/CocycleCohomology.lean` | 151 | 0 | None | None obvious. | None obvious. | 3 hit(s) at [87, 147, 149] | No sorrys. | No. | None | None |
| `TNLean/Algebra/GramMatrixLI.lean` | 78 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/Algebra/HermitianHelpers.lean` | 55 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/Algebra/IrreducibleTensorAction.lean` | 155 | 0 | `theorem isIrreducibleAction_of_isIrreducibleTensor` (34-155, 122 lines) | None obvious. | None obvious. | 10 hit(s); first hits [82, 84, 94, 98, 105, 115] | No sorrys. | No. | None | None |
| `TNLean/Algebra/MatrixAux.lean` | 128 | 0 | None | None obvious. | None obvious. | 1 hit(s) at [83] | No sorrys. | No. | None | None |
| `TNLean/Algebra/MatrixFrobenius.lean` | 27 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/Algebra/MatrixFunctionalCalculus.lean` | 30 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/Algebra/MatrixOperatorSpace.lean` | 156 | 0 | None | None obvious. | None obvious. | 4 hit(s) at [55, 61, 121, 127] | No sorrys. | No. | None | None |
| `TNLean/Algebra/NewtonGirard.lean` | 341 | 0 | None | None obvious. | None obvious. | 11 hit(s); first hits [118, 125, 126, 148, 149, 154] | No sorrys. | No. | None | None |
| `TNLean/Algebra/ProjectionTriangularTrace.lean` | 308 | 0 | `lemma evalWord_diagPart_eq` (110-236, 127 lines) | None obvious. | None obvious. | 26 hit(s); first hits [45, 82, 84, 88, 90, 95] | No sorrys. | No. | None | None |
| `TNLean/Algebra/ProjectiveRepresentation.lean` | 145 | 0 | None | None obvious. | None obvious. | 5 hit(s) at [66, 70, 86, 91, 113] | No sorrys. | No. | None | None |
| `TNLean/Algebra/ScalarCommutant.lean` | 55 | 0 | None | None obvious. | None obvious. | 1 hit(s) at [40] | No sorrys. | No. | None | None |
| `TNLean/Algebra/ScalarPowerSumIdentity.lean` | 89 | 0 | None | None obvious. | None obvious. | 2 hit(s) at [50, 86] | No sorrys. | No. | None | None |
| `TNLean/Algebra/SkolemNoether.lean` | 122 | 0 | `theorem skolemNoether_matrix` (61-122, 62 lines) | None obvious. | None obvious. | 6 hit(s) at [76, 93, 95, 97, 98, 120] | No sorrys. | No. | None | None |
| `TNLean/Algebra/TracePairing.lean` | 138 | 0 | None | None obvious. | None obvious. | 3 hit(s) at [46, 77, 119] | No sorrys. | No. | None | None |

Algebra remarks:

- The proof-length concentration is real here. `BurnsideTheorem.lean`, `IrreducibleTensorAction.lean`, `ProjectionTriangularTrace.lean`, and `SkolemNoether.lean` would all benefit from helper extraction.
- `ProjectionTriangularTrace.lean` is the strongest “spaghetti” candidate in this subtree: one 127-line lemma plus 26 broad `simp` hits.

## Analysis

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/Analysis/ConvergenceHelpers.lean` | 79 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/Analysis/Entropy.lean` | 311 | 0 | `theorem vonNeumannEntropy_le_log_dim` (122-202, 81 lines) | TODO in module prose at line 270: deferred SSA equality characterization. | None obvious. | 3 hit(s) at [134, 143, 156] | No sorrys. | No. | None | None |

Analysis remarks:

- Only one stale TODO in audited analysis code: the deferred SSA equality theorem note in `Entropy.lean`.
- No placeholder theorems in the audited analysis scope.

## MPS/MPDO

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/MPS/MPDO/Defs.lean` | 279 | 0 | None | None obvious. | None obvious. | 2 hit(s) at [94, 139] | No sorrys. | No. | None | None |

MPS/MPDO remarks:

- Clean mechanically.
- No obvious dead code, no TODOs, no placeholders.

## MPS

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/MPS/Defs.lean` | 249 | 0 | None | None obvious. | None obvious. | 11 hit(s); first hits [45, 46, 55, 57, 173, 174] | No sorrys. | No. | None | None |

MPS core remarks:

- Clean on placeholders and Lean 3 syntax.
- Broad `simp` use is frequent but not unusual for a core API file.

## MPS/Overlap

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/MPS/Overlap/Basic.lean` | 82 | 0 | None | None obvious. | None obvious. | 3 hit(s) at [45, 59, 66] | No sorrys. | No. | None | None |
| `TNLean/MPS/Overlap/CastDecay.lean` | 74 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/MPS/Overlap/CastLemmas.lean` | 86 | 0 | None | None obvious. | None obvious. | 4 hit(s) at [30, 37, 42, 58] | No sorrys. | No. | None | None |
| `TNLean/MPS/Overlap/PeripheralToSpectralGap.lean` | 489 | 0 | `lemma transferMap_conjTranspose` (61-198, 138 lines); `theorem transferMap_fixedPoint_eq_zero_of_trace_eq_zero` (199-256, 58 lines); `theorem transferMap_fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible` (257-347, 91 lines) | None obvious. | None obvious. | 10 hit(s); first hits [66, 109, 158, 162, 166, 170] | No sorrys. | No. | None | None |

Overlap remarks:

- `PeripheralToSpectralGap.lean` is a major proof-complexity hotspot.
- Three consecutive long results from line 61 through line 347 are a strong refactor candidate.

## MPS/Periodic

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/MPS/Periodic/Defs.lean` | 298 | 0 | None | None obvious. | Thin wrapper duplication around `PeriodicMPSTensor.{SameState,GaugeEquiv}` mirrors chain-level boilerplate from `TNLean/MPS/Chain/Defs.lean`. | 4 hit(s) at [180, 190, 239, 251] | No sorrys. | No. | None | None |

Periodic remarks:

- The only copy-paste smell I saw here is deliberate wrapper boilerplate around relation laws and equivalence instances.
- No placeholders or stale TODOs.

## MPS/Chain

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/MPS/Chain/AlgebraIsomorphism.lean` | 149 | 0 | `theorem virtual_bond_gauge [NeZero D]` (87-149, 63 lines) | None obvious. | None obvious. | 3 hit(s) at [51, 65, 113] | No sorrys. | No. | None | None |
| `TNLean/MPS/Chain/BlockedChainFT.lean` | 85 | 0 | None | None obvious. | None obvious. | 2 hit(s) at [34, 41] | No sorrys. | No. | None | None |
| `TNLean/MPS/Chain/Defs.lean` | 134 | 0 | None | None obvious. | Source of the relation-law boilerplate later mirrored in `TNLean/MPS/Periodic/Defs.lean`. | 4 hit(s) at [61, 95, 103, 113] | No sorrys. | No. | None | None |
| `TNLean/MPS/Chain/FundamentalTheorem.lean` | 73 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/MPS/Chain/OneSidedInverse.lean` | 81 | 0 | None | None obvious. | None obvious. | 1 hit(s) at [55] | No sorrys. | No. | None | None |
| `TNLean/MPS/Chain/SameStateBridge.lean` | 60 | 0 | None | None obvious. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/MPS/Chain/TensorEquality.lean` | 187 | 0 | `theorem tensor_proportional` (81-187, 107 lines) | None obvious. | None obvious. | 3 hit(s) at [45, 73, 95] | No sorrys. | No. | None | None |
| `TNLean/MPS/Chain/TranslationInvariance.lean` | 70 | 0 | None | None obvious. | None obvious. | 1 hit(s) at [63] | No sorrys. | No. | None | None |
| `TNLean/MPS/Chain/VirtualInsertion.lean` | 132 | 0 | None | None obvious. | None obvious. | 13 hit(s); first hits [56, 67, 85, 89, 91, 97] | No sorrys. | No. | None | None |

Chain remarks:

- `TensorEquality.lean` is the main long-proof candidate here.
- `VirtualInsertion.lean` has the densest broad-`simp` usage in this subtree.

## PEPS

| File | Lines | Sorry | Long proofs >50 lines | TODO/stale notes | Copy-paste | `simp` without `only` | Closable sorrys | Stub/placeholder | Axioms | Lean 3 style |
|---|---:|---:|---|---|---|---|---|---|---|---|
| `TNLean/PEPS/Defs.lean` | 73 | 0 | None | No obvious dead code, but PEPS remains exploratory and lightly connected outside the scaffold theorem file. | None obvious. | 0 hit(s) | No sorrys. | No. | None | None |
| `TNLean/PEPS/FundamentalTheorem.lean` | 252 | 6 | None | TODOs at [112, 118, 145, 162, 164, 184, 212, 246] | Heavy repeated TODO+`sorry` scaffold pattern across six theorems. | 0 hit(s) | Likely closable first: `applyGauge_stateCoeff` and then `GaugeEquiv.sameState`; the other four sorrys are blocked by missing PEPS-specific infrastructure explicitly noted in comments. | Yes: file header states it is a scaffold and 6 theorem bodies are placeholder `sorry`s. | None | None |

PEPS remarks:

- `TNLean/PEPS/FundamentalTheorem.lean` is the only audited file that is materially incomplete.
- The file itself explains why four of the placeholder theorems are not local proof cleanups:
  - `localGauge_exists` depends on a virtual-insertion / blocking reduction to a 1D MPS argument.
  - `gaugeConsistency` depends on assembling local gauges across edges.
  - `fundamentalTheorem_PEPS` still lacks a bond-dimension equality theorem.
  - `gauge_unique_up_to_scalar` depends on injectivity plus connectedness arguments not yet present.
- The first two sorrys are the only ones that currently look like reasonable closure targets without redesigning the local statement:
  - `applyGauge_stateCoeff`
  - `GaugeEquiv.sameState`

## Focused Recommendations

1. Treat `TNLean/PEPS/FundamentalTheorem.lean` as explicitly experimental until the scaffold is replaced or isolated from root imports.
2. Split long proof blocks in:
   - `TNLean/MPS/Overlap/PeripheralToSpectralGap.lean`
   - `TNLean/Algebra/ProjectionTriangularTrace.lean`
   - `TNLean/Algebra/BurnsideTheorem.lean`
   - `TNLean/Algebra/IrreducibleTensorAction.lean`
   - `TNLean/MPS/Chain/TensorEquality.lean`
   - `TNLean/PiAlgebra/CanonicalFormSepAux.lean`
3. If you want a smaller cleanup pass, factor the duplicated relation wrappers between `TNLean/MPS/Chain/Defs.lean` and `TNLean/MPS/Periodic/Defs.lean`.
4. If you want an easy placeholder reduction, start with:
   - `TNLean/PEPS/FundamentalTheorem.lean:108`
   - `TNLean/PEPS/FundamentalTheorem.lean:116`

## Bottom Line

- Audited scope is largely `sorry`-free and modern Lean 4 style.
- The only real incompleteness is the PEPS theorem scaffold.
- The main code-quality issue elsewhere is proof length and local proof density, not proof-system bypasses.
