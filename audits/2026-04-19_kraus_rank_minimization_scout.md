# Kraus-rank minimization scout (report-only)

Date: 2026-04-19  
Scope: feasibility of discharging `PRefinementInverseCanonicalization` in `TNLean/MPS/Periodic/Symmetry.lean` without source proof changes.

## 0) Target restatement and constraint

`PRefinementInverseCanonicalization` asks:

- Given `B : MPSTensor d D` with `IsIrreducibleForm B`, and
- `IsPDivisibleChannel (transferMap B) p` (i.e. `transferMap B = E'^p` for some CPTP `E'`),
- conclude `∃ A : MPSTensor d D, transferMap B = transferMap (blockTensor A p)`.

The current file already flags the hard part explicitly: one needs a Kraus-rank reduction/canonicalization bridge from an arbitrary CPTP root `E'` to a `d`-indexed Kraus family. In general, minimal Kraus rank of `E'` may exceed `d`.

## 1) TNLean surface (current)

### 1.1 Reverse theorem hook and where the gap is encoded

- `IsPDivisibleChannel` is existential over a CPTP root `E'` with no Kraus-cardinality bound.
- `PRefinementInverseCanonicalization` is an explicit hypothesis packaging the missing analytic step.
- `thm_4_1_p_refinement_reverse` already consumes that hypothesis and then applies `kraus_isometry_freedom_iff` to get the `W` witness once a `d`-indexed `A` exists.

So the reverse theorem is structurally complete *except* for producing a size-`d` Kraus witness from p-divisibility.

### 1.2 Choi/Jamiolkowski and Kraus files

- `ChoiJamiolkowski.cp_iff_choi_posSemidef`: CP iff Choi PSD.
- Converse direction builds Kraus families from `Matrix.posSemidef_iff_eq_sum_vecMulVec`.
- `exists_cpMap_of_choi_posSemidef` similarly constructs a CP map from PSD Choi via a finite decomposition.

Important scout observation: these constructions provide *some* finite Kraus family, but no “minimal rank” / “exactly r = rank(Choi)” API and no cardinality-optimality theorem.

- `KrausRepresentation`: normalization and sufficient-direction freedom lemmas.
- `KrausFreedom` + `KrausUnitaryFreedom`: necessary/sufficient rectangular/unitary freedom (`kraus_rectangular_freedom`, `kraus_isometry_freedom_iff`, `kraus_unitary_freedom_iff`).

These are strong once two Kraus families already exist, but they do not create a lower-cardinality family from a larger one nor identify minimal size with a Choi rank.

### 1.3 CanonicalGauge interaction

- `FixedPoint/CanonicalGauge.gauged_leftCanonical` / `gauged_unital` provide similarity gauges preserving transfer-map structure and canonical normalization constraints.
- These gauge lemmas do not change Kraus index cardinality by themselves; they are gauge-normalization tools, not rank-minimization tools.

## 2) Mathlib surface (closest available)

### 2.1 Available core algebraic tools

- `Matrix.rank`, `Matrix.rank_mul_le_left/right`, `Matrix.rank_conjTranspose_mul_self`, `Matrix.rank_self_mul_conjTranspose` in `LinearAlgebra/Matrix/Rank.lean`.
- PSD infrastructure in `LinearAlgebra/Matrix/PosDef.lean`, notably positivity lemmas and rank-1 PSD atoms via `posSemidef_vecMulVec_self_star`.
- TNLean already relies on `Matrix.posSemidef_iff_eq_sum_vecMulVec` to extract finite vecMulVec decompositions.

### 2.2 Missing direct API for this task

No direct Mathlib/TNLean theorem located of the form:

1. `minimalKrausCardinality(T) = rank(choiMatrix T)`, or
2. existence of a Kraus family indexed by `Fin (rank (choiMatrix T))`, or
3. cardinality monotonicity under channel powers/roots that would force an arbitrary root `E'` to have Kraus rank `≤ d` from knowledge about `E'^p = transferMap B` with `d` Kraus operators.

Hence, all “rank=minimal Kraus count” plumbing appears to be unformalized surface.

## 3) Feasibility verdict for the exact target

### Verdict: **not automatic from current assumptions; near-term direct discharge is high-risk without new theory.**

Reasoning:

1. `IsPDivisibleChannel` only gives existence of *some* CPTP root `E'`.
2. Current APIs do not bound the Kraus cardinality of that root by `d`.
3. `IsIrreducibleForm B` in current formalization feeds canonical/symmetry arguments, but no located theorem ties it to “every CPTP p-th root of `transferMap B` has Kraus rank ≤ d`”.
4. The paper’s 6-line converse step appears to implicitly assume availability of a root Kraus family compatible with physical dimension `d` (or assumes a minimality argument not spelled out there).

Therefore the claim “Kraus-rank = d is automatic from irreducibility + p-divisibility” is not currently justified by available formal surface.

## 4) Recommended decomposition

### Option A (formalization path, 3 PRs)

1. **PR-A: Choi rank ↔ minimal Kraus cardinality scaffold**
   - Add TNLean lemmas: finite Kraus decomposition with explicit cardinal bound from Choi decomposition; then prove lower bound via linear independence/Gram argument.
   - End theorem target: existence of a Kraus family with size `rank(choiMatrix T)`.

2. **PR-B: Root-cardinality bridge for p-divisibility in MPS setting**
   - Prove a sufficient criterion: for `E = transferMap B` with `B : MPSTensor d D`, any admissible root under chosen hypotheses has Kraus cardinality `≤ d` (or produce one such root).
   - If full generality fails, encode additional hypotheses needed.

3. **PR-C: Assemble reverse canonicalization**
   - Instantiate PR-A/B to produce `A : MPSTensor d D` in `PRefinementInverseCanonicalization`.
   - Remove/replace hypothesis in `thm_4_1_p_refinement_reverse` where possible.

### Option B (recommended if schedule-constrained)

Strengthen spec instead of proving minimization now:

- redefine/augment `IsPDivisibleChannel` with a witness carrying a `Fin d`-indexed Kraus family for the root (or a bounded-cardinality witness),
- or generalize `IsPRefinable` to permit root physical dimension `d'` and derive the original statement only under an extra bound hypothesis.

This avoids a large detour through minimal Kraus-rank theory and matches current proof architecture.

## 5) Effort estimate

- **PR-A (new theory):** ~500–1000 LOC, medium/high novelty (Choi-rank-minimal Kraus formal bridge).
- **PR-B (application bridge):** ~250–600 LOC, high mathematical risk (depends on whether the desired rank bound is true under current irreducibility notion).
- **PR-C (integration):** ~120–250 LOC, low/medium novelty once A/B exist.

If choosing Option B, a single focused design PR (~120–300 LOC) is likely enough.

## Final scout conclusion

Given current Mathlib/TNLean surface, discharging `PRefinementInverseCanonicalization` from
`IsIrreducibleForm B + IsPDivisibleChannel (transferMap B) p` alone is **not near-term routine**.
The blocker is exactly the missing formal bridge from p-divisibility root existence to a root Kraus family of size `d` (or `≤ d`), which the paper glosses over.
