# Issue #608 blocker note — `sectorGaugePhaseEquiv_succ_of_cyclicTransport`

## Scope

Target: the single `sorry` in
`TNLean/MPS/Periodic/Overlap.lean` for
`sectorGaugePhaseEquiv_succ_of_cyclicTransport`.

I worked in the isolated worktree branch
`feat/608-sectorgaugephase-succ` as requested.

## What I verified

- Read `CLAUDE.md`, `docs/PROOF_INTEGRITY.md`, and `docs/style.md`.
- Fetched the issue body with `gh issue view 608`.
- Ran `lake exe cache get`.
- Built the live target module with
  `lake build TNLean.MPS.Periodic.Overlap`.
- Confirmed the target `sorry` is still the one at the stated lemma.

## New progress beyond the earlier blocker report

A key part of the earlier "missing API" diagnosis can actually be derived from the
existing hypotheses.

Let `P : Fin m → MatrixAlg D` be the cyclic projections from `IsCyclicSectorDecomp`.
From

- orthogonal-projection partition of unity,
- `hCyclic : transferMap (fun i => (A i)ᴴ) (P (k + 1)) = P k`, and
- `eq_zero_of_sum_mul_conjTranspose_eq_zero`,

one can prove the one-site support identities

```lean
P (k + 1) * A i = P (k + 1) * A i * P k
P (k + 1) * A i = A i * P k
```

(and similarly for the `B`-side projections).

So the "one-site corner transition" relation is not fundamentally absent from the current
API; it is derivable.

## Remaining obstruction

The real gap is the next step: turning the given blocked-sector gauge-phase match

```lean
GaugePhaseEquiv
  (cast ... (blocksA u))
  (blocksB v)
```

into a blocked-sector gauge-phase match at the shifted pair `(u + 1, v + 1)`.

The one-site support identities above let one define the ambient corner transitions
`P (k + 1) * A i = A i * P k`, and they strongly suggest an MPV/state-level translation
argument. However, I could not close the theorem from the current hypotheses alone without
an additional bridge of one of the following forms:

1. **A reblocked translation / fixed-length chain bridge**
   that converts the sector match at `(u, v)` into a transported
   proportionality / equality statement for the shifted pair at the level of
   the induced one-site transition chains; or
2. **A direct factorization theorem for cyclic products**
   saying that gauge equivalence of the `m`-step cyclic products of two transition
   chains yields gauge equivalence of the cyclically shifted `m`-step products.

What I could not derive is an **invertible successor-sector gauge witness** from the
transported relation on the `m`-fold products. In other words, the sticking point is no
longer the existence of one-site transitions, but the absence of a proved theorem that
upgrades the transported blocked-word relation to the `GaugePhaseEquiv` conclusion required
by the target lemma.

## Why I am not committing a fake proof

Using downstream sorry-backed declarations here would be mathematically circular: the later
sector-match and repeated-block lemmas are intended to depend on this bridge. I therefore did
not replace the target `sorry` with a proof that merely hides the gap behind another admitted
result.

## Suggested next attack

The most promising route now seems to be:

1. package the derived one-site identities `P (k + 1) * A i = A i * P k` and
   `Q (l + 1) * B i = B i * Q l` as local helpers;
2. define the induced length-`m` transition chains between consecutive sectors;
3. prove the fixed-length translation identity on the corresponding chain/state coefficients;
4. use a dedicated chain/block gauge theorem to recover the successor `GaugePhaseEquiv`.

This note is intended for a draft PR / handoff, not as a merged-code change.
