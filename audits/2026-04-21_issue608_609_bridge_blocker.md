# Issues #608 / #609 blocker note — Tier-A periodic bridges after a fresh re-scout

## Scope

Targets:
- `sectorGaugePhaseEquiv_succ_of_cyclicTransport` in `TNLean/MPS/Periodic/Overlap.lean`
- `repeatedBlocks_of_blockedSectorGaugePhase` in the same file

Worktree / branch used for this audit:
- `.worktrees/issue-608-609`
- `feat/608-609-tier-a-bridges`

Per protocol, before attempting proof code I:
- read `CLAUDE.md`, `docs/PROOF_INTEGRITY.md`, `docs/style.md`, `docs/blueprint_style_guide.md`
- read the full issue threads for #608 and #609
- re-read `TNLean/MPS/Periodic/Overlap.lean`, `TNLean/MPS/Periodic/CornerTransition.lean`, and Appendix A of `Papers/1708.00029/main.tex`
- posted the required short scouting comments on both issues

## What I confirmed this session

### 1. The old “pure trace-level only” diagnosis was too pessimistic

In a local, uncommitted experiment, I strengthened the compression chain

- `exists_compressedTensor_of_supported_projection`
- `exists_blockDecomp_of_commuting_projections`
- `exists_cyclic_sector_decomp_after_blocking`

with an extra **pointwise compression field** of the form

```lean
∀ i, (φ (C i)).1 = A i
```

(and the corresponding blocked-sector version
`(φ k (blocks k i)).1 = P k * blockTensor A m i`).

Those local edits to `CyclicSectors.lean` and `Assembly.lean` compiled cleanly.
So the compressed-letter part of the Eq. A.8 bridge is not fundamentally
mysterious: it really is present in the construction, just not exposed by the
current API.

### 2. The real remaining gap is now the **one-site cyclic transition identity in the right form**

Once the pointwise compression identity is exposed, the next step should be a
clean theorem turning the cyclic projection relation

```lean
transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k
```

into the exact one-site matrix identity needed to assemble the staircase
product. In the current indexing conventions this is the shape

```lean
P (k + 1) * A i = A i * P k
```

(or the equivalent reindexed / forward version compatible with the chosen
corner-transition convention).

I got very close to a proof by combining

- orthogonal-projection partition of unity,
- `pairwise_mul_zero_of_orthogonalProjection_sum_one`, and
- `eq_zero_of_sum_mul_conjTranspose_eq_zero`

but the library still lacks this as a packaged reusable theorem, and the exact
indexing/orientation has to be nailed down carefully together with the
staircase definition. In other words: the compressed blocked letters can be
exposed pointwise, but the API still does not provide the exact one-site shift
lemma needed to turn them into the ambient Eq. A.8 staircase tensor in a clean,
reusable way.

### 3. #609 remains blocked even after that by a separate contraction lemma gap

Suppose the Eq. A.8 pointwise staircase bridge were added. The proof of
`repeatedBlocks_of_blockedSectorGaugePhase` still needs the paper’s
`Ω_u`-contraction argument from Eq. A.14–A.18. The current chain API provides

- `decompositionMap` / right inverses in `MPS/Chain/OneSidedInverse.lean`, and
- the **two-site** proportionality theorem `tensor_proportional` in
  `MPS/Chain/TensorEquality.lean`.

What is still missing is a reusable **m-factor / cyclic repeated-block
contraction theorem** (or an equivalent generalized tensor-proportionality
lemma) that packages the paper’s repeated blocked product cancellation around
the full cycle. Without that, #609 is still not honestly dischargeable in a
small local patch.

## Bottom line

I do **not** see an honest path to closing both target `sorry`s within the
requested file-local scope and without introducing fresh admitted helpers.

The blocker has become more precise than in the older audit notes:

1. **Expose the pointwise compression identity publicly** in the cyclic-sector
   construction chain (`CyclicSectors` / `Assembly`).
2. **Add a clean one-site cyclic transition theorem**
   (`P (k + 1) * A i = A i * P k`, or the exact reindexed equivalent used by the
   staircase convention), and then use it to prove the true Eq. A.8 theorem in
   `Overlap` / `CornerTransition`.
3. **Add an m-cycle contraction / phase-telescoping lemma** packaging the
   `Ω_u` argument needed for #609.

Only after (1)–(3) land do #608 and #609 become routine downstream bridge
proofs.

## Files touched in the abandoned local experiment

These source edits were intentionally **reverted** before writing this note, so
this branch currently contains only the audit artifact.

The temporary experiment touched:
- `TNLean/MPS/CanonicalForm/CyclicSectors.lean`
- `TNLean/MPS/CanonicalForm/Assembly.lean`
- `TNLean/MPS/Periodic/CornerTransition.lean`
- `TNLean/MPS/Periodic/Overlap.lean`

The reverted experiment is still useful conceptually: it shows that the
pointwise compression field is feasible, but it is not enough by itself to
finish the two Tier-A bridge theorems.

## Recommended next issue split

A clean serialization now looks like:

1. **Compression-pointwise API PR**
   - expose `(φ (C i)).1 = A i` and its blocked-sector corollaries
2. **One-site cyclic-shift / Eq. A.8 PR**
   - package the exact one-site relation and prove the staircase theorem
3. **Repeated-block contraction PR**
   - add the m-cycle `Ω_u` / phase telescope lemma
4. Retry **#608** and **#609** on top of those two infrastructure PRs

No Lean source changes are committed on this branch at the time of writing this
note.
