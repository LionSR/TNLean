# Cyclic-sector block-decomposition ladder: 2026-08-27 collapse

The cyclic-sector directory carried a five-rung ladder of block-decomposition
existence statements. Each rung is the rung above it with one conjunct of the
conclusion forgotten, and each is proved by destructuring the rung above and
repackaging the surviving components. The top of the ladder is the pair

* `MPSTensor.exists_blockDecomp_of_commuting_projections_with_letter_and_isometry`
  (`TNLean/MPS/CanonicalForm/CyclicSectors/CommutingProj.lean`), and
* `MPSTensor.exists_blockDecomp_of_adjoint_fixed_projections_with_letter_and_isometry`
  (`TNLean/MPS/CanonicalForm/CyclicSectors/FixedAdjoint.lean`),

which is live — it is consumed at
`TNLean/MPS/CanonicalForm/SectorComparison/CyclicSectorRelation.lean` — and is
the pair the blueprint tags in
`blueprint/src/appendix/ft_mps/ch09_canonical_blocking_and_sectors.tex`.

Below that pair, three rungs had no consumer at all outside the ladder itself.
This audit records their removal.

## Removed

| Removed | Replacement |
| --- | --- |
| `MPSTensor.exists_blockDecomp_of_commuting_projections` (`TNLean/MPS/CanonicalForm/CyclicSectors/CommutingProj.lean`) | `MPSTensor.exists_blockDecomp_of_commuting_projections_with_letter` (same file), whose conclusion adds the corner-letter identity |
| `MPSTensor.exists_blockDecomp_of_adjoint_fixed_projections` (`TNLean/MPS/CanonicalForm/CyclicSectors/FixedAdjoint.lean`) | `MPSTensor.exists_blockDecomp_of_adjoint_fixed_projections_with_letter_and_isometry` (same file) |
| `MPSTensor.exists_blockDecomp_of_adjoint_fixed_projections_with_letter` (`TNLean/MPS/CanonicalForm/CyclicSectors/FixedAdjoint.lean`) | `MPSTensor.exists_blockDecomp_of_adjoint_fixed_projections_with_letter_and_isometry` (same file) |

Each removed statement is its surviving neighbour with hypotheses unchanged and
one conjunct dropped from the existential body: the commuting-projection rung
and the letter-level adjoint rung each forget the corner-letter identity
\(\varphi_k(B_k^{(i)}) = P_k A_i P_k\), and the adjoint rung additionally
forgets the support isometries \(V_k\) with \(V_k^\dagger V_k = 1\),
\(V_kV_k^\dagger = P_k\) and \(\varphi_k(X) = V_kXV_k^\dagger\). Recovering a
removed statement from its replacement is one `obtain` and one anonymous
constructor, which is why no transition declaration is provided.

## Why no deprecation alias

All three are pass-throughs in the sense of the repository-local exception in
`docs/project_conventions.md` §Style: each merely forgets components of a
neighbouring theorem proved in the same file, and each had zero call sites
outside the ladder. The only reference to the commuting-projection rung came
from the adjoint rung, and the only reference to the letter-level adjoint rung
came from nothing at all; both referring sites are removed in the same change.
None of the three names appears in a blueprint `\lean{...}` tag, so no tag was
redirected.

## Module documentation adjusted

The `## Main declarations` lists of both edited modules named the removed rungs
and omitted the surviving isometry rungs, so each list was rewritten to name
the survivor rather than merely shortened. The hand-written directory waypoint
`TNLean/MPS/CanonicalForm/CyclicSectors.lean` cited the two removed names in
its `## Main statements` prose; both citations were repointed at the surviving
isometry statements.

## Residue

`MPSTensor.exists_blockDecomp_of_commuting_projections_with_letter` survives
this change with no remaining Lean consumer: its last consumer was the adjoint
letter rung removed here. It is retained because it is the natural
isometry-free reading of the top rung and its removal is a separate judgement
call about what the directory offers as public API.
