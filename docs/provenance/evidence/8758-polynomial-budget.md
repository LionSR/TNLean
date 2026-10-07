# Polynomial factors in the dyadic numerical budget

For every real exponent p, the weight (k+1)^p 2^(-δ₀ k/2) is eventually
bounded by 2^(-δ₀ k/4), is summable over nonnegative integer scales, and has
one positive bound on every finite subsum. The threshold and bound depend
only on p and the fixed exponent, independently of the domain, cut, origin,
radius and initial scale. Negative real exponents and empty finite sets are
included.

These are auxiliary numerical estimates used in OpenAI, *A two-dimensional
area law from a global spectral gap*, September 24, 2026, Section 11,
`geometry:total-repairs`, lines 668–692; polynomial absorption also appears
in lines 232–235. The pinned source is
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No upstream Lean proof text is reused.

The three results do not bound descendants of actual marks, construct
repairs, or compare repair counts with the convergent series. The full
`geometry:total-repairs` statement and both manuscript headline theorems
remain open.

## Exact source and canonical evidence

The verified source is `5652d02446787ee2b9248db1057df48adbe32492`, in
[TNLean #8848](https://github.com/LionSR/TNLean/pull/8848).
The mathematical module is byte-identical to the initial source
`2967bd3858ab0beefff6a9906ccca39eab3c28dc`.

| Check | Command | Result | Elapsed seconds |
|---|---|---|---|
| Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Exit 0 | 6.553 |
| Imported-declaration audit | `lake env lean docs/provenance/evidence/8758-polynomial-budget-axioms.lean` | Exit 0 | 3.443 |

The new leaf compiled in 2.4 seconds without warnings. The audit prints the
three exact imported theorem names; every dependency is one of `propext`,
`Classical.choice` and `Quot.sound`. No placeholder or prohibited proof
mechanism occurs in the contribution.

Both commands ran consecutively through the own-worktree
`scripts/lake_build_locked.sh --` under the shared repository lock, immediately
after the adjacent scale-separation check. Each contribution records its own
frozen revision. The warmed cache and pinned prebuilt Mathlib artifacts were
reused, without a local full-library or Mathlib source build, and waiting
for the lock consumed no CPU.

Committed evidence hashes:

- `8758-polynomial-budget-build.log`: `8422ee4d6dfeaed3c46b44a5c247e03b68f68890ea52df4c25a5b7c3f8565067`.
- `8758-polynomial-budget-axioms.log`: `30d19278dde6d52c59eba12cda2b0a30b87c4d80bc42cc7e6111a1cf3c245cf3`.

The logs include command, revision, elapsed time and exit code. Trailing
whitespace alone is removed from captured output. This promotion changes
only the three new provenance rows, leaving the other 185 rows and all
previous evidence unchanged. Complete current-policy validation includes
exact source, license, notices, log hashes and quoted axiom output.

## Integration checks

Non-mutating Lean elaboration with the package flags and independent
mathematical/source review passed before integration. Generated imports and
whitespace checks pass. Full blueprint source synchronization against the
exact pinned QICLean sources reports 20,142 distinct references and 20,136
theorem-like entries. The proof-pattern scan found no repeated block in the
new module.

Full-library and compiled blueprint checks are tracked in
[the source workflow](https://github.com/LionSR/TNLean/actions/runs/37651699227)
and subsequent checks on the published draft. They were queued at the time
this local evidence was recorded on October 7, 2026; their outcome is reported
separately on the pull request.
