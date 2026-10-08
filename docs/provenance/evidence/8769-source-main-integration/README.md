# Source constructions integrated with accepted main

This record concerns TNLean source revision
`17a29d2363acb4d040ce3360c2aef7c20ec1a645` and QICLean dependency revision
`4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0`. It brings the previously verified
source constructions together with accepted main. It introduces no new
mathematical theorem. The integrated statements construct common finite source
spaces, retain actual source occurrences and local branch labels, separate
operations by their participating parties, and expand the actual chronological
circuit. This integration does not establish the distributed compression theorem,
the polynomial PEPS theorem, or the ground-state area law.

The merge preserves all 142 changed mathematical source files from its two
parents, byte for byte. An independent comparison checked both Git object
identities and the recorded SHA256 values. The 2,927 unaffected modules also
agree exactly with accepted-main revision
`80bc49d17e833795fba00bfeaf1bd053649c4070`. These and the 66 selected modules
partition the 2,993 production modules outside the archive. The affected
import closure was independently recomputed; the unchanged predecessor record
identifies the reused artifacts. These comparisons do not replace a Lean check.

All 66 selected modules were checked directly with Lean, using the package
options, the mathematical style linters, and warnings as errors. Every command
returned zero without diagnostics; their total recorded time was 585.207 seconds.
The final QIC dependency adds the five accepted Schur-label modules and their
import list. Only the TNLean dependency interface and root import list are
affected within TNLean. They were checked again against the final dependency in
23.490 and 14.864 seconds, respectively. The mathematical TNLean sources did not
change. This was direct Lean verification with prebuilt dependencies; no local
Lake build, Mathlib rebuild, or CI timing is claimed.

After the final dependency update, the importing kernel audit checked all 342
public declarations from the ten source-construction contributions. Every axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`. The record
identifies and hashes all 14,616 imported artifacts. A separate direct Lean check
imports the integrated root and tests the presence of all 20,810 names in the
complete blueprint declaration list. This is an actual imported declaration
check, but it is not an invocation of `leanblueprint checkdecls`. Its first
generated checker failed the long-line style linter; shortening its file paths
resolved that failure without disabling the linter or changing any proof source.
Both attempts are retained.

The full provenance check passed for all 518 entries. An earlier invocation of
the historical ten-contribution replay failed because it scanned notices from
the merged main branch while loading only those ten contributions. The rejected
notice belonged to the additional distributed-operator contribution. The full
repository checker includes that contribution and passed. Both commands and
outputs are retained; the narrower replay is not represented as successful.

The blueprint source check passed for 20,804 recorded entries, yielding the
20,810-name declaration list checked above. Every one of the 342 incoming public
names occurs once in the focused chapters. The full source dependency graph has
7,656 nodes and 18,831 edges, with no duplicate labels or cycles. The complete
input routing has 55 entries, no duplicate inputs or missing files, and includes
all eleven incoming chapters. The focused rendering produced a 30-page PDF;
the browser check passed on seven pages containing 2,623 typeset elements.
The final PDF pages 27, 29, and 30 were visually inspected; the preceding
incoming chapters retain their previously inspected content.

The first focused web attempt retained a graph selection for an unrelated
chapter and reported its absent label. The focused configuration now selects
the source-partition graph; the original configuration and diagnostic are
retained, while the complete source graph is checked separately. The first
browser attempt lacked the installed blueprint Python package on its search
path. The corrected command supplied that path and passed. These were focused
rendering environment failures, not failed mathematical declarations.

The render was performed before the final dependency-pin commit. Its 2,997
TNLean source files (including the archive), 828 QICLean source files, and 632
tracked blueprint inputs were subsequently compared with the final revisions
and are unchanged. Only the two dependency-pin files in the disposable snapshot
were refreshed. The initial revision metadata and final comparison are both
retained; no second rendering is claimed.

QICLean's separate, immutable
[dependency integration record](https://github.com/LionSR/QICLean/tree/4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0/docs/provenance/evidence/pepsSourceLatestMainIntegration)
contains its complete build and blueprint checks. Its mathematical source is
`035e5cc6f208e7b069132ef8eff8c8afbfa012d9`. The local reference records exact
hashes of its manifest, verification summary, and explanatory note; those checks
are not described as newly performed by TNLean.

`manifest.json` binds the files in this directory, and `compression.json` binds
each deterministic gzip copy to its uncompressed bytes. The command records
preserve the actual paths used during verification. No compiled dependency
artifacts are copied into this evidence directory. To verify the recorded
hashes and their agreement with the current source tree, run from the repository
root:

```sh
python3 docs/provenance/evidence/8769-source-main-integration/validate-evidence.py --root .
```

This validates the evidence and source bytes; it does not rerun Lean, the
provenance checker, or the blueprint renderer. The exact original verification
scripts are included separately. The long importing audit is preserved as
`imported-audit/Axioms.lean.gz`; decompress it to `Axioms.lean` before replaying
its recorded command. Compression preserves the exact verified bytes and
keeps this historical evidence outside the production Lean file-length check.
