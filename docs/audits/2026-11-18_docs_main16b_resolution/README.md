# Six-document conflict resolution against main16b

Fixed parents:42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d and16b1dfbd7e45f0e8fed7f2607e25313cf5a9f931. Fetched main was exactly16b, already containing the10905 migration. No migration replayed. git merge-tree produced4059286841126d67a51e1ec2a55f1950cd692d69. Only the six assigned candidate blobs were loaded into a new independent worktree; no merge state completed or other family's content staged.

All seven conflicts resolve to existing42c4 content. Each conflict was compared, rather than selecting whole files blindly: resolution.json records each reason and the main changes already retained. Whole resolved candidate blobs equal42c4, including automatic merge neighbors. Thus there is no document content delta to cherry-pick relative42c4. This evidence-only child commit supplies exact final hashes and resolve-fixed-candidate.patch for the fixed conflicted merge candidate. The integrator may instead restore precisely the six listed document paths from this commit into its merge worktree. Do not restore other paths from this branch.

Preserved: e740 D₀:Nat safety parameter, hbox and0<1+e; zero-gap norm/PSD/canonical membership; Box size-one versus empty physical intersection distinction; F12 historical audit account. Model term hypotheses remain explicit, while rectangle total-Hermitian transport is not strengthened to termwise Hermitian. No production, fixture or dependency file changed.

Light verification: six exact byte comparisons imply all prior labels, citations, Lean references and formulas retained. No unmerged markers remain in those six files. The patch deliberately contains conflict-marker lines as deleted context. Final staged diff whitespace check passed. No Lean/PDF build or source-sync was run: source-sync belongs on the fully combined tree. Historical976-missing failure is not reported as success. Resource check:12GiB available, original checkout clean; no original source queue or cache modified.

The zero-context patch was independently applied with `git apply --unidiff-zero` to copies of all six conflicted blobs; all six outputs matched the final hashes. Use that flag when applying this patch.
