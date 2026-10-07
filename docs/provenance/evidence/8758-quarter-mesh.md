# Affine-mesh clearance and local layer exclusion: verification pending

These six proposed declarations establish the numerical mesh and layer
estimates used in the initial-star argument. All distances below are measured
in the sup norm on the plane.

For an origin \(o\in\mathbb R^2\) and a real spacing \(q\), the translated
mesh is

\[
\mathcal M(o,q)=\{o+qz:z\in\mathbb Z^2\}.
\]

The actual nine marks of any finite collection of dyadic cells of side
\(2^j\) lie in \(\mathcal M(o,2^\ell/4)\) whenever \(\ell\le j+1\).
For \(q>0\), distinct mesh points have distance at least \(q\). If
\(u,v,x\) belong to the mesh, the displacement \(v-u\) has horizontal,
vertical or diagonal slope, and \(x\) lies outside the affine span
\(L=\operatorname{aff}_{\mathbb R}\{u,v\}\), then

\[
\|x-y\|_\infty\ge q/2\qquad(y\in L).
\]

The case \(u=v\), in which the affine span is a single point, is included.
For the quarter mesh \(q=t/4\), these estimates give separation \(t/4\)
and clearance \(t/8\).

Write \(t_k=2^{\lfloor\zeta_0k\rfloor}\). For \(C\ge2\) and
\(k\ge50{,}000{,}000\), let \(x\in\overline{D_k}\) and
\(y\in\overline{D_h}\), where the closed dyadic layers have the same
origin, finite endpoint set and parameter \(C\). If \(k+2\le h\) or
\(h+2\le k\), then

\[
\|x-y\|_\infty\ge16t_k.
\]

Consequently, \(\|x-y\|_\infty<10t_k\) implies
\(h\le k+1\) and \(k\le h+1\). The index threshold is uniform in
\(h\), the origin, the endpoint set and the points. No nonemptiness
hypothesis is imposed on the endpoint set.

## Source, attribution and scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The mesh estimates are the numerical step in the proof of
`geometry:initial-stars`, lines 352–359, within the proof of
`prop:two-families`. Local layer exclusion uses lines 352–356, the earlier
`geometry:nonadjacent` estimate in lines 193–204, and the scale definitions
and comparison in lines 200–207. The explicit threshold and constants are
stated in separate blueprint entries for these numerical consequences.

The proofs are independently written; no upstream Lean source or proof text
is reused. OpenAI Codex (GPT-6) assists LionSR under the existing
[TNLean #8758 mesh claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044056435)
and its
[local-layer extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6044139454).

The remaining geometric construction includes active interfaces, fan coloring,
minimum incident-scale assignment to marks, isolated stars, contact completeness,
repairs, descendant counts and the complete two-family partition. The present
numerical consequences do not establish the isolated-star lemma or either
manuscript headline theorem.

## Proposed exact inventory

`TNLean/PEPS/AreaLaw/Geometry/MeshGeometry.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.affineMesh`;
- `TNLean.PEPS.AreaLaw.Geometry.beltMarks_subset_affineMesh`;
- `TNLean.PEPS.AreaLaw.Geometry.affineMesh_dist_ge`;
- `TNLean.PEPS.AreaLaw.Geometry.affineMesh_line_dist_ge`.

`TNLean/PEPS/AreaLaw/Geometry/LocalLayers.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_dist_nonadjacent_fineScale`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_nearby_indices`.

The combined shard is `docs/provenance/openai-math.d/8758-quarter-mesh.json`.
Its six entries remain planned, with proposed names and pending verification.
The immutable prior inventory contains 215 entries at
`98d26cdad5e212a7e241951618dd3645f3ae6b21`, including the previously existing
planned root-ledger entry. Every prior shard and its evidence must remain
unchanged. The completed primary-region, primary-count and belt-mark entries
retain their verified source revisions and actual logs.

## Canonical evidence to be recorded

Exact frozen source revision: **Pending**.
Published pull request and evidence head: **Pending**.

| Check | Expected command | Result | Elapsed seconds |
|---|---|---|---|
| Combined Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | Pending | Pending |
| Imported six-name audit | `lake env lean docs/provenance/evidence/8758-quarter-mesh-axioms.lean` | Pending | Pending |

Canonical commands must run from the warmed TNLean worktree through
`scripts/lake_build_locked.sh`, under the shared repository lock and with the
pinned prebuilt Mathlib artifacts. The source-only preparation worktree
performs no cache or build operation. Optional direct elaboration uses the
warmed environment and is recorded separately from the canonical target.

The final record must identify actual commands, frozen source, elapsed times,
exit codes, module diagnostics and SHA256 hashes of
`8758-quarter-mesh-build.log` and `8758-quarter-mesh-axioms.log`. Any
normalization of captured whitespace must be described. The exact audit
prints all six selected imported public names. Their actual dependencies
are recorded after the audit completes.

Static collection/schema/pinned-source/license validation has passed for 221
entries with the six proposed rows supplied outside the worktree. All prior
215 entries remain byte-identical. Exact six-name source, notice and audit
inventory validation: **Passed** against the current complete source. All six
blueprint declaration tags are distinct and match the proposed inventory.
The committed frozen revision and its canonical checks remain pending.

Promotion updates only the six new rows after the exact committed-source
build, imported-name audit and complete 221-entry validation pass. The
promotion helper performs static checks only and writes its reviewed output
in `/tmp`.

Independent mathematical review of the complete contribution: **Pending**.
Blueprint source synchronization and reverse coverage: **Pending**.
Generated imports, prose and formatter checks: **Pending**.
Full-library CI, compiled blueprint declarations and rendering: **Pending**.

The earlier primary-region work recorded a whole-library local
`leanblueprint checkdecls` failure caused by a missing pre-existing
`Fibonacci.olean` artifact. That historical failure log remains intact.
A repeated local whole-library check is not required for this changed-module
verification; complete compiled blueprint checking and rendering are tracked
separately in CI.
